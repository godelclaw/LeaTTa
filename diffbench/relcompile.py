#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""relcompile: certified delegation lane for the relational MeTTa fragment.

compileExpr (classic functional-logic flattening): MeTTa equality rules become
Prolog clauses `f(Args..., Result)`; function calls in patterns/exprs flatten
to body goals with fresh result variables (narrowing); tuples become lists;
`cons` is the list constructor relation; `and`/`or`/`not`/`==` are truth-table
relations; 2-arg `if` is a `cond=True` goal; 3-arg `if` and `case` become aux
predicates; `once` maps to committed choice in the meta-interpreter.

swipl FINDS (native SLD over the compiled clauses, one trace per answer);
Lean CHECKS (checktrace certifies every answer); the certified answer bag is
compared against native PeTTa's output. Verdicts:
  DELEGATED-CHECKED  all bangs compiled, every answer certified, bag agrees
  DELEGATED-DIFF     certified but bag differs from petta
  PERF-PROXY-AGREE  direct SWI clauses agree with PeTTa; not coverage
  PERF-PROXY-DIFF   direct SWI clauses terminate but differ from PeTTa
  NO-COMPILE         outside the v1 pure fragment (reason reported)
"""
import os
import collections
import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D

MI_PL = pathlib.Path(
    str(pathlib.Path(os.environ.get("ALGOS_LP_DIR", str(pathlib.Path.home()/"repos/MeTTapedia-algos-fix/lean/algos-lp"))) / "prolog/mi.pl"))
CHECKTRACE = pathlib.Path(
    str(pathlib.Path(os.environ.get("ALGOS_LP_DIR", str(pathlib.Path.home()/"repos/MeTTapedia-algos-fix/lean/algos-lp"))) / ".lake/build/bin/checktrace"))
PETTA_LIB = pathlib.Path(os.environ.get("PETTA_DIR", str(pathlib.Path.home()/"repos/PeTTa"))) / "lib"

# ---------------- MeTTa parsing ----------------

def tokenize(text):
    toks = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch in "()":
            toks.append(ch)
            i += 1
            continue
        if ch == '"':
            j = i + 1
            esc = False
            while j < n:
                c = text[j]
                if esc:
                    esc = False
                elif c == "\\":
                    esc = True
                elif c == '"':
                    j += 1
                    break
                j += 1
            toks.append(text[i:j])
            i = j
            continue
        j = i
        while j < n and (not text[j].isspace()) and text[j] not in "();":
            j += 1
        toks.append(text[i:j])
        i = j
    return toks

def parse_all(text):
    toks = tokenize(text)
    forms, i = [], 0
    def rec(i):
        if toks[i] == "(":
            out, i = [], i + 1
            while toks[i] != ")":
                node, i = rec(i)
                out.append(node)
            return out, i + 1
        return toks[i], i + 1
    while i < len(toks):
        f, i = rec(i)
        forms.append(f)
    return forms

def is_var(t): return isinstance(t, str) and t.startswith("$")

def psym(name):
    parts = []
    for ch in name:
        if ch.isalnum() or ch == "_":
            parts.append(ch)
        else:
            parts.append(f"_x{ord(ch):02x}_")
    s = "".join(parts) or "sym"
    if not re.match(r"[a-z]", s):
        s = "fn_" + s
    return s

def raw_to_forms(raw):
    forms, i = [], 0
    while i < len(raw):
        if raw[i] == "!" and i + 1 < len(raw):
            forms.append(["!", raw[i + 1]])
            i += 2
        else:
            forms.append(raw[i])
            i += 1
    return forms

def import_file(expr, base_dir=None):
    if not (isinstance(expr, list) and len(expr) >= 3 and expr[0] == "import!"):
        return None
    target = expr[2]
    if isinstance(target, list) and len(target) == 2 and target[0] == "library":
        return PETTA_LIB / (target[1] + ".metta")
    if isinstance(target, str) and target.startswith("../lib/"):
        p = PETTA_LIB / pathlib.Path(target).name
        return p if p.suffix else p.with_suffix(".metta")
    if isinstance(target, str) and base_dir is not None and not target.startswith("/"):
        p = pathlib.Path(base_dir) / target
        return p if p.suffix else p.with_suffix(".metta")
    return None

# ---------------- Compiler ----------------

BUILTIN_RELS = {
    "append": (
        "append_r([], B, B).",
        "append_r([H|T], B, [H|R]) :- append_r(T, B, R)."),
    "cons": ("cons_r(H, T, [H|T]).",),
    "member": (
        "member_r(X, [X|T0], 'True').",
        "member_r(X, [H0|T], R) :- member_r(X, T, R)."),
    "and": (
        "and_r(A,B,C) :- bool_norm(A, AN), bool_norm(B, BN), and_norm(AN, BN, C).",
        "bool_norm('True', true).", "bool_norm(true, true).",
        "bool_norm('False', false).", "bool_norm(false, false).",
        "and_norm(true, true, true).", "and_norm(true, false, false).",
        "and_norm(false, true, false).", "and_norm(false, false, false)."),
    "or": (
        "or_r(A,B,C) :- bool_norm(A, AN), bool_norm(B, BN), or_norm(AN, BN, C).",
        "bool_norm('True', true).", "bool_norm(true, true).",
        "bool_norm('False', false).", "bool_norm(false, false).",
        "or_norm(true, true, true).", "or_norm(true, false, true).",
        "or_norm(false, true, true).", "or_norm(false, false, false)."),
    "not": (
        "not_r(A,B) :- bool_norm(A, AN), not_norm(AN, B).",
        "bool_norm('True', true).", "bool_norm(true, true).",
        "bool_norm('False', false).", "bool_norm(false, false).",
        "not_norm(true, false).", "not_norm(false, true)."),
    "ueq": ("ueq_r(X, X, 'True').",),
    "ueq2": ("ueq2_r(X, X).",),
    "istrue": ("istrue_r('True').", "istrue_r(true)."),
}
FN_ARITY = {"append": 2, "cons": 2, "member": 2, "is-member": 2,
            "and": 2, "or": 2, "not": 1}
FN_ALIAS = {"is-member": "member"}
ROMAN_SET_OPS = {
    "/=\\": ("intersect", "="),
    "/==\\": ("intersect", "=="),
    "/=a\\": ("intersect", "=alpha"),
    "\\=": ("subtract", "="),
    "\\==": ("subtract", "=="),
    "\\=a": ("subtract", "=alpha"),
    "\\=/": ("union", "="),
    "\\==/": ("union", "=="),
    "\\=a/": ("union", "=alpha"),
}
# engine/space/nondet ops outside the pure SLD fragment -> NO-COMPILE (honest)
ENGINE_OPS = {"superpose", "new-space", "bind!", "match", "add-atom", "remove-atom",
              "bind!", "new-space", "msort", "car-atom", "cdr-atom",
              "cons-atom", "size-atom", "index-atom", "quote", "eval", "chain",
              "unify", "function", "return", "println!", "trace!", "get-type",
              }
ARITH_FN = {"+": "plus", "-": "minus", "*": "times", "#+": "plus", "#-": "minus",
            "/": "idiv", "%": "imod",
            ">": "cmp_gt", "<": "cmp_lt", ">=": "cmp_ge", "<=": "cmp_le",
            "min": "min_native", "max": "max_native"}

def metta_vars(e, acc=None):
    if acc is None: acc = []
    if is_var(e):
        if e not in acc: acc.append(e)
    elif isinstance(e, list):
        for x in e: metta_vars(x, acc)
    return acc

def prolog_conj(goals):
    if not goals:
        return "true"
    if len(goals) == 1:
        return goals[0]
    return "(" + ", ".join(goals) + ")"

class NoCompile(Exception): pass

class Compiler:
    def __init__(self, rules, native=False):
        self.rules = rules              # name -> [(params, rhs)]
        self.native = native
        self.aux = []                   # extra clauses (text later)
        self.used_rels = set()
        self.facts = []                 # (name, [prolog terms]) ground facts
        self.committed = []
        self.native_fns = set()
        self.fresh_n = 0
        self.aux_n = 0

    def fresh(self):
        self.fresh_n += 1
        return f"F{self.fresh_n}"

    def pvar(self, v):  # $xY -> XY-ish uppercase, keep unique
        return "V_" + re.sub(r"[^A-Za-z0-9_]", "_", v[1:])

    def const(self, t):
        if re.fullmatch(r"-?\d+", t): return t
        if re.fullmatch(r"-?\d+\.\d+", t): return t
        return "'" + t.replace("\\", "\\\\").replace("'", "\\'") + "'"

    def compile_data(self, e, literal_vars=False):
        if is_var(e):
            return self.const(e) if literal_vars else self.pvar(e)
        if isinstance(e, str):
            return self.const(e)
        if not e:
            return "[]"
        return "[" + ", ".join(self.compile_data(a, literal_vars=literal_vars) for a in e) + "]"

    def compile_pattern(self, e, goals):
        if isinstance(e, list) and e:
            h = e[0]
            if not isinstance(h, str) or is_var(h) or (
                h not in ARITH_FN and h not in ENGINE_OPS and not self.is_fn(h)
            ):
                return "[" + ", ".join(self.compile_pattern(a, goals) for a in e) + "]"
        return self.compile_expr(e, goals)

    def rel(self, name):
        self.used_rels.add(name)
        return name + "_r"

    def is_fn(self, h):
        return isinstance(h, str) and (h in self.rules or h in self.native_fns or h in FN_ARITY)

    def fn_arities(self, h):
        if h in FN_ARITY:
            return {FN_ARITY[h]}
        return {len(params) for params, _rhs in self.rules.get(h, [])}

    def compile_call_with_result(self, e, result, goals):
        if not (isinstance(e, list) and e and isinstance(e[0], str)):
            return False
        h = e[0]
        if h in ARITH_FN:
            args = [self.compile_expr(a, goals) for a in e[1:]]
            if len(args) == 1 and h in ("+", "-"):
                args = ["0", args[0]]
            if len(args) != 2:
                raise NoCompile(f"arith {h} arity {len(args)}")
            goals.append(f"{ARITH_FN[h]}({args[0]}, {args[1]}, {result})")
            if not hasattr(self, "arith_vars"): self.arith_vars = set()
            self.arith_vars.add(result)
            return True
        if self.is_fn(h):
            args = [self.compile_expr(a, goals) for a in e[1:]]
            rel = (self.rel(FN_ALIAS.get(h, h)) if h in FN_ARITY
                   else psym(h) + "_f")
            goals.append(f"{rel}({', '.join(args + [result])})")
            return True
        return False

    def compile_set_arg(self, e, goals):
        if isinstance(e, list) and e and isinstance(e[0], str) and is_var(e[0]):
            return self.compile_data(e)
        return self.compile_expr(e, goals)

    def compile_expr(self, e, goals):
        """Compile expression e; append goals; return Prolog term string."""
        if is_var(e): return self.pvar(e)
        if isinstance(e, str): return self.const(e)
        if not e: return "[]"
        h = e[0]
        if self.native and isinstance(h, str) and h in ROMAN_SET_OPS:
            if len(e) != 3:
                raise NoCompile(f"{h} arity")
            mode, pred = ROMAN_SET_OPS[h]
            left = self.compile_set_arg(e[1], goals)
            right = self.compile_set_arg(e[2], goals)
            r = self.fresh()
            goals.append(f"roman_set_native({self.const(mode)}, {self.const(pred)}, {left}, {right}, {r})")
            return r
        if h == "if":
            return self.compile_if(e, goals)
        if h == "let":
            _, pat, val, body = e
            vterm = self.compile_expr(val, goals)
            if not self.compile_call_with_result(pat, vterm, goals):
                pterm = self.compile_pattern(pat, goals)  # fn-call pattern narrows
                goals.append(f"{self.rel('ueq2')}({pterm}, {vterm})")
            return self.compile_expr(body, goals)
        if h == "let*":
            _, binds, body = e
            for bind in binds:
                if not (isinstance(bind, list) and len(bind) == 2):
                    raise NoCompile("let* binding shape")
                pat, val = bind
                vterm = self.compile_expr(val, goals)
                if not self.compile_call_with_result(pat, vterm, goals):
                    pterm = self.compile_pattern(pat, goals)
                    goals.append(f"{self.rel('ueq2')}({pterm}, {vterm})")
            return self.compile_expr(body, goals)
        if h == "match":
            if len(e) != 4:
                raise NoCompile("match arity")
            pat, ret = e[2], e[3]
            if self.native:
                pterm = self.compile_data(pat)
                bgoals = []
                rtmpl = self.compile_pattern(ret, bgoals)
                rv = self.fresh()
                goals.append(f"match_native({pterm}, {rtmpl}, {rv})")
                goals.extend(bgoals)
                return rv
            if not (isinstance(pat, list) and pat and isinstance(pat[0], str)):
                raise NoCompile("non-atom match pattern")
            pargs = [self.compile_expr(a, goals) for a in pat[1:]]
            self.used_facts = getattr(self, "used_facts", set()); self.used_facts.add(pat[0])
            goals.append(f"fact_{psym(pat[0])}({', '.join(pargs)})")
            return self.compile_expr(ret, goals)
        if h == "find" and self.native:
            if len(e) != 3:
                raise NoCompile("find arity")
            pat = self.compile_data(e[2])
            r = self.fresh()
            goals.append(f"find_native({pat}, {r})")
            return r
        if h == "for-each-in-atom" and self.native:
            if len(e) != 3:
                raise NoCompile("for-each-in-atom arity")
            if e[2] == "println!":
                xs = self.compile_expr(e[1], goals)
                r = self.fresh()
                goals.append(f"for_each_println_native({xs}, {r})")
                return r
        if h == "add-unique-or-fail" and self.native:
            if len(e) != 3:
                raise NoCompile("add-unique-or-fail arity")
            x = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"add_unique_native({x}, {r})")
            return r
        if h == "add-unique-item-or-empty" and self.native:
            if len(e) != 2:
                raise NoCompile("add-unique-item-or-empty arity")
            return self.compile_data(e)
        if h in ("add-atom", "remove-atom"):
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile(f"{h} arity")
            atom = e[2]
            r = self.fresh()
            if h == "add-atom" and isinstance(atom, list) and len(atom) == 3 \
                    and atom[0] == "=" and isinstance(atom[1], list) and atom[1]:
                fname = atom[1][0]
                self.native_fns.add(fname)
                head, rgoals = self.compile_rule(fname, atom[1][1:], atom[2])
                goals.append(f"assertz(({head} :- {prolog_conj(rgoals)}))")
                goals.append(f"add_atom_native({self.compile_data(atom)}, {r})")
            else:
                op = "add_atom_native" if h == "add-atom" else "remove_atom_native"
                goals.append(f"{op}({self.compile_data(atom)}, {r})")
            return r
        if h == "add-reduct":
            if not self.native:
                raise NoCompile("engine op add-reduct outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile("add-reduct arity")
            atom = e[2]
            if isinstance(atom, list) and len(atom) == 3 and atom[0] == "=":
                rhs = self.compile_expr(atom[2], goals)
                goals.append(f"assertz(space_fact(['=', {self.compile_data(atom[1])}, [{rhs}]]))")
                return self.const("true")
            return f"['add-reduct', {self.compile_data(e[1])}, 'false']"
        if h == "case":
            return self.compile_case(e, goals)
        if h == "eval":
            if not self.native:
                raise NoCompile("engine op eval outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("eval arity")
            return self.compile_expr(e[1], goals)
        if h == "trace!":
            if not self.native:
                raise NoCompile("engine op trace! outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile("trace! arity")
            return self.compile_expr(e[2], goals)
        if h == "progn" and self.native:
            if len(e) < 2:
                raise NoCompile("progn arity")
            r = "[]"
            for expr in e[1:]:
                r = self.compile_expr(expr, goals)
            return r
        if h == "prog1" and self.native:
            if len(e) < 2:
                raise NoCompile("prog1 arity")
            first = self.compile_expr(e[1], goals)
            for expr in e[2:]:
                self.compile_expr(expr, goals)
            return first
        if h == "catch":
            if not self.native:
                raise NoCompile("engine op catch outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("catch arity")
            inner_goals = []
            val = self.compile_expr(e[1], inner_goals)
            rv = self.fresh()
            goals.append(f"catch_eval_native({prolog_conj(inner_goals)}, {val}, {rv})")
            return rv
        if h == "if-error" and self.native and len(e) == 4:
            x = self.compile_expr(e[1], goals)
            then = self.compile_expr(e[2], goals)
            els = self.compile_expr(e[3], goals)
            r = self.fresh()
            goals.append(f"if_error_native({x}, {then}, {els}, {r})")
            return r
        if h == "return-on-error" and self.native and len(e) == 3:
            x = self.compile_expr(e[1], goals)
            els = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"if_error_native({x}, {x}, {els}, {r})")
            return r
        if h == "chain":
            if not self.native:
                raise NoCompile("engine op chain outside pure SLD fragment")
            if len(e) != 4:
                raise NoCompile("chain arity")
            vterm = self.compile_expr(e[1], goals)
            pterm = self.compile_pattern(e[2], goals)
            goals.append(f"{self.rel('ueq2')}({pterm}, {vterm})")
            return self.compile_expr(e[3], goals)
        if h == "unify" and self.native and len(e) == 5 and e[1] != "&self":
            a = self.compile_expr(e[1], goals)
            b = self.compile_expr(e[2], goals)
            cond = self.fresh()
            goals.append(f"eq_native({a}, {b}, {cond})")
            tgoals = []
            tterm = self.compile_expr(e[3], tgoals)
            egoals = []
            eterm = self.compile_expr(e[4], egoals)
            name = f"unifyaux{self.aux_n}"; self.aux_n += 1
            vs = [self.pvar(v) for v in metta_vars(e[1:])
                  if self.pvar(v) not in (cond,)]
            pre = ", ".join(vs) + ", " if vs else ""
            self.aux.append((f"{name}('True', {pre}{tterm})", tgoals))
            self.aux.append((f"{name}('False', {pre}{eterm})", egoals))
            rv = self.fresh()
            goals.append(f"{name}({cond}, {pre}{rv})")
            return rv
        if h == "unify" and self.native and len(e) == 5 and e[1] == "&self":
            pat = self.compile_data(e[2])
            tgoals = []
            tterm = self.compile_expr(e[3], tgoals)
            egoals = []
            eterm = self.compile_expr(e[4], egoals)
            if tgoals or egoals:
                raise NoCompile("unify &self branch goals")
            r = self.fresh()
            goals.append(f"unify_space_native({pat}, {tterm}, {eterm}, {r})")
            return r
        if h == "collapse":
            inner_goals = []
            r = self.compile_expr(e[1], inner_goals)
            vs = [self.pvar(v) for v in metta_vars(e[1])]
            name = f"goalaux{self.aux_n}"; self.aux_n += 1
            self.aux.append((f"{name}({', '.join(vs + [r])})", inner_goals))
            rv = self.fresh()
            goals.append(f"collapse_t({r}, {name}({', '.join(vs + [r])}), {rv})")
            return rv
        if h in ("superpose", "hyperpose"):
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile(f"{h} arity")
            r = self.fresh()
            choices = e[1]
            if isinstance(choices, list):
                if h == "hyperpose":
                    branches = []
                    for choice in choices:
                        cgoals = []
                        cterm = self.compile_expr(choice, cgoals)
                        branches.append(f"({prolog_conj(cgoals)}, {cterm})")
                    goals.append(f"hyperpose_native([{', '.join(branches)}], {r})")
                else:
                    name = f"choiceaux{self.aux_n}"; self.aux_n += 1
                    vs = [self.pvar(v) for v in metta_vars(choices)]
                    pre = ", ".join(vs) + ", " if vs else ""
                    for choice in choices:
                        cgoals = []
                        cterm = self.compile_expr(choice, cgoals)
                        self.aux.append((f"{name}({pre}{cterm})", cgoals))
                    goals.append(f"{name}({pre}{r})")
            else:
                xs = self.compile_expr(choices, goals)
                goals.append(f"member_native({r}, {xs})")
            return r
        if h == "once":
            inner_goals = []
            r = self.compile_expr(e[1], inner_goals)
            vs = [self.pvar(v) for v in metta_vars(e[1])]
            name = f"goalaux{self.aux_n}"; self.aux_n += 1
            self.aux.append((f"{name}({', '.join(vs + [r])})", inner_goals))
            arity = len(vs) + 1
            slots = ", ".join("_" for _ in range(arity))
            self.committed.append(f"committed_pred({name}({slots})).")
            rv = self.fresh()
            goals.append(f"once({name}({', '.join(vs + [rv])}))")
            return rv
        if h == "==":
            return self.compile_eq(e, goals)
        if h == "=alpha" and self.native:
            if len(e) != 3:
                raise NoCompile("=alpha arity")
            a = self.compile_data(e[1])
            b = self.compile_data(e[2])
            r = self.fresh()
            goals.append(f"alpha_eq_native({a}, {b}, {r})")
            return r
        if h == "assert" and self.native:
            if len(e) != 2:
                raise NoCompile("assert arity")
            cond = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"assert_native({cond}, {r})")
            return r
        if h == "=":  # unification-as-expression (PeTTa)
            a = self.compile_expr(e[1], goals)
            b = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"{self.rel('ueq')}({a}, {b}, {r})")
            return r
        if isinstance(h, str) and is_var(h) and self.native:
            if len(e) == 1 or h.startswith("$_"):
                return self.compile_data(e)
            args = [self.compile_expr(a, goals) for a in e[1:]]
            r = self.fresh()
            goals.append(f"call_or_tuple_native({self.pvar(h)}, [{', '.join(args)}], {r})")
            return r
        if h == "empty":
            if self.native:
                goals.append("fail")
                return "[]"
            raise NoCompile("(empty) outside if-else position")
        if h == "msort":
            if not self.native:
                raise NoCompile("engine op msort outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("msort arity")
            xs = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"msort_native({xs}, {r})")
            return r
        if h == "length":
            if not self.native:
                raise NoCompile("engine op length outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("length arity")
            xs = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"length_native({xs}, {r})")
            return r
        if h in ("car-atom", "cdr-atom", "cons-atom", "size-atom", "index-atom"):
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            args = [self.compile_expr(a, goals) for a in e[1:]]
            r = self.fresh()
            if h == "car-atom" and len(args) == 1:
                goals.append(f"car_atom_native({args[0]}, {r})")
            elif h == "cdr-atom" and len(args) == 1:
                goals.append(f"cdr_atom_native({args[0]}, {r})")
            elif h == "cons-atom" and len(args) == 2:
                goals.append(f"cons_r({args[0]}, {args[1]}, {r})")
            elif h == "size-atom" and len(args) == 1:
                goals.append(f"length_native({args[0]}, {r})")
            elif h == "index-atom" and len(args) == 2:
                goals.append(f"index_atom_native({args[0]}, {args[1]}, {r})")
            else:
                raise NoCompile(f"{h} arity")
            return r
        if h == "union-atom":
            if not self.native:
                raise NoCompile("engine op union-atom outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile("union-atom arity")
            left = self.compile_expr(e[1], goals)
            right = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"{self.rel('append')}({left}, {right}, {r})")
            return r
        if h in ("list_to_set", "exclude-item", "sort"):
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            args = [self.compile_expr(a, goals) for a in e[1:]]
            r = self.fresh()
            if h == "list_to_set" and len(args) == 1:
                goals.append(f"list_to_set_native({args[0]}, {r})")
            elif h == "exclude-item" and len(args) == 2:
                goals.append(f"exclude_item_native({args[0]}, {args[1]}, {r})")
            elif h == "sort" and len(args) == 1:
                goals.append(f"sort_native({args[0]}, {r})")
            else:
                raise NoCompile(f"{h} arity")
            return r
        if h == "last":
            if not self.native:
                raise NoCompile("engine op last outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("last arity")
            xs = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"last_native({xs}, {r})")
            return r
        if h == "reverse":
            if not self.native:
                raise NoCompile("engine op reverse outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("reverse arity")
            xs = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"reverse_native({xs}, {r})")
            return r
        if h == "foldl":
            if not self.native:
                raise NoCompile("engine op foldl outside pure SLD fragment")
            if len(e) != 4:
                raise NoCompile("foldl arity")
            fn = self.compile_expr(e[1], goals)
            xs = self.compile_expr(e[2], goals)
            acc0 = self.compile_expr(e[3], goals)
            r = self.fresh()
            goals.append(f"foldl_native({fn}, {xs}, {acc0}, {r})")
            return r
        if h == "is-expr":
            if not self.native:
                raise NoCompile("engine op is-expr outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("is-expr arity")
            x = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"is_expr_native({x}, {r})")
            return r
        if h == "id":
            if not self.native:
                raise NoCompile("engine op id outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("id arity")
            return self.compile_expr(e[1], goals)
        if h == "repr":
            if not self.native:
                raise NoCompile("engine op repr outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("repr arity")
            x = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"repr_native({x}, {r})")
            return r
        if h == "unquote":
            if not self.native:
                raise NoCompile("engine op unquote outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("unquote arity")
            arg = e[1]
            if isinstance(arg, list) and len(arg) == 2 and arg[0] == "quote":
                return self.compile_expr(arg[1], goals)
            return self.compile_data(e)
        if h == "noreduce-eq":
            if not self.native:
                raise NoCompile("engine op noreduce-eq outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile("noreduce-eq arity")
            a = self.compile_data(e[1])
            b = self.compile_data(e[2])
            r = self.fresh()
            goals.append(f"eq_native({a}, {b}, {r})")
            return r
        if h == "is-function":
            if not self.native:
                raise NoCompile("engine op is-function outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("is-function arity")
            x = self.compile_data(e[1])
            r = self.fresh()
            goals.append(f"is_function_native({x}, {r})")
            return r
        if h in ("first-from-pair", "second-from-pair"):
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile(f"{h} arity")
            x = self.compile_expr(e[1], goals)
            r = self.fresh()
            pred = "first_from_pair_native" if h == "first-from-pair" else "second_from_pair_native"
            goals.append(f"{pred}({x}, {r})")
            return r
        if h == "quote":
            if not self.native:
                raise NoCompile("engine op quote outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("quote arity")
            return self.compile_data(e[1])
        if h == "get-type":
            if not self.native:
                raise NoCompile("engine op get-type outside pure SLD fragment")
            if len(e) != 2:
                raise NoCompile("get-type arity")
            x = self.compile_expr(e[1], goals)
            r = self.fresh()
            goals.append(f"get_type_native({x}, {r})")
            return r
        if h == "get-type-space":
            if not self.native:
                raise NoCompile("engine op get-type-space outside pure SLD fragment")
            if len(e) != 3:
                raise NoCompile("get-type-space arity")
            space = self.compile_data(e[1])
            x = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"get_type_space_native({space}, {x}, {r})")
            return r
        if h == "unify":
            if not self.native:
                raise NoCompile(f"engine op {h} outside pure SLD fragment")
            return "[" + ", ".join(self.compile_data(a) for a in e) + "]"
        if isinstance(h, str) and h in ENGINE_OPS:
            raise NoCompile(f"engine op {h} outside pure SLD fragment")
        if isinstance(h, str) and h in ARITH_FN:
            args = [self.compile_expr(a, goals) for a in e[1:]]
            if self.native and len(args) < 2:
                return "[" + ", ".join([self.const(h)] + args) + "]"
            if len(args) == 1 and h in ("+", "-"):
                args = ["0", args[0]]
            if len(args) != 2:
                raise NoCompile(f"arith {h} arity {len(args)}")
            r = self.fresh()
            goals.append(f"{ARITH_FN[h]}({args[0]}, {args[1]}, {r})")
            if not hasattr(self, "arith_vars"): self.arith_vars = set()
            self.arith_vars.add(r)
            return r
        if self.is_fn(h):
            args = [self.compile_expr(a, goals) for a in e[1:]]
            r = self.fresh()
            rel = (self.rel(FN_ALIAS.get(h, h)) if h in FN_ARITY
                   else psym(h) + "_f")
            arities = self.fn_arities(h)
            if self.native and h not in FN_ARITY and len(args) not in arities:
                if any(len(args) < ar for ar in arities):
                    return "[" + ", ".join([self.const(h)] + args) + "]"
                if 0 in arities:
                    base = self.fresh()
                    goals.append(f"{rel}({base})")
                    goals.append(f"call_or_tuple_native({base}, [{', '.join(args)}], {r})")
                    return r
            goals.append(f"{rel}({', '.join(args + [r])})")
            return r
        # plain data tuple
        return "[" + ", ".join(self.compile_expr(a, goals) for a in e) + "]"

    def compile_eq(self, e, goals):
        if len(e) != 3:
            raise NoCompile(f"== arity {len(e)-1}")
        _, a, b = e
        # (== (size-atom $M) k) with literal k: M unifies with k fresh vars
        if isinstance(a, list) and a and a[0] == "size-atom" \
                and isinstance(b, str) and b.isdigit():
            m = self.compile_expr(a[1], goals)
            r = self.fresh()
            slots = ", ".join(self.fresh() for _ in range(int(b)))
            goals.append(f"{self.rel('ueq')}({m}, [{slots}], {r})")
            return r
        x = self.compile_expr(a, goals)
        y = self.compile_expr(b, goals)
        r = self.fresh()
        if self.native:
            goals.append(f"eq_native({x}, {y}, {r})")
            return r
        av = getattr(self, "arith_vars", set())
        def is_intish(t):
            return re.fullmatch(r"-?\d+", t) or t in av
        if is_intish(x) or is_intish(y):
            # boolean integer equality: certified oracle leaf (int_eq),
            # yields True/False like the cmp_* family
            goals.append(f"int_eq({x}, {y}, {r})")
        else:
            goals.append(f"{self.rel('ueq')}({x}, {y}, {r})")
        return r

    def compile_if(self, e, goals):
        cond = self.compile_expr(e[1], goals)
        if len(e) == 3 or (len(e) == 4 and e[3] == ["empty"]):
            goals.append(f"{self.rel('istrue')}({cond})")
            return self.compile_expr(e[2], goals)
        # 3-arg: aux predicate branching on the boolean
        tg, tgoals = None, []
        tg = self.compile_expr(e[2], tgoals)
        eg, egoals = None, []
        eg = self.compile_expr(e[3], egoals)
        vs = [self.pvar(v) for v in metta_vars(e[2]) + [x for x in metta_vars(e[3]) if x not in metta_vars(e[2])]]
        name = f"ifaux{self.aux_n}"; self.aux_n += 1
        rv = self.fresh()
        pre = ", ".join(vs) + ", " if vs else ""
        self.aux.append((f"{name}('True', {pre}{tg})", tgoals))
        self.aux.append((f"{name}(true, {pre}{tg})", tgoals))
        self.aux.append((f"{name}('False', {pre}{eg})", egoals))
        self.aux.append((f"{name}(false, {pre}{eg})", egoals))
        goals.append(f"{name}({cond}, {pre}{rv})")
        return rv

    def compile_case(self, e, goals):
        _, scrut, arms = e[0], e[1], e[2]
        sv = self.compile_expr(scrut, goals)
        name = f"caseaux{self.aux_n}"; self.aux_n += 1
        pattern_vars = []
        body_vars = []
        for arm in arms:
            for v in metta_vars(arm[0]):
                if v not in pattern_vars:
                    pattern_vars.append(v)
            for v in metta_vars(arm[1]):
                if v not in body_vars:
                    body_vars.append(v)
        free_vars = [self.pvar(v) for v in body_vars if v not in pattern_vars]
        pre = ", ".join(free_vars) + ", " if free_vars else ""
        for arm in arms:
            pat, body = arm[0], arm[1]
            pgoals = []
            pterm = self.compile_pattern(pat, pgoals)
            bterm = self.compile_expr(body, pgoals)
            self.aux.append((f"{name}({pre}{pterm}, {bterm})", pgoals))
        rv = self.fresh()
        goals.append(f"{name}({pre}{sv}, {rv})")
        return rv

    def mk_aux(self, goals, result):
        name = f"goalaux{self.aux_n}"; self.aux_n += 1
        self.aux.append((f"{name}({result})", goals))
        return name

    def compile_rule(self, fname, params, rhs):
        goals = []
        pterms = [self.compile_pattern(p, goals) for p in params]  # narrowing
        rterm = self.compile_expr(rhs, goals)
        fsan = psym(fname)
        head = f"{fsan}_f({', '.join(pterms + [rterm])})"
        return (head, goals)

# ---------------- clause emission ----------------

def reorder_goals(goals):
    """Source order preserved: the when/2 coroutines in mi.pl already delay
    arithmetic until its arguments are ground (mode flexibility), while
    keeping it EAGER when they are — reordering arith to the end let ifaux
    dispatch on unbound booleans (both branches open -> exponential search;
    the superpose_primes blowup). Old behavior kept commented for the record:
    structural goals first, mode-flexible arithmetic
    last, so inversions (X+35 = 42) see their arguments grounded."""
    struct = [g for g in goals if not re.match(r"(plus|minus|times|cmp_)", g)]
    return goals

def clause_vars(text):
    text = re.sub(r"'[^']*'", "", text)  # quoted atoms are not variables
    return sorted(v for v in set(re.findall(r"\b[A-Z_]\w*", text))
                  if v != "_" and not v.startswith("_"))

def emit_pl(clauses, queries, out_path, trace_base, extra=()):
    lines = [f":- ['{MI_PL}'].", ""] + list(extra) + [""]
    for i, (head, goals) in enumerate(clauses):
        body = "[" + ", ".join(reorder_goals(goals)) + "]"
        text = head + " " + body
        vs = clause_vars(text)
        names = "[" + ", ".join(f"'{v}'={v}" for v in vs) + "]"
        lines.append(f"pclause({i}, {head}, {body}, {names}).")
    lines.append("")
    lines.append("main :-")
    for qi, (qgoal, qvar) in enumerate(queries):
        lines.append(f"    ( run_traces({qgoal}, ['{qvar}'={qvar}], "
                     f"'{trace_base}-q{qi}') -> true ; true ),")
    lines.append("    halt(0).")
    out_path.write_text("\n".join(lines) + "\n")

NATIVE_HELPERS = r"""
:- use_module(library(thread)).
:- dynamic space_fact/1.

plus(X,Y,Z) :- call_builtin(plus(X,Y,Z)).
minus(X,Y,Z) :- call_builtin(minus(X,Y,Z)).
times(X,Y,Z) :- call_builtin(times(X,Y,Z)).
cmp_gt(X,Y,Z) :- call_builtin(cmp_gt(X,Y,Z)).
cmp_lt(X,Y,Z) :- call_builtin(cmp_lt(X,Y,Z)).
cmp_ge(X,Y,Z) :- call_builtin(cmp_ge(X,Y,Z)).
cmp_le(X,Y,Z) :- call_builtin(cmp_le(X,Y,Z)).
idiv(X,Y,Z) :- call_builtin(idiv(X,Y,Z)).
imod(X,Y,Z) :- call_builtin(imod(X,Y,Z)).
int_eq(X,Y,Z) :- call_builtin(int_eq(X,Y,Z)).
min_native(X,Y,Z) :- Z is min(X,Y).
max_native(X,Y,Z) :- Z is max(X,Y).
eq_native(X, Y, 'True') :- X == Y, !.
eq_native(_, _, 'False').
ueq_bool_native(X, Y, 'True') :- X = Y, !.
ueq_bool_native(_, _, 'False').
alpha_eq_native(X, Y, 'True') :- X =@= Y, !.
alpha_eq_native(_, _, 'False').
bool_norm_native('True', true).
bool_norm_native(true, true).
bool_norm_native('False', false).
bool_norm_native(false, false).
and_bool_native(A, B, R) :-
    bool_norm_native(A, AN),
    bool_norm_native(B, BN),
    and_norm_native(AN, BN, R).
and_norm_native(true, true, true).
and_norm_native(true, false, false).
and_norm_native(false, true, false).
and_norm_native(false, false, false).
or_bool_native(A, B, R) :-
    bool_norm_native(A, AN),
    bool_norm_native(B, BN),
    or_norm_native(AN, BN, R).
or_norm_native(true, true, true).
or_norm_native(true, false, true).
or_norm_native(false, true, true).
or_norm_native(false, false, false).
not_bool_native(A, R) :-
    bool_norm_native(A, AN),
    not_norm_native(AN, R).
not_norm_native(true, false).
not_norm_native(false, true).
cons_bool_native(H, T, [H|T]).
roman_pred_native('=', A, B, 'True') :- A = B, !.
roman_pred_native('=', _, _, 'False').
roman_pred_native('==', A, B, 'True') :- A == B, !.
roman_pred_native('==', _, _, 'False').
roman_pred_native('=alpha', A, B, 'True') :- A =@= B, !.
roman_pred_native('=alpha', _, _, 'False').
roman_any_native(Pred, A, [B|_]) :-
    roman_pred_native(Pred, A, B, 'True'), !.
roman_any_native(Pred, A, [_|Bs]) :-
    roman_any_native(Pred, A, Bs).
roman_set_native('intersect', _, [], _, []).
roman_set_native('intersect', Pred, [A|As], Bs, Out) :-
    ( roman_any_native(Pred, A, Bs)
      -> Out = [A|Rest],
         roman_set_native('intersect', Pred, As, Bs, Rest)
      ;  roman_set_native('intersect', Pred, As, Bs, Out)
    ).
roman_set_native('subtract', _, [], _, []).
roman_set_native('subtract', Pred, [A|As], Bs, Out) :-
    ( roman_any_native(Pred, A, Bs)
      -> roman_set_native('subtract', Pred, As, Bs, Out)
      ;  Out = [A|Rest],
         roman_set_native('subtract', Pred, As, Bs, Rest)
    ).
roman_set_native('union', _, [], Bs, Bs).
roman_set_native('union', Pred, [A|As], Bs, Out) :-
    ( roman_any_native(Pred, A, Bs)
      -> roman_set_native('union', Pred, As, Bs, Out)
      ;  Out = [A|Rest],
         roman_set_native('union', Pred, As, Bs, Rest)
    ).
assert_native('True', true) :- !.
assert_native(true, true) :- !.
catch_eval_native(Goal, Value, Result) :-
    catch((call(Goal), Result = Value), Error, error_term_native(Error, Result)).
error_term_native(error(type_error(_, _), _), ['Error', 'type_error']) :- !.
error_term_native(error(E, _), ['Error', E]) :- !.
error_term_native(_, ['Error', 'unknown']).

collapse_t(Tmpl, Call, L) :- findall(Tmpl, call(Call), L).
member_native(X, Xs) :- member(X, Xs).
hyperpose_native(Branches, Out) :-
    concurrent_and(member((Goal, Res), Branches), (call(Goal), Out = Res)).
msort_native(Xs, Ys) :- msort(Xs, Ys).
sort_native(Xs, Ys) :- sort(Xs, Ys).
length_native(Xs, N) :- length(Xs, N).
last_native(Xs, X) :- last(Xs, X).
car_atom_native([H|_], H).
cdr_atom_native([_|T], T).
index_atom_native(Xs, I, X) :- nth0(I, Xs, X).
list_to_set_native(Xs, Ys) :- list_to_set(Xs, Ys).
exclude_item_native(X, Xs, Ys) :- exclude(==(X), Xs, Ys).
is_expr_native(X, 'True') :- is_list(X), X \= [], !.
is_expr_native(_, 'False').
get_type_native(X, 'Number') :- number(X), !.
get_type_native(X, R) :- space_fact([':', X, R]), !.
get_type_native(_, 'Atom').
get_type_space_native('&self', X, R) :- space_fact([':', X, R]), !.
get_type_space_native(_, X, R) :- get_type_native(X, R).
unify_space_native(Pattern, Then, _, Then) :- space_fact(Pattern), !.
unify_space_native(_, _, Else, Else).
find_native(Pattern, 'True') :- space_fact(Pattern).
find_native(Pattern, 'False') :- \+ space_fact(Pattern).
reverse_native(Xs, Ys) :- reverse(Xs, Ys).
foldl_native(_, [], Acc, Acc).
foldl_native(F, [X|Xs], Acc0, Acc) :-
    call_fn_native(F, [X, Acc0], Acc1),
    foldl_native(F, Xs, Acc1, Acc).
add_unique_native(Expression, true) :-
    Key = ['s', Expression],
    \+ space_fact(Key), !,
    assertz(space_fact(Key)).
for_each_println_native(Xs, X) :- member(X, Xs).
for_each_println_native(Xs, Ys) :- same_length(Xs, Ys), maplist(=(true), Ys).
if_error_native(['Error'|_], Then, _, Then) :- !.
if_error_native(_, _, Else, Else).
is_function_native(['->'|Rest], 'True') :- Rest = [_,_|_], !.
is_function_native(_, 'False').
first_from_pair_native([A, _], A).
second_from_pair_native([_, B], B).
repr_native(T, R) :-
    with_output_to(atom(A), write_metta(T)),
    atom_concat('"', A, B),
    atom_concat(B, '"', R).

native_op('+', plus).
native_op('-', minus).
native_op('*', times).
native_op('/', idiv).
native_op('%', imod).
native_op('=', ueq_bool_native).
native_op('>', cmp_gt).
native_op('<', cmp_lt).
native_op('>=', cmp_ge).
native_op('<=', cmp_le).
native_op('==', eq_native).
native_op('=alpha', alpha_eq_native).
native_op('cons', cons_bool_native).
native_op('and', and_bool_native).
native_op('or', or_bool_native).
native_op('not', not_bool_native).

call_fn_native(F, Args, R) :-
    native_fun(F, Pred),
    length(Args, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !,
    append(Args, [R], Full),
    Goal =.. [Pred|Full],
    call(Goal).
call_fn_native(F, Args, R) :-
    native_op(F, Pred),
    length(Args, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !,
    append(Args, [R], Full),
    Goal =.. [Pred|Full],
    call(Goal).
call_fn_native([F|Fixed], Args, R) :-
    native_fun(F, Pred),
    append(Fixed, Args, All),
    length(All, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !,
    append(All, [R], Full),
    Goal =.. [Pred|Full],
    call(Goal).
call_fn_native([F|Fixed], Args, R) :-
    native_op(F, Pred),
    append(Fixed, Args, All),
    length(All, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !,
    append(All, [R], Full),
    Goal =.. [Pred|Full],
    call(Goal).

callable_native(F, Args) :-
    native_fun(F, Pred),
    length(Args, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !.
callable_native(F, Args) :-
    native_op(F, Pred),
    length(Args, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !.
callable_native([F|Fixed], Args) :-
    native_fun(F, Pred),
    append(Fixed, Args, All),
    length(All, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !.
callable_native([F|Fixed], Args) :-
    native_op(F, Pred),
    append(Fixed, Args, All),
    length(All, N),
    Arity is N + 1,
    current_predicate(Pred/Arity), !.

call_or_tuple_native(F, Args, R) :-
    callable_native(F, Args), !,
    call_fn_native(F, Args, R).
call_or_tuple_native(F, Args, R) :-
    R = [F|Args].

add_atom_native(Term, true) :- assertz(space_fact(Term)).
remove_atom_native(Term, true) :- retractall(space_fact(Term)).

match_native([','|Patterns], Out, Result) :- !,
    match_all_native(Patterns),
    \+ cyclic_term(Out),
    Result = Out.
match_native(Pattern, Out, Result) :-
    space_fact(Pattern),
    \+ cyclic_term(Out),
    Result = Out.

match_all_native([]).
match_all_native([Pattern|Patterns]) :-
    space_fact(Pattern),
    match_all_native(Patterns).

emit_answers([]).
emit_answers([A|As]) :-
    write('__ANSWER__\t'), write_metta(A), nl,
    emit_answers(As).

write_metta(T) :- var(T), !, write('$VAR').
write_metta([]) :- !, write('()').
write_metta([H|T]) :- !,
    write('('), write_metta_items([H|T]), write(')').
write_metta(T) :- number(T), !, write(T).
write_metta(T) :- atom(T), !, write(T).
write_metta(T) :-
    T =.. [F|Args],
    write('('), write(F), write_metta_args(Args), write(')').

write_metta_items([]).
write_metta_items([H]) :- !, write_metta(H).
write_metta_items([H|T]) :-
    write_metta(H), write(' '), write_metta_items(T).

write_metta_args([]).
write_metta_args([A|As]) :-
    write(' '), write_metta(A), write_metta_args(As).
"""

def emit_native_pl(clauses, queries, out_path):
    lines = [f":- ['{MI_PL}'].", "", NATIVE_HELPERS, ""]
    for head, goals in clauses:
        if goals:
            lines.append(f"{head} :- {', '.join(reorder_goals(goals))}.")
        else:
            lines.append(f"{head}.")
    lines.append("")
    lines.append("main :-")
    for qi, (qgoal, qvar) in enumerate(queries):
        lines.append(f"    findall({qvar}, {qgoal}, L{qi}),")
        lines.append(f"    emit_answers(L{qi}),")
    lines.append("    halt(0).")
    out_path.write_text("\n".join(lines) + "\n")

def native_answers(stdout):
    out = []
    for line in stdout.splitlines():
        if line.startswith("__ANSWER__\t"):
            out.append(line.split("\t", 1)[1].strip())
    return out

# ---------------- per-file driver ----------------

def sexp_answer(trace_file):
    """Extract the (answer ...) binding for R and render as MeTTa text."""
    txt = trace_file.read_text()
    m = re.search(r"\(answer \(bind \"R\" (.*?)\)\)\n", txt, re.S)
    if not m: return None
    return render(parse_sexp_term(m.group(1)))

def parse_sexp_term(s):
    toks = re.findall(r"[()]|\"[^\"]*\"|[^\s()]+", s)
    def rec(i):
        if toks[i] == "(":
            out, i = [], i + 1
            while toks[i] != ")":
                n, i = rec(i)
                out.append(n)
            return out, i + 1
        return toks[i].strip('"'), i + 1
    return rec(0)[0]

def render(t):
    if isinstance(t, str): return t
    tag = t[0]
    if tag == "c": return "()" if t[1] == "[]" else t[1]
    if tag == "v": return "$" + t[1]
    if tag == "f":
        fn = t[1]
        args = [render(x) for x in t[2:]]
        if fn == "[|]":  # cons cell -> flatten list
            out = [args[0]]
            rest = t[3]
            while isinstance(rest, list) and rest and rest[0] == "f" and rest[1] == "[|]":
                out.append(render(rest[2])); rest = rest[3]
            if isinstance(rest, list) and rest[0] == "c" and rest[1] == "[]":
                return "(" + " ".join(out) + ")"
            return "(" + " ".join(out) + " . " + render(rest) + ")"
        if fn == "[]": return "()"
        return "(" + fn + " " + " ".join(args) + ")"
    return str(t)

def compile_file(path, native=False):
    text = D.transform(path.read_text(errors="replace"))
    raw = parse_all(text)
    forms = []
    for f in raw_to_forms(raw):
        if native and isinstance(f, list) and len(f) == 2 and f[0] == "!":
            ipath = import_file(f[1], path.parent)
            if ipath is not None and ipath.exists():
                lib_text = ipath.read_text(errors="replace")
                lib_forms = [x for x in raw_to_forms(parse_all(lib_text))
                             if not (isinstance(x, list) and x and x[0] == "!")]
                forms.extend(lib_forms)
                forms.append(["!", "true"])
                continue
        forms.append(f)
    rules = collections.defaultdict(list)
    facts_raw = []
    bangs = []
    for f in forms:
        if isinstance(f, list) and f and f[0] == "=" and isinstance(f[1], list):
            rules[f[1][0]].append((f[1][1:], f[2]))
        elif isinstance(f, list) and f and f[0] == "!":
            b = f[1]
            if native and import_file(b, path.parent) is not None:
                bangs.append("true")
            elif native and isinstance(b, list) and b and b[0] == "add-translator-rule!":
                continue
            else:
                bangs.append(b)
        elif isinstance(f, list) and f and f[0] == ":":
            if native:
                facts_raw.append(f)
            continue
        elif isinstance(f, list) and f and isinstance(f[0], str):
            fgoals = []
            fargs = [c0.compile_expr(a, fgoals) if False else None for a in []]
            facts_raw.append(f)
        elif isinstance(f, list):
            raise NoCompile(f"top-level form with non-symbol head: {f[:1]}")
    c = Compiler(rules, native=native)
    clauses = []
    if native:
        for fname in sorted(rules):
            fsan = psym(fname)
            clauses.append((f"native_fun({c.const(fname)}, {fsan}_f)", []))
    for f in facts_raw:
        if native:
            clauses.append((f"space_fact({c.compile_data(f, literal_vars=(f[0] == ':'))})", []))
        else:
            fgoals = []
            fargs = [c.compile_expr(a, fgoals) for a in f[1:]]
            if fgoals:
                raise NoCompile(f"non-ground fact {f[0]}")
            name = "fact_" + psym(f[0])
            clauses.append((f"{name}({', '.join(fargs)})" if fargs else name, []))
    for fname, defs in rules.items():
        for params, rhs in defs:
            clauses.append(c.compile_rule(fname, params, rhs))
    queries = []
    for qi, b in enumerate(bangs):
        goals = []
        r = c.compile_expr(b, goals)
        name = f"query{qi}_f"
        clauses.append((f"{name}({r})", goals))
        queries.append((f"{name}(R)", "R"))
    # aux clauses
    for head, goals in c.aux:
        clauses.append((head, goals))
    # builtin relations
    seen_builtin = set()
    for rel in sorted(c.used_rels):
        for cl in BUILTIN_RELS[rel]:
            if cl in seen_builtin:
                continue
            seen_builtin.add(cl)
            h, _, b = cl.partition(":-")
            h = h.strip().rstrip(".")
            bgoals = [g.strip() for g in b.rstrip(".").split(",")] if b.strip() else []
            # naive split breaks on nested commas; builtin bodies are single goals
            bgoals = [b.strip().rstrip(".")] if b.strip() else []
            clauses.append((h, bgoals))
    return text, clauses, queries, c.committed

def route_file(path, timeout=30, workdir=None, petta_timeout=None,
               petta_timeout_multiplier=D.DEFAULT_PETTA_TIMEOUT_MULTIPLIER):
    text, clauses, queries, committed = compile_file(path, native=False)
    wd = pathlib.Path(workdir or tempfile.mkdtemp(prefix="relroute-"))
    plfile = wd / (path.stem + ".pl")
    emit_pl(clauses, queries, plfile, str(wd / path.stem), extra=committed)
    pr = subprocess.run(["swipl", "--stack-limit=12g", "-q", "-g", "main", str(plfile)],
                        capture_output=True, text=True, timeout=timeout)
    if pr.returncode != 0:
        raise NoCompile(f"swipl failed: {pr.stderr.strip()[:120]}")
    answers, certified, trusted = [], True, False
    for tf in sorted(wd.glob(path.stem + "-q*.sexp")):
        ck = subprocess.run([str(CHECKTRACE), str(tf)],
                            capture_output=True, text=True, timeout=timeout)
        if ck.returncode == 3:
            trusted = True          # certified except trusted collections
        elif ck.returncode != 0:
            certified = False
        a = sexp_answer(tf)
        if a is not None: answers.append(a)
    # oracle comparison
    with D.transformed_temp(path) as t:
        t.write(text)
        tpath = pathlib.Path(t.name)
    try:
        petta = D.petta_results(
            tpath,
            D.petta_timeout_for(timeout, petta_timeout,
                                petta_timeout_multiplier))
    finally:
        tpath.unlink(missing_ok=True)
    a_bag = collections.Counter(D.normalize(x) for x in answers)
    p_bag = collections.Counter(D.normalize(x) for x in petta)
    agree = a_bag == p_bag
    return (("DELEGATED-TRUSTED" if trusted else "DELEGATED-CHECKED")
            if certified and agree else
            "DELEGATED-DIFF" if certified else "UNCERTIFIED",
            answers, petta)

def route_file_native(path, timeout=30, workdir=None, petta_timeout=None,
                      petta_timeout_multiplier=D.DEFAULT_PETTA_TIMEOUT_MULTIPLIER):
    text, clauses, queries, _committed = compile_file(path, native=True)
    wd = pathlib.Path(workdir or tempfile.mkdtemp(prefix="relnative-"))
    plfile = wd / (path.stem + "-native.pl")
    emit_native_pl(clauses, queries, plfile)
    pr = subprocess.run(["swipl", "--stack-limit=12g", "-q", "-g", "main", str(plfile)],
                        capture_output=True, text=True, timeout=timeout)
    if pr.returncode != 0:
        raise NoCompile(f"native swipl failed: {pr.stderr.strip()[:120]}")
    answers = native_answers(pr.stdout)
    with D.transformed_temp(path) as t:
        t.write(text)
        tpath = pathlib.Path(t.name)
    try:
        petta = D.petta_results(
            tpath,
            D.petta_timeout_for(timeout, petta_timeout,
                                petta_timeout_multiplier))
    finally:
        tpath.unlink(missing_ok=True)
    a_bag = collections.Counter(D.normalize(x) for x in answers)
    p_bag = collections.Counter(D.normalize(x) for x in petta)
    return ("PERF-PROXY-AGREE" if a_bag == p_bag else "PERF-PROXY-DIFF",
            answers, petta)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--petta-timeout", type=float, default=None)
    parser.add_argument("--petta-timeout-multiplier", type=float,
                        default=D.DEFAULT_PETTA_TIMEOUT_MULTIPLIER)
    parser.add_argument("targets", nargs="+")
    args = parser.parse_args()
    cdir = pathlib.Path(os.environ.get("PETTA_DIR", str(pathlib.Path.home()/"repos/PeTTa"))) / "examples"
    for name in args.targets:
        p = cdir / name
        try:
            if args.native:
                verdict, ans, petta = route_file_native(
                    p,
                    timeout=args.timeout,
                    petta_timeout=args.petta_timeout,
                    petta_timeout_multiplier=args.petta_timeout_multiplier)
                print(f"{name}\t{verdict}\tnative-answers: {ans}\tpetta: {petta}")
            else:
                verdict, ans, petta = route_file(
                    p,
                    timeout=args.timeout,
                    petta_timeout=args.petta_timeout,
                    petta_timeout_multiplier=args.petta_timeout_multiplier)
                print(f"{name}\t{verdict}\tcertified-answers: {ans}\tpetta: {petta}")
        except NoCompile as e:
            print(f"{name}\tNO-COMPILE\t{e}")
        except subprocess.TimeoutExpired:
            print(f"{name}\tTIMEOUT")

if __name__ == "__main__":
    main()
