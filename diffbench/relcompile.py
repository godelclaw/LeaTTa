#!/usr/bin/env python3
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
  NO-COMPILE         outside the v1 pure fragment (reason reported)
"""
import collections
import pathlib
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D

MI_PL = pathlib.Path(
    "/home/oruzi/repos/MeTTapedia-algos-fix/lean/algos-lp/prolog/mi.pl")
CHECKTRACE = pathlib.Path(
    "/home/oruzi/repos/MeTTapedia-algos-fix/lean/algos-lp/.lake/build/bin/checktrace")

# ---------------- MeTTa parsing ----------------

def tokenize(text):
    text = re.sub(r";[^\n]*", "", text)
    return re.findall(r"[()]|[^\s()]+", text)

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
        "and_r('True','True','True').", "and_r('True','False','False').",
        "and_r('False','True','False').", "and_r('False','False','False')."),
    "or": (
        "or_r('True','True','True').", "or_r('True','False','True').",
        "or_r('False','True','True').", "or_r('False','False','False')."),
    "not": ("not_r('True','False').", "not_r('False','True')."),
    "ueq": ("ueq_r(X, X, 'True').",),
    "ueq2": ("ueq2_r(X, X).",),
    "istrue": ("istrue_r('True').",),
}
FN_ARITY = {"append": 2, "cons": 2, "member": 2, "and": 2, "or": 2, "not": 1}
# engine/space/nondet ops outside the pure SLD fragment -> NO-COMPILE (honest)
ENGINE_OPS = {"collapse", "superpose", "match", "add-atom", "remove-atom",
              "bind!", "new-space", "msort", "car-atom", "cdr-atom",
              "cons-atom", "size-atom", "index-atom", "quote", "eval", "chain",
              "unify", "function", "return", "println!", "trace!", "get-type",
              "/", "<", ">", "<=", ">=", "%"}
ARITH_FN = {"+": "plus", "-": "minus", "*": "times", "#+": "plus", "#-": "minus"}

def metta_vars(e, acc=None):
    if acc is None: acc = []
    if is_var(e):
        if e not in acc: acc.append(e)
    elif isinstance(e, list):
        for x in e: metta_vars(x, acc)
    return acc

class NoCompile(Exception): pass

class Compiler:
    def __init__(self, rules):
        self.rules = rules              # name -> [(params, rhs)]
        self.aux = []                   # extra clauses (text later)
        self.used_rels = set()
        self.committed = []
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
        return f"'{t}'"

    def rel(self, name):
        self.used_rels.add(name)
        return name + "_r"

    def is_fn(self, h):
        return isinstance(h, str) and (h in self.rules or h in FN_ARITY)

    def compile_expr(self, e, goals):
        """Compile expression e; append goals; return Prolog term string."""
        if is_var(e): return self.pvar(e)
        if isinstance(e, str): return self.const(e)
        if not e: return "[]"
        h = e[0]
        if h == "if":
            return self.compile_if(e, goals)
        if h == "let":
            _, pat, val, body = e
            vterm = self.compile_expr(val, goals)
            pterm = self.compile_expr(pat, goals)  # fn-call pattern narrows
            goals.append(f"{self.rel('ueq2')}({pterm}, {vterm})")
            return self.compile_expr(body, goals)
        if h == "case":
            return self.compile_case(e, goals)
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
            goals.append(f"{name}({', '.join(vs + [rv])})")
            return rv
        if h == "==":
            return self.compile_eq(e, goals)
        if h == "=":  # unification-as-expression (PeTTa)
            a = self.compile_expr(e[1], goals)
            b = self.compile_expr(e[2], goals)
            r = self.fresh()
            goals.append(f"{self.rel('ueq')}({a}, {b}, {r})")
            return r
        if h == "empty":
            raise NoCompile("(empty) outside if-else position")
        if isinstance(h, str) and h in ENGINE_OPS:
            raise NoCompile(f"engine op {h} outside pure SLD fragment")
        if isinstance(h, str) and h in ARITH_FN:
            args = [self.compile_expr(a, goals) for a in e[1:]]
            if len(args) != 2:
                raise NoCompile(f"arith {h} arity {len(args)}")
            r = self.fresh()
            goals.append(f"{ARITH_FN[h]}({args[0]}, {args[1]}, {r})")
            return r
        if self.is_fn(h):
            args = [self.compile_expr(a, goals) for a in e[1:]]
            r = self.fresh()
            rel = self.rel(h) if h in FN_ARITY else self.const(h)[1:-1] + "_f"
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
        self.aux.append((f"{name}('False', {pre}{eg})", egoals))
        goals.append(f"{name}({cond}, {pre}{rv})")
        return rv

    def compile_case(self, e, goals):
        _, scrut, arms = e[0], e[1], e[2]
        sv = self.compile_expr(scrut, goals)
        name = f"caseaux{self.aux_n}"; self.aux_n += 1
        for arm in arms:
            pat, body = arm[0], arm[1]
            pgoals = []
            pterm = self.compile_expr(pat, pgoals)
            bterm = self.compile_expr(body, pgoals)
            self.aux.append((f"{name}({pterm}, {bterm})", pgoals))
        rv = self.fresh()
        goals.append(f"{name}({sv}, {rv})")
        return rv

    def mk_aux(self, goals, result):
        name = f"goalaux{self.aux_n}"; self.aux_n += 1
        self.aux.append((f"{name}({result})", goals))
        return name

    def compile_rule(self, fname, params, rhs):
        goals = []
        pterms = [self.compile_expr(p, goals) for p in params]  # narrowing
        rterm = self.compile_expr(rhs, goals)
        head = f"{fname}_f({', '.join(pterms + [rterm])})"
        return (head, goals)

# ---------------- clause emission ----------------

def reorder_goals(goals):
    """Stable partition: structural goals first, mode-flexible arithmetic
    last, so inversions (X+35 = 42) see their arguments grounded."""
    struct = [g for g in goals if not re.match(r"(plus|minus|times)\(", g)]
    arith  = [g for g in goals if re.match(r"(plus|minus|times)\(", g)]
    return struct + arith

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
    if tag == "c": return t[1]
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

def route_file(path, timeout=30, workdir=None):
    text = D.transform(path.read_text(errors="replace"))
    raw = parse_all(text)
    forms, i = [], 0
    while i < len(raw):
        if raw[i] == "!" and i + 1 < len(raw):
            forms.append(["!", raw[i + 1]]); i += 2
        else:
            forms.append(raw[i]); i += 1
    rules = collections.defaultdict(list)
    bangs = []
    for f in forms:
        if isinstance(f, list) and f and f[0] == "=" and isinstance(f[1], list):
            rules[f[1][0]].append((f[1][1:], f[2]))
        elif isinstance(f, list) and f and f[0] == "!":
            bangs.append(f[1])
        elif isinstance(f, list) and f and f[0] == ":":
            continue
        elif isinstance(f, list):
            raise NoCompile(f"top-level fact/space form: {f[:1]}")
    c = Compiler(rules)
    clauses = []
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
    for rel in sorted(c.used_rels):
        for cl in BUILTIN_RELS[rel]:
            h, _, b = cl.partition(":-")
            h = h.strip().rstrip(".")
            bgoals = [g.strip() for g in b.rstrip(".").split(",")] if b.strip() else []
            # naive split breaks on nested commas; builtin bodies are single goals
            bgoals = [b.strip().rstrip(".")] if b.strip() else []
            clauses.append((h, bgoals))
    wd = pathlib.Path(workdir or tempfile.mkdtemp(prefix="relroute-"))
    plfile = wd / (path.stem + ".pl")
    emit_pl(clauses, queries, plfile, str(wd / path.stem), extra=c.committed)
    pr = subprocess.run(["swipl", "-q", "-g", "main", str(plfile)],
                        capture_output=True, text=True, timeout=timeout)
    if pr.returncode != 0:
        raise NoCompile(f"swipl failed: {pr.stderr.strip()[:120]}")
    answers, certified = [], True
    for tf in sorted(wd.glob(path.stem + "-q*.sexp")):
        ck = subprocess.run([str(CHECKTRACE), str(tf)],
                            capture_output=True, text=True, timeout=timeout)
        if ck.returncode != 0:
            certified = False
        a = sexp_answer(tf)
        if a is not None: answers.append(a)
    # oracle comparison
    with tempfile.NamedTemporaryFile("w", suffix=".metta", delete=False) as t:
        t.write(text)
    petta = D.petta_results(pathlib.Path(t.name), timeout)
    a_bag = collections.Counter(D.normalize(x) for x in answers)
    p_bag = collections.Counter(D.normalize(x) for x in petta)
    agree = a_bag == p_bag
    return ("DELEGATED-CHECKED" if certified and agree else
            "DELEGATED-DIFF" if certified else "UNCERTIFIED",
            answers, petta)

def main():
    targets = sys.argv[1:]
    cdir = pathlib.Path("/home/oruzi/repos/PeTTa/examples")
    for name in targets:
        p = cdir / name
        try:
            verdict, ans, petta = route_file(p)
            print(f"{name}\t{verdict}\tcertified-answers: {ans}\tpetta: {petta}")
        except NoCompile as e:
            print(f"{name}\tNO-COMPILE\t{e}")
        except subprocess.TimeoutExpired:
            print(f"{name}\tTIMEOUT")

if __name__ == "__main__":
    main()
