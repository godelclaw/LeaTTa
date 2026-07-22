-- SPDX-License-Identifier: Apache-2.0

/-
pleatta --trace: project the compiled program to the algos-lp certificate
wire format and re-derive each machine answer as a checkable SLD tree.

THE DOCTRINE (guard-erasure, = mi.pl's committed_pred stance): committed-
choice guards — cut, soft-cut's "sub had no answers", if's non-True test,
reduce/3's definedness test — are ERASED in the projection, yielding a plain
(possibly overlapping-clause) definite program. A certificate proves genuine
SLD-derivability of the answer in that guard-erased program; the machine's
guarded strategy only determines WHICH derivation is found. Negative claims
(else-branches' guards, collection exhaustiveness) have no finite
certificate: else-clauses are guard-erased, collections are trusted-labeled
tnodes (counted by the checker).

THE PROLOG GROUNDING of the two central forms:
- match: the space's atoms ARE the clause database — `(match &self p t)` is
  ordinary resolution against `self(a).` FACT clauses (one per initial space
  atom) [SPEC translator.pl:259-262 = query the fact store].
- superpose: a syntactic tuple compiles to one aux clause per element
  (disjunction = clause order) [SPEC translator.pl:112-114]; a COMPUTED
  tuple (spread) is the member/2 relation on cons-chains — two universal
  clauses, `chain_member`.
- first-class functions: `dyncall` bridge clauses mirror reduce/3's
  apply-or-data clause structure [SPEC translator.pl:50-64], with
  partial(Base,Bound) application via the two-clause `chain_append`.

Out of the certifiable fragment (poison relations, no defining clause —
derivations through them honestly fail): wact (world effects),
get-type/get-metatype (oracle-shaped machine ops). `catchg` normal answers
are projected as ordinary sub-derivations; caught runtime/type exceptions
remain outside this SLD certificate lane. `evalg` is projected through a
trusted wrapper whose dynamically compiled positive sub-derivation is still
checked against emitted aux clauses.
-/
import PLeaTTa.Machine
import PLeaTTa.Builtins
import MettaHyperonFull.Core.Pretty

namespace PLeaTTa.Trace

open Metta (Atom Subst)
open PLeaTTa

/-! ## Wire clauses (over PLeaTTa atoms; serialized at emission) -/

structure WAtom where
  rel : String
  args : List Atom
deriving Repr, Inhabited, BEq

structure WClause where
  head : WAtom
  body : List WAtom
deriving Repr, Inhabited

/-! ## Var collection -/

private def varsOfAtom : Atom → List String
  | Atom.var v => [v]
  | Atom.expr es => es.attach.flatMap (fun ⟨e, _⟩ => varsOfAtom e)
  | _ => []

private def varsOfWAtom (a : WAtom) : List String :=
  a.args.flatMap varsOfAtom

/-! ## The builtin-leaf relation names (checker-oracle vocabulary) -/

def binRel : String → String
  | "+" => "plus" | "-" => "minus" | "*" => "times"
  | "/" => "idiv" | "%" => "imod"
  | "<" => "cmp_lt" | ">" => "cmp_gt" | "<=" => "cmp_le" | ">=" => "cmp_ge"
  | "==" => "beq"
  | "min" => "min" | "max" => "max"
  | "is-var" => "is_var" | "=alpha" => "alpha_eq"
  | "and" => "b_and" | "or" => "b_or" | "not" => "b_not" | "xor" => "b_xor"
  | "car-atom" => "car_c" | "cdr-atom" => "cdr_c" | "cons-atom" => "cons_c"
  | "size-atom" => "size_c" | "index-atom" => "index_c"
  | "unique-atom" => "unique_atom" | "alpha-unique-atom" => "alpha_unique_atom"
  | "union-atom" => "union_atom" | "intersection-atom" => "intersection_atom"
  | "subtraction-atom" => "subtraction_atom" | "is-alpha-member" => "is_alpha_member"
  | "min-atom" => "min_atom" | "max-atom" => "max_atom" | "msort" => "msort"
  | "sqrt-math" => "sqrt_math" | "sin-math" => "sin_math"
  | "cos-math" => "cos_math" | "tan-math" => "tan_math"
  | "asin-math" => "asin_math" | "acos-math" => "acos_math"
  | "atan-math" => "atan_math" | "pow-math" => "pow_math"
  | "log-math" => "log_math" | "abs-math" => "abs_math"
  | "trunc-math" => "trunc_math" | "ceil-math" => "ceil_math"
  | "floor-math" => "floor_math" | "round-math" => "round_math"
  | "isnan-math" => "isnan_math" | "isinf-math" => "isinf_math"
  | op => "bop§" ++ op    -- no oracle entry: honestly uncertifiable leaf

def nilA' : Atom := Atom.sym "#nil"
def consC' (h t : Atom) : Atom := Atom.expr [Atom.sym "#c", h, t]

/-! ## Projection: compiled Goals → wire body atoms + aux clauses -/

structure PJ where
  aux : List WClause := []
  k : Nat := 0

private def freshK : StateM PJ Nat := do
  let s ← get; set { s with k := s.k + 1 }; pure s.k

private def pushAux (c : WClause) : StateM PJ Unit :=
  modify (fun s => { s with aux := s.aux ++ [c] })

mutual
partial def projGoal (g : Goal) : StateM PJ (List WAtom) := do
  match g with
  | .call f args res => pure [⟨"u_" ++ f, args ++ [res]⟩]
  | .bin op args res => pure [⟨binRel op, args ++ [res]⟩]
  | .eq a b => pure [⟨"ueq", [a, b]⟩]
  | .compileAlias a b => pure [⟨"ueq", [a, b]⟩]
  | .cut => pure []          -- guard-erased
  | .cutAt _ => pure []      -- guard-erased
  | .smatch pat =>
      match spacePatView pat with
      | (sp, p) =>
          if sp == selfSpace then pure [⟨"self", [p]⟩]
          else pure [⟨"unsupported§space", [sp, p]⟩]
  | .spread v res => pure [⟨"chain_member", [res, v]⟩]
  | .amb branches res => do
      -- superpose = disjunction, one clause per element
      -- [SPEC translator.pl:112-114]
      let n ← freshK
      let rel := s!"sup{n}"
      let vs := (branches.flatMap (fun (t, gs) =>
        varsOfAtom t ++ gs.flatMap varsOfGoal)).eraseDups.map Atom.var
      for (t, gs) in branches do
        let body ← projGoals gs
        pushAux ⟨⟨rel, vs ++ [t]⟩, body⟩
      pure [⟨rel, vs ++ [res]⟩]
  | .ite cond thn els res => do
      -- the compiled `(Cv == true -> Then ; Else)` [SPEC translator.pl:
      -- 156-162]; the else-guard is erased per the doctrine above
      let n ← freshK
      let rel := s!"ifte{n}"
      let vs := (varsOfAtom thn.1 ++ thn.2.flatMap varsOfGoal ++
                 varsOfAtom els.1 ++ els.2.flatMap varsOfGoal).eraseDups.map Atom.var
      let tb ← projGoals thn.2
      pushAux ⟨⟨rel, [Atom.sym "True"] ++ vs ++ [thn.1]⟩, tb⟩
      let eb ← projGoals els.2
      -- guard-erased else: the condition slot is a fresh unconstrained var
      pushAux ⟨⟨rel, [Atom.var s!"C§{n}"] ++ vs ++ [els.1]⟩, eb⟩
      pure [⟨rel, [cond] ++ vs ++ [res]⟩]
  | .onceg tmpl sub res => do
      -- once = committed choice [SPEC translator.pl:127-128]; cut-agnostic
      let n ← freshK
      let rel := s!"once{n}"
      let vs := (varsOfAtom tmpl ++ sub.flatMap varsOfGoal).eraseDups.map Atom.var
      let body ← projGoals sub
      pushAux ⟨⟨rel, vs ++ [tmpl]⟩, body⟩
      pure [⟨rel, vs ++ [res]⟩]
  | .transactiong tmpl sub => do
      -- Positive transaction certificates are committed first-solution
      -- derivations. Rollback is represented by the machine/spec step and
      -- has no positive SLD answer to project.
      let n ← freshK
      let rel := s!"txn{n}"
      let vs := (varsOfAtom tmpl ++ sub.flatMap varsOfGoal).eraseDups.map Atom.var
      let body ← projGoals sub
      pushAux ⟨⟨rel, vs⟩, body⟩
      pure [⟨rel, vs⟩]
  | .softcut tmpl sub thn els => do
      -- soft-cut powers case/unify [SPEC translator.pl:163-176, 388-399];
      -- both branches emitted, guards erased
      let n ← freshK
      let rel := s!"sc{n}"
      let vs := (varsOfAtom tmpl ++ (sub ++ thn ++ els).flatMap varsOfGoal).eraseDups.map Atom.var
      let sb ← projGoals sub
      let tb ← projGoals thn
      pushAux ⟨⟨rel, vs⟩, sb ++ tb⟩          -- some-branch
      let eb ← projGoals els
      pushAux ⟨⟨rel, vs⟩, eb⟩                -- guard-erased else-branch
      pure [⟨rel, vs⟩]
  | .callDyn hd args res =>
      pure [⟨"dyncall", [hd, chainOf args, res]⟩]
  | .findall tmpl sub res => do
      -- collapse = findall [SPEC translator.pl:115-116]: trusted collection
      let n ← freshK
      let rel := s!"coll{n}"
      let vs := (varsOfAtom tmpl ++ sub.flatMap varsOfGoal).eraseDups.map Atom.var
      let body ← projGoals sub
      pushAux ⟨⟨rel, vs ++ [tmpl]⟩, body⟩
      -- the trusted-collection body atom carries the enumeration call as a
      -- TERM; its kid is a tnode (checker skips the goal pairing)
      pure [⟨"collapse_t", [Atom.expr (Atom.sym rel :: vs), res]⟩]
  | .evalg v res => pure [⟨"eval_t", [v, res]⟩]
  | .catchg tmpl sub res => do
      -- Normal catch answers are the guarded sub-run's answers. Runtime/type
      -- exception reification is a separate machine fast path and is not
      -- claimed by this positive SLD certificate projection.
      let n ← freshK
      let rel := s!"catch{n}"
      let vs := (varsOfAtom tmpl ++ sub.flatMap varsOfGoal).eraseDups.map Atom.var
      let body ← projGoals sub
      pushAux ⟨⟨rel, vs ++ [tmpl]⟩, body⟩
      pure [⟨rel, vs ++ [res]⟩]
  | .wact _ _ _ => pure [⟨"unsupported§wact", []⟩]

partial def projGoals (gs : List Goal) : StateM PJ (List WAtom) := do
  let mut out : List WAtom := []
  for g in gs do
    out := out ++ (← projGoal g)
  pure out

partial def varsOfGoal (g : Goal) : List String :=
  match g with
  | .call _ args res => (args.map varsOfAtom).flatten ++ varsOfAtom res
  | .bin _ args res => (args.map varsOfAtom).flatten ++ varsOfAtom res
  | .callDyn h args res => varsOfAtom h ++ (args.map varsOfAtom).flatten ++ varsOfAtom res
  | .evalg v r => varsOfAtom v ++ varsOfAtom r
  | .catchg t sub r => varsOfAtom t ++ sub.flatMap varsOfGoal ++ varsOfAtom r
  | .softcut t sub thn els =>
      varsOfAtom t ++ (sub ++ thn ++ els).flatMap varsOfGoal
  | .eq a b | .compileAlias a b => varsOfAtom a ++ varsOfAtom b
  | .cut => [] | .cutAt _ => []
  | .findall t sub r => varsOfAtom t ++ sub.flatMap varsOfGoal ++ varsOfAtom r
  | .onceg t sub r => varsOfAtom t ++ sub.flatMap varsOfGoal ++ varsOfAtom r
  | .transactiong t sub => varsOfAtom t ++ sub.flatMap varsOfGoal
  | .amb bs r => bs.flatMap (fun (t, gs) => varsOfAtom t ++ gs.flatMap varsOfGoal) ++ varsOfAtom r
  | .ite c t e r => varsOfAtom c ++ varsOfAtom t.1 ++ t.2.flatMap varsOfGoal
      ++ varsOfAtom e.1 ++ e.2.flatMap varsOfGoal ++ varsOfAtom r
  | .spread v r => varsOfAtom v ++ varsOfAtom r
  | .smatch p => varsOfAtom p
  | .wact _ args res => (args.map varsOfAtom).flatten ++ varsOfAtom res
end

/-- The universal relations: unification, chain membership/append, and the
    reduce/3-shaped dynamic dispatch [SPEC translator.pl:50-64]. -/
def universalClauses (defs : List (String × Nat)) (binOps : List String) :
    List WClause :=
  let X := Atom.var "X§"; let H := Atom.var "H§"; let T := Atom.var "T§"
  let L := Atom.var "L§"; let R := Atom.var "R§"; let F := Atom.var "F§"
  let B := Atom.var "B§"; let As := Atom.var "As§"
  [ -- unification as the one universal fact
    ⟨⟨"ueq", [X, X]⟩, []⟩,
    -- spread = member/2 on cons-chains
    ⟨⟨"chain_member", [H, consC' H T]⟩, []⟩,
    ⟨⟨"chain_member", [X, consC' H T]⟩, [⟨"chain_member", [X, T]⟩]⟩,
    -- append/3 on cons-chains (partial application)
    ⟨⟨"chain_append", [nilA', L, L]⟩, []⟩,
    ⟨⟨"chain_append", [consC' H T, L, consC' H R]⟩,
      [⟨"chain_append", [T, L, R]⟩]⟩,
    -- partial(Base, Bound) applied: append the new args, re-dispatch
    ⟨⟨"dyncall", [consC' (Atom.sym "partial") (consC' F (consC' B nilA')),
                  As, R]⟩,
      [⟨"chain_append", [B, As, L]⟩, ⟨"dyncall", [F, L, R]⟩]⟩ ]
  -- per-defined-head bridges: dyncall(f, chain(A1..An), R) :- u_f(A1..An, R)
  ++ defs.map (fun (f, n) =>
      let vs := (List.range n).map (fun i => Atom.var s!"A§{i}")
      ⟨⟨"dyncall", [Atom.sym f, vs.foldr consC' nilA', R]⟩,
        [⟨"u_" ++ f, vs ++ [R]⟩]⟩)
  -- per-builtin bridges (binary ops through their oracle leaves)
  ++ binOps.map (fun op =>
      let a := Atom.var "A§0"; let b := Atom.var "A§1"
      ⟨⟨"dyncall", [Atom.sym op, consC' a (consC' b nilA'), R]⟩,
        [⟨binRel op, [a, b, R]⟩]⟩)
  -- guard-erased data fallback [SPEC translator.pl:62-64]
  ++ [⟨⟨"dyncall", [F, As, consC' F As]⟩, []⟩]
  -- CLAUSE-GROWN structural/boolean ops (moved OUT of the trusted oracle:
  -- these are pure Prolog — cons-chains ARE Prolog lists, translator.pl:3-8)
  ++ (let tS := Atom.sym "True"; let fS := Atom.sym "False"
      [ -- boolean truth tables (facts)
        ⟨⟨"b_and", [tS, tS, tS]⟩, []⟩, ⟨⟨"b_and", [tS, fS, fS]⟩, []⟩,
        ⟨⟨"b_and", [fS, tS, fS]⟩, []⟩, ⟨⟨"b_and", [fS, fS, fS]⟩, []⟩,
        ⟨⟨"b_or",  [tS, tS, tS]⟩, []⟩, ⟨⟨"b_or",  [tS, fS, tS]⟩, []⟩,
        ⟨⟨"b_or",  [fS, tS, tS]⟩, []⟩, ⟨⟨"b_or",  [fS, fS, fS]⟩, []⟩,
        ⟨⟨"b_xor", [tS, tS, fS]⟩, []⟩, ⟨⟨"b_xor", [tS, fS, tS]⟩, []⟩,
        ⟨⟨"b_xor", [fS, tS, tS]⟩, []⟩, ⟨⟨"b_xor", [fS, fS, fS]⟩, []⟩,
        ⟨⟨"b_not", [tS, fS]⟩, []⟩,     ⟨⟨"b_not", [fS, tS]⟩, []⟩,
        -- car/cdr/cons as pure facts
        ⟨⟨"car_c", [consC' H T, H]⟩, []⟩,
        ⟨⟨"cdr_c", [consC' H T, T]⟩, []⟩,
        ⟨⟨"cons_c", [H, T, consC' H T]⟩, []⟩,
        -- size/index as recursive relations over arithmetic leaves
        ⟨⟨"size_c", [nilA', Atom.gnd (Metta.Ground.int 0)]⟩, []⟩,
        ⟨⟨"size_c", [consC' H T, Atom.var "N§"]⟩,
          [⟨"size_c", [T, Atom.var "M§"]⟩,
           ⟨"plus", [Atom.var "M§", Atom.gnd (Metta.Ground.int 1),
                     Atom.var "N§"]⟩]⟩,
        ⟨⟨"index_c", [consC' H T, Atom.gnd (Metta.Ground.int 0), H]⟩, []⟩,
        ⟨⟨"index_c", [consC' H T, Atom.var "N§", X]⟩,
          [⟨"cmp_gt", [Atom.var "N§", Atom.gnd (Metta.Ground.int 0),
                       Atom.sym "True"]⟩,
           ⟨"minus", [Atom.var "N§", Atom.gnd (Metta.Ground.int 1),
                      Atom.var "M§"]⟩,
           ⟨"index_c", [T, Atom.var "M§", X]⟩]⟩,
        -- union-atom IS append on chains
        ⟨⟨"union_atom", [X, L, R]⟩, [⟨"chain_append", [X, L, R]⟩]⟩,
        -- min/max as two-clause relations over comparison leaves
        ⟨⟨"min", [X, L, X]⟩, [⟨"cmp_le", [X, L, Atom.sym "True"]⟩]⟩,
        ⟨⟨"min", [X, L, L]⟩, [⟨"cmp_gt", [X, L, Atom.sym "True"]⟩]⟩,
        ⟨⟨"max", [X, L, X]⟩, [⟨"cmp_ge", [X, L, Atom.sym "True"]⟩]⟩,
        ⟨⟨"max", [X, L, L]⟩, [⟨"cmp_lt", [X, L, Atom.sym "True"]⟩]⟩ ])

/-- Static compile environment used by answer-directed `eval_t` tracing. World
    effects are outside the certificate lane, so this is the source program's
    environment rather than a mutated runtime world. -/
def traceCEnv (prog : Prog) : CEnv :=
  mkEnv (fun n => (Metta.GroundingTable.lookup pleattaTable n).isSome)
    (prog.clauses.map (·.1)).eraseDups
    (prog.clauses.map (fun (f, c) => (f, c.params.length)))
    prog.typeDecls

/-- Project the whole compiled program (+ the initial space) to wire clauses.
    Returns (clauses, per-bang query aux info, eval tracing environment). -/
def projectProg (prog : Prog) (selfAtoms : List Atom)
    (queries : List (List Goal × Atom)) :
    List WClause × List (String × Atom) × CEnv := Id.run do
  let clauses := prog.clauses
  let defs := (clauses.map (fun (f, c) => (f, c.params.length))).eraseDups
  let binOps := ["+", "-", "*", "/", "%", "<", ">", "<=", ">=", "==",
                 "min", "max", "is-var", "=alpha",
                 "and", "or", "not", "xor",
                 "car-atom", "cdr-atom", "cons-atom", "size-atom", "index-atom",
                 "unique-atom", "alpha-unique-atom", "union-atom",
                 "intersection-atom", "subtraction-atom", "is-alpha-member",
                 "min-atom", "max-atom", "msort",
                 "sqrt-math", "sin-math", "cos-math", "tan-math",
                 "asin-math", "acos-math", "atan-math", "pow-math",
                 "log-math", "abs-math", "trunc-math", "ceil-math",
                 "floor-math", "round-math", "isnan-math", "isinf-math"]
  let mut st : PJ := {}
  let mut ws : List WClause := []
  for (f, c) in clauses do
    let (body, st') := (projGoals c.body).run st
    st := st'
    ws := ws ++ [⟨⟨"u_" ++ f, c.params ++ [c.result]⟩, body⟩]
  -- the space's atoms ARE fact clauses (the match story)
  let facts := selfAtoms.map (fun a => (⟨⟨"self", [a]⟩, []⟩ : WClause))
  -- per-bang query clauses
  let mut qs : List (String × Atom) := []
  let mut qcs : List WClause := []
  let mut i := 0
  for (goals, qterm) in queries do
    let (body, st') := (projGoals goals).run st
    st := st'
    qcs := qcs ++ [⟨⟨s!"query{i}", [qterm]⟩, body⟩]
    qs := qs ++ [(s!"query{i}", qterm)]
    i := i + 1
  pure (universalClauses defs binOps ++ ws ++ facts ++ st.aux ++ qcs, qs,
    traceCEnv prog)

/-! ## The answer-directed tree prover (first derivation, DFS, fuel-total) -/

inductive PTree where
  | node (g : WAtom) (ci : Nat) (binds : List (String × Atom))
         (kids : List PTree)
  | bnode (g : WAtom)
  | tnode (g : WAtom) (aux : List WClause) (kids : List PTree)
deriving Repr, Inhabited

/-- Resolve every stored atom through a substitution (used to MATERIALIZE a
    trusted collection's per-solution sub-derivation before its isolated
    bindings go out of scope). -/
partial def resolvePTree (b : Subst) : PTree → PTree
  | .node ⟨r, args⟩ ci binds kids =>
      .node ⟨r, args.map (subst b)⟩ ci
        (binds.map (fun (v, t) => (v, subst b t))) (kids.map (resolvePTree b))
  | .bnode ⟨r, args⟩ => .bnode ⟨r, args.map (subst b)⟩
  | .tnode ⟨r, args⟩ aux kids =>
      .tnode ⟨r, args.map (subst b)⟩ aux (kids.map (resolvePTree b))

/-- The REMAINING oracle leaves: genuinely grounded computation
    (arithmetic, comparisons, equality tests, and the set/sort family whose
    Prolog forms need disequality/ordering — not expressible in positive
    definite clauses). Booleans, structural chain ops, union, and min/max
    are CLAUSES now (see universalClauses). -/
def leafRels : List String :=
  ["plus", "minus", "times", "idiv", "imod", "cmp_lt", "cmp_gt", "cmp_le",
   "cmp_ge", "beq", "is_var", "alpha_eq",
   "unique_atom", "alpha_unique_atom",
   "intersection_atom", "subtraction_atom", "is_alpha_member",
   "min_atom", "max_atom", "msort",
   "sqrt_math", "sin_math", "cos_math", "tan_math", "asin_math", "acos_math",
   "atan_math", "pow_math", "log_math", "abs_math", "trunc_math",
   "ceil_math", "floor_math", "round_math", "isnan_math", "isinf_math"]

/-- Leaf rel → the engine's grounding-table op name (the SINGLE engine-side
    source of leaf semantics: evalLeaf delegates to pleattaTable, so the
    tracer cannot drift from the machine). -/
def leafOp : String → Option String
  | "plus" => some "+" | "minus" => some "-" | "times" => some "*"
  | "idiv" => some "/" | "imod" => some "%"
  | "cmp_lt" => some "<" | "cmp_gt" => some ">"
  | "cmp_le" => some "<=" | "cmp_ge" => some ">="
  | "beq" => some "==" | "is_var" => some "is-var"
  | "alpha_eq" => some "=alpha"
  | "unique_atom" => some "unique-atom"
  | "alpha_unique_atom" => some "alpha-unique-atom"
  | "intersection_atom" => some "intersection-atom"
  | "subtraction_atom" => some "subtraction-atom"
  | "is_alpha_member" => some "is-alpha-member"
  | "min_atom" => some "min-atom" | "max_atom" => some "max-atom"
  | "msort" => some "msort"
  | "sqrt_math" => some "sqrt-math" | "sin_math" => some "sin-math"
  | "cos_math" => some "cos-math" | "tan_math" => some "tan-math"
  | "asin_math" => some "asin-math" | "acos_math" => some "acos-math"
  | "atan_math" => some "atan-math" | "pow_math" => some "pow-math"
  | "log_math" => some "log-math" | "abs_math" => some "abs-math"
  | "trunc_math" => some "trunc-math" | "ceil_math" => some "ceil-math"
  | "floor_math" => some "floor-math" | "round_math" => some "round-math"
  | "isnan_math" => some "isnan-math" | "isinf_math" => some "isinf-math"
  | _ => none

/-- Evaluate a grounded oracle leaf by DELEGATING to the engine's own
    grounding table (pleattaTable) — one engine-side source of leaf
    semantics; the checker's independent oracle is the other side of the
    certificate. Only deterministic single-result ops qualify as leaves. -/
def evalLeaf (rel : String) (args : List Atom) (b : Subst) :
    Option Subst := do
  let av := args.map (subst b)
  let opName ← leafOp rel
  let g ← Metta.GroundingTable.lookup pleattaTable opName
  match g.impl av.dropLast with
  | Metta.ReduceResult.ok [r] =>
      match av.getLast? with
      | some res => unifyB b res (canonBool r)
      | none => none
  | _ => none


/-! ## The SLD prover: CPS with full backtracking (untrusted emitter — the
    trust lives in the checker; IO for the step-budget ref and collection
    accumulation). -/

structure PEnv where
  cs : Array WClause
  cenv : CEnv
  budget : IO.Ref Nat
  kref : IO.Ref Nat

def PEnv.freshK (env : PEnv) : IO Nat :=
  env.kref.modifyGet (fun n => (n, n + 1))

mutual
/-- Solve one goal; on each success call `cont`; `none` from cont = keep
    backtracking. -/
partial def solve {α : Type} (env : PEnv) (g : WAtom) (b : Subst)
    (cont : PTree → Subst → IO (Option α)) : IO (Option α) := do
  let n ← env.budget.get
  if n == 0 then return none
  env.budget.set (n - 1)
  if leafRels.contains g.rel then
    match evalLeaf g.rel g.args b with
    | some b' => cont (.bnode g) b'
    | none => return none
  else if g.rel == "collapse_t" then
    match g.args with
    | [Atom.expr (Atom.sym rel :: vs), res] =>
        match chainListM (subst b res) with
        | some items =>
            match (← proveItems env rel vs items b) with
            | some kids =>
                match unifyB b res (chainOf items) with
                | some b2 => cont (.tnode g [] kids) b2
                | none => return none
            | none => return none
        | none =>
            tryCollapsePrefixes env g rel vs res b cont
    | _ => return none
  else if g.rel == "eval_t" then
    match g.args with
    | [v, res] =>
        let vv := unchainify 10000 (subst b v)
        let start ← env.freshK
        match compileExprFresh env.cenv start vv with
        | .ok (t, gs, n') =>
            env.kref.set n'
            let projStart ← env.freshK
            let (body, st) := (projGoals (gs ++ [Goal.eq res t])).run { k := projStart }
            env.kref.set st.k
            let aux := st.aux
            let env' := { env with cs := (env.cs.toList ++ aux).toArray }
            solveSeq env' body b (fun kids b2 => cont (.tnode g aux kids) b2)
        | .error _ =>
            let idGoal : WAtom := ⟨"ueq", [res, chainify vv]⟩
            solve env idGoal b (fun kid b2 => cont (.tnode g [] [kid]) b2)
    | _ => return none
  else
    tryCl env g b 0 cont

/-- Prove every member in an already-materialized trusted collection.
    The collection claim itself remains trusted; each listed positive member is
    still checked as an ordinary SLD subtree. -/
partial def proveItems (env : PEnv) (rel : String) (vs : List Atom)
    (items : List Atom) (b : Subst) : IO (Option (List PTree)) := do
  match items with
  | [] => return some []
  | item :: rest =>
      match (← solve env ⟨rel, vs ++ [item]⟩ b
          (fun t b' => pure (some (resolvePTree b' t)))) with
      | none => return none
      | some t =>
          match (← proveItems env rel vs rest b) with
          | none => return none
          | some ts => return some (t :: ts)

/-- When a collection result variable is constrained later in the goal
    sequence, try finite prefixes of the derivable member stream and let the
    continuation select the answer-directed collection. -/
partial def tryCollapsePrefixes {α : Type} (env : PEnv) (g : WAtom)
    (rel : String) (vs : List Atom) (res : Atom) (b : Subst)
    (cont : PTree → Subst → IO (Option α)) : IO (Option α) := do
  match unifyB b res (chainOf []) with
  | some b0 =>
      match (← cont (.tnode g [] []) b0) with
      | some x => return some x
      | none => pure ()
  | none => pure ()
  let kv ← env.freshK
  let tv := Atom.var s!"T§{kv}"
  let acc ← IO.mkRef (α := List (PTree × Atom)) []
  solve env ⟨rel, vs ++ [tv]⟩ b
    (fun t b' => do
      let sols ← acc.get
      let item := subst b' tv
      let pt := resolvePTree b' t
      let kids := sols.map (·.1) ++ [pt]
      let items := sols.map (·.2) ++ [item]
      acc.set (sols ++ [(pt, item)])
      match unifyB b res (chainOf items) with
      | some b2 => cont (.tnode g [] kids) b2
      | none => pure none)

/-- Try clauses in order; backtrack into later clauses when downstream
    (including the caller's continuation) fails. -/
partial def tryCl {α : Type} (env : PEnv) (g : WAtom) (b : Subst) (ci : Nat)
    (cont : PTree → Subst → IO (Option α)) : IO (Option α) := do
  if h : ci < env.cs.size then
    let c := env.cs[ci]
    if c.head.rel != g.rel || c.head.args.length != g.args.length then
      tryCl env g b (ci + 1) cont
    else
      let k ← env.freshK
      let ps := c.head.args.map (renameAtom k)
      let body := c.body.map (fun w => (⟨w.rel, w.args.map (renameAtom k)⟩ : WAtom))
      match unifyB b (Atom.expr g.args) (Atom.expr ps) with
      | none => tryCl env g b (ci + 1) cont
      | some b' =>
        let origVars := (c.head.args ++ c.body.flatMap (·.args))
          |>.flatMap varsOfAtom |>.eraseDups
        let binds := origVars.map (fun v =>
          (v, Atom.var (v ++ "#" ++ toString k)))
        let r ← solveSeq env body b'
          (fun kids b2 => cont (.node g ci binds kids) b2)
        match r with
        | some x => return some x
        | none => tryCl env g b (ci + 1) cont
  else return none

/-- Solve a goal sequence left-to-right with full backtracking. -/
partial def solveSeq {α : Type} (env : PEnv) (gs : List WAtom) (b : Subst)
    (cont : List PTree → Subst → IO (Option α)) : IO (Option α) := do
  match gs with
  | [] => cont [] b
  | g :: rest =>
      solve env g b (fun t b' =>
        solveSeq env rest b' (fun ts b2 => cont (t :: ts) b2))
end

/-! ## Emission (byte format of mi.pl / Adapter.Sexp) -/

private def esc (s : String) : String :=
  (s.replace "\"" "§q§")

partial def termS (b : Subst) (a : Atom) : String :=
  match subst b a with
  | Atom.var v => s!"(v \"{esc v}\")"
  | Atom.sym s => s!"(c \"{esc s}\")"
  | Atom.gnd (Metta.Ground.int n) => s!"(c \"{n}\")"
  | Atom.gnd (Metta.Ground.float f) => s!"(c \"{f}\")"
  | Atom.gnd (Metta.Ground.str s) => s!"(c \"§str§{esc s}\")"
  | Atom.gnd g => s!"(c \"§gnd§{esc (reprStr g)}\")"
  | Atom.expr (Atom.sym h :: t) =>
      s!"(f \"{esc h}\"" ++ String.join ((t.map (fun e => " " ++ termS b e))) ++ ")"
  | Atom.expr es =>
      s!"(f \"§expr§\"" ++ String.join ((es.map (fun e => " " ++ termS b e))) ++ ")"

def atomS (b : Subst) (a : WAtom) : String :=
  s!"(atom \"{esc a.rel}\"" ++
    String.join (a.args.map (fun t => " " ++ termS b t)) ++ ")"

/-- Program clauses serialize UNSUBSTITUTED (original variable names). -/
def clauseS (c : WClause) : String :=
  s!"  (clause {atomS [] c.head}" ++
    String.join (c.body.map (fun a => " " ++ atomS [] a)) ++ ")"

partial def treeS (b : Subst) : PTree → String
  | .bnode g => s!"(bnode {atomS b g})"
  | .tnode g _ kids =>
      s!"(tnode {atomS b g}" ++
        String.join (kids.map (fun t => " " ++ treeS b t)) ++ ")"
  | .node g ci binds kids =>
      let bs := String.join (binds.map (fun (v, t) =>
        s!" (bind \"{esc v}\" {termS b t})"))
      s!"(node {atomS b g} {ci} ({bs})" ++
        String.join (kids.map (fun t => " " ++ treeS b t)) ++ ")"

partial def treeAux : PTree → List WClause
  | .bnode _ => []
  | .node _ _ _ kids => kids.flatMap treeAux
  | .tnode _ aux kids => aux ++ kids.flatMap treeAux

def emitTrace (cs : List WClause) (qrel : String) (answer : Atom)
    (tree : PTree) (b : Subst) : String :=
  let cs' := cs ++ treeAux tree
  "(program\n" ++ String.intercalate "\n" (cs'.map clauseS) ++ "\n)\n" ++
  s!"(query (atom \"{qrel}\" (v \"R§\")))\n" ++
  s!"(answer (bind \"R§\" {termS [] answer}))\n" ++
  s!"(proof {treeS b tree})\n"

/-- Re-derive one machine answer and emit its certificate text. -/
def traceAnswer (cs : List WClause) (cenv : CEnv) (qrel : String) (answer : Atom)
    (budget : Nat) : IO (Option String) := do
  let ref ← IO.mkRef budget
  let kref ← IO.mkRef 5000000
  let env : PEnv := { cs := cs.toArray, cenv, budget := ref, kref := kref }
  solve env ⟨qrel, [answer]⟩ []
    (fun t b => pure (some (emitTrace cs qrel answer t b)))

end PLeaTTa.Trace
