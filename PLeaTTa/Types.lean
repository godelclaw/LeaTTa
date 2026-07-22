-- SPDX-License-Identifier: Apache-2.0

/-
PLeaTTa — core PeTTa, done the LeaTTa way: the formal semantics of PeTTa in
Lean (PLeaTTa/Semantics.lean) comes FIRST; the executable machine
(PLeaTTa/Machine.lean) mirrors it; correspondence is proved, not hoped.

PeTTa's semantics IS compilation to definite clauses plus SLD resolution
(eager, leftmost, clause-ordered, cut, assert-survives-backtracking). These
are the shared syntactic types: compiled goals, clauses, programs.

See PETTA-LP.md for the informal statement of the compile equations and the
machine; this tree is the formal one.
-/
import MettaHyperonFull.Core.Atom
import MettaHyperonFull.Core.Substitution

namespace PLeaTTa

open Metta (Atom VarName Subst)

def selfSpace : Atom := Atom.sym "&self"

def spacePat (sp pat : Atom) : Atom :=
  Atom.expr [Atom.sym "#space", sp, pat]

def spacePatView : Atom → Atom × Atom
  | Atom.expr [Atom.sym "#space", sp, pat] => (sp, pat)
  | pat => (selfSpace, pat)

/-- A compiled goal. `cut` is compile-produced; `cutAt` is its runtime form,
    tagged at clause entry with the barrier index it cuts to. -/
inductive Goal where
  /-- Apply a defined function: `f(args…, res)` as a relation. -/
  | call (f : String) (args : List Atom) (res : Atom)
  /-- Grounded builtin (arithmetic, comparisons, tuple ops): ground-mode,
      delayed until its arguments are ground. -/
  | bin (op : String) (args : List Atom) (res : Atom)
  /-- Dynamic application: the head is a term (variable at compile time)
      that must resolve to a defined symbol at run time (first-class
      function values — `foldall`, `map`-style HOFs). -/
  | callDyn (head : Atom) (args : List Atom) (res : Atom)
  /-- Runtime evaluation of a VALUE (`eval`): a call-shaped chain applies;
      anything else evaluates to itself. (Full meta-circular translate-at-
      run-time — [SPEC metta.pl:245] — is the ledgered v2.) -/
  | evalg (val : Atom) (res : Atom)
  /-- Error-catching evaluation [SPEC translator.pl:293-300]: run the
      translated subexpression; ordinary failure remains failure, while a
      runtime/type exception is reified as an `(Error ...)` value. -/
  | catchg (tmpl : Atom) (sub : List Goal) (res : Atom)
  /-- Soft cut, Prolog's `(Sub -> Then ; Else)`: run `sub` to its FIRST
      answer; on success re-bind `tmpl ≐ instance` in the caller and run
      `thn`; on failure run `els`. Powers `unify/4` and first-match `case`
      (including the `Empty` arm on scrutinee failure). -/
  | softcut (tmpl : Atom) (sub : List Goal) (thn : List Goal)
            (els : List Goal)
  /-- Unification. -/
  | eq (a b : Atom)
  /-- Translation-time variable sharing emitted by pinned `build_branch/4`.
      Source-facing compiler entry points solve and erase every such marker
      over the whole expression or clause before execution.  Raw compiler
      proof surfaces retain it so the distinction from runtime unification is
      explicit; the machine treats an accidental leak as ordinary equality. -/
  | compileAlias (a b : Atom)
  /-- Committed choice, untagged (as compiled). -/
  | cut
  /-- Committed choice, tagged with the clause-entry barrier index. -/
  | cutAt (n : Nat)
  /-- Exhaustive collection: run `sub` to completion, bind `res` to the tuple
      of `tmpl` instances in answer order. -/
  | findall (tmpl : Atom) (sub : List Goal) (res : Atom)
  /-- Committed sub-goal (`once`): run `sub` to its FIRST answer, bind `res`
      to that answer's `tmpl` instance. Opaque to outer cut (Prolog `once/1`
      is `call`-scoped, not clause-scoped). -/
  | onceg (tmpl : Atom) (sub : List Goal) (res : Atom)
  /-- SWI `transaction/1`: run a committed first solution; commit world
      mutations on success and restore the entry world on failure. `tmpl`
      carries source-visible bindings back to the caller. -/
  | transactiong (tmpl : Atom) (sub : List Goal)
  /-- Branch-local nondeterminism (`superpose`): one alternative per element,
      each with its own compiled goals. -/
  | amb (branches : List (Atom × List Goal)) (res : Atom)
  /-- Runtime spread: enumerate the members of an already-computed chain
      value (`superpose` over a variable/computed tuple). -/
  | spread (val : Atom) (res : Atom)
  /-- `(if c t e)`: `cond` is already a value/variable (its goals were
      emitted before); only the taken branch's goals run. -/
  | ite (cond : Atom) (thn : Atom × List Goal) (els : Atom × List Goal)
        (res : Atom)
  /-- Match a pattern against the current space's atoms (snapshot: an open
      match does not see later additions — the logical update view). -/
  | smatch (pat : Atom)
  /-- World effect (`add-atom`, `remove-atom`, …): immediate, sequenced,
      NOT undone on backtracking (Prolog assert discipline). -/
  | wact (op : String) (args : List Atom) (res : Atom)
deriving Repr, Inhabited, BEq

mutual

/-- Apply a substitution throughout one compiled goal. -/
def instantiateGoal (s : Subst) : Goal → Goal
  | .call f args res =>
      .call f (args.map (Metta.Subst.apply s)) (Metta.Subst.apply s res)
  | .bin op args res =>
      .bin op (args.map (Metta.Subst.apply s)) (Metta.Subst.apply s res)
  | .callDyn head args res =>
      .callDyn (Metta.Subst.apply s head)
        (args.map (Metta.Subst.apply s)) (Metta.Subst.apply s res)
  | .evalg val res =>
      .evalg (Metta.Subst.apply s val) (Metta.Subst.apply s res)
  | .catchg tmpl sub res =>
      .catchg (Metta.Subst.apply s tmpl) (instantiateGoals s sub)
        (Metta.Subst.apply s res)
  | .softcut tmpl sub thn els =>
      .softcut (Metta.Subst.apply s tmpl) (instantiateGoals s sub)
        (instantiateGoals s thn) (instantiateGoals s els)
  | .eq a b => .eq (Metta.Subst.apply s a) (Metta.Subst.apply s b)
  | .compileAlias a b =>
      .compileAlias (Metta.Subst.apply s a) (Metta.Subst.apply s b)
  | .cut => .cut
  | .cutAt n => .cutAt n
  | .findall tmpl sub res =>
      .findall (Metta.Subst.apply s tmpl) (instantiateGoals s sub)
        (Metta.Subst.apply s res)
  | .onceg tmpl sub res =>
      .onceg (Metta.Subst.apply s tmpl) (instantiateGoals s sub)
        (Metta.Subst.apply s res)
  | .transactiong tmpl sub =>
      .transactiong (Metta.Subst.apply s tmpl) (instantiateGoals s sub)
  | .amb branches res =>
      .amb (instantiateBranches s branches) (Metta.Subst.apply s res)
  | .spread val res =>
      .spread (Metta.Subst.apply s val) (Metta.Subst.apply s res)
  | .ite cond thn els res =>
      .ite (Metta.Subst.apply s cond)
        (Metta.Subst.apply s thn.1, instantiateGoals s thn.2)
        (Metta.Subst.apply s els.1, instantiateGoals s els.2)
        (Metta.Subst.apply s res)
  | .smatch pat => .smatch (Metta.Subst.apply s pat)
  | .wact op args res =>
      .wact op (args.map (Metta.Subst.apply s)) (Metta.Subst.apply s res)

/-- Apply a substitution throughout a compiled goal sequence. -/
def instantiateGoals (s : Subst) : List Goal → List Goal
  | [] => []
  | g :: gs => instantiateGoal s g :: instantiateGoals s gs

/-- Apply a substitution throughout nondeterministic compiled branches. -/
def instantiateBranches (s : Subst) : List (Atom × List Goal) →
    List (Atom × List Goal)
  | [] => []
  | (tmpl, goals) :: rest =>
      (Metta.Subst.apply s tmpl, instantiateGoals s goals) ::
        instantiateBranches s rest

end

/-- A compiled clause of a defined function `f`:
    `f(params…, result) :- body.` (kept in source order). -/
structure Clause where
  params : List Atom
  result : Atom
  body : List Goal
deriving Repr, Inhabited, BEq

/-- One source clause retained for higher-order specialization.  The source
    syntax is kept alongside its generic compiled IR so generated clauses can
    remain observable without recompiling a different semantics.

    Native PeTTa records these entries newest-first in `fun_meta` while
    translating a clause [SPEC translator.pl:18-24]. -/
structure MetaClause where
  parent : String
  sourceParams : List Atom
  sourceBody : Atom
  /-- Optional α-key of the visible source clause.  Ordinary captures can
      derive it from `compiled`; generated captures keep executable IR in
      `compiled` and store the distinct visible removal key here. -/
  sourceKey : String := ""
  compiled : Clause
deriving Repr, Inhabited, BEq

/-- Structural identity of a specialization.  Public names are a rendering
    of this key, but reuse and cycle detection compare the structure itself.
    [SPEC specializer.pl:18-31] -/
structure SpecKey where
  parent : String
  bindings : List Atom
deriving Repr, Inhabited, BEq

/-- A committed specialization and its stable public function name. -/
structure SpecRecord where
  key : SpecKey
  name : String
deriving Repr, Inhabited, BEq

/-- Proof-facing provenance for one installed specialization clause.  The
    executable never consults this ledger: it records the exact parent,
    binding, guarded normal form, and recursively rewritten clause produced
    by the transactional builder so semantic simulation does not need to
    invert public names or clause lowering. -/
structure SpecClauseProvenance where
  name : String
  parent : String
  parentClause : Clause
  /-- Binding before PeTTa's clause-local `copy_term` boundary.  Retained
      only as proof evidence for the generated binding's alpha-copy origin. -/
  sourceBinding : Subst := []
  /-- Static actual tuple from the discovery call site.  The executable does
      not consult it; call simulation uses it to reconnect a generated clause
      to the exact specialization request that produced it. -/
  discoveryActuals : List Atom := []
  binding : Subst
  guardedClause : Clause
  executableClause : Clause
deriving Repr, Inhabited, BEq

/-- A compiled program: named clauses in source order, plus the space's
    initial fact atoms and stored type declarations. -/
structure Prog where
  clauses : List (String × Clause)
  facts : List Atom
  typeDecls : List (Atom × Atom)   -- (subject, type)
deriving Repr, Inhabited

def Prog.clausesOf (p : Prog) (f : String) : List Clause :=
  p.clauses.filterMap (fun (n, c) => if n == f then some c else none)

end PLeaTTa
