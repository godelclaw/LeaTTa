/-
Module: PLeaTTa.Proofs.PredicateAdequacy
Purpose: Source-anchored representation and runtime facts for PeTTa's
  `Predicate/2` (`=../2`) conversion.
Trusted boundary: none
-/
import PLeaTTa.Proofs.CompilerAdequacy
import PLeaTTa.Machine

namespace PLeaTTa.PredicateAdequacy

open Metta (Atom ReduceResult)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.PeTTaSpec.PrologCore

/-- Contextual agreement for values produced by pinned `Predicate/2`.

This deliberately does not extend ordinary `TermAgrees`: the executable
cons-chain represents a source Prolog list, whereas a positive-arity Prolog
compound carries the private `prologCompoundC` provenance tag.  The nonempty
constructor also keeps `=../2`'s singleton-list/atom case structurally
separate. [SPEC metta.pl:275] -/
inductive PredicatePayloadAgrees : Term → Atom → Prop where
  | atom {term : Term} {runtime : Atom}
      (agreement : TermAgrees term runtime) :
      PredicatePayloadAgrees term runtime
  | compound {functor : String} {firstTerm : Term} {terms : List Term}
      {firstAtom : Atom} {atoms : List Atom}
      (head : TermAgrees firstTerm firstAtom)
      (tail : TermsAgree terms atoms) :
      PredicatePayloadAgrees
        (.compound functor (firstTerm :: terms))
        (prologCompoundC functor (chainOf (firstAtom :: atoms)))

/-- The contextual positive-arity compound representation cannot be decoded
as a source Prolog list. -/
theorem compound_not_proper_list (functor : String) (first : Atom)
    (rest : List Atom) :
    chainListM (prologCompoundC functor (chainOf (first :: rest))) = none := by
  simp

/-- Predicate/2 and the compiler overlap at exactly the pinned `partial/2`
term.  This replaces the former provenance-disjointness claim and pins both
the functor and the two-field argument spine. -/
theorem compound_eq_partial_iff (compoundFunctor partialFunctor : String)
    (compoundArguments partialArguments : Atom) :
    prologCompoundC compoundFunctor compoundArguments =
        partialC partialFunctor partialArguments ↔
      compoundFunctor = "partial" ∧
        compoundArguments = chainOf [.sym partialFunctor, partialArguments] := by
  constructor
  · exact prologCompoundC_injective
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Observation erases only the private compound tag and recursively exposes
the exact source-shaped arguments. -/
theorem unchainify_compound (fuel : Nat) (functor : String)
    (arguments : List Atom) :
    unchainify (fuel + 1) (prologCompoundC functor (chainOf arguments)) =
      .expr (.sym functor :: arguments.map (unchainify fuel)) := by
  simp only [unchainify, prologCompoundView?_prologCompoundC,
    chainListM_chainOf_exact]

/-- Positive-arity `=../2` conversion is exact and retains provenance. -/
theorem predicateOp_compound (functor : String) (first : Atom)
    (rest : List Atom) :
    predicateOp [chainOf (.sym functor :: first :: rest)] =
      .ok [prologCompoundC functor (chainOf (first :: rest))] := by
  rw [chainOf_cons]
  simp [predicateOp, consC]

/-- A singleton input list is the zero-arity Prolog atom case. -/
theorem predicateOp_atom (functor : String) :
    predicateOp [chainOf [.sym functor]] = .ok [.sym functor] := by
  rw [chainOf_cons]
  simp [predicateOp, consC]

/-- The empty list does not match pinned `Predicate([F|Args], Term)`. -/
theorem predicateOp_empty : predicateOp [nilA] = .noReduce := by
  rfl

/-- A bare variable first matches `[F|Args]`, then `=../2` observes an open
functor and raises an instantiation error. -/
theorem predicateOp_bare_variable (name : String) :
    predicateOp [.var name] =
      .runtimeError "=../2: Arguments are not sufficiently instantiated" := by
  rfl

/-- The same instantiation error arises from an explicit proper list whose
functor remains open after substitution. -/
theorem predicateOp_open_functor (name : String) (arguments : List Atom) :
    predicateOp [chainOf (.var name :: arguments)] =
      .runtimeError "=../2: Arguments are not sufficiently instantiated" := by
  rw [chainOf_cons]
  simp [predicateOp, consC]

/-- A non-atom functor takes the distinct `type_error(atom, Actual)` lane. -/
theorem predicateOp_nonatom_functor (actual first : Atom)
    (rest : List Atom)
    (notSymbol : ∀ name, actual ≠ .sym name)
    (notVariable : ∀ name, actual ≠ .var name) :
    predicateOp [chainOf (actual :: first :: rest)] =
      .incorrectArgument "=../2: atom functor expected" := by
  rw [chainOf_cons]
  cases actual <;> simp_all [predicateOp, consC]

/-- The executable error preflight preserves pinned's structured
instantiation exception rather than laundering it through a message string. -/
theorem bare_variable_error_exact (name : String) :
    predicateErrorAtom? [.var name] = some predicateInstantiationErrorAtom := by
  rfl

/-- The executable error preflight retains the offending non-atom term in the
structured type exception. -/
theorem nonatom_error_exact (actual first : Atom) (rest : List Atom)
    (notSymbol : ∀ name, actual ≠ .sym name)
    (notVariable : ∀ name, actual ≠ .var name) :
    predicateErrorAtom? [chainOf (actual :: first :: rest)] =
      some (predicateTypeErrorAtom actual) := by
  rw [chainOf_cons]
  cases actual <;> simp_all [predicateErrorAtom?, consC]

private def taggedFact : Atom :=
  prologCompoundC "probe" (chainOf [.sym "input", .sym "output"])

private def rawQuotedFact : Atom :=
  chainOf [.sym "probe", .sym "input", .sym "output"]

/-- A privately tagged function-convention fact decodes to the exact local
clause consumed by ordered resolution. -/
theorem tagged_fact_decodes :
    predicateClause? pleattaTable taggedFact =
      some ("probe",
        { params := [.sym "input"], result := .sym "output", body := [] }) := by
  rfl

/-- The same privately tagged value is decoded by the typed Prolog-call
boundary, including its exact ordered arguments.  This is the handoff used by
`callPredicate` after the local `Predicate` builtin has constructed a value. -/
theorem tagged_fact_builds_call :
    buildPrologCall taggedFact =
      some ("probe", [.atom "input", .atom "output"], []) := by
  unfold buildPrologCall deepUnchain taggedFact
  rw [unchainify_compound]
  simp [atomToPrologTerm, prologVars, prologVarsRaw, prologVarsRawList]

/-- The same cons-chain without `Predicate` provenance is merely a quoted
source list and cannot install a Prolog clause.  This is the anti-forgery
witness for the representation split. -/
theorem raw_quoted_fact_rejected :
    predicateClause? pleattaTable rawQuotedFact = none := by
  rfl

private def rawPredicateClause : Clause :=
  { params := []
    result := .sym "value"
    body := [] }

private def rawAssertedWorld : PWorld :=
  installPredicateClause ({} : PWorld) false "raw-prolog" rawPredicateClause

/-- A raw `assertzPredicate` clause becomes directly callable Prolog state
without entering PeTTa's separate `fun/1` registry.  This exact distinction
prevents later clause-shaped Predicate payloads from executing merely because
an earlier assertion used the same functor. -/
theorem raw_assertion_does_not_register :
    rawAssertedWorld.isRegisteredHead "raw-prolog" = false ∧
    rawAssertedWorld.progClauses = [("raw-prolog", rawPredicateClause)] := by
  constructor <;> rfl

private def rawAssertedDynamicCall : Conf :=
  { cur := some
      ([Goal.callDyn (.sym "raw-prolog") [.sym "payload"] (.var "result")], [])
    alts := []
    world := rawAssertedWorld
    counter := 10
    qterm := .var "result" }

private def emptyProg : Prog :=
  { clauses := []
    facts := []
    typeDecls := [] }

/-- Anti-vacuity witness: changing dynamic dispatch back to “any live clause
means a MeTTa function” makes this exact transition false.  The raw Prolog
clause is present, but the unregistered source expression remains data. -/
theorem raw_asserted_head_remains_dynamic_data :
    step emptyProg [] 10 rawAssertedDynamicCall =
      { rawAssertedDynamicCall with
        cur := some
          ([Goal.eq (.var "result")
            (chainOf [.sym "raw-prolog", .sym "payload"])], []) } := by
  have noBuiltin :
      Metta.GroundingTable.lookup [] "raw-prolog" = none := rfl
  simp [rawAssertedDynamicCall, step, raw_assertion_does_not_register.1,
    noBuiltin]

/-- Concrete source definition used by the executable expected-divergence
gate for pinned SWI's static-procedure protection. -/
def predicateShadowingDefinition : Atom :=
  .expr [.sym "=", .expr [.sym "Predicate", .var "value"], .sym "shadowed"]

/-- PLeaTTa's current source registrar accepts the attempted definition;
pinned PeTTa instead fails while asserting the resulting clause into static
`Predicate/2`.  This theorem pins the executable side of that known FAIL. -/
theorem shadowing_definition_is_registered :
    sourceFunctionArity? predicateShadowingDefinition =
      some ("Predicate", 1) := by
  rfl

/-- Special-form dispatch remains builtin-owned even after that source
registration event, explaining why the executable fixture still evaluates
the owned conversion instead of the attempted definition. -/
theorem predicate_dispatch_is_special :
    classifyAppCoreHead "Predicate" = .hPredicate := by
  rfl

end PLeaTTa.PredicateAdequacy
