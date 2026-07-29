-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguComposition
Purpose: Compose an open residual-MGU quotient with the carried source and
  executable substitutions on one explicit observable alpha support.
Trusted boundary: none
Main exports:
  installGenerated,
  continuationAlphaSupport,
  AlphaCumulativeResidualVariantAgreesOn,
  AlphaResidualVariantAgreesOn.carry,
  AlphaResidualVariantAgrees.carryTrimForContinuation,
  AlphaCumulativeResidualVariantAgreesOn.trimFor
-/
import PLeaTTa.PersistentSubst
import PLeaTTa.Proofs.PrologGoalMguVariant

namespace PLeaTTa.PrologMguComposition

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PrologGoalAlpha
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant

/-!
The independently ordered source MGU and the executable MGU may orient one
residual alias differently.  Consequently, composing the carried bindings
cannot honestly restore pointwise equality with the source MGU.  The
relations below retain the same residual representative and compose both
carried states only on an explicit observable support.
-/

/-- The exact installation policy used by executable `unifyB`: an empty
generated MGU preserves the carried state literally; a nonempty generated
MGU is eagerly composed over it.  Naming this operation keeps subsequent
proof interfaces independent of eliminator details for the list case split. -/
def installGenerated (generated base : Subst) : Subst :=
  match generated with
  | [] => base
  | _ :: _ => Metta.Subst.compose generated base

/-- The carried independent state fixes every source identity observed by
one alpha subgraph. -/
def AlphaReferenceIdentitiesFixed
    (support : List (LogicVar × String))
    (binding : Substitution) : Prop :=
  ∀ {identity name}, (identity, name) ∈ support →
    binding.applyTerm (.variable identity) = .variable identity

/-- The carried executable state has no lookup for every runtime name
observed by one alpha subgraph. -/
def AlphaRuntimeNamesAvoid
    (support : List (LogicVar × String)) (binding : Subst) : Prop :=
  ∀ {identity name}, (identity, name) ∈ support →
    Metta.Subst.lookup binding name = none

/-- A conservative executable check that one independent identity is not a
source key of the carried independent substitution.  Absence is stronger
than semantic fixedness, but it is decidable and sufficient to prove
fixedness without comparing open source terms for equality. -/
def referenceIdentityUnbound
    (binding : Substitution) (identity : LogicVar) : Bool :=
  binding.all fun entry => entry.1 != identity

/-- A carried source substitution fixes every identity that is absent from
its source-key list. -/
theorem referenceIdentityUnbound_applyTerm
    (binding : Substitution) (identity : LogicVar)
    (unbound : referenceIdentityUnbound binding identity = true) :
    binding.applyTerm (.variable identity) = .variable identity := by
  induction binding with
  | nil =>
      rfl
  | cons entry rest induction =>
      rcases entry with ⟨source, replacement⟩
      simp only [referenceIdentityUnbound, List.all_cons,
        Bool.and_eq_true, bne_iff_ne] at unbound
      simp only [Substitution.applyTerm, induction unbound.2,
        Term.instantiateOne]
      exact if_neg (Ne.symm unbound.1)

/-- A conservative subgraph selected for the carried-state and `trimFor`
proofs using only executable checks.

An alpha graph may legally contain unused links.  Filtering is therefore
essential: graph membership alone cannot imply that a name is an observable
trim root.  Source-key absence and runtime lookup absence ensure that the
older carried states cannot rewrite a selected link. -/
def continuationAlphaSupport
    (alpha : List (LogicVar × String))
    (referenceBase : Substitution) (runtimeBase : Subst)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    List (LogicVar × String) :=
  alpha.filter fun pair =>
    referenceIdentityUnbound referenceBase pair.1 &&
      (Metta.Subst.lookup runtimeBase pair.2).isNone &&
      PLeaTTa.isTrimRoot goals qterm pair.2

theorem mem_continuationAlphaSupport_iff
    {alpha : List (LogicVar × String)}
    {referenceBase : Substitution} {runtimeBase : Subst}
    {goals : List PLeaTTa.Goal} {qterm : Atom}
    {identity : LogicVar} {name : String} :
    (identity, name) ∈
        continuationAlphaSupport
          alpha referenceBase runtimeBase goals qterm ↔
      (identity, name) ∈ alpha ∧
        referenceIdentityUnbound referenceBase identity = true ∧
        Metta.Subst.lookup runtimeBase name = none ∧
        PLeaTTa.isTrimRoot goals qterm name = true := by
  simp [continuationAlphaSupport, Bool.and_eq_true, and_assoc]

theorem continuationAlphaSupport.included
    (alpha : List (LogicVar × String))
    (referenceBase : Substitution) (runtimeBase : Subst)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    ∀ pair,
      pair ∈
          continuationAlphaSupport
            alpha referenceBase runtimeBase goals qterm →
        pair ∈ alpha := by
  intro pair member
  rcases pair with ⟨identity, name⟩
  exact (mem_continuationAlphaSupport_iff.mp member).1

theorem continuationAlphaSupport.referenceFixed
    (alpha : List (LogicVar × String))
    (referenceBase : Substitution) (runtimeBase : Subst)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    AlphaReferenceIdentitiesFixed
      (continuationAlphaSupport
        alpha referenceBase runtimeBase goals qterm)
      referenceBase := by
  intro identity name member
  exact referenceIdentityUnbound_applyTerm referenceBase identity
    (mem_continuationAlphaSupport_iff.mp member).2.1

theorem continuationAlphaSupport.runtimeAvoids
    (alpha : List (LogicVar × String))
    (referenceBase : Substitution) (runtimeBase : Subst)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    AlphaRuntimeNamesAvoid
      (continuationAlphaSupport
        alpha referenceBase runtimeBase goals qterm)
      runtimeBase := by
  intro identity name member
  exact (mem_continuationAlphaSupport_iff.mp member).2.2.1

theorem continuationAlphaSupport.live
    (alpha : List (LogicVar × String))
    (referenceBase : Substitution) (runtimeBase : Subst)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    AlphaRuntimeNamesLive
      (continuationAlphaSupport
        alpha referenceBase runtimeBase goals qterm)
      goals qterm := by
  intro identity name member
  exact (mem_continuationAlphaSupport_iff.mp member).2.2.2

/-- The support extractor is not definitionally empty: an unbound source
identity paired with a live, unbound runtime name survives. -/
theorem continuationAlphaSupport_keeps_live_unbound_link :
    (LogicVar.source "X", "x") ∈
      continuationAlphaSupport
        [(LogicVar.source "X", "x")] [] [] [] (.var "x") := by
  exact mem_continuationAlphaSupport_iff.mpr
    ⟨by simp, by simp [referenceIdentityUnbound],
      by simp [Metta.Subst.lookup], PLeaTTa.isTrimRoot_qterm_var [] "x"⟩

/-- Conversely, a runtime name already owned by the carried substitution is
excluded even when it is live.  This is the executable side of the
load-bearing avoidance condition used by `carry`. -/
theorem continuationAlphaSupport_drops_carried_runtime_link :
    (LogicVar.source "X", "x") ∉
      continuationAlphaSupport
        [(LogicVar.source "X", "x")] []
        [("x", .sym "carried")] [] (.var "x") := by
  intro member
  have lookupNone :=
    (mem_continuationAlphaSupport_iff.mp member).2.2.1
  simp [Metta.Subst.lookup] at lookupNone

/-- One residual-MGU representative after composing the older independent
and executable states.

`canonical` remains the actual independently ordered head MGU.  The hidden
`representative` is a mutual semantic variant of it and is the only
orientation used to interpret the runtime substitution.  The older
independent state is appended to that representative in the same order as
source clause entry. -/
def AlphaCumulativeResidualVariantAgreesOn
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Subst) : Prop :=
  ∃ representative : TreeSubstitution,
    TreeSubstitutionVariants canonical representative ∧
    TreeSubstitutionTopological canonical ∧
    TreeSubstitutionTopological representative ∧
    Nonempty (PLeaTTa.SubstTopological runtime) ∧
    AlphaValuationAgreesOn alpha support
      (representative ++ Substitution.denote referenceBase) runtime

/-- Exact goal/control structure paired with the cumulative residual
valuation used by an entered local task.  No whole-goal substitution or
hidden-field commutation is asserted. -/
def AlphaGoalsCumulativeResidualVariantAgreesOn
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Subst)
    (references : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal) : Prop :=
  AlphaGoalsAgree alpha barrier references executables ∧
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase runtime

/-- Compose one residual-MGU quotient with both carried states on a support
that those older states cannot rewrite.

The generated executable block must avoid the base domain.  This is exactly
the invariant established by `unifyTopExact_avoidsExternal` for normalized
inputs; it is stated independently here so the composition theorem does not
depend on a particular unifier entry point. -/
theorem AlphaResidualVariantAgreesOn.carry
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {generated base installed : Subst}
    {referenceBase : Substitution}
    (agreement :
      AlphaResidualVariantAgreesOn alpha support canonical generated)
    (baseTopological : PLeaTTa.SubstTopological base)
    (generatedAvoidsBase : PLeaTTa.SubstEntriesAvoid base generated)
    (referenceFixed :
      AlphaReferenceIdentitiesFixed support referenceBase)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support base)
    (installedShape :
      installed = installGenerated generated base) :
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase installed := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeTopological, ⟨generatedTopological⟩, valuation⟩
  have installedTopological :
      PLeaTTa.SubstTopological installed := by
    cases generated with
    | nil =>
        have installedEq : installed = base := by
          simpa [installGenerated] using installedShape
        rw [installedEq]
        exact baseTopological
    | cons head tail =>
        rw [installedShape]
        simp only [installGenerated]
        exact PLeaTTa.SubstTopological.compose_of_avoids
          base (head :: tail) baseTopological generatedTopological
          generatedAvoidsBase
  have installedSubstEqGenerated
      (atom : Atom) (atomAvoids : PLeaTTa.AtomAvoids base atom) :
      PLeaTTa.subst installed atom =
        PLeaTTa.subst generated atom := by
    cases generated with
    | nil =>
        rw [installedShape]
        simp only [installGenerated]
        rw [PLeaTTa.subst_eq_self_of_domain_free base atom atomAvoids]
        simp
    | cons head tail =>
        rw [installedShape]
        simp only [installGenerated]
        exact PLeaTTa.PersistentSubst.subst_compose_eq_generated_of_avoids
          base (head :: tail) baseTopological generatedTopological
          generatedAvoidsBase atomAvoids
  refine
    ⟨representative, variants, canonicalTopological,
      representativeTopological, ⟨installedTopological⟩, ?_⟩
  intro identity name linked
  have referenceBaseFixed :
      TreeSubstitution.apply (Substitution.denote referenceBase)
          (.variable identity) =
        .variable identity := by
    have fixed := congrArg Term.denote (referenceFixed linked)
    simpa only [Substitution.denote_applyTerm, Term.denote] using fixed
  have referenceEq :
      TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (.variable identity) =
        TreeSubstitution.apply representative (.variable identity) := by
    rw [TreeSubstitution.apply_append, referenceBaseFixed]
  have runtimeAtomAvoids :
      PLeaTTa.AtomAvoids base (.var name) := by
    intro candidate member
    simp only [Atom.vars, List.mem_singleton] at member
    subst candidate
    exact runtimeAvoids linked
  have runtimeEq :
      PLeaTTa.subst installed (.var name) =
        PLeaTTa.subst generated (.var name) :=
    installedSubstEqGenerated (.var name) runtimeAtomAvoids
  rw [referenceEq, runtimeEq]
  exact valuation linked

/-- Liveness trimming changes only the executable spelling of a cumulative
residual state and preserves the same observable representative. -/
theorem AlphaCumulativeResidualVariantAgreesOn.trimFor
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Subst}
    (agreement :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support canonical referenceBase runtime)
    {goals : List PLeaTTa.Goal} {qterm : Atom}
    (live : AlphaRuntimeNamesLive support goals qterm) :
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase
        (PLeaTTa.trimFor goals qterm runtime) := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeTopological, ⟨runtimeTopological⟩, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      representativeTopological,
      ⟨PLeaTTa.SubstTopological.trimFor
        goals qterm runtime runtimeTopological⟩,
      AlphaValuationAgreesOn.trimFor
        valuation runtimeTopological live⟩

/-- Goal/control structure is unaffected by liveness trimming; only its
explicit observable valuation is restricted through the runtime state. -/
theorem AlphaGoalsCumulativeResidualVariantAgreesOn.trimFor
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      AlphaGoalsCumulativeResidualVariantAgreesOn
        alpha support barrier canonical referenceBase runtime
        references executables)
    {goals : List PLeaTTa.Goal} {qterm : Atom}
    (live : AlphaRuntimeNamesLive support goals qterm) :
    AlphaGoalsCumulativeResidualVariantAgreesOn
      alpha support barrier canonical referenceBase
        (PLeaTTa.trimFor goals qterm runtime)
        references executables :=
  ⟨agreement.1, agreement.2.trimFor live⟩

/-- Compose and trim on the structurally extracted continuation support.

This theorem discharges all three *safety* premises of carried-state
composition.  It deliberately does not assert that the extracted support is
complete for every future observation; that is a separate compiler/caller
invariant rather than a fact obtainable from an arbitrary alpha graph. -/
theorem AlphaResidualVariantAgrees.carryTrimForContinuation
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {generated base installed : Subst}
    {referenceBase : Substitution}
    (agreement :
      AlphaResidualVariantAgrees alpha canonical generated)
    (baseTopological : PLeaTTa.SubstTopological base)
    (generatedAvoidsBase : PLeaTTa.SubstEntriesAvoid base generated)
    (installedShape :
      installed = installGenerated generated base)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    AlphaCumulativeResidualVariantAgreesOn
      alpha
      (continuationAlphaSupport
        alpha referenceBase base goals qterm)
      canonical referenceBase
      (PLeaTTa.trimFor goals qterm installed) := by
  have cumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha
        (continuationAlphaSupport
          alpha referenceBase base goals qterm)
        canonical referenceBase installed :=
    AlphaResidualVariantAgreesOn.carry
      (agreement.on
        (continuationAlphaSupport.included
          alpha referenceBase base goals qterm))
      baseTopological generatedAvoidsBase
      (continuationAlphaSupport.referenceFixed
        alpha referenceBase base goals qterm)
      (continuationAlphaSupport.runtimeAvoids
        alpha referenceBase base goals qterm)
      installedShape
  exact cumulative.trimFor
    (continuationAlphaSupport.live
      alpha referenceBase base goals qterm)

/-- The runtime-avoidance premise of `AlphaResidualVariantAgreesOn.carry`
is load-bearing.  Even with no generated MGU at all, observing a name in the
carried base domain changes its value, so it cannot be compared using the
pre-carry residual valuation. -/
theorem carried_runtime_avoidance_is_necessary :
    PLeaTTa.subst
        (installGenerated [] [("x", .sym "carried")]) (.var "x") ≠
      PLeaTTa.subst [] (.var "x") := by
  simp [installGenerated, Metta.Subst.lookup]

end PLeaTTa.PrologMguComposition
