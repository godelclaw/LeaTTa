-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologGoalMguVariant
Purpose: Preserve exact goal/control structure while interpreting every
  related term leaf through one shared residual-MGU representative.
Trusted boundary: none
Main exports:
  AlphaGoalsAgree.mono,
  AlphaGoalsResidualVariantAgrees,
  AlphaGoalsResidualVariantAgrees.term
-/
import PLeaTTa.Proofs.PrologGoalAlpha
import PLeaTTa.Proofs.PrologMguVariant

namespace PLeaTTa.PrologGoalMguVariant

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open CompilerAdequacy
open PrologStateBridge
open PrologGoalAlpha
open PrologPrefilterBridge
open PrologMguBridge
open PrologMguTopology
open PrologMguVariant

/-!
The executable unifier and the independently ordered source MGU can orient a
residual variable alias differently.  Substituting whole executable goals and
then asking for syntactic equality is therefore both too strong and, for
hidden compiler carries such as `typeCheckBindingTemplate`, false in general.

This file keeps the already-certified `AlphaGoalAgrees` control structure
verbatim and gives all of its term leaves one shared semantic valuation.
Nothing here claims that arbitrary substitution commutes with goal encoders.
-/

/-! ## Alpha-graph weakening for complete goal structures -/

/-- Hidden type-check fields are monotone under alpha-graph inclusion.  The
compiler's exact carry equation is retained rather than recomputed after
substitution. -/
theorem AlphaTypeCheckExpectedAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {reference : Term} {executable template : Atom}
    (agreement :
      AlphaTypeCheckExpectedAgrees smaller reference executable template) :
    AlphaTypeCheckExpectedAgrees larger reference executable template :=
  ⟨PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono
      included agreement.term,
    agreement.template_eq⟩

/-- Literal `amb` branches preserve order and every repeated hidden output
field while the alpha graph is enlarged. -/
theorem AlphaLiteralAmbBranchesAgree.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (agreement :
      AlphaLiteralAmbBranchesAgree smaller referenceOutput executableOutput
        referenceBranches executableBranches) :
    AlphaLiteralAmbBranchesAgree larger referenceOutput executableOutput
      referenceBranches executableBranches := by
  induction agreement with
  | nil output =>
      exact .nil
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | cons value output tail inductionHypothesis =>
      exact .cons
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        inductionHypothesis

mutual

/-- Complete goal agreement is monotone under alpha-graph inclusion.  Every
constructor is rebuilt, so hidden branch fields and nested control structure
cannot disappear during weakening. -/
theorem AlphaGoalAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : PLeaTTa.Goal}
    (agreement : AlphaGoalAgrees smaller barrier reference executable) :
    AlphaGoalAgrees larger barrier reference executable := by
  cases agreement with
  | unify left right =>
      exact .unify
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included left)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included right)
  | compileAlias left right =>
      exact .compileAlias
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included left)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included right)
  | cut =>
      exact .cut
  | builtin arguments result =>
      exact .builtin
        (PLeaTTa.PrologMguBridge.AlphaTermsAgree.mono included arguments)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included result)
  | definedCall arguments result =>
      exact .definedCall
        (PLeaTTa.PrologMguBridge.AlphaTermsAgree.mono included arguments)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included result)
  | softCutTruth condition otherwise =>
      exact .softCutTruth
        (AlphaGoalsAgree.mono included condition)
        (AlphaGoalsAgree.mono included otherwise)
  | typeCheckSoftCut value expected direct metaTerm =>
      exact .typeCheckSoftCut
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (AlphaTypeCheckExpectedAgrees.mono included expected)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included direct)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included metaTerm)
  | shortCircuitAnd condition body output bodyGoals =>
      exact .shortCircuitAnd
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included condition)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included body)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included bodyGoals)
  | shortCircuitOr condition body output bodyGoals =>
      exact .shortCircuitOr
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included condition)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included body)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included bodyGoals)
  | findall template body output =>
      exact .findall
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included template)
        (AlphaGoalsAgree.mono included body)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | literalAmb branches =>
      exact .literalAmb
        (AlphaLiteralAmbBranchesAgree.mono included branches)
  | builtAmb branches =>
      exact .builtAmb
        (AlphaSuperposeBranchesAgree.mono included branches)
  | spread value output =>
      exact .spread
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | conditional condition output thenBranch elseBranch =>
      exact .conditional
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included condition)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaIfBranchAgrees.mono included thenBranch)
        (AlphaIfBranchAgrees.mono included elseBranch)

/-- Normalized `if` branches weaken without losing the executable-only
output carried by a failing branch. -/
theorem AlphaIfBranchAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat} {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    (agreement :
      AlphaIfBranchAgrees smaller barrier referenceOutput executableOutput
        reference executable) :
    AlphaIfBranchAgrees larger barrier referenceOutput executableOutput
      reference executable := by
  cases agreement with
  | empty value output =>
      exact .empty
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | aliased output goals =>
      exact .aliased
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included goals)
  | nonvariable value output goals =>
      exact .nonvariable
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included goals)
  | failed output =>
      exact .failed
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)

/-- One syntactic-superpose branch weakens structurally. -/
theorem AlphaSuperposeBranchAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat} {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    (agreement :
      AlphaSuperposeBranchAgrees smaller barrier referenceOutput
        executableOutput reference executable) :
    AlphaSuperposeBranchAgrees larger barrier referenceOutput
      executableOutput reference executable := by
  cases agreement with
  | empty value output =>
      exact .empty
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | aliased output goals nonempty =>
      exact .aliased
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included goals) nonempty
  | nonvariable value output goals =>
      exact .nonvariable
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included value)
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
        (AlphaGoalsAgree.mono included goals)

/-- Ordered syntactic-superpose alternatives weaken pointwise. -/
theorem AlphaSuperposeBranchesAgree.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat} {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    (agreement :
      AlphaSuperposeBranchesAgree smaller barrier referenceOutput
        executableOutput references executables) :
    AlphaSuperposeBranchesAgree larger barrier referenceOutput
      executableOutput references executables := by
  cases agreement with
  | nil output =>
      exact .nil
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included output)
  | cons head tail =>
      exact .cons
        (AlphaSuperposeBranchAgrees.mono included head)
        (AlphaSuperposeBranchesAgree.mono included tail)

/-- Ordered flattened goal lists weaken without reordering or flattening a
different conjunction structure. -/
theorem AlphaGoalsAgree.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : AlphaGoalsAgree smaller barrier references executables) :
    AlphaGoalsAgree larger barrier references executables := by
  cases agreement with
  | nil =>
      exact .nil
  | cons head tail =>
      exact .cons
        (AlphaGoalAgrees.mono included head)
        (AlphaGoalsAgree.mono included tail)
  | conjunction block tail =>
      exact .conjunction
        (AlphaGoalsAgree.mono included block)
        (AlphaGoalsAgree.mono included tail)

end

/-! ## One representative for the whole control structure -/

/-- Exact source/executable goal structure plus one shared residual
representative and valuation for every alpha-linked term leaf.

The representative is shared by the entire structure.  This prevents a proof
from choosing a different residual orientation independently at each goal
leaf, while retaining the topology facts needed by later liveness trimming.
-/
def AlphaGoalsResidualVariantAgrees
    (alpha : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (runtime : Subst)
    (references : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal) : Prop :=
  ∃ representative : TreeSubstitution,
    AlphaGoalsAgree alpha barrier references executables ∧
    TreeSubstitutionVariants canonical representative ∧
    TreeSubstitutionTopological canonical ∧
    TreeSubstitutionTopological representative ∧
    Nonempty (PLeaTTa.SubstTopological runtime) ∧
    AlphaValuationAgrees alpha representative runtime

/-- Residual-MGU agreement and exact goal structure compose without
substituting or rewriting the goal constructors themselves. -/
theorem AlphaResidualVariantAgrees.goals
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {runtime : Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (residual :
      AlphaResidualVariantAgrees alpha canonical runtime)
    (control : AlphaGoalsAgree alpha barrier references executables) :
    AlphaGoalsResidualVariantAgrees alpha barrier canonical runtime
      references executables := by
  rcases residual with
    ⟨representative, variants, canonicalTopological,
      representativeTopological, _representativeCovered,
      runtimeTopological, valuation⟩
  exact
    ⟨representative, control, variants, canonicalTopological,
      representativeTopological, runtimeTopological, valuation⟩

/-- Every term leaf certified by the shared alpha graph has the same
post-MGU denotation under the one representative stored for the whole goal
structure. -/
theorem AlphaGoalsResidualVariantAgrees.term
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {runtime : Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (goals :
      AlphaGoalsResidualVariantAgrees alpha barrier canonical runtime
        references executables)
    {reference : Term} {executable : Atom}
    (leaf : AlphaTermAgrees alpha reference executable) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants canonical representative ∧
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply representative (Term.denote reference))
        (PLeaTTa.subst runtime executable) := by
  rcases goals with
    ⟨representative, _control, variants, _canonicalTopological,
      _representativeTopological, _runtimeTopological, valuation⟩
  exact
    ⟨representative, variants,
      canonicalRuntimeAgrees_apply
        (AlphaTermAgrees.canonicalRuntimeAgrees leaf) valuation⟩

/-- Ordered term lists use the same representative pointwise. -/
theorem AlphaGoalsResidualVariantAgrees.terms
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {runtime : Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (goals :
      AlphaGoalsResidualVariantAgrees alpha barrier canonical runtime
        references executables)
    {reference : List Term} {executable : List Atom}
    (leaves : AlphaTermsAgree alpha reference executable) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants canonical representative ∧
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees alpha
            (TreeSubstitution.apply representative (Term.denote term))
            (PLeaTTa.subst runtime atom))
        reference executable := by
  rcases goals with
    ⟨representative, _control, variants, _canonicalTopological,
      _representativeTopological, _runtimeTopological, valuation⟩
  refine ⟨representative, variants, ?_⟩
  induction leaves with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees head) valuation)
        inductionHypothesis

end PLeaTTa.PrologGoalMguVariant
