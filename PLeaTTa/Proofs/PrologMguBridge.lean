-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguBridge
Purpose: Transport one canonical Prolog unifier through one shared runtime
  alpha map into the actual comparator-parametric executable unifier.
Trusted boundary: none
Main exports: AlphaValuationAgrees,
  SharedAlphaEquationsAgree,
  unifyTopExact_complete_of_shared_alpha_equations,
  unifyB_complete_of_shared_alpha_equations
-/
import PLeaTTa.Proofs.PrologPrefilterCallBridge

namespace PLeaTTa.PrologMguBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open OpenBindingAgreement
open PrologStateBridge
open PrologPrefilterBridge

/-! ## One shared alpha map

The conservative prefilter may use independent alpha maps on the two sides
because variables are wildcards there.  MGU transport cannot: repeated
variables must retain one name across every equation.  The following
functional condition is the exact part of a finite alpha bijection needed to
compare two runtime realizations of the same canonical tree. -/

/-- One canonical identity has at most one executable spelling in the shared
alpha graph. -/
def AlphaForwardFunctional (alpha : List (LogicVar × String)) : Prop :=
  ∀ {identity left right},
    (identity, left) ∈ alpha →
    (identity, right) ∈ alpha →
    left = right

/-- One executable spelling has at most one canonical identity in the shared
alpha graph.  Later substitution construction needs this inverse direction;
the completeness transport below needs only `AlphaForwardFunctional`. -/
def AlphaBackwardFunctional (alpha : List (LogicVar × String)) : Prop :=
  ∀ {left right name},
    (left, name) ∈ alpha →
    (right, name) ∈ alpha →
    left = right

/-- A finite shared runtime alpha graph is functional in both directions.
This is deliberately a property of the graph itself, so query and freshly
copied clause graphs can later be merged only after their cross-disjointness
has been proved.  Exact duplicate pairs are observationally irrelevant; the
two functional fields exclude every aliasing ambiguity. -/
structure SharedRuntimeAlpha (alpha : List (LogicVar × String)) : Prop where
  forward : AlphaForwardFunctional alpha
  backward : AlphaBackwardFunctional alpha

/-! ### Composing finite alpha graphs -/

/-- Cross-graph form of forward functionality. -/
def AlphaForwardCompatible
    (left right : List (LogicVar × String)) : Prop :=
  ∀ {identity leftName rightName},
    (identity, leftName) ∈ left →
    (identity, rightName) ∈ right →
    leftName = rightName

/-- Cross-graph form of inverse functionality. -/
def AlphaBackwardCompatible
    (left right : List (LogicVar × String)) : Prop :=
  ∀ {leftIdentity rightIdentity name},
    (leftIdentity, name) ∈ left →
    (rightIdentity, name) ∈ right →
    leftIdentity = rightIdentity

/-- Two internally functional alpha graphs remain forward-functional after
append exactly when their shared canonical identities have compatible
runtime spellings. -/
theorem AlphaForwardFunctional.append
    {left right : List (LogicVar × String)}
    (leftFunctional : AlphaForwardFunctional left)
    (rightFunctional : AlphaForwardFunctional right)
    (cross : AlphaForwardCompatible left right) :
    AlphaForwardFunctional (left ++ right) := by
  intro identity first second firstMember secondMember
  simp only [List.mem_append] at firstMember secondMember
  rcases firstMember with firstMember | firstMember <;>
    rcases secondMember with secondMember | secondMember
  · exact leftFunctional firstMember secondMember
  · exact cross firstMember secondMember
  · exact (cross secondMember firstMember).symm
  · exact rightFunctional firstMember secondMember

/-- Inverse counterpart of `AlphaForwardFunctional.append`. -/
theorem AlphaBackwardFunctional.append
    {left right : List (LogicVar × String)}
    (leftFunctional : AlphaBackwardFunctional left)
    (rightFunctional : AlphaBackwardFunctional right)
    (cross : AlphaBackwardCompatible left right) :
    AlphaBackwardFunctional (left ++ right) := by
  intro first second name firstMember secondMember
  simp only [List.mem_append] at firstMember secondMember
  rcases firstMember with firstMember | firstMember <;>
    rcases secondMember with secondMember | secondMember
  · exact leftFunctional firstMember secondMember
  · exact cross firstMember secondMember
  · exact (cross secondMember firstMember).symm
  · exact rightFunctional firstMember secondMember

/-- Appending two compatible finite alpha bijections yields one shared graph.
The cross premises are intentionally separate: freshness proves them by
different arguments on the independent and executable sides. -/
theorem SharedRuntimeAlpha.append
    {left right : List (LogicVar × String)}
    (leftShared : SharedRuntimeAlpha left)
    (rightShared : SharedRuntimeAlpha right)
    (forwardCross : AlphaForwardCompatible left right)
    (backwardCross : AlphaBackwardCompatible left right) :
    SharedRuntimeAlpha (left ++ right) :=
  ⟨AlphaForwardFunctional.append leftShared.forward rightShared.forward
      forwardCross,
    AlphaBackwardFunctional.append leftShared.backward rightShared.backward
      backwardCross⟩

/-- The standardization-apart case: disjoint canonical supports and disjoint
runtime supports discharge both cross-compatibility premises. -/
theorem SharedRuntimeAlpha.append_of_projection_disjoint
    {left right : List (LogicVar × String)}
    (leftShared : SharedRuntimeAlpha left)
    (rightShared : SharedRuntimeAlpha right)
    (referenceDisjoint :
      List.Disjoint (left.map Prod.fst) (right.map Prod.fst))
    (executableDisjoint :
      List.Disjoint (left.map Prod.snd) (right.map Prod.snd)) :
    SharedRuntimeAlpha (left ++ right) := by
  apply SharedRuntimeAlpha.append leftShared rightShared
  · intro identity leftName rightName leftMember rightMember
    exfalso
    exact (List.disjoint_left.mp referenceDisjoint)
      (List.mem_map.mpr ⟨(identity, leftName), leftMember, rfl⟩)
      (List.mem_map.mpr ⟨(identity, rightName), rightMember, rfl⟩)
  · intro leftIdentity rightIdentity name leftMember rightMember
    exfalso
    exact (List.disjoint_left.mp executableDisjoint)
      (List.mem_map.mpr ⟨(leftIdentity, name), leftMember, rfl⟩)
      (List.mem_map.mpr ⟨(rightIdentity, name), rightMember, rfl⟩)

private theorem alphaForwardFunctional_of_fst_nodup
    {alpha : List (LogicVar × String)}
    (nodup : (alpha.map Prod.fst).Nodup) :
    AlphaForwardFunctional alpha := by
  induction alpha with
  | nil =>
      intro identity left right leftMember
      simp at leftMember
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headIdentity, headName⟩
      rw [List.map_cons, List.nodup_cons] at nodup
      intro identity left right leftMember rightMember
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · rcases rightMember with rightHead | rightTail
        · exact congrArg Prod.snd (leftHead.trans rightHead.symm)
        · exfalso
          have identityEq : identity = headIdentity :=
            congrArg (fun pair : LogicVar × String => pair.1) leftHead
          have identityMember : identity ∈ tail.map Prod.fst :=
            List.mem_map.mpr ⟨(identity, right), rightTail, rfl⟩
          rw [identityEq] at identityMember
          exact nodup.1 identityMember
      · rcases rightMember with rightHead | rightTail
        · exfalso
          have identityEq : identity = headIdentity :=
            congrArg (fun pair : LogicVar × String => pair.1) rightHead
          have identityMember : identity ∈ tail.map Prod.fst :=
            List.mem_map.mpr ⟨(identity, left), leftTail, rfl⟩
          rw [identityEq] at identityMember
          exact nodup.1 identityMember
        · exact inductionHypothesis nodup.2 leftTail rightTail

private theorem alphaBackwardFunctional_of_snd_nodup
    {alpha : List (LogicVar × String)}
    (nodup : (alpha.map Prod.snd).Nodup) :
    AlphaBackwardFunctional alpha := by
  induction alpha with
  | nil =>
      intro left right name leftMember
      simp at leftMember
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headIdentity, headName⟩
      rw [List.map_cons, List.nodup_cons] at nodup
      intro left right name leftMember rightMember
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · rcases rightMember with rightHead | rightTail
        · exact congrArg Prod.fst (leftHead.trans rightHead.symm)
        · exfalso
          have nameEq : name = headName :=
            congrArg (fun pair : LogicVar × String => pair.2) leftHead
          have nameMember : name ∈ tail.map Prod.snd :=
            List.mem_map.mpr ⟨(right, name), rightTail, rfl⟩
          rw [nameEq] at nameMember
          exact nodup.1 nameMember
      · rcases rightMember with rightHead | rightTail
        · exfalso
          have nameEq : name = headName :=
            congrArg (fun pair : LogicVar × String => pair.2) rightHead
          have nameMember : name ∈ tail.map Prod.snd :=
            List.mem_map.mpr ⟨(left, name), leftTail, rfl⟩
          rw [nameEq] at nameMember
          exact nodup.1 nameMember
        · exact inductionHypothesis nodup.2 leftTail rightTail

/-- The positional graph exported by the clause-freshening bridge is already
a shared finite alpha bijection; no second naming assumption is needed. -/
theorem RuntimeAlpha.graph_shared
    {reference : List LogicVar} {executable : List String}
    (alpha : RuntimeAlpha reference executable) :
    SharedRuntimeAlpha (RuntimeAlpha.graph reference executable) := by
  constructor
  · apply alphaForwardFunctional_of_fst_nodup
    rw [alpha.graph_reference]
    exact alpha.referenceInjective
  · apply alphaBackwardFunctional_of_snd_nodup
    rw [alpha.graph_executable]
    exact alpha.executableInjective

/-- A query support below the independent fresh frontier is disjoint from
every target reserved for the next clause copy.  Source and anonymous
identities are automatically separate from the generated namespace. -/
theorem referenceFreshTargets_disjoint_of_generatedBelow
    {seed : Nat} {querySupport clauseSupport : List LogicVar}
    (below : GeneratedBelow seed querySupport) :
    List.Disjoint querySupport
      (referenceFreshTargets seed clauseSupport) := by
  rw [List.disjoint_left]
  intro identity queryMember clauseMember
  obtain ⟨index, identityShape, lower⟩ :=
    referenceFreshTargets_generated_lower clauseMember
  subst identity
  exact (Nat.not_lt_of_ge lower) (below index queryMember)

/-- Executable counterpart of the previous theorem.  Every query spelling
belongs to the live surface used by `resolutionFreshSuffix`, while every
clause target is an original spelling with that suffix appended. -/
theorem executableFreshTargets_disjoint_of_highWater
    (argsv : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (query : Atom) (seed : Nat)
    {queryNames : List String} {clauseSupport : List LogicVar}
    (queryLive :
      ∀ name, name ∈ queryNames →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed) :
    List.Disjoint queryNames
      (executableFreshTargets
        (resolutionFreshSuffix argsv result rest binding query seed)
        clauseSupport) := by
  rw [List.disjoint_left]
  intro name queryMember clauseMember
  simp only [executableFreshTargets, List.mem_map] at clauseMember
  obtain ⟨source, _sourceMember, targetShape⟩ := clauseMember
  exact
    (resolutionFreshSuffix_target_ne argsv result rest binding query seed
      highWater (logicVarExecutableName source) name
      (queryLive name queryMember)) targetShape

private theorem substLookup_some_mem_local :
    ∀ {binding : Subst} {source : String} {target : Atom},
      Metta.Subst.lookup binding source = some target →
        (source, target) ∈ binding
  | [], _, _, lookup => by
      simp [Metta.Subst.lookup] at lookup
  | (key, value) :: rest, source, target, lookup => by
      by_cases equal : source = key
      · subst source
        simp [Metta.Subst.lookup] at lookup
        subst target
        simp
      · simp only [Metta.Subst.lookup, equal, beq_iff_eq, if_false] at lookup
        exact List.mem_cons_of_mem (key, value)
          (substLookup_some_mem_local lookup)

/-- A freshly suffixed clause variable is outside the carried executable
substitution domain.  The proof uses a successful-lookup witness to put the
name back into the exact occupied surface, where suffix freshness refutes it.
-/
theorem resolutionFreshSuffix_lookup_none
    (argsv : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (query : Atom) (seed : Nat)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (source : String) :
    Metta.Subst.lookup binding
      (source ++
        resolutionFreshSuffix argsv result rest binding query seed) =
      none := by
  let target :=
    source ++ resolutionFreshSuffix argsv result rest binding query seed
  cases lookupEq : Metta.Subst.lookup binding target with
  | none =>
      rfl
  | some value =>
      have pairMember : (target, value) ∈ binding :=
        substLookup_some_mem_local lookupEq
      have targetOccupied :
          target ∈
            resolutionOccupiedVars argsv result rest binding query := by
        simp only [resolutionOccupiedVars, List.mem_append,
          List.mem_flatMap]
        left
        right
        exact ⟨(target, value), pairMember, by simp⟩
      exact False.elim
        ((resolutionFreshSuffix_target_ne argsv result rest binding query
          seed highWater source target targetOccupied) rfl)

/-- Deep executable substitution cannot capture any variable in one atom
renamed by the actual resolution suffix. -/
theorem subst_renameAtomSuffix_resolutionFreshSuffix
    (argsv : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (query : Atom) (seed : Nat)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (atom : Atom) :
    PLeaTTa.subst binding
        (renameAtomSuffix
          (resolutionFreshSuffix argsv result rest binding query seed)
          atom) =
      renameAtomSuffix
        (resolutionFreshSuffix argsv result rest binding query seed)
        atom := by
  apply PLeaTTa.subst_eq_self_of_domain_free
  intro name member
  rw [PrologStateBridge.renameAtomSuffix_vars_exact,
    List.mem_map] at member
  obtain ⟨source, _sourceMember, rfl⟩ := member
  exact resolutionFreshSuffix_lookup_none
    argsv result rest binding query seed highWater source

/-- The carried executable substitution fixes the complete freshly copied
clause head.  Thus `unifyB` sees exactly the shared-alpha payload after it
normalizes both sides, rather than a subtly captured variant. -/
theorem subst_freshenResolutionClause_head_eq_self
    (argsv args : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (query : Atom) (seed barrier : Nat)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (clause : PLeaTTa.Clause) :
    ((freshenResolutionClause argsv args result rest binding query
        seed barrier clause).params.map (PLeaTTa.subst binding) =
      (freshenResolutionClause argsv args result rest binding query
        seed barrier clause).params) ∧
    PLeaTTa.subst binding
        (freshenResolutionClause argsv args result rest binding query
          seed barrier clause).result =
      (freshenResolutionClause argsv args result rest binding query
        seed barrier clause).result := by
  constructor
  · simp only [freshenResolutionClause, List.map_map]
    apply List.map_congr_left
    intro atom _member
    exact subst_renameAtomSuffix_resolutionFreshSuffix
      argsv result rest binding query seed highWater atom
  · simp only [freshenResolutionClause]
    exact subst_renameAtomSuffix_resolutionFreshSuffix
      argsv result rest binding query seed highWater clause.result

/-- The actual two allocator arguments produce one shared alpha graph for a
live caller and one freshly copied executable clause.  This theorem does not
invent a global naming convention: its premises are the query's finite alpha
certificate plus the two already-enforced high-water invariants. -/
theorem SharedRuntimeAlpha.append_resolution_clause
    {queryAlpha : List (LogicVar × String)}
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (reference : LocalClause) (freshSeed : Nat)
    (encoding : EncodingInjectiveOn reference.variables)
    (argsv : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (query : Atom) (seed : Nat)
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed) :
    SharedRuntimeAlpha
      (queryAlpha ++
        RuntimeAlpha.graph
          (referenceFreshTargets
            (reference.freshCopy freshSeed).firstFresh reference.variables)
          (executableFreshTargets
            (resolutionFreshSuffix argsv result rest binding query seed)
            reference.variables)) := by
  let clauseAlpha :=
    freshenClause_alpha_agrees reference freshSeed
      (resolutionFreshSuffix argsv result rest binding query seed) encoding
  apply queryShared.append_of_projection_disjoint
    (PLeaTTa.PrologMguBridge.RuntimeAlpha.graph_shared clauseAlpha)
  · rw [clauseAlpha.graph_reference]
    exact referenceFreshTargets_disjoint_of_generatedBelow
      queryReferenceBelow
  · rw [clauseAlpha.graph_executable]
    exact executableFreshTargets_disjoint_of_highWater
      argsv result rest binding query seed queryExecutableLive highWater

private def conflictingAlpha : List (LogicVar × String) :=
  [(.source "X", "left"), (.source "X", "right")]

private def aliasingAlpha : List (LogicVar × String) :=
  [(.source "X", "same"), (.source "Y", "same")]

/-- A graph that renames one repeated canonical variable two different ways
is rejected.  This is the small anti-vacuity guard for the shared-alpha
condition: independent per-equation renamings cannot be merged merely by
concatenating their graphs. -/
theorem conflicting_alpha_is_not_shared :
    ¬ SharedRuntimeAlpha conflictingAlpha := by
  intro shared
  have impossible : "left" = "right" :=
    shared.forward (identity := .source "X") (left := "left")
      (right := "right") (by simp [conflictingAlpha])
      (by simp [conflictingAlpha])
  simp at impossible

/-- The inverse functionality field is independently load-bearing: two
canonical identities cannot be collapsed onto one executable name. -/
theorem aliasing_alpha_is_not_shared :
    ¬ SharedRuntimeAlpha aliasingAlpha := by
  intro shared
  have impossible : LogicVar.source "X" = LogicVar.source "Y" :=
    shared.backward (left := .source "X") (right := .source "Y")
      (name := "same") (by simp [aliasingAlpha]) (by simp [aliasingAlpha])
  simp at impossible

/-! ### Weakening structural agreement into a merged graph -/

mutual

/-- Structural alpha agreement is monotone under graph inclusion. -/
theorem AlphaTermAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {term : Term} {atom : Atom}
    (agreement : AlphaTermAgrees smaller term atom) :
    AlphaTermAgrees larger term atom := by
  cases agreement with
  | «variable» linked =>
      exact .variable (included _ linked)
  | atom notTrue notFalse =>
      exact .atom notTrue notFalse
  | trueAtom =>
      exact .trueAtom
  | falseAtom =>
      exact .falseAtom
  | integer value =>
      exact .integer value
  | float value =>
      exact .float value
  | string value =>
      exact .string value
  | partialValue arguments =>
      exact .partialValue (AlphaProperListAgrees.mono included arguments)
  | properList elements =>
      exact .properList (AlphaProperListAgrees.mono included elements)

/-- Proper-list counterpart of `AlphaTermAgrees.mono`. -/
theorem AlphaProperListAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {terms : List Term} {atom : Atom}
    (agreement : AlphaProperListAgrees smaller terms atom) :
    AlphaProperListAgrees larger terms atom := by
  cases agreement with
  | nil =>
      exact .nil
  | cons head rest =>
      exact .cons (AlphaTermAgrees.mono included head)
        (AlphaProperListAgrees.mono included rest)

end

/-- Pointwise term-list agreement is monotone under graph inclusion. -/
theorem AlphaTermsAgree.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {terms : List Term} {atoms : List Atom}
    (agreement : AlphaTermsAgree smaller terms atoms) :
    AlphaTermsAgree larger terms atoms := by
  induction agreement with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono included head)
        inductionHypothesis

/-! ## Substitution-independent semantic relation -/

/-- Canonical and executable substitutions agree on every variable named by
one alpha graph.  The relation speaks only about their denotations; it does
not assume identical substitution orientation or list spelling. -/
def AlphaValuationAgrees (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  ∀ {identity name}, (identity, name) ∈ alpha →
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical (.variable identity))
      (PLeaTTa.subst runtime (.var name))

/-- Canonical and executable substitutions agree on the observable part of
one alpha graph.  `support` is deliberately separate from `alpha`: the full
graph still interprets residual variables in the resulting terms, while a
caller may observe only query variables and let `trimFor` discard dead
clause-local bindings. -/
def AlphaValuationAgreesOn
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  ∀ {identity name}, (identity, name) ∈ support →
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical (.variable identity))
      (PLeaTTa.subst runtime (.var name))

/-- Every executable name in the observed alpha support is directly live in
the remaining machine continuation. -/
def AlphaRuntimeNamesLive
    (support : List (LogicVar × String))
    (goals : List Goal) (qterm : Atom) : Prop :=
  ∀ {identity name}, (identity, name) ∈ support →
    PLeaTTa.isTrimRoot goals qterm name = true

/-- Full valuation agreement restricts to any subgraph of the shared alpha
graph. -/
theorem AlphaValuationAgrees.on
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime)
    (included : ∀ pair, pair ∈ support → pair ∈ alpha) :
    AlphaValuationAgreesOn alpha support canonical runtime := by
  intro identity name linked
  exact valuation (included (identity, name) linked)

/-- The support-indexed relation is definitionally the original relation
when every alpha link is observable. -/
theorem alphaValuationAgreesOn_self_iff
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst} :
    AlphaValuationAgreesOn alpha alpha canonical runtime ↔
      AlphaValuationAgrees alpha canonical runtime :=
  Iff.rfl

/-- Executable liveness trimming preserves canonical/runtime denotation on
exactly the observed alpha support.  Dead bindings outside `support` may be
removed; no association-list equality or orientation is assumed. -/
theorem AlphaValuationAgreesOn.trimFor
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgreesOn alpha support canonical runtime)
    (topological : PLeaTTa.SubstTopological runtime)
    {goals : List Goal} {qterm : Atom}
    (live : AlphaRuntimeNamesLive support goals qterm) :
    AlphaValuationAgreesOn alpha support canonical
      (PLeaTTa.trimFor goals qterm runtime) := by
  intro identity name linked
  have unchanged :=
    PLeaTTa.subst_trimFor_eq_of_topological
      goals qterm runtime topological (.var name) (by
        intro candidate member
        simp only [Atom.vars, List.mem_singleton] at member
        subst candidate
        exact live linked)
  rw [unchanged]
  exact valuation linked

/-! ### The liveness premise is load-bearing -/

private def trimWitnessIdentity : LogicVar := .source "dead"

private def trimWitnessAlpha : List (LogicVar × String) :=
  [(trimWitnessIdentity, "x#r10")]

private def trimWitnessCanonical : TreeSubstitution :=
  [(trimWitnessIdentity, .node (.atom "input") [])]

private def trimWitnessRuntime : Subst :=
  [("answer", .sym "output"),
   ("x#r10", .sym "input"),
   ("result#r10", .sym "output")]

/-- Deep executable substitution commutes with the chain encoder. -/
private theorem subst_chainOf_local (runtime : Subst) (atoms : List Atom) :
    PLeaTTa.subst runtime (chainOf atoms) =
      chainOf (atoms.map (PLeaTTa.subst runtime)) := by
  induction atoms with
  | nil =>
      simp [chainOf, nilA]
  | cons head tail inductionHypothesis =>
      change
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (chainOf (tail.map (PLeaTTa.subst runtime)))
      rw [show
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (PLeaTTa.subst runtime (chainOf tail)) by
              simp [consC, PLeaTTa.subst_expr]]
      rw [inductionHypothesis]

/-- Semantic valuation agreement lifts structurally through every supported
canonical/runtime term.  This is the reusable substitution lemma: it neither
constructs nor inspects an executable unifier result. -/
theorem canonicalRuntimeAgrees_apply
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime) :
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  induction agreement with
  | «variable» linked =>
      exact valuation linked
  | atom notTrue notFalse =>
      simpa using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa using (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa using (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa using (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa using (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa using (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | partialValue arguments inductionHypothesis =>
      simpa [partialC, partialTagA, TreeSubstitution.apply_node,
        subst_chainOf_local] using
        (CanonicalRuntimeAgrees.partialValue inductionHypothesis)
  | nil =>
      simpa [nilA] using (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [TreeSubstitution.apply_node, consC, PLeaTTa.subst_expr] using
        (CanonicalRuntimeAgrees.cons headInduction tailInduction)

/-! ## Common canonical denotation implies runtime comparator equivalence -/

/-- Exact chain construction preserves comparator-relative equivalence. -/
private theorem chainOf_equivalent
    {left right : List Atom}
    (equivalent :
      AtomsEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical
      (chainOf left) (chainOf right) := by
  induction left generalizing right with
  | nil =>
      cases equivalent
      exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | cons leftHead leftTail inductionHypothesis =>
      cases equivalent with
      | cons head tail =>
          exact .expression
            (.cons (.symbol "#c")
              (.cons head
                (.cons (inductionHypothesis tail) .nil)))

/-- Inversion for the non-injective runtime-float-to-Prolog-key projection.
The canonical-key equality is retained explicitly rather than asking
dependent elimination to recover raw `Float` equality, which is false for
distinct NaN payloads. -/
private theorem canonicalRuntimeAgrees_float_inv
    {alpha : List (LogicVar × String)}
    {identity : PLeaTTa.PrologFloatIdentity} {atom : Atom}
    (agreement :
      CanonicalRuntimeAgrees alpha (.node (.float identity) []) atom) :
    ∃ value : Float,
      atom = .gnd (.float value) ∧
        PLeaTTa.PrologFloatIdentity.ofFloat value = identity := by
  cases agreement with
  | float value =>
      exact ⟨value, rfl, rfl⟩

/-- Runtime spelling of one independent Prolog atom at the PeTTa boundary. -/
private def runtimeAtomName (name : String) : String :=
  if name = "true" then "True"
  else if name = "false" then "False"
  else name

/-- Inversion for the three source-atom spelling constructors. -/
private theorem canonicalRuntimeAgrees_atom_inv
    {alpha : List (LogicVar × String)}
    {name : String} {atom : Atom}
    (agreement :
      CanonicalRuntimeAgrees alpha (.node (.atom name) []) atom) :
    atom = .sym (runtimeAtomName name) := by
  cases agreement with
  | atom notTrue notFalse =>
      simp [runtimeAtomName, notTrue, notFalse]
  | trueAtom =>
      simp [runtimeAtomName]
  | falseAtom =>
      simp [runtimeAtomName]

/-- Topologicality alone does not make trimming invisible.  The original
runtime substitution agrees with the canonical valuation, but a continuation
which does not mention its sole executable name removes that binding and
destroys the agreement.  This concrete discriminator prevents the liveness
premise of `AlphaValuationAgreesOn.trimFor` from becoming decorative. -/
theorem dead_alpha_name_is_not_trim_preserved :
    ∃ _ : PLeaTTa.SubstTopological trimWitnessRuntime,
      AlphaValuationAgreesOn trimWitnessAlpha trimWitnessAlpha
        trimWitnessCanonical trimWitnessRuntime ∧
      ¬ AlphaRuntimeNamesLive trimWitnessAlpha [] (.var "answer") ∧
      ¬ AlphaValuationAgreesOn trimWitnessAlpha trimWitnessAlpha
        trimWitnessCanonical
          (PLeaTTa.trimFor [] (.var "answer") trimWitnessRuntime) := by
  have topological : PLeaTTa.SubstTopological trimWitnessRuntime :=
    PLeaTTa.SubstTopological.cons_of_fresh
      [("x#r10", .sym "input"), ("result#r10", .sym "output")]
      (PLeaTTa.SubstTopological.cons_of_fresh
        [("result#r10", .sym "output")]
        (PLeaTTa.SubstTopological.cons_of_fresh
          [] PLeaTTa.emptySubstTopological
          "result#r10" (.sym "output")
          (by simp [Metta.Subst.lookup])
          (by simp [Atom.vars])
          (by simp [PLeaTTa.AtomAvoids, Atom.vars,
            Metta.Subst.lookup]))
        "x#r10" (.sym "input")
        (by simp [Metta.Subst.lookup])
        (by simp [Atom.vars])
        (by simp [PLeaTTa.AtomAvoids, Atom.vars,
          Metta.Subst.lookup]))
      "answer" (.sym "output")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [PLeaTTa.AtomAvoids, Atom.vars,
        Metta.Subst.lookup])
  have before :
      AlphaValuationAgreesOn trimWitnessAlpha trimWitnessAlpha
        trimWitnessCanonical trimWitnessRuntime := by
    intro identity name linked
    simp only [trimWitnessAlpha, List.mem_singleton,
      Prod.mk.injEq] at linked
    rcases linked with ⟨rfl, rfl⟩
    simpa [trimWitnessCanonical, trimWitnessIdentity,
      TreeSubstitution.apply, Tree.instantiateOne,
      trimWitnessRuntime, PLeaTTa.subst, PLeaTTa.substN,
      Metta.Subst.lookup] using
        (CanonicalRuntimeAgrees.atom
          (alpha := trimWitnessAlpha)
          (name := "input") (by decide) (by decide))
  have notLive :
      ¬ AlphaRuntimeNamesLive trimWitnessAlpha [] (.var "answer") := by
    intro live
    have root := live
      (identity := trimWitnessIdentity) (name := "x#r10") (by
        simp [trimWitnessAlpha])
    have preserved :=
      PLeaTTa.trimFor_lookup_of_root
        [] (.var "answer") trimWitnessRuntime "x#r10" root
    change
      Metta.Subst.lookup
          (PLeaTTa.trimFor [] (.var "answer")
            [("answer", .sym "output"),
             ("x#r10", .sym "input"),
             ("result#r10", .sym "output")])
          "x#r10" =
        Metta.Subst.lookup
          [("answer", .sym "output"),
           ("x#r10", .sym "input"),
           ("result#r10", .sym "output")]
          "x#r10" at preserved
    rw [PLeaTTa.trimFor_ordered_target_specialized "input" "output"]
      at preserved
    simp [Metta.Subst.lookup] at preserved
  have trimExact :
      PLeaTTa.trimFor [] (.var "answer") trimWitnessRuntime =
        [("answer", .sym "output")] := by
    simpa [trimWitnessRuntime] using
      PLeaTTa.trimFor_ordered_target_specialized "input" "output"
  refine ⟨topological, before, notLive, ?_⟩
  intro after
  have impossible := after
    (identity := trimWitnessIdentity) (name := "x#r10") (by
      simp [trimWitnessAlpha])
  rw [trimExact] at impossible
  have normalized :
      CanonicalRuntimeAgrees trimWitnessAlpha
        (.node (.atom "input") []) (.var "x#r10") := by
    simpa [trimWitnessCanonical, trimWitnessIdentity,
      TreeSubstitution.apply, Tree.instantiateOne,
      PLeaTTa.subst, PLeaTTa.substN,
      Metta.Subst.lookup] using impossible
  have shape := canonicalRuntimeAgrees_atom_inv normalized
  simp [runtimeAtomName] at shape

/-- Two runtime encodings of the same canonical tree are equivalent under
exact Prolog ground identity.  Forward functionality is load-bearing only
for variables; NaN payloads are compared by their shared canonical float
identity rather than by raw `Float` equality. -/
theorem CanonicalRuntimeAgrees.equivalent_of_same
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {tree : Tree} {left right : Atom}
    (leftAgreement : CanonicalRuntimeAgrees alpha tree left)
    (rightAgreement : CanonicalRuntimeAgrees alpha tree right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical left right := by
  induction leftAgreement generalizing right with
  | «variable» leftLinked =>
      cases rightAgreement with
      | «variable» rightLinked =>
          rw [functional leftLinked rightLinked]
          exact .variable _
  | atom notTrue notFalse =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName, notTrue, notFalse]
      exact .symbol _
  | trueAtom =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName]
      exact .symbol _
  | falseAtom =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName]
      exact .symbol _
  | integer value =>
      cases rightAgreement with
      | integer =>
          exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | float value =>
      obtain ⟨rightValue, rfl, identity⟩ :=
        canonicalRuntimeAgrees_float_inv rightAgreement
      apply AtomEquivalentWith.ground
      rw [PLeaTTa.prologGroundIdentical_eq_true_iff]
      simp only [PLeaTTa.PrologGroundIdentity.ofGround,
        PrologGroundIdentity.floating.injEq]
      exact identity.symm
  | string value =>
      cases rightAgreement with
      | string =>
          exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | partialValue arguments inductionHypothesis =>
      cases rightAgreement with
      | partialValue rightArguments =>
          apply AtomEquivalentWith.expression
          exact .cons
            (.ground (PLeaTTa.prologGroundIdentical_self _))
            (.cons (.symbol _) (.cons
              (inductionHypothesis rightArguments) .nil))
  | nil =>
      cases rightAgreement with
      | nil =>
          exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | cons head tail headInduction tailInduction =>
      cases rightAgreement with
      | cons rightHead rightTail =>
          exact .expression
            (.cons (.symbol "#c")
              (.cons (headInduction rightHead)
                (.cons (tailInduction rightTail) .nil)))

/-! ## Ordered head-equation transport -/

/-- Every equation in one canonical head worklist is represented by the two
runtime atom lists under the same alpha graph.  Unlike the conservative
prefilter relation, this type cannot choose a fresh graph per equation. -/
inductive SharedAlphaEquationsAgree
    (alpha : List (LogicVar × String)) :
    List (Term × Term) → List Atom → List Atom → Prop where
  | nil : SharedAlphaEquationsAgree alpha [] [] []
  | cons {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
      {equations : List (Term × Term)}
      {leftAtoms rightAtoms : List Atom}
      (left : AlphaTermAgrees alpha leftTerm leftAtom)
      (right : AlphaTermAgrees alpha rightTerm rightAtom)
      (tail :
        SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
      SharedAlphaEquationsAgree alpha
        ((leftTerm, rightTerm) :: equations)
        (leftAtom :: leftAtoms) (rightAtom :: rightAtoms)

/-- Two pointwise term payloads under one shared alpha graph induce the
complete ordered head-equation relation.  Equal arity is explicit: malformed
fallback equations containing `$missing` are not silently included. -/
theorem SharedAlphaEquationsAgree.of_terms
    {alpha : List (LogicVar × String)}
    {leftTerms rightTerms : List Term}
    {leftAtoms rightAtoms : List Atom}
    (left : AlphaTermsAgree alpha leftTerms leftAtoms)
    (right : AlphaTermsAgree alpha rightTerms rightAtoms)
    (lengths : leftTerms.length = rightTerms.length) :
    SharedAlphaEquationsAgree alpha
      (argumentEquations leftTerms rightTerms) leftAtoms rightAtoms := by
  induction left generalizing rightTerms rightAtoms with
  | nil =>
      cases right with
      | nil =>
          exact .nil
      | cons =>
          simp at lengths
  | @cons leftTerm leftAtom leftTerms leftAtoms leftHead leftTail
      inductionHypothesis =>
      cases right with
      | nil =>
          simp at lengths
      | @cons rightTerm rightAtom rightTerms rightAtoms rightHead rightTail =>
          have tailLengths : leftTerms.length = rightTerms.length := by
            simpa using Nat.succ.inj lengths
          exact .cons leftHead rightHead
            (inductionHypothesis rightTail tailLengths)

/-- Standardization-apart constructor for an entire equation family.  The
two payloads are weakened into one appended graph only after both projections
are proved disjoint; this is the reusable bridge from independently
freshened query/clause payloads to MGU transport. -/
theorem SharedAlphaEquationsAgree.of_disjoint_terms
    {leftAlpha rightAlpha : List (LogicVar × String)}
    (leftShared : SharedRuntimeAlpha leftAlpha)
    (rightShared : SharedRuntimeAlpha rightAlpha)
    (referenceDisjoint :
      List.Disjoint (leftAlpha.map Prod.fst) (rightAlpha.map Prod.fst))
    (executableDisjoint :
      List.Disjoint (leftAlpha.map Prod.snd) (rightAlpha.map Prod.snd))
    {leftTerms rightTerms : List Term}
    {leftAtoms rightAtoms : List Atom}
    (left : AlphaTermsAgree leftAlpha leftTerms leftAtoms)
    (right : AlphaTermsAgree rightAlpha rightTerms rightAtoms)
    (lengths : leftTerms.length = rightTerms.length) :
    SharedRuntimeAlpha (leftAlpha ++ rightAlpha) ∧
      SharedAlphaEquationsAgree (leftAlpha ++ rightAlpha)
        (argumentEquations leftTerms rightTerms) leftAtoms rightAtoms := by
  constructor
  · exact leftShared.append_of_projection_disjoint rightShared
      referenceDisjoint executableDisjoint
  · apply SharedAlphaEquationsAgree.of_terms
      (PLeaTTa.PrologMguBridge.AlphaTermsAgree.mono
        (fun pair member => List.mem_append_left rightAlpha member) left)
      (PLeaTTa.PrologMguBridge.AlphaTermsAgree.mono
        (fun pair member => List.mem_append_right leftAlpha member) right)
      lengths

/-- The actual independent/executable clause-copy certificate and one
query payload produce a single shared-alpha head equation family.  This is
the first theorem in the lane that uses the real per-resolution suffix
rather than the empty-suffix conservative prefilter graph. -/
theorem FreshenedClauseAlphaAgrees.sharedHeadEquations
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term} {queryAtoms : List Atom}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms queryAtoms)
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length) :
    SharedRuntimeAlpha
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables)) ∧
      SharedAlphaEquationsAgree
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables))
        (argumentEquations queryTerms
          (reference.freshCopy freshSeed).clause.arguments)
        queryAtoms
        ((freshenResolutionClause argsv args result rest binding query
            seed barrier executable).params ++
          [(freshenResolutionClause argsv args result rest binding query
            seed barrier executable).result]) := by
  rcases freshened.headPayload.outputLast with
    ⟨referenceParameters, referenceResult, referenceArguments,
      parameterAgreement, resultAgreement⟩
  have clausePayload :
      AlphaTermsAgree
        (RuntimeAlpha.graph
          (referenceFreshTargets
            (reference.freshCopy freshSeed).firstFresh reference.variables)
          (executableFreshTargets
            (resolutionFreshSuffix argsv result rest binding query seed)
            reference.variables))
        (reference.freshCopy freshSeed).clause.arguments
        ((freshenResolutionClause argsv args result rest binding query
            seed barrier executable).params ++
          [(freshenResolutionClause argsv args result rest binding query
            seed barrier executable).result]) := by
    rw [referenceArguments]
    exact PrologPrefilterBridge.AlphaTermsAgree.append_singleton
      parameterAgreement resultAgreement
  have referenceDisjoint :
      List.Disjoint (queryAlpha.map Prod.fst)
        ((RuntimeAlpha.graph
          (referenceFreshTargets
            (reference.freshCopy freshSeed).firstFresh reference.variables)
          (executableFreshTargets
            (resolutionFreshSuffix argsv result rest binding query seed)
            reference.variables)).map Prod.fst) := by
    rw [freshened.alpha.graph_reference]
    exact referenceFreshTargets_disjoint_of_generatedBelow
      queryReferenceBelow
  have executableDisjoint :
      List.Disjoint (queryAlpha.map Prod.snd)
        ((RuntimeAlpha.graph
          (referenceFreshTargets
            (reference.freshCopy freshSeed).firstFresh reference.variables)
          (executableFreshTargets
            (resolutionFreshSuffix argsv result rest binding query seed)
            reference.variables)).map Prod.snd) := by
    rw [freshened.alpha.graph_executable]
    exact executableFreshTargets_disjoint_of_highWater
      argsv result rest binding query seed queryExecutableLive highWater
  exact SharedAlphaEquationsAgree.of_disjoint_terms
    queryShared
    (PLeaTTa.PrologMguBridge.RuntimeAlpha.graph_shared freshened.alpha)
    referenceDisjoint executableDisjoint queryPayload clausePayload lengths

/-- A shared-alpha valuation implementing one canonical unifier makes the
two complete runtime head payloads comparator-equivalent after deep
substitution. -/
theorem SharedAlphaEquationsAgree.atomsEquivalent_of_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    AtomsEquivalentWith PLeaTTa.prologGroundIdentical
      (leftAtoms.map (PLeaTTa.subst runtime))
      (rightAtoms.map (PLeaTTa.subst runtime)) := by
  induction agreement with
  | nil =>
      exact .nil
  | @cons leftTerm rightTerm leftAtom rightAtom equations leftAtoms
      rightAtoms left right tail inductionHypothesis =>
      have leftApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees left) valuation
      have rightApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees right) valuation
      have headEquality :
          TreeSubstitution.apply (Substitution.denote candidate)
              (Term.denote leftTerm) =
            TreeSubstitution.apply (Substitution.denote candidate)
              (Term.denote rightTerm) :=
        unifies (leftTerm, rightTerm) (by simp)
      rw [headEquality] at leftApplied
      exact .cons
        (CanonicalRuntimeAgrees.equivalent_of_same
          functional leftApplied rightApplied)
        (inductionHypothesis (by
          intro equation member
          exact unifies equation (List.mem_cons_of_mem _ member)))

/-- The comparator-relative unifier witness for the two expression payloads
assembled from a shared-alpha canonical head. -/
theorem SharedAlphaEquationsAgree.deepEquivalentUnifies
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    PLeaTTa.DeepEquivalentUnifies PLeaTTa.prologGroundIdentical runtime
      [(.expr leftAtoms, .expr rightAtoms)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  simp only [PLeaTTa.subst_expr]
  exact .expression
    (agreement.atomsEquivalent_of_unifier functional valuation unifies)

/-- A canonical shared-alpha head unifier reaches the actual executable
top-level unifier. -/
theorem unifyTopExact_complete_of_shared_alpha_equations
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    ∃ result,
      PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  apply PLeaTTa.unifyTopExact_complete_of_prolog_equivalent_unifier
    (.expr leftAtoms) (.expr rightAtoms) runtime
  exact agreement.deepEquivalentUnifies functional valuation unifies
    (.expr leftAtoms, .expr rightAtoms) (by simp)

/-- The same bridge after an existing executable binding has normalized the
raw head payload.  The relation is stated on the exact post-`base` atoms,
matching `unifyB` rather than assuming the base substitution is empty. -/
theorem unifyB_complete_of_shared_alpha_equations
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (PLeaTTa.subst base))
        (rightAtoms.map (PLeaTTa.subst base)))
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    ∃ result,
      PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  apply PLeaTTa.unifyB_complete_of_prolog_equivalent_unifier
    base (.expr leftAtoms) (.expr rightAtoms) runtime
  simpa only [PLeaTTa.subst_expr] using
    (agreement.deepEquivalentUnifies functional valuation unifies
      (.expr (leftAtoms.map (PLeaTTa.subst base)),
        .expr (rightAtoms.map (PLeaTTa.subst base))) (by simp))

/-- The real executable `unifyB` call at one retained clause head succeeds
whenever the independent ordered head equations have a canonical unifier and
that unifier's valuation is represented under the merged live alpha graph.
All allocator, capture, arity, and whole-equation-family obligations are
discharged here; construction of `valuation` remains the next isolated
cross-representation theorem. -/
theorem FreshenedClauseAlphaAgrees.unifyB_complete
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (PLeaTTa.subst binding) ++
          [PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables))
        (Substitution.denote candidate) runtime)
    (unifies :
      DenotationalUnifiesEquations candidate
        (argumentEquations queryTerms
          (reference.freshCopy freshSeed).clause.arguments)) :
    ∃ executableResult,
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result])) =
        some executableResult := by
  have shared :=
    PLeaTTa.PrologMguBridge.FreshenedClauseAlphaAgrees.sharedHeadEquations
      freshened queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  have stable :=
    subst_freshenResolutionClause_head_eq_self
      argsv args result rest binding query seed barrier highWater executable
  have normalizedAgreement :
      SharedAlphaEquationsAgree
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables))
        (argumentEquations queryTerms
          (reference.freshCopy freshSeed).clause.arguments)
        ((args ++ [result]).map (PLeaTTa.subst binding))
        (((freshenResolutionClause argsv args result rest binding query
              seed barrier executable).params ++
            [(freshenResolutionClause argsv args result rest binding query
              seed barrier executable).result]).map
          (PLeaTTa.subst binding)) := by
    subst argsv
    simpa only [List.map_append, List.map_singleton, stable.1, stable.2]
      using shared.2
  exact unifyB_complete_of_shared_alpha_equations binding shared.1.forward
    normalizedAgreement valuation unifies

/-! ## Anti-vacuity: repeated variable plus distinct NaN payloads -/

private def nanAlpha : List (LogicVar × String) :=
  [(.source "X", "X")]

private def nanCanonicalEquations :
    List (Term × Term) :=
  [(.variable (.source "X"), .float .nan),
   (.variable (.source "X"), .float .nan)]

private def nanCanonicalBinding : Substitution :=
  [(.source "X", .float .nan)]

/-- The bridge is strong enough to preserve one repeated-variable constraint
across two distinct runtime NaN payloads.  A relation that forgot either the
shared alpha map or Prolog's NaN identity could not prove this witness. -/
theorem repeated_variable_distinct_nan_payloads_complete
    (left right : Float)
    (leftNan : left.isNaN = true)
    (rightNan : right.isNaN = true) :
    ∃ result,
      PLeaTTa.unifyTopExact
          (.expr [.var "X", .var "X"])
          (.expr [.gnd (.float left), .gnd (.float right)]) =
        some result := by
  let runtime : Subst := [("X", .gnd (.float left))]
  have functional : AlphaForwardFunctional nanAlpha := by
    intro identity first second firstMember secondMember
    simp [nanAlpha] at firstMember secondMember
    exact firstMember.2.trans secondMember.2.symm
  have agreement :
      SharedAlphaEquationsAgree nanAlpha nanCanonicalEquations
        [.var "X", .var "X"]
        [.gnd (.float left), .gnd (.float right)] := by
    exact .cons
      (.variable (by simp [nanAlpha]))
      (by
        simpa [PLeaTTa.PrologFloatIdentity.ofFloat, leftNan] using
          (AlphaTermAgrees.float (alpha := nanAlpha) left))
      (.cons
        (.variable (by simp [nanAlpha]))
        (by
          simpa [PLeaTTa.PrologFloatIdentity.ofFloat, rightNan] using
            (AlphaTermAgrees.float (alpha := nanAlpha) right))
        .nil)
  have valuation :
      AlphaValuationAgrees nanAlpha
        (Substitution.denote nanCanonicalBinding) runtime := by
    intro identity name member
    simp [nanAlpha] at member
    rcases member with ⟨rfl, rfl⟩
    change
      CanonicalRuntimeAgrees nanAlpha
        (TreeSubstitution.apply
          [(.source "X", .node (.float .nan) [])]
          (.variable (.source "X")))
        (PLeaTTa.subst runtime (.var "X"))
    simpa [TreeSubstitution.apply, Tree.instantiateOne, runtime,
      PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup,
      PLeaTTa.PrologFloatIdentity.ofFloat, leftNan] using
        (CanonicalRuntimeAgrees.float (alpha := nanAlpha) left)
  have unifies :
      DenotationalUnifiesEquations nanCanonicalBinding
        nanCanonicalEquations := by
    intro equation member
    have equationShape :
        equation =
          (.variable (.source "X"), .float .nan) := by
      simpa [nanCanonicalEquations] using member
    subst equation
    simp [DenotationalUnifier, nanCanonicalBinding, Term.denote,
      Substitution.denote, TreeSubstitution.apply, Tree.instantiateOne]
  exact unifyTopExact_complete_of_shared_alpha_equations
    functional agreement valuation unifies

end PLeaTTa.PrologMguBridge
