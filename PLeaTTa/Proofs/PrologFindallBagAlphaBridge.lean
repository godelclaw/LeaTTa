-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallBagAlphaBridge
Purpose: Rejoin one findall bag and its suspended caller under one shared
  runtime alpha, without identifying residual-MGU association-list spelling.
Trusted boundary: none
Main exports: RuntimeTermsAgreesWith,
  FindallFrameVariantPayloadAgrees.successorSemanticHead
-/
import PLeaTTa.Proofs.PrologFindallVariantExitPayloadBridge
import PLeaTTa.Proofs.PrologAlphaFreshFrontierBridge
import PLeaTTa.Proofs.PrologMguDirectSimulation
import PLeaTTa.Proofs.PrologRepresentativeTaskActivationBridge
import PLeaTTa.Proofs.PrologTaskContinuationBridge

namespace PLeaTTa.PrologFindallBagAlphaBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Copy
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open OpenBindingAgreement
open PrologFindallCopyBridge
open PrologFindallExitBridge
open PrologFindallVariantExitPayloadBridge
open PrologAlphaFreshFrontierBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologMguDirectSimulation
open PrologMguTopology
open PrologMguVariantRenaming
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge
open DemandDrivenStep

/-! ## Chronological independent-copy separation -/

/-- Additive strengthening of the extensional collection debt.  The original
frontier remains available through `debt`; the two extra fields retain the
chronology needed to construct one shared bag alpha at payment time.

`referenceFloor` is the independent allocator frontier at collector entry.
Every copied solution is allocated at or above that floor, and the reverse
discovery accumulator is pairwise variable-disjoint. -/
structure SeparatedCollectionCopyFrontier
    (entryBindings : Substitution)
    (referenceFloor referenceFrontier executableFrontier : Nat)
    (referenceCopiedRev : List Term) (executableRawRev : List Atom) : Prop where
  debt :
    CollectionCopyFrontier referenceFrontier executableFrontier
      referenceCopiedRev executableRawRev
  floorLeFrontier : referenceFloor ≤ referenceFrontier
  aboveFloor :
    ∀ reference, reference ∈ referenceCopiedRev →
      reference.GeneratedAtLeast referenceFloor
  pairwiseReference :
    referenceCopiedRev.Pairwise fun earlier later =>
      List.Disjoint (termVariables earlier) (termVariables later)
  entrySourcesDisjoint :
    ∀ reference, reference ∈ referenceCopiedRev →
      List.Disjoint (entryBindings.map Prod.fst) (termVariables reference)
  entryStable :
    ∀ reference, reference ∈ referenceCopiedRev →
      entryBindings.applyTerm reference = reference

namespace SeparatedCollectionCopyFrontier

private theorem substitutionVariables_mem_append_right
    (extension entry : Substitution) {identity : LogicVar}
    (member : identity ∈ substitutionVariables entry) :
    identity ∈ substitutionVariables (extension ++ entry) := by
  induction extension with
  | nil => simpa using member
  | cons binding extension inductionHypothesis =>
      rcases binding with ⟨source, value⟩
      simp only [List.cons_append, substitutionVariables,
        List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr inductionHypothesis)

/-- An empty collector retains its entry frontier exactly. -/
theorem empty (entryBindings : Substitution)
    (referenceFloor executableFrontier : Nat) :
    SeparatedCollectionCopyFrontier entryBindings referenceFloor referenceFloor
      executableFrontier [] [] := by
  exact
    { debt := CollectionCopyFrontier.empty _ _
      floorLeFrontier := Nat.le_refl _
      aboveFloor := by simp
      pairwiseReference := by simp
      entrySourcesDisjoint := by simp
      entryStable := by simp }

/-- Advancing either allocator preserves every chronological separation fact.
No copied value or support is reconstructed by this rule. -/
theorem advance
    {entryBindings : Substitution}
    {referenceFloor referenceBefore referenceAfter
      executableBefore executableAfter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      SeparatedCollectionCopyFrontier entryBindings referenceFloor referenceBefore
        executableBefore referenceCopiedRev executableRawRev)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    SeparatedCollectionCopyFrontier entryBindings referenceFloor referenceAfter
      executableAfter referenceCopiedRev executableRawRev := by
  exact
    { debt := agreement.debt.advance referenceMono executableMono
      floorLeFrontier :=
        Nat.le_trans agreement.floorLeFrontier referenceMono
      aboveFloor := agreement.aboveFloor
      pairwiseReference := agreement.pairwiseReference
      entrySourcesDisjoint := agreement.entrySourcesDisjoint
      entryStable := agreement.entryStable }

private theorem deferred_exists_of_mem
    {referenceFrontier : Nat} :
    ∀ {references : List Term} {raws : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt referenceFrontier) references raws →
      ∀ {reference}, reference ∈ references →
        ∃ raw, DeferredCopyAgreesAt referenceFrontier reference raw
  | _, _, .nil, _, member => by simp at member
  | _, _, .cons head tail, reference, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, head⟩
      · exact deferred_exists_of_mem tail member

/-- Every reference value recorded by the old debt lies below its current
frontier.  This is recovered from the actual `copyTerm` witness, not inferred
from a numeric list length. -/
theorem referenceGeneratedBelow
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    {reference : Term} (member : reference ∈ referenceCopiedRev) :
    GeneratedBelow referenceFrontier (termVariables reference) := by
  have existsRaw :
      ∃ raw, DeferredCopyAgreesAt referenceFrontier reference raw :=
    deferred_exists_of_mem agreement.debt member
  rcases existsRaw with ⟨raw, witness, reserved⟩
  rw [witness.copied]
  exact
    (copyTerm_generatedBelowNextFresh witness.firstFresh witness.source).mono
      (by simpa [witness.next] using reserved)

/-- One actual answer-time copy extends the chronology.  The new independent
copy starts above the old frontier, hence is disjoint from every retained
older copy; the old pairwise proof is reused literally. -/
theorem collect
    {referenceFloor executableBefore executableAfter : Nat}
    {session : Session}
    {entryBindings : Substitution}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      SeparatedCollectionCopyFrontier entryBindings referenceFloor
        session.resolver.nextFresh executableBefore
        referenceCopiedRev executableRawRev)
    (template : Term) (answerBindings : Substitution) (raw : Atom)
    (lineage : BindingLineage entryBindings answerBindings)
    (sourceAgrees :
      RuntimeTermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template)))
    (executableMono : executableBefore ≤ executableAfter)
    (rawBound :
      resolutionSeedHighWaterNames raw.vars ≤ executableAfter) :
    SeparatedCollectionCopyFrontier entryBindings referenceFloor
      (collectTemplate session template answerBindings).session.resolver.nextFresh
      executableAfter
      ((collectTemplate session template answerBindings).prepared.copied ::
        referenceCopiedRev)
      (raw :: executableRawRev) := by
  let collected := collectTemplate session template answerBindings
  have currentLeFirst :
      session.resolver.nextFresh ≤ collected.prepared.firstFresh := by
    exact prepareTermCopy_first_ge_allocator _ _ _
  have floorLeFirst : referenceFloor ≤ collected.prepared.firstFresh :=
    Nat.le_trans agreement.floorLeFrontier currentLeFirst
  have copiedAboveFloor :
      collected.prepared.copied.GeneratedAtLeast referenceFloor := by
    have copiedAboveFirst :
        collected.prepared.copied.GeneratedAtLeast
          collected.prepared.firstFresh := by
      exact copyTerm_generatedAtLeast _ _
    exact generatedAtLeast_mono_term floorLeFirst copiedAboveFirst
  have newDisjoint :
      ∀ older, older ∈ referenceCopiedRev →
        List.Disjoint (termVariables collected.prepared.copied)
          (termVariables older) := by
    intro older olderMember
    have olderBelowCurrent :=
      referenceGeneratedBelow agreement.debt olderMember
    have olderBelowFirst := olderBelowCurrent.mono currentLeFirst
    exact copyTerm_variables_disjoint_of_generatedBelow
      collected.prepared.firstFresh collected.prepared.materialized older
      olderBelowFirst
  have entryBelowFirst :
      GeneratedBelow collected.prepared.firstFresh
        (substitutionVariables entryBindings) := by
    rcases lineage with ⟨extension, answerShape⟩
    have allAnswerBelow :=
      prepareTermCopy_first_dominates_live session.resolver.nextFresh
        answerBindings template
    intro index member
    apply allAnswerBelow index
    apply List.mem_append_left
    rw [answerShape]
    exact substitutionVariables_mem_append_right
      extension entryBindings member
  have copiedStable :
      entryBindings.applyTerm collected.prepared.copied =
        collected.prepared.copied := by
    apply Substitution.applyTerm_eq_self_of_generatedAtLeast
      (Substitution.domainsBelow_of_generatedBelow entryBelowFirst)
    exact copyTerm_generatedAtLeast _ _
  have copiedSourcesDisjoint :
      List.Disjoint (entryBindings.map Prod.fst)
        (termVariables collected.prepared.copied) := by
    rw [List.disjoint_left]
    intro identity sourceMember copiedMember
    obtain ⟨index, identityShape, copiedAtLeast⟩ :=
      generatedAtLeast_index_of_mem_term
        (copyTerm_generatedAtLeast
          collected.prepared.firstFresh collected.prepared.materialized)
        copiedMember
    subst identity
    have sourceVariableMember :
        LogicVar.generated index ∈ substitutionVariables entryBindings := by
      obtain ⟨⟨source, replacement⟩, entryMember, sourceShape⟩ :=
        List.mem_map.mp sourceMember
      have exactSource : source = LogicVar.generated index := by
        simpa using sourceShape
      subst source
      exact
        PLeaTTa.PrologRepresentativeActivationBridge.Substitution.source_mem_substitutionVariables
          entryMember
    exact (Nat.not_lt_of_ge copiedAtLeast)
      (entryBelowFirst index sourceVariableMember)
  exact
    { debt := agreement.debt.collect template answerBindings raw
        sourceAgrees encoding executableMono rawBound
      floorLeFrontier :=
        Nat.le_trans agreement.floorLeFrontier
          (collectTemplate_nextFresh_mono session template answerBindings)
      aboveFloor := by
        intro reference member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact copiedAboveFloor
        · exact agreement.aboveFloor reference member
      pairwiseReference := by
        exact List.pairwise_cons.mpr
          ⟨newDisjoint, agreement.pairwiseReference⟩
      entrySourcesDisjoint := by
        intro reference member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact copiedSourcesDisjoint
        · exact agreement.entrySourcesDisjoint reference member
      entryStable := by
        intro reference member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact copiedStable
        · exact agreement.entryStable reference member }

end SeparatedCollectionCopyFrontier

/-! ## Tight support of one paid copy -/

private theorem prologList_occurs_of_items
    {identity : LogicVar} :
    ∀ (items : List Tree) (tail : Option Tree),
      Trees.occurs identity items = true →
        Tree.occurs identity (Tree.prologList items tail) = true
  | [], _, present => by simp [Trees.occurs] at present
  | head :: items, tail, present => by
      simp only [Trees.occurs, Bool.or_eq_true] at present
      simp only [Tree.prologList, Tree.occurs, Trees.occurs,
        Bool.or_eq_true]
      rcases present with present | present
      · exact Or.inl present
      · exact Or.inr (Or.inl (prologList_occurs_of_items items tail present))

private theorem prologList_occurs_of_tail
    {identity : LogicVar} :
    ∀ (items : List Tree) (tail : Tree),
      Tree.occurs identity tail = true →
        Tree.occurs identity (Tree.prologList items (some tail)) = true
  | [], _, present => present
  | head :: items, tail, present => by
      simp only [Tree.prologList, Tree.occurs, Trees.occurs,
        Bool.or_eq_true]
      exact Or.inr (Or.inl (prologList_occurs_of_tail items tail present))

mutual

private theorem Term.denote_occurs_true_of_mem
    {identity : LogicVar} :
    ∀ (term : Term), identity ∈ termVariables term →
      Tree.occurs identity (Term.denote term) = true
  | .variable candidate, member => by
      simp only [termVariables, List.mem_singleton] at member
      subst candidate
      simp [Term.denote, Tree.occurs]
  | .atom _, member => by simp [termVariables] at member
  | .integer _, member => by simp [termVariables] at member
  | .float _, member => by simp [termVariables] at member
  | .string _, member => by simp [termVariables] at member
  | .compound _ arguments, member => by
      simpa [Term.denote, Tree.occurs] using
        (Terms.denote_occurs_true_of_mem arguments member)
  | .list items none, member => by
      exact prologList_occurs_of_items (Terms.denote items) none
        (Terms.denote_occurs_true_of_mem items member)
  | .list items (some tail), member => by
      simp only [termVariables, List.mem_append] at member
      rcases member with member | member
      · exact prologList_occurs_of_items (Terms.denote items)
          (some (Term.denote tail))
          (Terms.denote_occurs_true_of_mem items member)
      · exact prologList_occurs_of_tail (Terms.denote items)
          (Term.denote tail) (Term.denote_occurs_true_of_mem tail member)

private theorem Terms.denote_occurs_true_of_mem
    {identity : LogicVar} :
    ∀ (terms : List Term), identity ∈ termsVariables terms →
      Trees.occurs identity (Terms.denote terms) = true
  | [], member => by simp [termsVariables] at member
  | term :: terms, member => by
      simp only [termsVariables, List.mem_append] at member
      simp only [Terms.denote, Trees.occurs, Bool.or_eq_true]
      rcases member with member | member
      · exact Or.inl (Term.denote_occurs_true_of_mem term member)
      · exact Or.inr (Terms.denote_occurs_true_of_mem terms member)

end

/-- Runtime agreement whose alpha supports contain no irrelevant edges: every
independent support identity occurs in the reference term and every runtime
support name occurs in the executable atom.  Tightness is what lets allocator
separation compose element certificates into one bag certificate. -/
structure TightRuntimeTermAgreesWith
    (referenceSupport : List LogicVar) (executableSupport : List String)
    (reference : Term) (executable : Atom) : Prop where
  runtimeAlpha : RuntimeAlpha referenceSupport executableSupport
  value :
    CanonicalRuntimeAgrees
      (RuntimeAlpha.graph referenceSupport executableSupport)
      (Term.denote reference) executable
  referenceUsed :
    ∀ identity, identity ∈ referenceSupport →
      identity ∈ termVariables reference
  executableUsed :
    ∀ name, name ∈ executableSupport → name ∈ executable.vars

/-- Existential tight-support view for clients which do not need the concrete
active support lists. -/
def TightRuntimeTermAgrees (reference : Term) (executable : Atom) : Prop :=
  ∃ referenceSupport executableSupport,
    TightRuntimeTermAgreesWith referenceSupport executableSupport
      reference executable

namespace TightRuntimeTermAgreesWith

/-- Forgetting tightness recovers the established existential one-value
runtime agreement. -/
theorem runtime
    {reference : Term} {executable : Atom}
    {referenceSupport : List LogicVar} {executableSupport : List String}
    (agreement :
      TightRuntimeTermAgreesWith referenceSupport executableSupport
        reference executable) :
    RuntimeTermAgrees reference executable :=
  ⟨referenceSupport, executableSupport,
    agreement.runtimeAlpha, agreement.value⟩

end TightRuntimeTermAgreesWith

/-- The exact common suffix selected by one executable `findall` copy.  A
closed value allocates nothing but is still extensionally equal to renaming
by this harmless suffix. -/
def findallCopySuffix (counter : Nat) (raw : Atom) : String :=
  if resolutionAtomClosed raw then
    resolutionCompactSuffix counter
  else
    resolutionCompactSuffix (advanceCounterPastAtoms counter [raw])

/-- The executable copied value is literally the common-suffix renaming named
by `findallCopySuffix`, including the allocation-free closed case. -/
theorem copyFindallAtom_value_eq_rename (counter : Nat) (raw : Atom) :
    (copyFindallAtom counter raw).value =
      renameAtomSuffix (findallCopySuffix counter raw) raw := by
  unfold copyFindallAtom findallCopySuffix
  split
  next closed =>
    symm
    exact renameAtomSuffix_eq_self_of_resolutionAtomClosed _ raw closed
  next _ =>
    rfl

/-- Boolean occurrence is membership in the executable atom's ordered
variable-occurrence list. -/
private theorem atom_mem_vars_of_occurs_true (source : String)
    (atom : Atom) (present : Metta.Subst.occurs source atom = true) :
    source ∈ atom.vars := by
  induction atom with
  | sym name =>
      simp [Metta.Subst.occurs] at present
  | «variable» name =>
      simpa [Metta.Subst.occurs, Atom.vars] using present
  | ground ground =>
      simp [Metta.Subst.occurs] at present
  | expression atoms inductionHypothesis =>
      simp only [Metta.Subst.occurs, List.any_eq_true] at present
      obtain ⟨child, childPresent⟩ := present
      simp only [Atom.vars, List.mem_flatten, List.mem_map]
      exact
        ⟨child.val.vars, ⟨child.val, child.property, rfl⟩,
          inductionHypothesis child.val child.property childPresent.2⟩

/-- Paying one semantic copy debt exposes the exact active alpha supports and
proves both are tight in the resulting values.  The executable suffix is
chosen only by the certified copier at the supplied current high-water. -/
theorem copyTerm_copyFindallAtom_tight
    {source : Term} {raw : Atom}
    (agreement : RuntimeTermAgrees source raw)
    (firstFresh counter : Nat) :
    ∃ copiedReferenceSupport copiedExecutableSupport,
      TightRuntimeTermAgreesWith copiedReferenceSupport
        copiedExecutableSupport (copyTerm firstFresh source)
        (copyFindallAtom counter raw).value := by
  rcases agreement with
    ⟨referenceSupport, executableSupport, alpha, values⟩
  let suffix := findallCopySuffix counter raw
  let copiedReferenceSupport :=
    runtimeCopyReferenceSupport firstFresh source
      referenceSupport executableSupport
  let copiedExecutableSupport :=
    runtimeCopyExecutableSupport suffix source
      referenceSupport executableSupport
  have copiedAlpha :
      RuntimeAlpha copiedReferenceSupport copiedExecutableSupport := by
    exact runtimeCopy_runtimeAlpha alpha firstFresh suffix source
  have copiedValue :
      CanonicalRuntimeAgrees
        (RuntimeAlpha.graph copiedReferenceSupport copiedExecutableSupport)
        (Term.denote (copyTerm firstFresh source))
        (copyFindallAtom counter raw).value := by
    rw [copyFindallAtom_value_eq_rename]
    change
      CanonicalRuntimeAgrees
        (RuntimeAlpha.graph copiedReferenceSupport copiedExecutableSupport)
        (Term.denote (copyTerm firstFresh source))
        (renameAtomSuffix suffix raw)
    rw [show
      Term.denote (copyTerm firstFresh source) =
        Tree.renameVariables (copyRename firstFresh source)
          (Term.denote source) by
      simp only [copyTerm, Term.denote_renameVariables]]
    apply canonicalRuntimeAgrees_alpha_rename
      (domain := copyVariables source)
      (before := RuntimeAlpha.graph referenceSupport executableSupport)
      (after :=
        RuntimeAlpha.graph copiedReferenceSupport copiedExecutableSupport)
    · intro identity name linked member
      exact runtimeCopy_graph_member linked source
        (List.mem_eraseDups.mp member) firstFresh suffix
    · exact values
    · exact Term.denote_variablesSatisfy_of_occurrences source
        (fun _ member => List.mem_eraseDups.mpr member)
  refine ⟨copiedReferenceSupport, copiedExecutableSupport, ?_⟩
  refine
    { runtimeAlpha := copiedAlpha
      value := copiedValue
      referenceUsed := ?_
      executableUsed := ?_ }
  · intro identity member
    change
      identity ∈
        ((runtimeCopyActivePairs source referenceSupport executableSupport).map
          Prod.fst).map (copyRename firstFresh source) at member
    rcases List.mem_map.mp member with
      ⟨sourceIdentity, sourceIdentityMember, rfl⟩
    rcases List.mem_map.mp sourceIdentityMember with
      ⟨pair, pairMember, rfl⟩
    have active : pair.1 ∈ copyVariables source := by
      simpa [runtimeCopyActivePairs] using (List.mem_filter.mp pairMember).2
    rw [copyTerm, termVariables_renameVariables]
    exact List.mem_map.mpr
      ⟨pair.1, List.mem_eraseDups.mp active, rfl⟩
  · intro copiedName member
    change
      copiedName ∈
        ((runtimeCopyActivePairs source referenceSupport executableSupport).map
          Prod.snd).map (fun name => name ++ suffix) at member
    rcases List.mem_map.mp member with ⟨name, nameMember, rfl⟩
    rcases List.mem_map.mp nameMember with ⟨pair, pairMember, rfl⟩
    have activeParts := List.mem_filter.mp pairMember
    have sourceMember : pair.1 ∈ termVariables source := by
      have active : pair.1 ∈ copyVariables source := by
        simpa using activeParts.2
      exact List.mem_eraseDups.mp active
    have canonicalOccurs :
        Tree.occurs pair.1 (Term.denote source) = true :=
      Term.denote_occurs_true_of_mem source sourceMember
    have runtimeOccurs : Metta.Subst.occurs pair.2 raw = true := by
      rw [← CanonicalRuntimeAgrees.occurs_eq
        (RuntimeAlpha.graph_shared alpha) activeParts.1 values]
      exact canonicalOccurs
    have rawMember : pair.2 ∈ raw.vars :=
      atom_mem_vars_of_occurs_true pair.2 raw runtimeOccurs
    rw [copyFindallAtom_value_eq_rename]
    exact (mem_renameAtomSuffix_vars suffix raw _).mpr
      ⟨pair.2, rawMember, rfl⟩

/-! ## Tight list composition -/

/-- Two finite positional alphas with disjoint projections append to one
finite positional alpha. -/
theorem RuntimeAlpha.append_of_disjoint
    {leftReference rightReference : List LogicVar}
    {leftExecutable rightExecutable : List String}
    (left : RuntimeAlpha leftReference leftExecutable)
    (right : RuntimeAlpha rightReference rightExecutable)
    (referenceDisjoint : List.Disjoint leftReference rightReference)
    (executableDisjoint : List.Disjoint leftExecutable rightExecutable) :
    RuntimeAlpha (leftReference ++ rightReference)
      (leftExecutable ++ rightExecutable) := by
  constructor
  · simp only [List.length_append]
    rw [left.cardinality, right.cardinality]
  · apply List.nodup_append.mpr
    refine ⟨left.referenceInjective, right.referenceInjective, ?_⟩
    intro leftIdentity leftMember rightIdentity rightMember same
    subst rightIdentity
    exact (List.disjoint_left.mp referenceDisjoint)
      leftMember rightMember
  · apply List.nodup_append.mpr
    refine ⟨left.executableInjective, right.executableInjective, ?_⟩
    intro leftName leftMember rightName rightMember same
    subst rightName
    exact (List.disjoint_left.mp executableDisjoint)
      leftMember rightMember

/-- The positional graph of appended supports is the append of the two
positional graphs when the left cardinalities agree. -/
theorem RuntimeAlpha.graph_append
    {leftReference rightReference : List LogicVar}
    {leftExecutable rightExecutable : List String}
    (left : RuntimeAlpha leftReference leftExecutable) :
    RuntimeAlpha.graph (leftReference ++ rightReference)
        (leftExecutable ++ rightExecutable) =
      RuntimeAlpha.graph leftReference leftExecutable ++
        RuntimeAlpha.graph rightReference rightExecutable := by
  unfold RuntimeAlpha.graph
  exact List.zip_append left.cardinality

/-- Ordered tight term agreement under one combined alpha.  The occurrence
fields state that the combined supports are still exact subsets of the
ordered values, enabling another disjoint append. -/
structure TightRuntimeTermsAgreesWith
    (referenceSupport : List LogicVar) (executableSupport : List String)
    (references : List Term) (executables : List Atom) : Prop where
  runtimeAlpha : RuntimeAlpha referenceSupport executableSupport
  terms :
    List.Forall₂
      (fun reference executable =>
        CanonicalRuntimeAgrees
          (RuntimeAlpha.graph referenceSupport executableSupport)
          (Term.denote reference) executable)
      references executables
  referenceUsed :
    ∀ identity, identity ∈ referenceSupport →
      ∃ reference, reference ∈ references ∧
        identity ∈ termVariables reference
  executableUsed :
    ∀ name, name ∈ executableSupport →
      ∃ executable, executable ∈ executables ∧ name ∈ executable.vars

private theorem canonical_forall₂_mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ∀ {references : List Term} {executables : List Atom},
      List.Forall₂
          (fun reference executable =>
            CanonicalRuntimeAgrees smaller (Term.denote reference) executable)
          references executables →
        List.Forall₂
          (fun reference executable =>
            CanonicalRuntimeAgrees larger (Term.denote reference) executable)
          references executables
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons
        (PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
          included head)
        (canonical_forall₂_mono included tail)

/-- Pointwise tight values with pairwise-disjoint variable occurrences
compose into one tight shared-alpha certificate without changing list order
or multiplicity. -/
theorem tightRuntimeTerms_of_pointwise :
    ∀ {references : List Term} {executables : List Atom},
      List.Forall₂ TightRuntimeTermAgrees references executables →
      references.Pairwise
        (fun left right =>
          List.Disjoint (termVariables left) (termVariables right)) →
      executables.Pairwise
        (fun left right => List.Disjoint left.vars right.vars) →
      ∃ referenceSupport executableSupport,
        TightRuntimeTermsAgreesWith referenceSupport executableSupport
          references executables
  | [], [], .nil, _, _ => by
      exact
        ⟨[], [],
          { runtimeAlpha := ⟨rfl, by simp, by simp⟩
            terms := .nil
            referenceUsed := by simp
            executableUsed := by simp }⟩
  | reference :: references, executable :: executables,
      .cons head tail, referencePairwise, executablePairwise => by
      rw [List.pairwise_cons] at referencePairwise executablePairwise
      rcases head with
        ⟨headReferenceSupport, headExecutableSupport, headAgreement⟩
      rcases tightRuntimeTerms_of_pointwise tail referencePairwise.2
          executablePairwise.2 with
        ⟨tailReferenceSupport, tailExecutableSupport, tailAgreement⟩
      have referenceDisjoint :
          List.Disjoint headReferenceSupport tailReferenceSupport := by
        rw [List.disjoint_left]
        intro identity headMember tailMember
        obtain ⟨tailReference, tailReferenceMember, tailIdentityMember⟩ :=
          tailAgreement.referenceUsed identity tailMember
        have valueDisjoint :=
          referencePairwise.1 tailReference tailReferenceMember
        exact (List.disjoint_left.mp valueDisjoint)
          (headAgreement.referenceUsed identity headMember)
          tailIdentityMember
      have executableDisjoint :
          List.Disjoint headExecutableSupport tailExecutableSupport := by
        rw [List.disjoint_left]
        intro name headMember tailMember
        obtain ⟨tailExecutable, tailExecutableMember, tailNameMember⟩ :=
          tailAgreement.executableUsed name tailMember
        have valueDisjoint :=
          executablePairwise.1 tailExecutable tailExecutableMember
        exact (List.disjoint_left.mp valueDisjoint)
          (headAgreement.executableUsed name headMember)
          tailNameMember
      let combinedReferenceSupport :=
        headReferenceSupport ++ tailReferenceSupport
      let combinedExecutableSupport :=
        headExecutableSupport ++ tailExecutableSupport
      have combinedAlpha :
          RuntimeAlpha combinedReferenceSupport combinedExecutableSupport :=
        RuntimeAlpha.append_of_disjoint headAgreement.runtimeAlpha
          tailAgreement.runtimeAlpha referenceDisjoint executableDisjoint
      have graphEq :
          RuntimeAlpha.graph combinedReferenceSupport
              combinedExecutableSupport =
            RuntimeAlpha.graph headReferenceSupport headExecutableSupport ++
              RuntimeAlpha.graph tailReferenceSupport tailExecutableSupport :=
        RuntimeAlpha.graph_append headAgreement.runtimeAlpha
      refine ⟨combinedReferenceSupport, combinedExecutableSupport, ?_⟩
      refine
        { runtimeAlpha := combinedAlpha
          terms := ?_
          referenceUsed := ?_
          executableUsed := ?_ }
      · rw [graphEq]
        exact .cons
          (PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
            (fun pair member => List.mem_append_left _ member)
            headAgreement.value)
          (canonical_forall₂_mono
            (fun pair member => List.mem_append_right _ member)
            tailAgreement.terms)
      · intro identity member
        change identity ∈
          headReferenceSupport ++ tailReferenceSupport at member
        rcases List.mem_append.mp member with member | member
        · exact ⟨reference, by simp,
            headAgreement.referenceUsed identity member⟩
        · obtain ⟨value, valueMember, identityMember⟩ :=
            tailAgreement.referenceUsed identity member
          exact ⟨value, by simp [valueMember], identityMember⟩
      · intro name member
        change name ∈
          headExecutableSupport ++ tailExecutableSupport at member
        rcases List.mem_append.mp member with member | member
        · exact ⟨executable, by simp,
            headAgreement.executableUsed name member⟩
        · obtain ⟨value, valueMember, nameMember⟩ :=
            tailAgreement.executableUsed name member
          exact ⟨value, by simp [valueMember], nameMember⟩

/-- Paying one old deferred entry produces the stronger tight certificate;
the deferred frontier is irrelevant to content but records that the
independent copy was allocated by a real earlier collection step. -/
theorem DeferredCopyAgreesAt.payTight
    {referenceFrontier : Nat} {referenceCopied : Term}
    {executableRaw : Atom}
    (agreement :
      DeferredCopyAgreesAt referenceFrontier referenceCopied executableRaw)
    (counter : Nat) :
    TightRuntimeTermAgrees referenceCopied
      (copyFindallAtom counter executableRaw).value := by
  rcases agreement with ⟨witness, _reserved⟩
  rw [witness.copied]
  exact copyTerm_copyFindallAtom_tight
    witness.sourceAgrees witness.firstFresh counter

private theorem deferred_forall₂_pay_tight
    {referenceFrontier : Nat} :
    ∀ {references : List Term} {raws : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt referenceFrontier) references raws →
      ∀ counter,
        List.Forall₂ TightRuntimeTermAgrees references
          (copyFindallBag counter raws).values
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, counter => by
      simp only [copyFindallBag]
      exact .cons (DeferredCopyAgreesAt.payTight head counter)
        (deferred_forall₂_pay_tight tail
          (copyFindallAtom counter _).counter)

/-- Paying a chronologically separated collection debt yields one tight
shared-alpha bag certificate.  Both copy timings remain independent; the
result graph is derived from their actual paid values and exact active
supports. -/
theorem SeparatedCollectionCopyFrontier.payTight
    {entryBindings : Substitution}
    {referenceFloor referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      SeparatedCollectionCopyFrontier entryBindings referenceFloor referenceFrontier
        executableFrontier referenceCopiedRev executableRawRev)
    (counter : Nat) :
    ∃ referenceSupport executableSupport,
      TightRuntimeTermsAgreesWith referenceSupport executableSupport
        referenceCopiedRev.reverse
        (copyFindallBag counter executableRawRev.reverse).values := by
  have pointwise :
      List.Forall₂ TightRuntimeTermAgrees referenceCopiedRev.reverse
        (copyFindallBag counter executableRawRev.reverse).values :=
    deferred_forall₂_pay_tight (List.rel_reverse agreement.debt.debt)
      counter
  have referencePairwise :
      referenceCopiedRev.reverse.Pairwise
        (fun left right =>
          List.Disjoint (termVariables left) (termVariables right)) := by
    exact agreement.pairwiseReference.reverse.imp
      (fun disjoint => disjoint.symm)
  have executablePairwise :
      (copyFindallBag counter executableRawRev.reverse).values.Pairwise
        (fun left right => List.Disjoint left.vars right.vars) :=
    PLeaTTa.FindallCopy.copyFindallBag_pairwise_variable_disjoint
      counter executableRawRev.reverse
  exact tightRuntimeTerms_of_pointwise pointwise referencePairwise
    executablePairwise

/-- Paying a separated debt at a caller-related executable frontier produces
exact bag supports disjoint from both caller-alpha projections.  This is the
allocator theorem which later discharges caller/bag alpha compatibility; no
compatibility is accepted as an exit argument. -/
theorem SeparatedCollectionCopyFrontier.payTightProjectionDisjoint
    {entryBindings : Substitution}
    {callerAlpha : List (LogicVar × String)}
    {referenceFloor referenceFrontier executableFrontier counter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      SeparatedCollectionCopyFrontier entryBindings referenceFloor
        referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (callerFrontier :
      AlphaFreshFrontier callerAlpha referenceFloor counter) :
    ∃ referenceSupport executableSupport,
      TightRuntimeTermsAgreesWith referenceSupport executableSupport
          referenceCopiedRev.reverse
          (copyFindallBag counter executableRawRev.reverse).values ∧
        List.Disjoint (callerAlpha.map Prod.fst) referenceSupport ∧
        List.Disjoint (callerAlpha.map Prod.snd) executableSupport ∧
        List.Disjoint (entryBindings.map Prod.fst) referenceSupport ∧
        (∀ name, name ∈ executableSupport →
          counter < resolutionSeedHighWaterName name) := by
  rcases agreement.payTight counter with
    ⟨referenceSupport, executableSupport, tight⟩
  have executableAbove :
      ∀ name, name ∈ executableSupport →
        counter < resolutionSeedHighWaterName name := by
    intro name supportMember
    obtain ⟨copied, copiedMember, nameMember⟩ :=
      tight.executableUsed name supportMember
    exact PLeaTTa.FindallCopy.copyFindallBag_value_above_input
      counter executableRawRev.reverse copied copiedMember name nameMember
  refine
    ⟨referenceSupport, executableSupport, tight, ?_, ?_, ?_,
      executableAbove⟩
  · rw [List.disjoint_left]
    intro identity callerMember supportMember
    obtain ⟨reference, referenceMember, identityMember⟩ :=
      tight.referenceUsed identity supportMember
    have sourceMember : reference ∈ referenceCopiedRev := by
      simpa using (List.mem_reverse.mp referenceMember)
    obtain ⟨index, identityShape, atLeast⟩ :=
      generatedAtLeast_index_of_mem_term
        (agreement.aboveFloor reference sourceMember) identityMember
    subst identity
    exact (Nat.not_lt_of_ge atLeast)
      (callerFrontier.1 index callerMember)
  · rw [List.disjoint_left]
    intro name callerMember supportMember
    have callerBelow : resolutionSeedHighWaterName name ≤ counter :=
      (PersistentSubst.resolutionSeedHighWaterNames_le_iff
        (callerAlpha.map Prod.snd) counter).mp callerFrontier.2
        name callerMember
    exact (Nat.not_lt_of_ge callerBelow) (executableAbove name supportMember)
  · rw [List.disjoint_left]
    intro identity entryMember supportMember
    obtain ⟨reference, referenceMember, identityMember⟩ :=
      tight.referenceUsed identity supportMember
    have sourceMember : reference ∈ referenceCopiedRev := by
      simpa using (List.mem_reverse.mp referenceMember)
    exact
      (List.disjoint_left.mp
        (agreement.entrySourcesDisjoint reference sourceMember))
        entryMember identityMember

/-!
`List.Forall₂ RuntimeTermAgrees` is deliberately adequate for recording copy
debt one solution at a time, but it is not adequate for the final bag.  Its
existential runtime alpha may be chosen independently at every position, so
it cannot rule out collapsing two distinct variables from different
solutions onto one executable name.

The relation below retains one finite alpha bijection for the complete
ordered bag.  It therefore preserves cross-solution separation and sharing.
The exit theorem then appends this bag graph to the historical caller graph
under explicit forward/backward compatibility.  Freshness of the actual copy
history must discharge that compatibility; it is not assumed implicitly by
the caller payload.
-/

/-- Ordered term agreement under one finite runtime alpha shared by every bag
position.  The two support lists remain explicit so later copy-history proofs
can establish their allocator bounds and cross-disjointness. -/
structure RuntimeTermsAgreesWith
    (referenceSupport : List LogicVar) (executableSupport : List String)
    (references : List Term) (executables : List Atom) : Prop where
  runtimeAlpha : RuntimeAlpha referenceSupport executableSupport
  terms :
    List.Forall₂
      (fun reference executable =>
        CanonicalRuntimeAgrees
          (RuntimeAlpha.graph referenceSupport executableSupport)
          (Term.denote reference) executable)
      references executables

/-- Existential shared-alpha view for clients that do not need the concrete
copy supports. -/
def RuntimeTermsAgrees (references : List Term)
    (executables : List Atom) : Prop :=
  ∃ referenceSupport executableSupport,
    RuntimeTermsAgreesWith referenceSupport executableSupport
      references executables

namespace TightRuntimeTermsAgreesWith

/-- Forgetting aggregate tightness yields the shared bag relation consumed by
the exit theorem. -/
theorem sharedBag
    {referenceSupport : List LogicVar} {executableSupport : List String}
    {references : List Term} {executables : List Atom}
    (agreement :
      TightRuntimeTermsAgreesWith referenceSupport executableSupport
        references executables) :
    RuntimeTermsAgreesWith referenceSupport executableSupport
      references executables :=
  ⟨agreement.runtimeAlpha, agreement.terms⟩

end TightRuntimeTermsAgreesWith

namespace RuntimeTermsAgreesWith

private theorem pointwiseOfAlpha
    {referenceSupport : List LogicVar} {executableSupport : List String}
    (runtimeAlpha : RuntimeAlpha referenceSupport executableSupport)
    {references : List Term} {executables : List Atom}
    (agreement :
      List.Forall₂
        (fun reference executable =>
          CanonicalRuntimeAgrees
            (RuntimeAlpha.graph referenceSupport executableSupport)
            (Term.denote reference) executable)
        references executables) :
    List.Forall₂ RuntimeTermAgrees references executables := by
  induction agreement with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        ⟨referenceSupport, executableSupport, runtimeAlpha, head⟩
        inductionHypothesis

/-- The positional runtime-alpha graph is functional in both directions. -/
theorem shared
    {referenceSupport : List LogicVar} {executableSupport : List String}
    {references : List Term} {executables : List Atom}
    (agreement :
      RuntimeTermsAgreesWith referenceSupport executableSupport
        references executables) :
    SharedRuntimeAlpha
      (RuntimeAlpha.graph referenceSupport executableSupport) :=
  PLeaTTa.PrologMguBridge.RuntimeAlpha.graph_shared
    agreement.runtimeAlpha

/-- A shared bag certificate conservatively implies the older pointwise copy
relation.  The converse is false, as witnessed below. -/
theorem pointwise
    {referenceSupport : List LogicVar} {executableSupport : List String}
    {references : List Term} {executables : List Atom}
    (agreement :
      RuntimeTermsAgreesWith referenceSupport executableSupport
        references executables) :
    List.Forall₂ RuntimeTermAgrees references executables :=
  pointwiseOfAlpha agreement.runtimeAlpha agreement.terms

end RuntimeTermsAgreesWith

/-- Pointwise canonical readings under one shared alpha induce the exact
proper-list reading without changing order or duplicate multiplicity. -/
theorem CanonicalRuntimeTermsAgree.properList
    {alpha : List (LogicVar × String)}
    {references : List Term} {executables : List Atom}
    (agreement :
      List.Forall₂
        (fun reference executable =>
          CanonicalRuntimeAgrees alpha (Term.denote reference) executable)
        references executables) :
    CanonicalRuntimeAgrees alpha
      (Term.denote (.list references none)) (chainOf executables) := by
  induction agreement with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- A shared ordered-bag alpha yields one runtime agreement for the complete
proper-list value.  In particular, sharing edges between different positions
remain observable. -/
theorem RuntimeTermsAgreesWith.properList
    {referenceSupport : List LogicVar} {executableSupport : List String}
    {references : List Term} {executables : List Atom}
    (agreement :
      RuntimeTermsAgreesWith referenceSupport executableSupport
        references executables) :
    RuntimeTermAgrees (.list references none) (chainOf executables) :=
  ⟨referenceSupport, executableSupport, agreement.runtimeAlpha,
    PLeaTTa.PrologFindallBagAlphaBridge.CanonicalRuntimeTermsAgree.properList
      agreement.terms⟩

/-- Pointwise runtime agreement can collapse two variables which occur in
different bag positions.  A single shared bag alpha rejects the same data.

This is the anti-vacuity witness for `RuntimeTermsAgreesWith`: replacing it by
the older `Forall₂` would make the eventual findall equality unsound with
respect to cross-solution variable separation. -/
theorem pointwise_aliasing_does_not_make_shared_bag :
    let first : LogicVar := .source "first"
    let second : LogicVar := .source "second"
    let references : List Term := [.variable first, .variable second]
    let executables : List Atom := [.var "same", .var "same"]
    List.Forall₂ RuntimeTermAgrees references executables ∧
      ¬ RuntimeTermsAgrees references executables := by
  let first : LogicVar := .source "first"
  let second : LogicVar := .source "second"
  let references : List Term := [.variable first, .variable second]
  let executables : List Atom := [.var "same", .var "same"]
  have firstAlpha : RuntimeAlpha [first] ["same"] := by
    exact ⟨rfl, by simp, by simp⟩
  have secondAlpha : RuntimeAlpha [second] ["same"] := by
    exact ⟨rfl, by simp, by simp⟩
  have firstAgreement :
      RuntimeTermAgrees (.variable first) (.var "same") := by
    exact
      ⟨[first], ["same"], firstAlpha,
        PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          (.variable (by simp [RuntimeAlpha.graph]))⟩
  have secondAgreement :
      RuntimeTermAgrees (.variable second) (.var "same") := by
    exact
      ⟨[second], ["same"], secondAlpha,
        PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          (.variable (by simp [RuntimeAlpha.graph]))⟩
  constructor
  · exact .cons firstAgreement (.cons secondAgreement .nil)
  · rintro ⟨referenceSupport, executableSupport, whole⟩
    have shared := whole.shared
    cases whole.terms with
    | cons firstTerm tail =>
        cases firstTerm with
        | «variable» firstLinked =>
            cases tail with
            | cons secondTerm rest =>
                cases secondTerm with
                | «variable» secondLinked =>
                    have impossible : first = second :=
                      shared.backward firstLinked secondLinked
                    simp [first, second] at impossible

/-- Compatibility of a historical caller graph with one fresh bag graph.
Both directions are explicit because they protect different observable
aliasing edges. -/
structure CallerBagAlphaCompatible
    (callerAlpha : List (LogicVar × String))
    (bagReferenceSupport : List LogicVar)
    (bagExecutableSupport : List String) : Prop where
  forward :
    AlphaForwardCompatible callerAlpha
      (RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
  backward :
    AlphaBackwardCompatible callerAlpha
      (RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)

/-- Projection disjointness is the allocator-facing way to discharge caller
and bag compatibility. -/
theorem CallerBagAlphaCompatible.ofProjectionDisjoint
    {callerAlpha : List (LogicVar × String)}
    {bagReferenceSupport : List LogicVar}
    {bagExecutableSupport : List String}
    (bagRuntimeAlpha :
      RuntimeAlpha bagReferenceSupport bagExecutableSupport)
    (referenceDisjoint :
      List.Disjoint (callerAlpha.map Prod.fst) bagReferenceSupport)
    (executableDisjoint :
      List.Disjoint (callerAlpha.map Prod.snd) bagExecutableSupport) :
    CallerBagAlphaCompatible callerAlpha bagReferenceSupport
      bagExecutableSupport := by
  constructor
  · intro identity leftName rightName leftMember rightMember
    exfalso
    have callerProjection : identity ∈ callerAlpha.map Prod.fst :=
      List.mem_map.mpr ⟨(identity, leftName), leftMember, rfl⟩
    have bagProjection :
        identity ∈
          (RuntimeAlpha.graph bagReferenceSupport
            bagExecutableSupport).map Prod.fst :=
      List.mem_map.mpr ⟨(identity, rightName), rightMember, rfl⟩
    rw [bagRuntimeAlpha.graph_reference] at bagProjection
    exact (List.disjoint_left.mp referenceDisjoint)
      callerProjection bagProjection
  · intro leftIdentity rightIdentity name leftMember rightMember
    exfalso
    have callerProjection : name ∈ callerAlpha.map Prod.snd :=
      List.mem_map.mpr ⟨(leftIdentity, name), leftMember, rfl⟩
    have bagProjection :
        name ∈
          (RuntimeAlpha.graph bagReferenceSupport
            bagExecutableSupport).map Prod.snd :=
      List.mem_map.mpr ⟨(rightIdentity, name), rightMember, rfl⟩
    rw [bagRuntimeAlpha.graph_executable] at bagProjection
    exact (List.disjoint_left.mp executableDisjoint)
      callerProjection bagProjection

/-- The actual separated copy history and its payment derive both the shared
bag relation and caller compatibility.  The bag alpha is therefore a result
of the producer certificate, never an arbitrary argument chosen at exit. -/
theorem SeparatedCollectionCopyFrontier.paySharedCompatible
    {entryBindings : Substitution}
    {callerAlpha : List (LogicVar × String)}
    {referenceFloor referenceFrontier executableFrontier counter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      SeparatedCollectionCopyFrontier entryBindings referenceFloor
        referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (callerFrontier :
      AlphaFreshFrontier callerAlpha referenceFloor counter) :
    ∃ referenceSupport executableSupport,
      RuntimeTermsAgreesWith referenceSupport executableSupport
          referenceCopiedRev.reverse
          (copyFindallBag counter executableRawRev.reverse).values ∧
        CallerBagAlphaCompatible callerAlpha referenceSupport
          executableSupport := by
  rcases agreement.payTightProjectionDisjoint callerFrontier with
    ⟨referenceSupport, executableSupport, tight,
      referenceDisjoint, executableDisjoint, _entryDisjoint,
      _executableAbove⟩
  refine
    ⟨referenceSupport, executableSupport, tight.sharedBag, ?_⟩
  exact CallerBagAlphaCompatible.ofProjectionDisjoint
    tight.runtimeAlpha referenceDisjoint executableDisjoint

private def separationWitnessTemplate : Term :=
  .variable (.source "x")

private def separationWitnessEntryBindings : Substitution :=
  [(.source "z", .variable (.generated 0))]

private def separationWitnessRaw : Atom :=
  .var "x"

private def separationWitnessInitialSession : Session :=
  { resolver := { nextFresh := 1 } }

private def separationWitnessFirst : CollectedTemplate :=
  collectTemplate separationWitnessInitialSession separationWitnessTemplate
    separationWitnessEntryBindings

private def separationWitnessSecond : CollectedTemplate :=
  collectTemplate separationWitnessFirst.session separationWitnessTemplate
    separationWitnessEntryBindings

private def separationWitnessCallerAlpha : List (LogicVar × String) :=
  [(.generated 0, "x" ++ resolutionCompactSuffix 0)]

/-- Positive anti-vacuity witness for chronological bag separation.  Two
solutions of the same unbound generator variable are copied through two
actual collector transitions above a nonempty entry binding and caller
alpha.  Both copied values remain non-ground, their variable sets and
concrete identities are distinct, and paying the history exercises all four
producer-derived freshness conclusions non-vacuously. -/
theorem two_nonground_collection_copies_exercise_separation :
    separationWitnessEntryBindings ≠ [] ∧
      separationWitnessCallerAlpha ≠ [] ∧
      ∃ _history :
        SeparatedCollectionCopyFrontier separationWitnessEntryBindings 1
          separationWitnessSecond.session.resolver.nextFresh 1
          [separationWitnessSecond.prepared.copied,
            separationWitnessFirst.prepared.copied]
          [separationWitnessRaw, separationWitnessRaw],
        termVariables separationWitnessFirst.prepared.copied ≠ [] ∧
          termVariables separationWitnessSecond.prepared.copied ≠ [] ∧
          List.Disjoint
            (termVariables separationWitnessSecond.prepared.copied)
            (termVariables separationWitnessFirst.prepared.copied) ∧
          separationWitnessFirst.prepared.copied =
            .variable (.generated 1) ∧
          separationWitnessSecond.prepared.copied =
            .variable (.generated 2) ∧
          ∃ referenceSupport executableSupport,
            TightRuntimeTermsAgreesWith referenceSupport executableSupport
                [separationWitnessFirst.prepared.copied,
                  separationWitnessSecond.prepared.copied]
                (copyFindallBag 1
                  [separationWitnessRaw, separationWitnessRaw]).values ∧
              List.Disjoint
                (separationWitnessCallerAlpha.map Prod.fst)
                referenceSupport ∧
              List.Disjoint
                (separationWitnessCallerAlpha.map Prod.snd)
                executableSupport ∧
              List.Disjoint (separationWitnessEntryBindings.map Prod.fst)
                referenceSupport ∧
              (∀ name, name ∈ executableSupport →
                1 < resolutionSeedHighWaterName name) := by
  constructor
  · simp [separationWitnessEntryBindings]
  · constructor
    · simp [separationWitnessCallerAlpha]
    · have encoding :
        EncodingInjectiveOn (copyVariables separationWitnessTemplate) := by
        intro left right leftMember rightMember same
        simp [separationWitnessTemplate, copyVariables, termVariables]
          at leftMember rightMember
        simp [leftMember, rightMember]
      have sourceAgrees :
        RuntimeTermAgrees
          (Substitution.applyTerm separationWitnessEntryBindings
            separationWitnessTemplate)
          separationWitnessRaw := by
        have namesDifferent : ("x" : String) ≠ "z" := by decide
        simpa [separationWitnessEntryBindings, separationWitnessTemplate,
          separationWitnessRaw, Substitution.applyTerm,
          Term.instantiateOne, namesDifferent] using
          (runtimeTermAgrees_of_termAgrees
            (TermAgrees.sourceVariable "x") encoding)
      have rawBound :
          resolutionSeedHighWaterNames separationWitnessRaw.vars ≤ 1 := by
        simp [separationWitnessRaw, Atom.vars,
          resolutionSeedHighWaterNames, resolutionSeedHighWaterName,
          terminalResolutionSeed?, terminalResolutionSeedRev]
      have emptyHistory :
          SeparatedCollectionCopyFrontier separationWitnessEntryBindings
            1 1 1 [] [] :=
        SeparatedCollectionCopyFrontier.empty
          separationWitnessEntryBindings 1 1
      have firstHistory :=
        emptyHistory.collect (session := separationWitnessInitialSession)
          separationWitnessTemplate separationWitnessEntryBindings
          separationWitnessRaw
          (BindingLineage.refl separationWitnessEntryBindings)
          sourceAgrees encoding (Nat.le_refl 1) rawBound
      have secondHistory :=
        firstHistory.collect (session := separationWitnessFirst.session)
          separationWitnessTemplate separationWitnessEntryBindings
          separationWitnessRaw
          (BindingLineage.refl separationWitnessEntryBindings)
          sourceAgrees encoding (Nat.le_refl 1) rawBound
      have callerFrontier :
          AlphaFreshFrontier separationWitnessCallerAlpha 1 1 := by
        have callerWater :
            resolutionSeedHighWaterName
              ("x" ++ resolutionCompactSuffix 0) = 1 := by
          simp [resolutionSeedHighWaterName,
            terminalResolutionSeed?_append]
        constructor
        · intro index member
          simp [separationWitnessCallerAlpha] at member
          omega
        · simp [separationWitnessCallerAlpha,
            resolutionSeedHighWaterNames, callerWater]
      rcases secondHistory.payTightProjectionDisjoint callerFrontier with
        ⟨referenceSupport, executableSupport, tight,
          referenceDisjoint, executableDisjoint, entryDisjoint,
          executableAbove⟩
      refine ⟨secondHistory, ?_, ?_, ?_, ?_, ?_, referenceSupport,
        executableSupport, ?_, referenceDisjoint, executableDisjoint,
        entryDisjoint, executableAbove⟩
      · decide
      · decide
      · simpa [separationWitnessFirst, separationWitnessSecond] using
          secondHistory.pairwiseReference
      · rfl
      · rfl
      · simpa [separationWitnessFirst, separationWitnessSecond] using tight

/-- Cumulative residual-variant agreement is monotone in the ambient alpha
graph while retaining the literal representative, support, and runtime
substitution. -/
theorem cumulative_monoAlpha
    {smaller larger support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Subst}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (agreement :
      AlphaCumulativeResidualVariantAgreesOn smaller support canonical
        referenceBase runtime) :
    AlphaCumulativeResidualVariantAgreesOn larger support canonical
      referenceBase runtime := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeCovered, runtimeTopological, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
        included representativeCovered,
      runtimeTopological,
      PLeaTTa.PrologRepresentativeTaskActivationBridge.AlphaValuationAgreesOn.monoAlpha
        included valuation⟩

/-- A runtime name strictly above the complete occupied substitution surface
is absent from that substitution's domain. -/
private theorem runtime_lookup_none_of_below_and_above
    (runtime : Subst) (counter : Nat) (name : String)
    (runtimeBelow :
      resolutionSeedHighWaterNames (resolutionSubstVars runtime) ≤ counter)
    (nameAbove : counter < resolutionSeedHighWaterName name) :
    Metta.Subst.lookup runtime name = none := by
  cases lookupEq : Metta.Subst.lookup runtime name with
  | none => rfl
  | some value =>
      have keyMember : name ∈ runtime.map Prod.fst :=
        (PersistentSubst.subst_lookup_isSome_iff_mem_keys runtime name).mp
          (by simp [lookupEq])
      obtain ⟨⟨key, replacement⟩, entryMember, keyShape⟩ :=
        List.mem_map.mp keyMember
      have keyExact : key = name := by simpa using keyShape
      subst key
      have occupied : name ∈ resolutionSubstVars runtime := by
        simp only [resolutionSubstVars, List.mem_flatMap]
        exact ⟨(name, replacement), entryMember, by simp⟩
      have nameBelow : resolutionSeedHighWaterName name ≤ counter :=
        (PersistentSubst.resolutionSeedHighWaterNames_le_iff
          (resolutionSubstVars runtime) counter).mp runtimeBelow
          name occupied
      omega

/-- Extending a cumulative residual valuation by one allocator-fresh bag
graph also extends the observable support.  The hidden independent
representative and executable substitution are retained literally: both are
proved to fix every new bag variable from producer-side domain separation
and the executable high-water bound. -/
theorem cumulative_appendFreshSupport
    {callerAlpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Subst}
    {bagReferenceSupport : List LogicVar}
    {bagExecutableSupport : List String}
    {counter : Nat}
    (agreement :
      AlphaCumulativeResidualVariantAgreesOn callerAlpha support canonical
        referenceBase runtime)
    (bagRuntimeAlpha :
      RuntimeAlpha bagReferenceSupport bagExecutableSupport)
    (referenceDisjoint :
      List.Disjoint (callerAlpha.map Prod.fst) bagReferenceSupport)
    (entrySourcesDisjoint :
      List.Disjoint (current.map Prod.fst) bagReferenceSupport)
    (bindingShape :
      current = TreeSubstitution.reify canonical ++ referenceBase)
    (runtimeBelow :
      resolutionSeedHighWaterNames (resolutionSubstVars runtime) ≤ counter)
    (executableAbove :
      ∀ name, name ∈ bagExecutableSupport →
        counter < resolutionSeedHighWaterName name) :
    AlphaCumulativeResidualVariantAgreesOn
      (callerAlpha ++
        RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
      (support ++
        RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
      canonical referenceBase runtime := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeCovered, runtimeTopological, valuation⟩
  let bagAlpha :=
    RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport
  have callerIncluded :
      ∀ pair, pair ∈ callerAlpha → pair ∈ callerAlpha ++ bagAlpha := by
    intro pair member
    exact List.mem_append_left _ member
  have combinedValuation :
      AlphaValuationAgreesOn (callerAlpha ++ bagAlpha)
        (support ++ bagAlpha)
        (representative ++ Substitution.denote referenceBase) runtime := by
    intro identity name linked
    simp only [List.mem_append] at linked
    rcases linked with historical | fresh
    · exact
        PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
          callerIncluded (valuation historical)
    · have referenceMember : identity ∈ bagReferenceSupport := by
        rw [← bagRuntimeAlpha.graph_reference]
        exact List.mem_map.mpr ⟨(identity, name), fresh, rfl⟩
      have executableMember : name ∈ bagExecutableSupport := by
        rw [← bagRuntimeAlpha.graph_executable]
        exact List.mem_map.mpr ⟨(identity, name), fresh, rfl⟩
      have representativeAbsent :
          identity ∉ TreeSubstitution.keys representative := by
        intro member
        obtain ⟨⟨source, replacement⟩, entryMember, sourceShape⟩ :=
          List.mem_map.mp
            (show identity ∈ representative.map Prod.fst by
              simpa [TreeSubstitution.keys] using member)
        have sourceExact : source = identity := by simpa using sourceShape
        subst source
        rcases (representativeCovered (identity, replacement) entryMember).1
          with ⟨callerName, callerLinked⟩
        have callerMember : identity ∈ callerAlpha.map Prod.fst :=
          List.mem_map.mpr ⟨(identity, callerName), callerLinked, rfl⟩
        exact (List.disjoint_left.mp referenceDisjoint)
          callerMember referenceMember
      have baseAbsent :
          identity ∉
            TreeSubstitution.keys (Substitution.denote referenceBase) := by
        intro member
        have baseSource : identity ∈ referenceBase.map Prod.fst := by
          rw [
            PLeaTTa.PrologRepresentativeActivationBridge.Substitution.denote_keys]
            at member
          exact member
        have currentSource : identity ∈ current.map Prod.fst := by
          rw [bindingShape, List.map_append]
          exact List.mem_append_right _ baseSource
        exact (List.disjoint_left.mp entrySourcesDisjoint)
          currentSource referenceMember
      have independentFixed :
          TreeSubstitution.apply
              (representative ++ Substitution.denote referenceBase)
              (.variable identity) =
            .variable identity := by
        apply TreeSubstitution.apply_eq_self_of_variables_outside
        change
          identity ∉
            TreeSubstitution.keys
              (representative ++ Substitution.denote referenceBase)
        intro member
        simp only [TreeSubstitution.keys, List.map_append,
          List.mem_append] at member
        rcases member with member | member
        · exact representativeAbsent member
        · exact baseAbsent member
      have runtimeLookup : Metta.Subst.lookup runtime name = none :=
        runtime_lookup_none_of_below_and_above runtime counter name
          runtimeBelow (executableAbove name executableMember)
      rw [independentFixed,
        PLeaTTa.subst_var_of_lookup_none runtime name runtimeLookup]
      exact CanonicalRuntimeAgrees.variable
        (List.mem_append_right callerAlpha fresh)
  exact
    ⟨representative, variants, canonicalTopological,
      PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
        callerIncluded representativeCovered,
      runtimeTopological, combinedValuation⟩

namespace FindallFrameVariantPayloadAgrees

/-- Exact mixed semantic packet installed at one `findall` exit.

The historical task data and tail remain in the ordinary raw-alpha relation,
while the newly copied bag is related at canonical denotation level.  This is
intentional: copy debt is semantic and does not imply that an arbitrary
source `Term` uses the preferred raw list/partial-value presentation.

`support` is still the historical caller support.  A later producer must
extend it with the fresh bag graph and prove both carried substitutions act
as the identity there before the equality step can use this packet. -/
structure FindallSuccessorSemanticHeadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (cell : PrologFindallFrameZipperBridge.SourceCollectionCell)
    (frame : FindallFrame) (copiedValues : List Atom) : Prop where
  data :
    TaskDataAgrees alpha support canonical referenceBase cell.entryBindings
      frame.binding
  output : AlphaTermAgrees alpha cell.output frame.result
  bag :
    CanonicalRuntimeAgrees alpha
      (Term.denote (.list cell.reversed.reverse none))
      (chainOf copiedValues)
  tail :
    NormalizedAlphaGoalsAgree alpha barrier cell.tail frame.rest

/-- A historical caller payload and one compatible shared bag alpha construct
the exact semantic equality-head packet installed after collection exit.

The canonical residual state, older base, entry substitutions, caller tail,
and cut barrier are reused literally.  Only the ambient alpha graph grows by
the fresh bag graph.  Thus no residual orientation is reselected at exit and
no per-solution alpha can silently collapse sharing across bag positions.

[SPEC translator.pl:112-116; SWI:findall/3] -/
theorem successorSemanticHead
    {callerAlpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : PrologFindallFrameZipperBridge.SourceCollectionCell}
    {frame : FindallFrame}
    {bagReferenceSupport : List LogicVar}
    {bagExecutableSupport : List String}
    {copiedValues : List Atom}
    (caller :
      FindallFrameVariantPayloadAgrees callerAlpha support barrier cell frame)
    (bag :
      RuntimeTermsAgreesWith bagReferenceSupport bagExecutableSupport
        cell.reversed.reverse copiedValues)
    (compatible :
      CallerBagAlphaCompatible callerAlpha bagReferenceSupport
        bagExecutableSupport) :
    ∃ canonical : TreeSubstitution, ∃ referenceBase : Substitution,
      FindallSuccessorSemanticHeadAgrees
        (callerAlpha ++
          RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
        support barrier canonical referenceBase cell frame copiedValues := by
  rcases caller.components with
    ⟨canonical, referenceBase, data, _template, output, tail,
      _outputSupported, _continuationLive⟩
  let bagAlpha :=
    RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport
  have callerIncluded :
      ∀ pair, pair ∈ callerAlpha → pair ∈ callerAlpha ++ bagAlpha := by
    intro pair member
    exact List.mem_append_left _ member
  have combinedShared : SharedRuntimeAlpha (callerAlpha ++ bagAlpha) :=
    data.alphaShared.append bag.shared compatible.forward compatible.backward
  have combinedValuation :
      AlphaCumulativeResidualVariantAgreesOn
        (callerAlpha ++ bagAlpha) support canonical referenceBase
          frame.binding :=
    cumulative_monoAlpha callerIncluded data.valuation
  have outputCombined :
      AlphaTermAgrees (callerAlpha ++ bagAlpha) cell.output frame.result :=
    PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono callerIncluded output
  have bagCombined :
      CanonicalRuntimeAgrees (callerAlpha ++ bagAlpha)
        (Term.denote (.list cell.reversed.reverse none))
        (chainOf copiedValues) := by
    apply
      PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
        (smaller := bagAlpha)
    · intro pair member
      exact List.mem_append_right _ member
    · exact
        PLeaTTa.PrologFindallBagAlphaBridge.CanonicalRuntimeTermsAgree.properList
          bag.terms
  have tailCombined :
      NormalizedAlphaGoalsAgree (callerAlpha ++ bagAlpha) barrier
        cell.tail frame.rest :=
    tail.mono callerIncluded
  refine ⟨canonical, referenceBase, ?_⟩
  exact
    { data :=
        { alphaShared := combinedShared
          canonicalWellFormed := data.canonicalWellFormed
          bindingShape := data.bindingShape
          valuation := combinedValuation }
      output := outputCombined
      bag := bagCombined
      tail := tailCombined }

/-- The execution-derived exit theorem.  A separated copy history is paid at
the current executable counter; its exact tight supports become both the new
ambient alpha graph and the new observable support.  Caller compatibility,
entry-substitution freshness, and executable-substitution freshness are all
conclusions of the copy producer and allocator bounds.

[SPEC translator.pl:112-116; SWI:findall/3] -/
theorem successorSemanticHead_ofSeparatedCopy
    {callerAlpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : PrologFindallFrameZipperBridge.SourceCollectionCell}
    {frame : FindallFrame}
    {referenceFloor referenceFrontier executableFrontier counter : Nat}
    {executableRawRev : List Atom}
    (caller :
      FindallFrameVariantPayloadAgrees callerAlpha support barrier cell frame)
    (copies :
      SeparatedCollectionCopyFrontier cell.entryBindings referenceFloor
        referenceFrontier executableFrontier cell.reversed executableRawRev)
    (callerFrontier :
      AlphaFreshFrontier callerAlpha referenceFloor counter)
    (runtimeBelow :
      resolutionSeedHighWaterNames
          (resolutionSubstVars frame.binding) ≤ counter) :
    ∃ bagReferenceSupport bagExecutableSupport,
      ∃ canonical : TreeSubstitution, ∃ referenceBase : Substitution,
        FindallSuccessorSemanticHeadAgrees
          (callerAlpha ++
            RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
          (support ++
            RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport)
          barrier canonical referenceBase cell frame
          (copyFindallBag counter executableRawRev.reverse).values := by
  rcases copies.payTightProjectionDisjoint callerFrontier with
    ⟨bagReferenceSupport, bagExecutableSupport, tight,
      referenceDisjoint, executableDisjoint, entrySourcesDisjoint,
      executableAbove⟩
  rcases caller.components with
    ⟨canonical, referenceBase, data, _template, output, tail,
      _outputSupported, _continuationLive⟩
  let bagAlpha :=
    RuntimeAlpha.graph bagReferenceSupport bagExecutableSupport
  have callerIncluded :
      ∀ pair, pair ∈ callerAlpha → pair ∈ callerAlpha ++ bagAlpha := by
    intro pair member
    exact List.mem_append_left _ member
  have compatible :
      CallerBagAlphaCompatible callerAlpha bagReferenceSupport
        bagExecutableSupport :=
    CallerBagAlphaCompatible.ofProjectionDisjoint
      tight.runtimeAlpha referenceDisjoint executableDisjoint
  have combinedShared : SharedRuntimeAlpha (callerAlpha ++ bagAlpha) :=
    data.alphaShared.append tight.sharedBag.shared
      compatible.forward compatible.backward
  have combinedValuation :
      AlphaCumulativeResidualVariantAgreesOn
        (callerAlpha ++ bagAlpha) (support ++ bagAlpha)
        canonical referenceBase frame.binding :=
    cumulative_appendFreshSupport data.valuation tight.runtimeAlpha
      referenceDisjoint entrySourcesDisjoint data.bindingShape
      runtimeBelow executableAbove
  have outputCombined :
      AlphaTermAgrees (callerAlpha ++ bagAlpha) cell.output frame.result :=
    PLeaTTa.PrologMguBridge.AlphaTermAgrees.mono callerIncluded output
  have bagCombined :
      CanonicalRuntimeAgrees (callerAlpha ++ bagAlpha)
        (Term.denote (.list cell.reversed.reverse none))
        (chainOf
          (copyFindallBag counter executableRawRev.reverse).values) := by
    apply
      PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
        (smaller := bagAlpha)
    · intro pair member
      exact List.mem_append_right _ member
    · exact
        PLeaTTa.PrologFindallBagAlphaBridge.CanonicalRuntimeTermsAgree.properList
          tight.terms
  have tailCombined :
      NormalizedAlphaGoalsAgree (callerAlpha ++ bagAlpha) barrier
        cell.tail frame.rest :=
    tail.mono callerIncluded
  refine
    ⟨bagReferenceSupport, bagExecutableSupport, canonical, referenceBase,
      ?_⟩
  exact
    { data :=
        { alphaShared := combinedShared
          canonicalWellFormed := data.canonicalWellFormed
          bindingShape := data.bindingShape
          valuation := combinedValuation }
      output := outputCombined
      bag := bagCombined
      tail := tailCombined }

end FindallFrameVariantPayloadAgrees

end PLeaTTa.PrologFindallBagAlphaBridge
