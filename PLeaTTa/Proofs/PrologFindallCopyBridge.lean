-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallCopyBridge
Purpose: Relate answer-time independent findall copies to the executable
  collector's later bounded copy phase without identifying allocator counters.
Trusted boundary: none
Main exports: RuntimeTermAgrees, DeferredCopyAgreesAt,
  CollectionCopyFrontier, CopyPaymentAgrees
-/
import PLeaTTa.Proofs.FindallCopy
import PLeaTTa.Proofs.PrologStateBridge

namespace PLeaTTa.PrologFindallCopyBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Copy
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge

/-!
# The private-copy timing seam

The independent search semantics copies a `findall/3` template as soon as its
generator answer is collected.  The executable macro stores the materialized
answer and its additive fine lane copies the completed bag later.  Neither
choice is observable before collection finishes, but their allocation
counters cannot be equated: nested calls may allocate between two answers.

The bridge below records an ordered *copy debt*.  Each independent copied term
is paired with the still-raw executable answer from which it arose.  Advancing
either allocator preserves the debt.  During the bounded executable copy
phase, one `BagCopyStep` pays exactly one entry and produces an explicit finite
alpha bijection for that value.  Thus the timing difference is represented in
the state relation rather than erased by an answer-list quotient or a
zero-step copy.
-/

/-- Independent targets chosen by the deterministic finite-term copier, in
stable first-occurrence order. -/
def termCopyReferenceTargets (firstFresh : Nat) (source : Term) :
    List LogicVar :=
  (copyVariables source).map (copyRename firstFresh source)

/-- Executable suffix targets for the same independently derived finite
support. -/
def termCopyExecutableTargets (suffix : String) (source : Term) :
    List String :=
  executableFreshTargets suffix (copyVariables source)

/-- The positional alpha graph used to compare the two actual copy
implementations. -/
def termCopyAlphaGraph (firstFresh : Nat) (suffix : String)
    (source : Term) : List (LogicVar × String) :=
  RuntimeAlpha.graph
    (termCopyReferenceTargets firstFresh source)
    (termCopyExecutableTargets suffix source)

private theorem eraseDups_nodup :
    ∀ support : List LogicVar, support.eraseDups.Nodup
  | [] => by
      simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup
          (tail.filter (fun identity => !identity == head))
termination_by support => support.length
decreasing_by
  have lengthBound :=
    List.length_filter_le (fun identity : LogicVar => !identity == head) tail
  simp only [List.length_cons]
  omega

private theorem copyVariables_nodup (source : Term) :
    (copyVariables source).Nodup := by
  exact eraseDups_nodup (termVariables source)

/-- The independent copy targets are injective on the complete finite source
support. -/
theorem termCopyReferenceTargets_nodup (firstFresh : Nat) (source : Term) :
    (termCopyReferenceTargets firstFresh source).Nodup := by
  apply (copyVariables_nodup source).map_on
  intro left leftMember right rightMember same
  have sameIndex :
      (copyVariables source).idxOf left =
        (copyVariables source).idxOf right := by
    unfold copyRename at same
    injection same with generated
    omega
  exact (List.idxOf_inj leftMember).mp sameIndex

/-- The two target lists have the same independently determined cardinality
and are both injective under the already-explicit source/generated spelling
premise. -/
theorem termCopy_runtimeAlpha (firstFresh : Nat) (suffix : String)
    (source : Term) (encoding : EncodingInjectiveOn (copyVariables source)) :
    RuntimeAlpha
      (termCopyReferenceTargets firstFresh source)
      (termCopyExecutableTargets suffix source) := by
  constructor
  · simp [termCopyReferenceTargets, termCopyExecutableTargets,
      executableFreshTargets]
  · exact termCopyReferenceTargets_nodup firstFresh source
  · exact executableFreshTargets_nodup
      (copyVariables_nodup source) encoding suffix

private theorem termCopyAlphaGraph_eq_map (firstFresh : Nat)
    (suffix : String) (source : Term) :
    termCopyAlphaGraph firstFresh suffix source =
      (copyVariables source).map fun identity =>
        (copyRename firstFresh source identity,
          logicVarExecutableName identity ++ suffix) := by
  unfold termCopyAlphaGraph RuntimeAlpha.graph
  unfold termCopyReferenceTargets termCopyExecutableTargets
  unfold executableFreshTargets
  induction copyVariables source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.zip_cons_cons, inductionHypothesis]

/-- Every occurring source identity is linked to the two concrete targets at
its stable support position. -/
theorem termCopyAlphaGraph_member (firstFresh : Nat) (suffix : String)
    (source : Term) (identity : LogicVar)
    (member : identity ∈ termVariables source) :
    (copyRename firstFresh source identity,
      logicVarExecutableName identity ++ suffix) ∈
        termCopyAlphaGraph firstFresh suffix source := by
  rw [termCopyAlphaGraph_eq_map, List.mem_map]
  exact ⟨identity, List.mem_eraseDups.mpr member, rfl⟩

/-- Representation agreement is stable under an arbitrary independent
variable renaming and the executable's common-suffix renaming, provided the
same finite alpha graph links every variable in the independently supplied
domain. -/
theorem termAgrees_alpha_rename
    {rename : LogicVar → LogicVar} {suffix : String}
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        (rename identity, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {term : Term} {atom : Atom} (agreement : TermAgrees term atom)
    (supported : termVariablesIn domain term) :
    AlphaTermAgrees alpha
      (term.renameVariables rename)
      (renameAtomSuffix suffix atom) := by
  apply TermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        AlphaTermAgrees alpha
          (term.renameVariables rename)
          (renameAtomSuffix suffix atom))
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        AlphaProperListAgrees alpha
          (Terms.renameVariables rename terms)
          (renameAtomSuffix suffix atom))
  · intro name member
    simpa [Term.renameVariables, renameAtomSuffix_var,
      logicVarExecutableName] using
      (AlphaTermAgrees.variable
        (variableAgreement (.source name) member))
  · intro index member
    simpa [Term.renameVariables, renameAtomSuffix_var,
      logicVarExecutableName, generatedExecutableName,
      compilerGeneratedName] using
      (AlphaTermAgrees.variable
        (variableAgreement (.generated index) member))
  · intro name notTrue notFalse _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.atom (alpha := alpha) notTrue notFalse)
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.trueAtom (alpha := alpha))
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.falseAtom (alpha := alpha))
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.integer (alpha := alpha) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.float (alpha := alpha) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.string (alpha := alpha) value)
  · intro head terms encoded arguments inductionHypothesis support
    have termsSupport : termsVariablesIn domain terms := by
      simpa [termVariablesIn, termsVariablesIn] using support
    simpa [Term.renameVariables, Terms.renameVariables,
      renameAtomSuffix_chainOf,
      renameAtomSuffix_sym] using
      (AlphaTermAgrees.partialValue
        (inductionHypothesis termsSupport))
  · intro items encoded elements inductionHypothesis support
    have itemsSupport : termsVariablesIn domain items := by
      simpa [termVariablesIn] using support
    simpa [Term.renameVariables] using
      (AlphaTermAgrees.properList (inductionHypothesis itemsSupport))
  · intro _supported
    simpa [Terms.renameVariables, nilA, renameAtomSuffix_sym] using
      (AlphaProperListAgrees.nil (alpha := alpha))
  · intro term atom terms tail head rest headInduction tailInduction support
    simpa [Terms.renameVariables, consC, renameAtomSuffix_expr,
      renameAtomSuffix_sym] using
      (AlphaProperListAgrees.cons
        (headInduction support.1) (tailInduction support.2))
  · exact agreement
  · exact supported

/-- The actual independent term copier and one executable suffix copy are
structurally alpha-related through the complete source support. -/
theorem copyTerm_renameAtomSuffix_alpha
    {source : Term} {raw : Atom} (agreement : TermAgrees source raw)
    (firstFresh : Nat) (suffix : String) :
    AlphaTermAgrees (termCopyAlphaGraph firstFresh suffix source)
      (copyTerm firstFresh source) (renameAtomSuffix suffix raw) := by
  unfold copyTerm
  apply termAgrees_alpha_rename
    (domain := copyVariables source)
    (alpha := termCopyAlphaGraph firstFresh suffix source)
  · intro identity member
    exact termCopyAlphaGraph_member firstFresh suffix source identity
      (List.mem_eraseDups.mp member)
  · exact agreement
  · exact termVariablesIn_of_occurrences (copyVariables source) source
      (fun _ member => List.mem_eraseDups.mpr member)

/-- Cross-runtime agreement for one copied value.  The supports are explicit
and form a finite bijection; this is stronger than merely comparing printed
normal forms. -/
def RuntimeTermAgrees (reference : Term) (executable : Atom) : Prop :=
  ∃ referenceSupport executableSupport,
    RuntimeAlpha referenceSupport executableSupport ∧
      AlphaTermAgrees
        (RuntimeAlpha.graph referenceSupport executableSupport)
        reference executable

/-- Paying one deferred entry at any later executable counter yields a
runtime-alpha-equivalent copied value.  The counter is universally
quantified: intervening executable allocations may change the chosen suffix
but cannot invalidate the debt. -/
theorem copyTerm_copyFindallAtom_runtime_agrees
    {source : Term} {raw : Atom} (agreement : TermAgrees source raw)
    (encoding : EncodingInjectiveOn (copyVariables source))
    (firstFresh counter : Nat) :
    RuntimeTermAgrees (copyTerm firstFresh source)
      (copyFindallAtom counter raw).value := by
  unfold copyFindallAtom
  split
  next closed =>
    let suffix := resolutionCompactSuffix counter
    refine ⟨termCopyReferenceTargets firstFresh source,
      termCopyExecutableTargets suffix source,
      termCopy_runtimeAlpha firstFresh suffix source encoding, ?_⟩
    have copied :=
      copyTerm_renameAtomSuffix_alpha agreement firstFresh suffix
    change
      AlphaTermAgrees
        (termCopyAlphaGraph firstFresh suffix source)
        (copyTerm firstFresh source) raw
    simpa [suffix,
      renameAtomSuffix_eq_self_of_resolutionAtomClosed suffix raw closed]
      using copied
  next _ =>
    let suffix :=
      resolutionCompactSuffix (advanceCounterPastAtoms counter [raw])
    exact
      ⟨termCopyReferenceTargets firstFresh source,
        termCopyExecutableTargets suffix source,
        termCopy_runtimeAlpha firstFresh suffix source encoding,
        copyTerm_renameAtomSuffix_alpha agreement firstFresh suffix⟩

/-- Data and proof carried by one private independent copy paired with the raw
executable answer whose copy is still owed. -/
structure DeferredCopyWitness
    (referenceCopied : Term) (executableRaw : Atom) where
  source : Term
  firstFresh : Nat
  nextFresh : Nat
  sourceAgrees : TermAgrees source executableRaw
  encoding : EncodingInjectiveOn (copyVariables source)
  copied :
    referenceCopied = copyTerm firstFresh source
  next :
    nextFresh = copyNextFresh firstFresh source

/-- One private independent copy paired with the raw executable answer whose
copy is still owed.  The reserved upper bound is below the current independent
frontier, while the executable counter is intentionally absent: payment is
valid at every later counter. -/
def DeferredCopyAgreesAt (referenceFrontier : Nat)
    (referenceCopied : Term) (executableRaw : Atom) : Prop :=
  ∃ witness : DeferredCopyWitness referenceCopied executableRaw,
    witness.nextFresh ≤ referenceFrontier

/-- A debt remains valid when the independent allocator advances. -/
theorem DeferredCopyAgreesAt.mono
    {before after : Nat} {referenceCopied : Term} {executableRaw : Atom}
    (agreement :
      DeferredCopyAgreesAt before referenceCopied executableRaw)
    (advance : before ≤ after) :
    DeferredCopyAgreesAt after referenceCopied executableRaw := by
  rcases agreement with ⟨witness, reserved⟩
  exact ⟨witness, Nat.le_trans reserved advance⟩

/-- One debt entry can be paid at any executable frontier. -/
theorem DeferredCopyAgreesAt.pay
    {referenceFrontier : Nat} {referenceCopied : Term}
    {executableRaw : Atom}
    (agreement :
      DeferredCopyAgreesAt referenceFrontier referenceCopied executableRaw)
    (counter : Nat) :
    RuntimeTermAgrees referenceCopied
      (copyFindallAtom counter executableRaw).value := by
  rcases agreement with ⟨witness, _reserved⟩
  rw [witness.copied]
  exact copyTerm_copyFindallAtom_runtime_agrees witness.sourceAgrees
    witness.encoding witness.firstFresh counter

/-- The real answer-time independent collector creates exactly one debt entry
against a related raw executable answer. -/
theorem collectTemplate_deferred
    (session : Session) (template : Term)
    (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      TermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template))) :
    DeferredCopyAgreesAt
      (collectTemplate session template answerBindings).session.resolver.nextFresh
      (collectTemplate session template answerBindings).prepared.copied raw := by
  let collected := collectTemplate session template answerBindings
  refine ⟨
    { source := answerBindings.applyTerm template
      firstFresh := collected.prepared.firstFresh
      nextFresh := collected.prepared.nextFresh
      sourceAgrees := sourceAgrees
      encoding := encoding
      copied := ?_
      next := ?_ },
    Nat.le_refl _⟩
  · rfl
  · rfl

/-- Ordered reverse-discovery debt plus the honest allocator frontiers.  The
executable bound covers every still-raw answer variable; the independent
bound is carried per entry because its copied variables were allocated at
different answer times. -/
structure CollectionCopyFrontier
    (referenceFrontier executableFrontier : Nat)
    (referenceCopiedRev : List Term) (executableRawRev : List Atom) : Prop where
  debt :
    List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
      referenceCopiedRev executableRawRev
  executableBound :
    resolutionSeedHighWaterNames
      (executableRawRev.flatMap Atom.vars) ≤ executableFrontier

/-- Empty collectors relate at arbitrary, potentially unequal frontiers. -/
theorem CollectionCopyFrontier.empty
    (referenceFrontier executableFrontier : Nat) :
    CollectionCopyFrontier referenceFrontier executableFrontier [] [] := by
  exact ⟨.nil, by simp [resolutionSeedHighWaterNames]⟩

private theorem deferred_forall₂_mono
    {before after : Nat} (advance : before ≤ after) :
    ∀ {referenceCopied : List Term} {executableRaw : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt before)
          referenceCopied executableRaw →
        List.Forall₂ (DeferredCopyAgreesAt after)
          referenceCopied executableRaw
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (head.mono advance) (deferred_forall₂_mono advance tail)

/-- Advancing either allocator cannot invalidate an existing debt. -/
theorem CollectionCopyFrontier.advance
    {referenceBefore referenceAfter executableBefore executableAfter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceBefore executableBefore
        referenceCopiedRev executableRawRev)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    CollectionCopyFrontier referenceAfter executableAfter
      referenceCopiedRev executableRawRev := by
  constructor
  · exact deferred_forall₂_mono referenceMono agreement.debt
  · exact Nat.le_trans agreement.executableBound executableMono

/-- One answer-time independent copy extends the reverse-discovery debt,
while the executable lane keeps the corresponding materialized raw answer.
All older entries are lifted across the new independent high-water. -/
theorem CollectionCopyFrontier.collect
    {session : Session} {executableBefore executableAfter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier session.resolver.nextFresh executableBefore
        referenceCopiedRev executableRawRev)
    (template : Term) (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      TermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template)))
    (executableMono : executableBefore ≤ executableAfter)
    (rawBound :
      resolutionSeedHighWaterNames raw.vars ≤ executableAfter) :
    CollectionCopyFrontier
      (collectTemplate session template answerBindings).session.resolver.nextFresh
      executableAfter
      ((collectTemplate session template answerBindings).prepared.copied ::
        referenceCopiedRev)
      (raw :: executableRawRev) := by
  let collected := collectTemplate session template answerBindings
  have referenceMono :
      session.resolver.nextFresh ≤ collected.session.resolver.nextFresh :=
    collectTemplate_nextFresh_mono session template answerBindings
  constructor
  · exact .cons
      (collectTemplate_deferred session template answerBindings raw
        sourceAgrees encoding)
      (deferred_forall₂_mono referenceMono agreement.debt)
  · simpa only [List.flatMap_cons, resolutionSeedHighWaterNames_append,
      Nat.max_le] using
      And.intro rawBound
        (Nat.le_trans agreement.executableBound executableMono)

/-- The copy-debt frontier is a concrete, non-numeric instantiation of the
abstract persistent-state bridge. -/
def CopyDebtFrontier (referenceCopiedRev : List Term)
    (executableRawRev : List Atom) : FreshFrontierRelation :=
  fun referenceFrontier executableFrontier =>
    CollectionCopyFrontier referenceFrontier executableFrontier
      referenceCopiedRev executableRawRev

/-- Persistent database/world agreement equipped with the exact private
collector debt. -/
abbrev CollectionSessionRelates
    (referenceCopiedRev : List Term) (executableRawRev : List Atom)
    (session : Session) (persistent : DemandDrivenStep.Persistent) : Prop :=
  SessionRelatesPersistent
    (CopyDebtFrontier referenceCopiedRev executableRawRev)
    session persistent

/-- Pairing one real independent collection with one executable raw-answer
insertion preserves the full persistent bridge: database/world agreement is
unchanged, the independent allocator advances immediately, and the
executable allocator may advance independently while the new debt records
the pending copy. -/
theorem CollectionSessionRelates.collect
    {session : Session}
    {persistentBefore persistentAfter : DemandDrivenStep.Persistent}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionSessionRelates referenceCopiedRev executableRawRev
        session persistentBefore)
    (template : Term) (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      TermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template)))
    (world : persistentAfter.world = persistentBefore.world)
    (counterMono : persistentBefore.counter ≤ persistentAfter.counter)
    (rawBound :
      resolutionSeedHighWaterNames raw.vars ≤ persistentAfter.counter) :
    CollectionSessionRelates
      ((collectTemplate session template answerBindings).prepared.copied ::
        referenceCopiedRev)
      (raw :: executableRawRev)
      (collectTemplate session template answerBindings).session
      persistentAfter := by
  constructor
  · rw [collectTemplate_database]
    simpa [world] using agreement.database
  · exact agreement.fresh.collect template answerBindings raw
      sourceAgrees encoding counterMono rawBound

private theorem deferred_forall₂_pay
    {referenceFrontier : Nat} :
    ∀ {referenceCopied : List Term} {executableRaw : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
          referenceCopied executableRaw →
        ∀ counter,
          List.Forall₂ RuntimeTermAgrees referenceCopied
            (copyFindallBag counter executableRaw).values
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, counter => by
      simp only [copyFindallBag]
      exact .cons (head.pay counter)
        (deferred_forall₂_pay tail
          (copyFindallAtom counter _).counter)

/-- A list-level copy debt can be paid after arbitrary intervening allocation:
the resulting executable bag agrees position-for-position with the independent
bag in source discovery order. -/
theorem CollectionCopyFrontier.pay
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    List.Forall₂ RuntimeTermAgrees referenceCopiedRev.reverse
      (copyFindallBag counter executableRawRev.reverse).values := by
  exact deferred_forall₂_pay (List.rel_reverse agreement.debt) counter

/-! ## Step-for-step debt payment

The relation below exposes the copy phase's intermediate prefixes.  Its
outstanding side is in source order; its paid side is reverse source order,
matching `BagCopyState.copiedRev`. -/

/-- Exact correspondence between outstanding/paid independent values and one
bounded executable copy state. -/
structure CopyPaymentAgrees (referenceFrontier : Nat)
    (referenceRemaining : List Term) (referencePaidRev : List Term)
    (phase : FindallCopy.BagCopyState) : Prop where
  outstanding :
    List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
      referenceRemaining phase.remaining
  paid :
    List.Forall₂ RuntimeTermAgrees referencePaidRev phase.copiedRev

/-- A reverse-discovery debt initializes the executable phase with every
entry outstanding and none paid. -/
theorem CollectionCopyFrontier.payment_initial
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    CopyPaymentAgrees referenceFrontier referenceCopiedRev.reverse []
      (FindallCopy.BagCopyState.initial counter executableRawRev.reverse) := by
  exact ⟨List.rel_reverse agreement.debt, .nil⟩

/-- The complete bounded phase pays every debt entry in exactly one
microstep, ends with no outstanding reference value, and leaves the private
reverse accumulators pointwise alpha-related. -/
theorem CollectionCopyFrontier.payment_exact
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    ∃ final,
      FindallCopy.BagCopyStepsN executableRawRev.length
        (FindallCopy.BagCopyState.initial counter executableRawRev.reverse)
        final ∧
      CopyPaymentAgrees referenceFrontier [] referenceCopiedRev final := by
  let copied := copyFindallBag counter executableRawRev.reverse
  let final : FindallCopy.BagCopyState :=
    { remaining := []
      copiedRev := copied.values.reverse
      counter := copied.counter }
  have run :
      FindallCopy.BagCopyStepsN executableRawRev.length
        (FindallCopy.BagCopyState.initial counter executableRawRev.reverse)
        final := by
    simpa [final, copied] using
      (FindallCopy.BagCopyStepsN.run_initial
        counter executableRawRev.reverse)
  have paidDiscovery := agreement.pay counter
  have paidReverse := List.rel_reverse paidDiscovery
  have paid :
      List.Forall₂ RuntimeTermAgrees referenceCopiedRev
        copied.values.reverse := by
    simpa [copied] using paidReverse
  exact ⟨final, run, .mk .nil paid⟩

/-- One certified executable microstep pays exactly the head debt entry and
prepends exactly one alpha-related copied value. -/
theorem CopyPaymentAgrees.next
    {referenceFrontier : Nat} {reference : Term}
    {referenceRemaining referencePaidRev : List Term}
    {before after : FindallCopy.BagCopyState}
    (agreement :
      CopyPaymentAgrees referenceFrontier
        (reference :: referenceRemaining) referencePaidRev before)
    (step : FindallCopy.BagCopyStep before after) :
    CopyPaymentAgrees referenceFrontier referenceRemaining
      (reference :: referencePaidRev) after := by
  cases step with
  | next counter source remaining copiedRev =>
      cases agreement.outstanding with
      | cons head tail =>
          exact ⟨tail, .cons (head.pay counter) agreement.paid⟩

/-- Paying a debt is genuinely compatible with unequal allocation currencies:
one independent copied variable reserved at index ten relates to an
executable copy whose suffix allocation starts at zero. -/
theorem witness_copy_debt_frontiers_need_not_equal :
    ∃ referenceCopied raw,
      CollectionCopyFrontier 11 0 [referenceCopied] [raw] ∧
        (11 : Nat) ≠ 0 := by
  let source : Term := .variable (.source "x")
  let raw : Atom := .var "x"
  let referenceCopied := copyTerm 10 source
  have encoding : EncodingInjectiveOn (copyVariables source) := by
    intro left right leftMember rightMember same
    simp [source, copyVariables, termVariables] at leftMember rightMember
    simp [leftMember, rightMember]
  have deferred :
      DeferredCopyAgreesAt 11 referenceCopied raw := by
    refine ⟨
      { source := source
        firstFresh := 10
        nextFresh := 11
        sourceAgrees := ?_
        encoding := encoding
        copied := rfl
        next := ?_ },
      Nat.le_refl 11⟩
    · exact TermAgrees.sourceVariable "x"
    · change 11 =
        copyNextFresh 10 (.variable (.source "x"))
      decide
  refine ⟨referenceCopied, raw, ?_, by omega⟩
  constructor
  · exact .cons deferred .nil
  · dsimp [raw]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [Atom.vars, resolutionSeedHighWaterNames,
      resolutionSeedHighWaterName, terminalResolutionSeed?,
      terminalResolutionSeedRev]

end PLeaTTa.PrologFindallCopyBridge
