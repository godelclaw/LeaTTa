-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedCallPrefixInductionBridge
Purpose: Compose an arbitrary finite spine of exact locally owned call
  activations, beginning from the literal-root activation certificate.
Trusted boundary: none
Main exports:
  NestedCallPushes,
  NestedCallPushes.sourceSteps,
  NestedCallPushes.fineSteps,
  RepresentativeRootCallSuccessorFacts.extend_nested_prefix
-/
import PLeaTTa.Proofs.PrologRootCallReadyBridge

namespace PLeaTTa.PrologNestedCallPrefixInductionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologAlphaFreshFrontierBridge
open PeTTaSpec.PrologCore.Trace
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologStateBridge
open PrologRootCallReadyBridge

/-- One chronological call-activation label: the exact number of source-only
rejected pulls followed by the request that was opened. -/
abbrev PushEntry := Nat × CallRequest

/-- Exact source cost of a chronological call-activation spine. -/
def sourceCost : List PushEntry → Nat
  | [] => 0
  | (rejects, _) :: rest => rejects + 2 + sourceCost rest

/-- Requests in the same chronological order as their activations. -/
def requests (entries : List PushEntry) : List CallRequest :=
  entries.map Prod.snd

/-- The fine lane uses call-entry, pull, and body activation once per entry. -/
def fineCost (entries : List PushEntry) : Nat :=
  3 * entries.length

@[simp] theorem sourceCost_append (left right : List PushEntry) :
    sourceCost (left ++ right) = sourceCost left + sourceCost right := by
  induction left with
  | nil => simp [sourceCost]
  | cons entry tail ih =>
      rcases entry with ⟨rejects, request⟩
      simp [sourceCost, ih, Nat.add_assoc]

@[simp] theorem requests_append (left right : List PushEntry) :
    requests (left ++ right) = requests left ++ requests right := by
  simp [requests]

@[simp] theorem fineCost_append (left right : List PushEntry) :
    fineCost (left ++ right) = fineCost left + fineCost right := by
  simp [fineCost, Nat.mul_add]

/-- A finite chronological chain whose only advancing constructor consumes
the complete representative successor packet.  In particular, the visible
rejection count is backed by `RejectedPullsN`, both exact skipped banks, and
their length equations; it cannot be an unrelated source-step budget.

This is a Prop-valued forward composition relation.  Its intermediate
Type-valued carriers deliberately cannot be extracted as data from an
arbitrary proof.  Later heterogeneous step-kind composition must use a
Type-valued zipper rather than trying to recover those hidden carriers. -/
inductive NestedCallPushes (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable) :
    List PushEntry → RepresentativeActivePayloadState →
      RepresentativeActivePayloadState → Prop where
  | nil (state : RepresentativeActivePayloadState) :
      NestedCallPushes prog gt [] state state
  | snoc {entries : List PushEntry}
      {before middle : RepresentativeActivePayloadState}
      {head : NestedCallHead middle.carrier}
      {rejects : Nat} {skippedBranches : List ClauseBranch}
      {skippedClauses : List PLeaTTa.Clause}
      {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause} {installed : Subst}
      {after : RepresentativeActivePayloadState}
      (earlier : NestedCallPushes prog gt entries before middle)
      (facts :
        RepresentativeNestedCallSuccessorFacts prog gt middle head rejects
          skippedBranches skippedClauses finish branch clause branchTail
          clauseTail altTail copied installed after) :
      NestedCallPushes prog gt
        (entries ++
          [(rejects,
            requestFor head.predicate head.referencePayload
              middle.carrier.index.current)])
        before after

namespace RepresentativeNestedCallSuccessorFacts

/-- One certified nested activation advances every source-side allocator
high-water.  The database is intentionally absent: logical-update reachability
is a separate relation, while these four fields are pure chronology. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    {head : NestedCallHead before.carrier}
    {count : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause} {installed : Subst}
    {after : RepresentativeActivePayloadState}
    (facts :
      RepresentativeNestedCallSuccessorFacts prog gt before head count
        skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied installed after) :
    SessionHighWatersExtend before.carrier.index.session
      after.carrier.index.session := by
  rw [facts.sessionExact]
  refine
    ⟨Nat.le_refl _,
      openLocalCall_nextFresh_mono before.carrier.index.session
        (requestFor head.predicate head.referencePayload
          before.carrier.index.current), ?_, ?_, ?_⟩
  · simp [openedFor]
  · simp [openedFor]
  · simp [openedFor]

/-- The selected clause occurrence starts no lower than the incoming global
source fresh high-water.  This includes the query-ceiling repair, every exact
rejected pull, and the selected member's reserved interval. -/
theorem sourceFresh_le_selected
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    {head : NestedCallHead before.carrier}
    {count : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause} {installed : Subst}
    {after : RepresentativeActivePayloadState}
    (facts :
      RepresentativeNestedCallSuccessorFacts prog gt before head count
        skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied installed after) :
    before.carrier.index.session.resolver.nextFresh ≤ branch.firstFresh := by
  have branchMember : branch ∈ finish.remaining := by
    rw [facts.frontier.finishRemaining]
    simp
  exact Nat.le_trans
    (openLocalCall_reservationStart_ge before.carrier.index.session
      (requestFor head.predicate head.referencePayload
        before.carrier.index.current))
    (Nat.le_trans facts.frontier.finishReservationStart
      (facts.frontier.finishWellFormed.1.start_le_member_first branchMember))

/-- One certified nested activation advances the executable allocation
counter.  The proof is inherited from the exact three-step call-fine run,
not reconstructed from the selected clause count. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    {head : NestedCallHead before.carrier}
    {count : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause} {installed : Subst}
    {after : RepresentativeActivePayloadState}
    (facts :
      RepresentativeNestedCallSuccessorFacts prog gt before head count
        skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied installed after) :
    before.carrier.index.openConf.persistent.counter ≤
      after.carrier.index.openConf.persistent.counter := by
  simpa [ActivePayloadState.fineState, DemandDrivenCallStep.FineConf.counter]
    using facts.certificate.fineSteps.counter_mono

end RepresentativeNestedCallSuccessorFacts

namespace NestedCallPushes

/-- Arbitrarily many call activations retain the exact source step cost and
the exact order of opened requests. -/
theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    StepsN (sourceCost entries) before.carrier.sourceState
      ((requests entries).map Observation.opened)
      after.carrier.sourceState := by
  induction chain with
  | nil state =>
      exact StepsN.zero state.carrier.sourceState
  | snoc earlier facts ih =>
      have combined := StepsN.trans ih facts.certificate.sourceSteps
      simpa [sourceCost, requests, Nat.add_assoc] using combined

/-- The same chain takes exactly three fine steps per activation. -/
theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    DemandDrivenCallStep.StepsN prog gt (fineCost entries)
      before.carrier.fineState after.carrier.fineState := by
  induction chain with
  | nil state =>
      exact DemandDrivenCallStep.StepsN.zero state.carrier.fineState
  | snoc earlier facts ih =>
      have combined :=
        DemandDrivenCallStep.StepsN.trans ih facts.certificate.fineSteps
      simpa [fineCost, Nat.mul_add, Nat.add_assoc] using combined

/-- Every source allocator high-water advances monotonically through an
arbitrary activation chain. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    SessionHighWatersExtend before.carrier.index.session
      after.carrier.index.session := by
  induction chain with
  | nil state =>
      exact SessionHighWatersExtend.refl state.carrier.index.session
  | snoc earlier facts ih =>
      exact SessionHighWatersExtend.trans ih
        (RepresentativeNestedCallSuccessorFacts.sessionHighWaters facts)

/-- The executable fresh-name counter cannot roll back anywhere in an
arbitrary activation chain. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    before.carrier.index.openConf.persistent.counter ≤
      after.carrier.index.openConf.persistent.counter := by
  simpa [ActivePayloadState.fineState, DemandDrivenCallStep.FineConf.counter]
    using chain.fineSteps.counter_mono

/-- Arbitrarily many activations form one exact chronological alpha suffix,
allocated above the literal predecessor's source and executable high-waters.
The proof lowers each successor's local allocation floors back to the chain
origin before composing suffixes, so later calls cannot hide a stale floor. -/
theorem alphaExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    AlphaExtendsAbove before.carrier.index.alpha after.carrier.index.alpha
      before.carrier.index.session.resolver.nextFresh
      before.carrier.index.openConf.persistent.counter := by
  induction chain with
  | nil state =>
      exact AlphaExtendsAbove.refl state.carrier.index.alpha
        state.carrier.index.session.resolver.nextFresh
        state.carrier.index.openConf.persistent.counter
  | snoc earlier facts ih =>
      have sourceOlder :=
        Nat.le_trans earlier.sessionHighWaters.fresh
          (RepresentativeNestedCallSuccessorFacts.sourceFresh_le_selected
            facts)
      have executableOlder := earlier.executableCounter_mono
      exact ih.trans
        (facts.alphaExtension.weaken sourceOlder executableOlder)

/-- Alpha ownership grows monotonically through every activation as a
corollary of the exact floor-preserving suffix theorem. -/
theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    ∀ pair, pair ∈ before.carrier.index.alpha →
      pair ∈ after.carrier.index.alpha := by
  exact chain.alphaExtension.included

/-- Every activation prepends, rather than replaces, the cumulative residual
representative. -/
theorem representativeExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative := by
  induction chain with
  | nil state =>
      exact ⟨[], rfl⟩
  | snoc earlier facts ih =>
      obtain ⟨olderExtension, olderEq⟩ := ih
      obtain ⟨newExtension, newEq⟩ := facts.representativeExtension
      refine ⟨newExtension ++ olderExtension, ?_⟩
      rw [newEq, olderEq, List.append_assoc]

/-- The exact erased payload spine records one new cell per activation.  Heads
are returned chronologically; the runtime zipper stores the newest head first,
so the equation reverses that chronological list exactly once. -/
theorem payloadCells
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    ∃ heads : List PayloadCellIdentity,
      heads.length = entries.length ∧
        after.carrier.cellIdentities =
          heads.reverse ++ before.carrier.cellIdentities := by
  induction chain with
  | nil state =>
      exact ⟨[], rfl, rfl⟩
  | snoc earlier facts ih =>
      obtain ⟨heads, headsLength, middleCells⟩ := ih
      obtain ⟨cell, afterCells⟩ := facts.certificate.payloadCells
      refine ⟨heads ++ [cell], ?_, ?_⟩
      · simp [headsLength]
      · rw [afterCells, middleCells]
        simp

/-- Cell count is an arithmetic consequence of the exact spine equation, not
a separately threaded counter. -/
theorem cellCount
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    after.carrier.cellCount = before.carrier.cellCount + entries.length := by
  obtain ⟨heads, headsLength, cells⟩ := chain.payloadCells
  calc
    after.carrier.cellCount = after.carrier.cellIdentities.length :=
      after.carrier.cellIdentities_length.symm
    _ = (heads.reverse ++ before.carrier.cellIdentities).length :=
      congrArg List.length cells
    _ = before.carrier.cellCount + entries.length := by
      rw [List.length_append, List.length_reverse,
        before.carrier.cellIdentities_length, headsLength]
      omega

/-- Dropping exactly the number of chronological pushes recovers the literal
predecessor's payload-cell spine. -/
theorem dropCells
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {entries : List PushEntry}
    {before after : RepresentativeActivePayloadState}
    (chain : NestedCallPushes prog gt entries before after) :
    after.carrier.cellIdentities.drop entries.length =
      before.carrier.cellIdentities := by
  obtain ⟨heads, headsLength, cells⟩ := chain.payloadCells
  rw [cells, ← headsLength]
  simp

/-- Two complete successor packets cannot collapse to one activation.  Their
chain exposes two source requests in chronological order, exactly six fine
steps, two retained payload cells, and one exact alpha suffix above the
literal predecessor's allocator floors. -/
theorem two_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {firstRejects secondRejects : Nat}
    {firstRequest secondRequest : CallRequest}
    {before after : RepresentativeActivePayloadState}
    (chain :
      NestedCallPushes prog gt
        [(firstRejects, firstRequest), (secondRejects, secondRequest)]
        before after) :
    StepsN (firstRejects + secondRejects + 4) before.carrier.sourceState
        [.opened firstRequest, .opened secondRequest]
        after.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 6 before.carrier.fineState
        after.carrier.fineState ∧
      AlphaExtendsAbove before.carrier.index.alpha after.carrier.index.alpha
        before.carrier.index.session.resolver.nextFresh
        before.carrier.index.openConf.persistent.counter ∧
      after.carrier.cellCount = before.carrier.cellCount + 2 ∧
      after.carrier.cellIdentities.drop 2 =
        before.carrier.cellIdentities := by
  refine ⟨?_, ?_, chain.alphaExtension, ?_, ?_⟩
  · simpa [sourceCost, requests, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using chain.sourceSteps
  · simpa [fineCost] using chain.fineSteps
  · simpa using chain.cellCount
  · simpa using chain.dropCells

end NestedCallPushes

/-- One literal root activation followed by an arbitrary finite spine of
locally owned calls.  Every observable, allocator, semantic representative,
and payload-cell fact is indexed by the same final carrier.

`rootAfter` remains explicit because the literal task has no predecessor
`ActivePayloadState`: the nested payload-cell zipper begins only after the
root activation has constructed that carrier. -/
structure RootedNestedPrefixCertificate
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (rootRejects : Nat) (rootRequest : CallRequest)
    (entries : List PushEntry)
    (sourceStart : GoalSemantics.State)
    (fineStart : DemandDrivenCallStep.FineConf)
    (entryAlpha : List (LogicVar × String))
    (entrySession : GoalSemantics.Session)
    (entryExecutableCounter : Nat)
    (entryRepresentative : TreeSubstitution)
    (rootAfter final : RepresentativeActivePayloadState) : Prop where
  sourceSteps :
    StepsN (rootRejects + 2 + sourceCost entries) sourceStart
      (Observation.opened rootRequest ::
        (requests entries).map Observation.opened)
      final.carrier.sourceState
  fineSteps :
    DemandDrivenCallStep.StepsN prog gt (3 + fineCost entries) fineStart
      final.carrier.fineState
  alphaExtension :
    AlphaExtendsAbove entryAlpha final.carrier.index.alpha
      entrySession.resolver.nextFresh entryExecutableCounter
  sessionHighWaters :
    SessionHighWatersExtend entrySession final.carrier.index.session
  executableCounter_mono :
    entryExecutableCounter ≤
      final.carrier.index.openConf.persistent.counter
  representativeExtension :
    ∃ extension : TreeSubstitution,
      final.representative = extension ++ entryRepresentative
  nestedPayloadCells :
    ∃ heads : List PayloadCellIdentity,
      heads.length = entries.length ∧
        final.carrier.cellIdentities =
          heads.reverse ++ rootAfter.carrier.cellIdentities

/-- Compose the independently certified literal-root activation with any
exact representative-preserving nested-call spine.

The alpha conclusion is deliberately stated at the literal entry session and
counter, not at the first selected clause.  Both the root suffix and every
nested suffix are weakened back to those original floors before exact suffix
composition, preventing a later activation from hiding a stale allocator. -/
theorem extend_literal_root_nested_prefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution}
    {referenceBase : OpenSubstitution.Substitution}
    {session : GoalSemantics.Session}
    {before : DemandDrivenStep.OpenConf}
    {scope : GoalSemantics.CutScopeId}
    {predicate : String} {referencePayload : List PeTTaSpec.PrologCore.Term}
    {referenceBindings : OpenSubstitution.Substitution}
    {args : List Atom} {res : Atom} {binding : Subst}
    {branches : List PLeaTTa.Alt} {finalCounter callerBarrier : Nat}
    {rejects : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {independentResult : OpenSubstitution.Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {rootAfter final : RepresentativeActivePayloadState}
    {entries : List PushEntry}
    (root :
      RepresentativeRootCallSuccessorFacts prog gt alpha support canonical
        referenceBase session before scope predicate referencePayload
        referenceBindings args res binding branches finalCounter callerBarrier
        rejects skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed rootAfter)
    (tail : NestedCallPushes prog gt entries rootAfter final) :
    RootedNestedPrefixCertificate prog gt rejects
      (requestFor predicate referencePayload referenceBindings) entries
      (.running session
        (.task scope [.call predicate referencePayload] referenceBindings))
      (.ready before) alpha session before.persistent.counter representative
      rootAfter final := by
  have branchMember : branch ∈ finish.remaining := by
    rw [root.frontier.finishRemaining]
    simp
  have rootSource_le_selected :
      session.resolver.nextFresh ≤ branch.firstFresh :=
    Nat.le_trans
      (openLocalCall_reservationStart_ge session
        (requestFor predicate referencePayload referenceBindings))
      (Nat.le_trans root.frontier.finishReservationStart
        (root.frontier.finishWellFormed.1.start_le_member_first branchMember))
  have rootSession :
      SessionHighWatersExtend session rootAfter.carrier.index.session := by
    rw [root.sessionExact]
    refine
      ⟨Nat.le_refl _,
        openLocalCall_nextFresh_mono session
          (requestFor predicate referencePayload referenceBindings),
        ?_, ?_, ?_⟩
    · simp [openedFor]
    · simp [openedFor]
    · simp [openedFor]
  have rootCounter :
      before.persistent.counter ≤
        rootAfter.carrier.index.openConf.persistent.counter := by
    simpa [ActivePayloadState.fineState,
      DemandDrivenCallStep.FineConf.counter]
      using root.fineSteps.counter_mono
  have rootAlpha :
      AlphaExtendsAbove alpha rootAfter.carrier.index.alpha
        session.resolver.nextFresh before.persistent.counter := by
    simpa [DemandDrivenStep.OpenConf.toConf,
      DemandDrivenStep.Control.toConf] using
      root.alphaExtension.weaken rootSource_le_selected (Nat.le_refl _)
  have tailAlpha :
      AlphaExtendsAbove rootAfter.carrier.index.alpha
        final.carrier.index.alpha session.resolver.nextFresh
        before.persistent.counter :=
    tail.alphaExtension.weaken rootSession.fresh rootCounter
  obtain ⟨tailRepresentative, tailRepresentativeEq⟩ :=
    tail.representativeExtension
  refine
    { sourceSteps := ?_
      fineSteps := ?_
      alphaExtension := rootAlpha.trans tailAlpha
      sessionHighWaters :=
        SessionHighWatersExtend.trans rootSession tail.sessionHighWaters
      executableCounter_mono :=
        Nat.le_trans rootCounter tail.executableCounter_mono
      representativeExtension := ?_
      nestedPayloadCells := tail.payloadCells }
  · have combined := StepsN.trans root.sourceSteps tail.sourceSteps
    simpa [Nat.add_assoc] using combined
  · have combined :=
      DemandDrivenCallStep.StepsN.trans root.fineSteps tail.fineSteps
    simpa [Nat.add_assoc] using combined
  · refine ⟨tailRepresentative ++ flattenedRepresentative, ?_⟩
    rw [tailRepresentativeEq, root.carrierRepresentative,
      List.append_assoc]

end PLeaTTa.PrologNestedCallPrefixInductionBridge
