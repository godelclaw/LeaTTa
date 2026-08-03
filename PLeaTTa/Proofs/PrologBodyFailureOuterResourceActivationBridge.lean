-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologBodyFailureOuterResourceActivationBridge
Purpose: Consume the source-only rejected prefix inside the first live outer
  predicate resource exposed after body-failure catch-up.
Trusted boundary: none
Main exports:
  RejectedPrefixPulledHeadOffsetAgrees,
  SpinedFirstLiveReadyOffsetRelates,
  SpinedFirstLiveOuterResourceFrontierRelates.consumeRejectedPrefix
-/
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge

namespace PLeaTTa.PrologBodyFailureOuterResourceActivationBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeCallPrefilterBridge
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedCursorOwnershipBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCallFrontierBridge
open PrologSupportedCursorAlternativeBridge

/-!
After outer-resource catch-up, the executable has already pulled the first
live alternative into `cur`.  The independent source is still at the
resource's original cursor and must execute every conservative rejection
which preceded that retained occurrence.

This module accounts for exactly that source-only work.  It does not create a
synthetic call-entry state: the original resource ownership is sufficient to
decompose its real `ResolutionScan`, and the installed executable head is
checked against the retained clause produced by that decomposition.
-/

/-- A ranked source-only rejected prefix reaches the precise
executable-ahead retained-head offset.

The source cursor is still unadvanced at `finish`; `offset` records that the
executable has already consumed the retained head alternative and owns the
advanced tail cursor. -/
structure RejectedPrefixPulledHeadOffsetAgrees
    (alpha : List (LogicVar × String))
    (before finish : PreparedCursor)
    (count : Nat)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) : Prop where
  pulls : RejectedPullsN count before finish
  offset :
    PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
      resource remainingAlts

/-- Exact source state after the first live resource's internal rejected
prefix has been consumed, but before the retained head is selected. -/
def firstLiveReadySourceFrontier
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (finish : PreparedCursor) : Search :=
  ActiveProductContext.plug partition.survivingContext
    (frameRetainedFrontier partition.firstFrame finish)

/-- Consume the maximal conservative rejection prefix inside the first live
resource using only its ranked partition and the current persistent session.

This is the source-only kernel of the later body-failure composition theorem.
It starts at the literal first-live frontier, performs exactly one silent
transition per rejected occurrence, and stops immediately before selecting
the retained head.  No historical call packet, executable predecessor, or
fine-machine state occurs in the statement. -/
theorem OuterResourceCatchupPartition.consumeRejectedPrefix
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (session : Session) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (finish : PreparedCursor)
        (branch : ClauseBranch) (clause : PLeaTTa.Clause)
        (branchTail : List ClauseBranch)
        (clauseTail : List PLeaTTa.Clause)
        (copied : PLeaTTa.Clause),
      partition.firstCursor.remaining =
        skippedBranches ++ (branch :: branchTail) ∧
      candidates = skippedClauses ++ (clause :: clauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN count
        (.running session (firstLiveSourceFrontier partition))
        []
        (.running session
          (firstLiveReadySourceFrontier partition finish)) ∧
      RejectedPrefixPulledHeadOffsetAgrees alpha partition.firstCursor finish
        count branch clause branchTail copied partition.first partition.tail ∧
      resolutionAlt partition.first.argsv partition.first.args
          partition.first.res partition.first.rest partition.first.binding
          partition.first.qterm partition.first.barrier
          partition.first.counter clause =
        .br partition.goals partition.binding := by
  rcases partition.firstOwnership with
    ⟨callStart, firstPosition, firstOwnership⟩
  rcases firstOwnership.scan with
    ⟨candidates, cursorWellFormed, query, substitutedArgs,
      supportedCandidates, candidateArities, candidateScan⟩
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining,
      finishContext, ready⟩ :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.ResolutionScan.decomposeRepresentativeRejectedPrefix
      candidateScan supportedCandidates query cursorWellFormed
      (.refl partition.firstCursor) (.refl partition.firstCursor) rfl
      (fun _branch member => member) candidateArities
  have firstNonempty : partition.first.alts ≠ [] := by
    rw [partition.firstHead]
    simp
  have readyNonempty : readyBranches ≠ [] :=
    ready.branches_nonempty_of_alts_nonempty firstNonempty
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      readyBranchesEq, readyClausesEq, priorAlts, supported, arity,
      retained, tailSupported, tailScan⟩ :=
    ready.retained_shape readyNonempty
  let copied :=
    PLeaTTa.freshenResolutionClause partition.first.argsv
      partition.first.args partition.first.res partition.first.rest
      partition.first.binding partition.first.qterm partition.first.counter
      partition.first.barrier clause
  have cursorRemaining :
      finish.remaining = branch :: branchTail :=
    finishRemaining.trans readyBranchesEq
  have finishWellFormed : finish.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      pulls cursorWellFormed
  have queryAtFinish :
      RepresentativeNormalizedCallAgrees alpha finish partition.first.argsv
        (PLeaTTa.subst partition.first.binding partition.first.res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      finishContext (.refl partition.firstCursor) query
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
        finish.arguments finish.bindings branch clause :=
    finishContext.supportedPreparedCandidate supported
  have advancedContext :
      CursorCallContext (finish.advance branch branchTail)
        partition.firstCursor.callGeneration
        partition.firstCursor.predicate
        partition.firstCursor.arguments
        partition.firstCursor.bindings :=
    finishContext.advance branch branchTail
  have advancedWellFormed :
      (finish.advance branch branchTail).WellFormed :=
    finish.advance_wellFormed finishWellFormed cursorRemaining
  have queryAtAdvanced :
      RepresentativeNormalizedCallAgrees alpha
        (finish.advance branch branchTail) partition.first.argsv
        (PLeaTTa.subst partition.first.binding partition.first.res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      advancedContext finishContext queryAtFinish
  have tailArities :
      ∀ candidate, candidate ∈ clauseTail →
        candidate.params.length = partition.first.argsv.length := by
    intro candidate member
    apply candidateArities candidate
    rw [clausesEq, readyClausesEq]
    simp [member]
  have tailSupportedAtAdvanced :
      List.Forall₂
        (SupportedPreparedCandidateAgrees
          (finish.advance branch branchTail).callGeneration
          (finish.advance branch branchTail).predicate
          (finish.advance branch branchTail).arguments
          (finish.advance branch branchTail).bindings)
        (finish.advance branch branchTail).remaining clauseTail := by
    have transported :
        List.Forall₂
          (SupportedPreparedCandidateAgrees
            (finish.advance branch branchTail).callGeneration
            (finish.advance branch branchTail).predicate
            (finish.advance branch branchTail).arguments
            (finish.advance branch branchTail).bindings)
          branchTail clauseTail :=
      tailSupported.imp
        (fun _branch _clause item =>
          advancedContext.supportedPreparedCandidate item)
    simpa [PreparedCursor.advance] using transported
  have finishPositioned :
      CallScopedCursorPosition callStart finish
        (firstPosition + count) :=
    CallScopedCursorPosition.afterRejected pulls firstOwnership.positioned
  have tailOwnership :
      (afterPulledHead partition.first altTail).Owns alpha
        callStart (finish.advance branch branchTail)
          ((firstPosition + count) + 1) := by
    have advancedIdentity :
        PreparedCallIdentity.ofCursor (finish.advance branch branchTail) =
          PreparedCallIdentity.ofCursor partition.firstCursor := by
      apply PreparedCallIdentity.ofCursor_eq_of_callContext advancedContext
      simpa [PreparedCursor.advance] using
        (PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
          pulls)
    refine ⟨?_, ?_, finishPositioned.advance cursorRemaining⟩
    · calc
        (afterPulledHead partition.first altTail).callIdentity =
            partition.first.callIdentity := rfl
        _ = PreparedCallIdentity.ofCursor partition.firstCursor :=
          firstOwnership.identity
        _ = PreparedCallIdentity.ofCursor
            (finish.advance branch branchTail) := advancedIdentity.symm
    · exact
        ⟨clauseTail, advancedWellFormed, queryAtAdvanced,
          substitutedArgs, tailSupportedAtAdvanced, tailArities, tailScan⟩
  have offsetAtAltTail :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        partition.first altTail :=
    ⟨cursorRemaining, finishWellFormed, queryAtFinish, substitutedArgs,
      supportedAtFinish, arity, retained, priorAlts, rfl,
      ⟨callStart, firstPosition + count, finishPositioned, tailOwnership⟩⟩
  have banksEqual :
      resolutionAlt partition.first.argsv partition.first.args
            partition.first.res partition.first.rest partition.first.binding
            partition.first.qterm partition.first.barrier
            partition.first.counter clause ::
          altTail =
        .br partition.goals partition.binding :: partition.tail :=
    priorAlts.symm.trans partition.firstHead
  have altTailExact : altTail = partition.tail :=
    (List.cons.inj banksEqual).2
  have headExact :
      resolutionAlt partition.first.argsv partition.first.args
          partition.first.res partition.first.rest partition.first.binding
          partition.first.qterm partition.first.barrier
          partition.first.counter clause =
        .br partition.goals partition.binding :=
    (List.cons.inj banksEqual).1
  have offset :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        partition.first partition.tail := by
    simpa [altTailExact] using offsetAtAltTail
  have sourceSteps :
      StepsN count
        (.running session (firstLiveSourceFrontier partition))
        []
        (.running session
          (firstLiveReadySourceFrontier partition finish)) := by
    have lifted :=
      PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
        pulls partition.survivingContext partition.firstFrame session
    simpa [firstLiveSourceFrontier, firstLiveReadySourceFrontier] using lifted
  refine
    ⟨count, skippedBranches, skippedClauses, candidates, finish, branch,
      clause, branchTail, clauseTail, copied, ?_, ?_, branchCount,
      clauseCount, sourceSteps, ⟨pulls, offset⟩, headExact⟩
  · calc
      partition.firstCursor.remaining =
          skippedBranches ++ readyBranches := branchesEq
      _ = skippedBranches ++ (branch :: branchTail) := by
        rw [readyBranchesEq]
  · rw [clausesEq, readyClausesEq]

/-- Exact executable state after its eager pull has installed the retained
clause which the source is about to select.

Unlike `firstLiveExecutableConf`, this spelling is indexed by the certified
freshened clause rather than by an opaque `goals` field from the structural
partition.  The composition theorem proves the two configurations equal. -/
def firstLiveSelectedExecutableConf
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (pending : DemandDrivenCallStep.PendingCall)
    (predecessor : OpenConf)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (baseAlts : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause) : PLeaTTa.Conf :=
  { predecessor.toConf with
    cur :=
      some
        (PLeaTTa.Goal.eq
              (.expr (partition.first.args ++ [partition.first.res]))
              (.expr (copied.params ++ [copied.result])) ::
            copied.body ++ partition.first.rest,
          partition.first.binding)
    alts :=
      partition.tail ++ PLeaTTa.Alt.barrier ::
        flattenOwnedAlts partition.survivingResources baseAlts
    barriers :=
      popBarrierCacheN partition.crossedResources.length
        pending.outer.barriers }

/-- Fully composed ready-offset phase for the first live outer resource.

`initial` retains the exact typed source/control/resource suffix exposed by
catch-up.  `prefix` names the current semantic cursor and the consumed
executable alternative.  No historical `PendingCall` for the outer predicate
is invented: `executableExact` is a statement solely about the actual current
configuration. -/
structure SpinedFirstLiveReadyOffsetRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (outerScope : CutScopeId) (suffixBarrier : Nat)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (count : Nat) (finish : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (source : Search) (successor : OpenConf) : Prop where
  initial :
    SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
      pending qterm outerScope suffixBarrier segments resources context
      baseAlts predecessor partition (firstLiveSourceFrontier partition)
      successor
  rejectedPrefix :
    RejectedPrefixPulledHeadOffsetAgrees alpha partition.firstCursor finish
      count branch clause branchTail copied partition.first partition.tail
  sourceShape : source = firstLiveReadySourceFrontier partition finish
  executableExact :
    successor.toConf =
      firstLiveSelectedExecutableConf pending predecessor partition baseAlts
        copied

/-- Consume the maximal conservative rejection prefix inside the first live
outer resource.

The source performs exactly one silent transition per rejected occurrence.
The executable performs no additional transition: its earlier eager pull has
already installed the retained head.  The resulting offset owns the exact
advanced source cursor and the exact remaining executable alternative bank. -/
theorem
    SpinedFirstLiveOuterResourceFrontierRelates.consumeRejectedPrefix
    {freshFrontier : FreshFrontierRelation}
    {alpha : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {qterm : Atom} {outerScope : CutScopeId} {suffixBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {partition :
      OuterResourceCatchupPartition alpha segments resources context}
    {source : Search} {successor : OpenConf}
    (agreement :
      SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
        pending qterm outerScope suffixBarrier segments resources context
        baseAlts predecessor partition source successor) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (finish : PreparedCursor)
        (branch : ClauseBranch) (clause : PLeaTTa.Clause)
        (branchTail : List ClauseBranch)
        (clauseTail : List PLeaTTa.Clause)
        (copied : PLeaTTa.Clause),
      partition.firstCursor.remaining =
        skippedBranches ++ (branch :: branchTail) ∧
      candidates = skippedClauses ++ (clause :: clauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN count
        (.running opened.session source)
        []
        (.running opened.session
          (firstLiveReadySourceFrontier partition finish)) ∧
      SpinedFirstLiveReadyOffsetRelates freshFrontier alpha opened pending
        qterm outerScope suffixBarrier segments resources context baseAlts
        predecessor partition count finish branch clause branchTail copied
        (firstLiveReadySourceFrontier partition finish) successor := by
  obtain
    ⟨count, skippedBranches, skippedClauses, candidates, finish, branch,
      clause, branchTail, clauseTail, copied, cursorSplit, candidatesSplit,
      branchCount, clauseCount, sourceStepsAtFrontier, rejectedPrefix,
      headExact⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceActivationBridge.OuterResourceCatchupPartition.consumeRejectedPrefix
      partition opened.session
  have sourceSteps :
      StepsN count
        (.running opened.session source)
        []
        (.running opened.session
          (firstLiveReadySourceFrontier partition finish)) := by
    rw [agreement.sourceShape]
    exact sourceStepsAtFrontier
  have selectedHead :
      PLeaTTa.Alt.br
          (PLeaTTa.Goal.eq
                (.expr
                  (partition.first.args ++ [partition.first.res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ partition.first.rest)
          partition.first.binding =
        PLeaTTa.Alt.br partition.goals partition.binding := by
    rw [rejectedPrefix.offset.copiedExact]
    simpa [resolutionAlt] using headExact
  have selectedFields :
      (PLeaTTa.Goal.eq
            (.expr (partition.first.args ++ [partition.first.res]))
            (.expr (copied.params ++ [copied.result])) ::
          copied.body ++ partition.first.rest =
        partition.goals) ∧
      partition.first.binding = partition.binding := by
    injection selectedHead with goalsExact bindingExact
    exact ⟨goalsExact, bindingExact⟩
  have goalsExact := selectedFields.1
  have bindingExact := selectedFields.2
  have executableExact :
      successor.toConf =
        firstLiveSelectedExecutableConf pending predecessor partition baseAlts
          copied := by
    rw [agreement.executableExact]
    simp only [firstLiveExecutableConf, firstLiveSelectedExecutableConf]
    rw [← goalsExact, ← bindingExact]
  have initial :
      SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
        pending qterm outerScope suffixBarrier segments resources context
        baseAlts predecessor partition (firstLiveSourceFrontier partition)
        successor :=
    ⟨agreement.persistent, agreement.queryTerm, agreement.frames,
      agreement.suffixAlignment, rfl, agreement.executableExact⟩
  refine
    ⟨count, skippedBranches, skippedClauses, candidates, finish, branch,
      clause, branchTail, clauseTail, copied, cursorSplit, candidatesSplit,
      branchCount,
      clauseCount, sourceSteps, ?_⟩
  exact
    ⟨initial,
      rejectedPrefix,
      rfl,
      executableExact⟩

/-! ## Anti-vacuity: a rejected occurrence before a retained head -/

private def prefixRejectedReference : VersionedClause :=
  { id := 0
    clause :=
      { predicate := "ranked-ready"
        arguments := [.integer 2]
        body := [] }
    created := 0 }

private def prefixRetainedReference : VersionedClause :=
  { id := 1
    clause :=
      { predicate := "ranked-ready"
        arguments := [.integer 1]
        body := [] }
    created := 0 }

private def prefixRejectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 2)
    body := [] }

private def prefixRetainedExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 1)
    body := [] }

private def prefixRejectedBranch : ClauseBranch :=
  preparedBranchOf 0 [.integer 1] [] 0 prefixRejectedReference

private def prefixRetainedBranch : ClauseBranch :=
  preparedBranchOf 0 [.integer 1] [] prefixRejectedBranch.nextFresh
    prefixRetainedReference

private def prefixCursor : PreparedCursor :=
  { callGeneration := 0
    predicate := "ranked-ready"
    arguments := [.integer 1]
    bindings := []
    reservationStart := 0
    remaining := [prefixRejectedBranch, prefixRetainedBranch]
    reservedUntil := prefixRetainedBranch.nextFresh }

private def prefixFinish : PreparedCursor :=
  prefixCursor.advance prefixRejectedBranch [prefixRetainedBranch]

private def prefixResource : RetainedAlternativeSegment :=
  { callIdentity := PreparedCallIdentity.ofCursor prefixCursor
    argsv := []
    args := []
    res := .gnd (.int 1)
    rest := []
    binding := []
    qterm := .sym "query"
    barrier := 0
    counter := 0
    alts :=
      [resolutionAlt [] [] (.gnd (.int 1)) [] [] (.sym "query") 0 0
        prefixRetainedExecutable]
    finalCounter := 1 }

private def prefixCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] (.gnd (.int 1)) [] []
    (.sym "query") 0 0 prefixRetainedExecutable

private theorem prefixRejectedCandidateAgreement :
    CandidateClauseAgrees "ranked-ready" prefixRejectedReference
      prefixRejectedExecutable := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact ⟨[], .integer 2, rfl, .nil, .integer 2⟩
  · intro name
    simp [prefixRejectedReference, prefixRejectedExecutable,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables,
      goalsVariables]

private theorem prefixRetainedCandidateAgreement :
    CandidateClauseAgrees "ranked-ready" prefixRetainedReference
      prefixRetainedExecutable := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact ⟨[], .integer 1, rfl, .nil, .integer 1⟩
  · intro name
    simp [prefixRetainedReference, prefixRetainedExecutable,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables,
      goalsVariables]

private theorem prefixRejectedSupported :
    SupportedPreparedCandidateAgrees 0 "ranked-ready" [.integer 1] []
      prefixRejectedBranch prefixRejectedExecutable := by
  refine .intro prefixRejectedReference 0 prefixRejectedExecutable
    prefixRejectedCandidateAgreement ?_ ?_
  · intro left right leftMember rightMember
    simp [prefixRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        prefixRejectedCandidateAgreement.body
    have proofEq :
        prefixRejectedCandidateAgreement.body =
          (CompilerAdequacy.GoalsAgree.nil :
            CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem prefixRetainedSupported :
    SupportedPreparedCandidateAgrees 0 "ranked-ready" [.integer 1] []
      prefixRetainedBranch prefixRetainedExecutable := by
  refine .intro prefixRetainedReference prefixRejectedBranch.nextFresh
    prefixRetainedExecutable
    prefixRetainedCandidateAgreement ?_ ?_
  · intro left right leftMember rightMember
    simp [prefixRetainedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        prefixRetainedCandidateAgreement.body
    have proofEq :
        prefixRetainedCandidateAgreement.body =
          (CompilerAdequacy.GoalsAgree.nil :
            CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem prefixCursorWellFormed : prefixCursor.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change
      FreshReservation 0 [prefixRejectedBranch, prefixRetainedBranch]
        prefixRetainedBranch.nextFresh
    simpa [prefixRejectedBranch, prefixRetainedBranch,
      preparedBranchOf, prefixRejectedReference, prefixRetainedReference,
      reserveVisible] using
      (reserveVisible_freshReservation 0 [.integer 1] [] 0
        [prefixRejectedReference, prefixRetainedReference])
  · intro index member
    simp [prefixCursor, termsVariables, termVariables,
      substitutionVariables] at member
  · intro branch member
    simp [prefixCursor] at member
    rcases member with rfl | rfl
    · change 0 = 0
      rfl
    · change 0 = 0
      rfl
  · intro branch member source index targetMember
    simp [prefixCursor] at member
    rcases member with rfl | rfl
    · simpa [prefixRejectedBranch, preparedBranchOf] using
        prefixRejectedReference.clause.freshCopy_target_range 0 targetMember
    · simpa [prefixRetainedBranch, preparedBranchOf] using
        prefixRetainedReference.clause.freshCopy_target_range
          prefixRejectedBranch.nextFresh targetMember

private theorem prefixQuery :
    RepresentativeNormalizedCallAgrees [] prefixCursor []
      (.gnd (.int 1)) := by
  apply NormalizedCallAgrees.representative
  constructor
  simpa [prefixCursor] using
    (AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 1)
      AlphaTermsAgree.nil)

private theorem prefixRejectedClash :
    ¬ ∃ result, HeadResolution prefixRejectedBranch result := by
  have normalizedQuery :
      NormalizedCallAgrees [] prefixCursor [] (.gnd (.int 1)) := by
    constructor
    simpa [prefixCursor] using
      (AlphaTermsAgree.cons
        (AlphaTermAgrees.integer (alpha := []) 1)
        AlphaTermsAgree.nil)
  have head :
      NormalizedHeadAgrees prefixRejectedBranch [] (.gnd (.int 1))
        prefixRejectedExecutable :=
    supportedPreparedCandidate_normalizedHeadAgrees normalizedQuery
      prefixCursorWellFormed (by simp [prefixCursor])
      prefixRejectedSupported (by rfl)
  exact head.no_headResolution_of_rejected (by rfl)

private theorem prefixPull :
    RejectedPullsN 1 prefixCursor prefixFinish := by
  simpa [prefixFinish] using
    (RejectedPullsN.succ 0 prefixCursor prefixRejectedBranch
      [prefixRetainedBranch] prefixFinish (by rfl) prefixRejectedClash
      (.zero prefixFinish))

private theorem prefixOwnership :
    prefixResource.Owns [] prefixCursor prefixCursor 0 := by
  refine ⟨rfl, ?_, CallScopedCursorPosition.refl prefixCursor⟩
  refine
    ⟨[prefixRejectedExecutable, prefixRetainedExecutable],
      prefixCursorWellFormed, ?_, rfl,
      .cons prefixRejectedSupported (.cons prefixRetainedSupported .nil),
      ?_, ?_⟩
  · simpa [prefixResource] using prefixQuery
  · intro clause member
    simp [prefixRejectedExecutable, prefixRetainedExecutable] at member
    rcases member with rfl | rfl <;> rfl
  · have rejected :
        resolutionClauseRetained [] (.gnd (.int 1))
          prefixRejectedExecutable = false := by
      rfl
    have retained :
        resolutionClauseRetained [] (.gnd (.int 1))
          prefixRetainedExecutable = true := by
      rfl
    have rejectedAfterSubst :
        resolutionClauseRetained []
          (PLeaTTa.subst [] (.gnd (.int 1)))
          prefixRejectedExecutable = false := by
      simpa using rejected
    have retainedAfterSubst :
        resolutionClauseRetained []
          (PLeaTTa.subst [] (.gnd (.int 1)))
          prefixRetainedExecutable = true := by
      simpa using retained
    simpa [prefixResource] using
      (ResolutionScan.skipped prefixRejectedExecutable
        [prefixRetainedExecutable] 0 1
        [resolutionAlt [] [] (.gnd (.int 1)) [] [] (.sym "query") 0 0
          prefixRetainedExecutable]
        rejectedAfterSubst
        (ResolutionScan.retained prefixRetainedExecutable [] 0 1 []
          retainedAfterSubst (ResolutionScan.nil 1)))

private theorem prefixFinishOwnership :
    prefixResource.Owns [] prefixCursor prefixFinish 1 := by
  have finishWellFormed : prefixFinish.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      prefixPull prefixCursorWellFormed
  have finishContext :
      CursorCallContext prefixFinish 0 "ranked-ready" [.integer 1] [] :=
    (CursorCallContext.refl prefixCursor).advance prefixRejectedBranch
      [prefixRetainedBranch]
  have queryAtFinish :
      RepresentativeNormalizedCallAgrees [] prefixFinish []
        (.gnd (.int 1)) :=
    CursorCallContext.representativeNormalizedCallAgrees finishContext
      (.refl prefixCursor) prefixQuery
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees prefixFinish.callGeneration
        prefixFinish.predicate prefixFinish.arguments prefixFinish.bindings
        prefixRetainedBranch prefixRetainedExecutable :=
    finishContext.supportedPreparedCandidate prefixRetainedSupported
  have positioned : CallScopedCursorPosition prefixCursor prefixFinish 1 := by
    simpa using
      (CallScopedCursorPosition.afterRejected prefixPull
        (CallScopedCursorPosition.refl prefixCursor))
  refine ⟨?_, ?_, positioned⟩
  · rfl
  · refine
      ⟨[prefixRetainedExecutable], finishWellFormed,
        (by simpa [prefixResource] using queryAtFinish), rfl,
        .cons supportedAtFinish .nil, ?_, ?_⟩
    · intro clause member
      simp [prefixRetainedExecutable] at member
      subst clause
      rfl
    · have retained :
          resolutionClauseRetained [] (.gnd (.int 1))
            prefixRetainedExecutable = true := by
        rfl
      simpa [prefixResource] using
        (ResolutionScan.retained prefixRetainedExecutable [] 0 1 []
          (by simpa using retained) (ResolutionScan.nil 1))

private theorem prefixOffset :
    PulledHeadOffsetAgrees [] prefixFinish prefixRetainedBranch
      prefixRetainedExecutable [] prefixCopied prefixResource [] := by
  have finishWellFormed : prefixFinish.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      prefixPull prefixCursorWellFormed
  have finishContext :
      CursorCallContext prefixFinish 0 "ranked-ready" [.integer 1] [] :=
    (CursorCallContext.refl prefixCursor).advance prefixRejectedBranch
      [prefixRetainedBranch]
  have queryAtFinish :
      RepresentativeNormalizedCallAgrees [] prefixFinish []
        (.gnd (.int 1)) :=
    CursorCallContext.representativeNormalizedCallAgrees finishContext
      (.refl prefixCursor) prefixQuery
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees prefixFinish.callGeneration
        prefixFinish.predicate prefixFinish.arguments prefixFinish.bindings
        prefixRetainedBranch prefixRetainedExecutable :=
    finishContext.supportedPreparedCandidate prefixRetainedSupported
  have retainedAtResource :
      resolutionClauseRetained prefixResource.argsv
        (PLeaTTa.subst prefixResource.binding prefixResource.res)
        prefixRetainedExecutable = true := by
    have retained :
        resolutionClauseRetained [] (.gnd (.int 1))
          prefixRetainedExecutable = true := by
      rfl
    simpa [prefixResource] using retained
  have finishPositioned :
      CallScopedCursorPosition prefixCursor prefixFinish 1 :=
    prefixFinishOwnership.positioned
  have tailOwnership :
      (afterPulledHead prefixResource []).Owns []
        prefixCursor (prefixFinish.advance prefixRetainedBranch [])
          (1 + 1) := by
    refine ⟨rfl, ?_, finishPositioned.advance (by rfl)⟩
    refine ⟨[], ?_, ?_, rfl, .nil, ?_, ?_⟩
    · exact prefixFinish.advance_wellFormed finishWellFormed (by rfl)
    · have advancedContext :=
        finishContext.advance prefixRetainedBranch []
      simpa [afterPulledHead, prefixResource] using
        CursorCallContext.representativeNormalizedCallAgrees advancedContext
          finishContext queryAtFinish
    · intro clause member
      simp at member
    · simpa [afterPulledHead, prefixResource] using
        (ResolutionScan.nil 1 :
          ResolutionScan [] [] (.gnd (.int 1)) [] [] (.sym "query") 0
            [] 1 [] 1)
  exact
    ⟨rfl, finishWellFormed, by simpa [prefixResource] using queryAtFinish,
      rfl, supportedAtFinish, rfl, retainedAtResource, rfl, rfl,
      ⟨prefixCursor, 1, finishPositioned, tailOwnership⟩⟩

/-- The ready-offset relation genuinely contains a nonzero rejected prefix
before a retained occurrence.  Thus it cannot be satisfied only by
`RejectedPullsN.zero`, nor can the executable head be paired with the wrong
source occurrence. -/
theorem one_rejected_before_retained_offset_is_inhabited :
    ∃ before finish branch clause copied resource,
      before.remaining.length = 2 ∧
      finish.remaining = [branch] ∧
      resource.alts.length = 1 ∧
      RejectedPrefixPulledHeadOffsetAgrees [] before finish 1 branch clause
        [] copied resource [] := by
  exact
    ⟨prefixCursor, prefixFinish, prefixRetainedBranch,
      prefixRetainedExecutable, prefixCopied, prefixResource,
      rfl, rfl, rfl, ⟨prefixPull, prefixOffset⟩⟩

/-- The absolute source coordinate cannot be reconstructed from the
executable resolution counter.  In this real scan the first occurrence is
rejected silently, so the retained head is at source position one while the
counter feeding its executable alternative is still zero. -/
theorem one_rejected_source_position_one_counter_zero :
    ∃ (before finish : PreparedCursor)
        (resource : RetainedAlternativeSegment),
      RejectedPullsN 1 before finish /\
      CallScopedCursorPosition before finish 1 /\
      finish.remaining.length = 1 /\
      resource.Owns [] before finish 1 /\
      resource.counter = 0 /\
      resource.alts.length = 1 := by
  have positioned : CallScopedCursorPosition prefixCursor prefixFinish 1 := by
    simpa using
      (CallScopedCursorPosition.afterRejected prefixPull
        (CallScopedCursorPosition.refl prefixCursor))
  exact
    ⟨prefixCursor, prefixFinish, prefixResource, prefixPull, positioned,
      rfl, prefixFinishOwnership, rfl, rfl⟩

end PLeaTTa.PrologBodyFailureOuterResourceActivationBridge
