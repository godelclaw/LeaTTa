-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge
Purpose: Execute the exact ranked source catch-up hidden by one eager
  executable pull across exhausted outer local-predicate resources.
Trusted boundary: none
Main exports:
  CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame,
  CrossedEmptyResourceFramesAgrees.sourceCatchupTerminal,
  SpinedExhaustedPostFailureOffsetRelates.catchupFirstLive,
  SpinedExhaustedPostFailureOffsetRelates.catchupTerminal,
  SpinedExhaustedPostFailureOffsetRelates.catchupClassified
-/
import PLeaTTa.Proofs.PrologBodyFailureExhaustedResourceTransitionBridge
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge

namespace PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologAlphaFreshFrontierBridge
open PrologGoalAlpha
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologPrefilterBridge
open PrologPrefilterScanBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The executable body-failure transition calls `pull` once.  That single
machine transition may cross several empty outer predicate banks and install
the first branch of a later bank.  The independent source is intentionally
finer grained: every rejected clause occurrence is a present silent step,
and every exhausted predicate frame is crossed by one further transition.

This module executes that hidden source work exactly.  It does not quotient
silent steps and does not infer an empty source cursor from an empty
executable bank.  The ranked `CrossedEmptyResourceFramesAgrees` evidence
supplies every rejected occurrence explicitly.
-/

/-! ## Exact executable barrier-cache traversal -/

/-- Apply the executable marker-pop operation an exact number of times. -/
def popBarrierCacheN : Nat → Option Nat → Option Nat
  | 0, cache => cache
  | count + 1, cache =>
      popBarrierCacheN count (PLeaTTa.popBarrierCache cache)

@[simp] theorem popBarrierCacheN_zero (cache : Option Nat) :
    popBarrierCacheN 0 cache = cache := rfl

@[simp] theorem popBarrierCacheN_succ (count : Nat)
    (cache : Option Nat) :
    popBarrierCacheN (count + 1) cache =
      popBarrierCacheN count (PLeaTTa.popBarrierCache cache) := rfl

/-- The tracked executable traversal crosses exactly the empty resource
markers before the first live branch.

In particular it does not pop the first live resource's marker; that marker
remains in the returned alternative suffix. -/
theorem pullAuxTracked_flattenOwnedAlts_first_nonempty
    (cache : Option Nat)
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Metta.Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    PLeaTTa.pullAuxTracked cache
        (flattenOwnedAlts (emptyPrefix ++ first :: rest) base) =
      (some
        ((goals, binding),
          tail ++ PLeaTTa.Alt.barrier :: flattenOwnedAlts rest base),
        popBarrierCacheN emptyPrefix.length cache) := by
  induction emptyPrefix generalizing cache with
  | nil =>
      rw [List.nil_append, flattenOwnedAlts_cons, firstHead]
      cases cache <;> rfl
  | cons resource resources inductionHypothesis =>
      have headEmpty : resource.alts = [] :=
        prefixEmpty resource (by simp)
      have tailEmpty :
          ∀ item ∈ resources, item.alts = [] := by
        intro item member
        exact prefixEmpty item (by simp [member])
      rw [List.cons_append, flattenOwnedAlts_cons, headEmpty]
      cases cache with
      | none =>
          simpa [PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached,
            PLeaTTa.pullAux,
            popBarrierCacheN] using
            inductionHypothesis none tailEmpty
      | some depth =>
          simpa [PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached,
            popBarrierCacheN] using
            inductionHypothesis (some (depth - 1)) tailEmpty

/-- The complete executable `pull` installs the first live branch, exact
alternative suffix, and exact post-pop barrier cache in one equation. -/
theorem pull_flattenOwnedAlts_first_nonempty_exact
    (conf : PLeaTTa.Conf)
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Metta.Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    let before :=
      { conf with
        cur := none
        alts :=
          flattenOwnedAlts
            (emptyPrefix ++ first :: rest) base }
    PLeaTTa.pull before =
      { before with
        cur := some (goals, binding)
        alts :=
          tail ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts rest base
        barriers :=
          popBarrierCacheN emptyPrefix.length conf.barriers } := by
  dsimp only
  unfold PLeaTTa.pull
  rw [pullAuxTracked_flattenOwnedAlts_first_nonempty conf.barriers
    emptyPrefix first rest base goals binding tail prefixEmpty firstHead]

/-- Empty resource markers are a tracked traversal prefix even when the
arbitrary base later selects a branch or crosses more markers. -/
theorem pullAuxTracked_flattenOwnedAlts_all_empty
    (cache : Option Nat)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (allEmpty : ∀ resource ∈ resources, resource.alts = []) :
    PLeaTTa.pullAuxTracked cache (flattenOwnedAlts resources base) =
      PLeaTTa.pullAuxTracked
        (popBarrierCacheN resources.length cache) base := by
  induction resources generalizing cache with
  | nil =>
      rfl
  | cons resource resources inductionHypothesis =>
      have headEmpty : resource.alts = [] :=
        allEmpty resource (by simp)
      have tailEmpty :
          ∀ item ∈ resources, item.alts = [] := by
        intro item member
        exact allEmpty item (by simp [member])
      rw [flattenOwnedAlts_cons, headEmpty]
      cases cache with
      | none =>
          simpa [PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached,
            PLeaTTa.pullAux,
            popBarrierCacheN] using
            inductionHypothesis none tailEmpty
      | some depth =>
          simpa [PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached,
            popBarrierCacheN] using
            inductionHypothesis (some (depth - 1)) tailEmpty

/-! ## Executable anti-vacuity witnesses -/

private def trackedEmptyWitnessResource : RetainedAlternativeSegment :=
  { argsv := []
    args := []
    res := .sym "result"
    rest := []
    binding := []
    qterm := .sym "query"
    barrier := 1
    counter := 0
    alts := []
    finalCounter := 0 }

private def trackedLiveWitnessResource : RetainedAlternativeSegment :=
  { trackedEmptyWitnessResource with
    barrier := 2
    alts := [.br [.call "witness" [] (.sym "result")] []] }

/-- The first live resource's marker is retained while exactly the earlier
empty marker is reflected in the tracked cache. -/
theorem tracked_empty_then_live_retains_live_marker :
    PLeaTTa.pullAuxTracked (some 2)
        (flattenOwnedAlts
          [trackedEmptyWitnessResource, trackedLiveWitnessResource] []) =
      (some
        (([.call "witness" [] (.sym "result")], []),
          [PLeaTTa.Alt.barrier]),
        some 1) := by
  rfl

/-- A terminal arbitrary base may cross more markers after all local
resources.  Thus terminal cache accounting must retain the tracked base
outcome, not merely pop once per local descriptor. -/
theorem terminal_base_marker_requires_tracked_base :
    PLeaTTa.pullAuxTracked (some 3)
        (flattenOwnedAlts [trackedEmptyWitnessResource]
          [PLeaTTa.Alt.barrier]) =
      (none, some 0) ∧
    popBarrierCacheN [trackedEmptyWitnessResource].length (some 3) =
      some 2 := by
  constructor <;> rfl

/-! ## Frame-native exhausted frontiers -/

/-- The retained predicate frontier represented by one active product frame.

This is the frame-native form of `sourceProductFrontier`.  It avoids
fabricating a call-opening derivation for an already-open outer predicate. -/
def frameRetainedFrontier
    (frame : ActiveProductFrame) (cursor : PreparedCursor) : Search :=
  .product frame.callerScope
    (.cutBoundary frame.predicateScope
      (.clauses frame.predicateScope cursor))
    frame.callerRest

/-- An empty retained cursor completes its predicate frontier in exactly one
raw step.  The completion observation remains visible until an enclosing
choice consumes it. -/
theorem frameRetainedFrontier_exhausted
    (session : Session) (frame : ActiveProductFrame)
    (cursor : PreparedCursor) (empty : cursor.remaining = []) :
    RawStep session (frameRetainedFrontier frame cursor)
      [.completed] .none session (.terminal .completed) := by
  have pulled : LocalPull cursor .exhausted :=
    .exhausted cursor empty
  have clauses :
      RawStep session (.clauses frame.predicateScope cursor)
        [.completed] .none session (.terminal .completed) := by
    simpa [localPullEvents, localPullTarget] using
      (RawStep.clausesPull frame.predicateScope cursor .exhausted session
        pulled)
  have boundary :
      RawStep session
        (.cutBoundary frame.predicateScope
          (.clauses frame.predicateScope cursor))
        [.completed] .none session (.terminal .completed) :=
    .cutBoundaryComplete frame.predicateScope _ session session clauses
  exact
    .productComplete frame.callerScope _ frame.callerRest [.completed]
      session session boundary (by simp [Trace.AnswerFree])

/-- The named current predicate frontier is the same one-step exhausted
state as its frame-native presentation. -/
theorem sourceProductFrontier_exhausted
    (callerScope : CutScopeId) (opened : OpenedCall)
    (cursor : PreparedCursor)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (empty : cursor.remaining = []) :
    RawStep opened.session
      (sourceProductFrontier callerScope opened cursor referenceRest)
      [.completed] .none opened.session (.terminal .completed) := by
  let frame : ActiveProductFrame :=
    { callerScope := callerScope
      predicateScope := opened.scope
      retained := .clauses opened.scope cursor
      callerRest := referenceRest }
  simpa [frame, frameRetainedFrontier, sourceProductFrontier] using
    frameRetainedFrontier_exhausted opened.session frame cursor empty

/-- Completion of an inner focus promotes one outer frame's retained cursor
without publishing the consumed completion event. -/
theorem ActiveProductFrame.promoteCompleted
    (frame : ActiveProductFrame) (session : Session)
    (focus : Search) (cursor : PreparedCursor)
    (retainedShape :
      frame.retained = .clauses frame.predicateScope cursor)
    (completed :
      RawStep session focus [.completed] .none session
        (.terminal .completed)) :
    RawStep session (frame.wrap focus) [] .none session
      (.running (frameRetainedFrontier frame cursor)) := by
  have choice :
      RawStep session
        (.choice frame.predicateScope focus frame.retained)
        [] .none session (.running frame.retained) :=
    .choiceComplete frame.predicateScope focus frame.retained session session
      completed
  have boundary :
      RawStep session
        (.cutBoundary frame.predicateScope
          (.choice frame.predicateScope focus frame.retained))
        [] .none session
        (.running
          (.cutBoundary frame.predicateScope frame.retained)) :=
    .cutBoundaryProgress frame.predicateScope _ _ [] session session choice
  have product :
      RawStep session (frame.wrap focus) [] .none session
        (.running
          (.product frame.callerScope
            (.cutBoundary frame.predicateScope frame.retained)
            frame.callerRest)) :=
    .productProgress frame.callerScope _ _ frame.callerRest [] .none
      session session boundary (by simp [Trace.AnswerFree])
  simpa [frameRetainedFrontier, retainedShape] using product

/-- Promotion through one frame lifts through every still-outer source frame
as one genuine top-level transition. -/
theorem ActiveProductContext.promoteCompleted
    (outer : ActiveProductContext) (frame : ActiveProductFrame)
    (session : Session) (focus : Search) (cursor : PreparedCursor)
    (retainedShape :
      frame.retained = .clauses frame.predicateScope cursor)
    (completed :
      RawStep session focus [.completed] .none session
        (.terminal .completed)) :
    Transition
      (.running session
        (ActiveProductContext.plug (frame :: outer) focus))
      []
      (.running session
        (ActiveProductContext.plug outer
          (frameRetainedFrontier frame cursor))) := by
  have promoted :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.ActiveProductFrame.promoteCompleted
      frame session focus cursor retainedShape completed
  have lifted :=
    ActiveProductContext.liftProgress outer promoted
      (by simp [Trace.AnswerFree])
  exact .ordinary _ _ _ _ _ lifted

/-- Exactly counted rejected pulls inside a frame-native frontier lift
through every still-outer source frame. -/
theorem RejectedPullsN.frameRetainedFrontierContextStepsN
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (outer : ActiveProductContext) (frame : ActiveProductFrame)
    (session : Session) :
    StepsN count
      (.running session
        (ActiveProductContext.plug outer
          (frameRetainedFrontier frame before)))
      []
    (.running session
        (ActiveProductContext.plug outer
          (frameRetainedFrontier frame after))) := by
  -- `OpenedCall` is proof-local packaging only: the reused theorem consumes
  -- the frontier shape and never claims or requests a call-opening step.
  let opened : OpenedCall :=
    { scope := frame.predicateScope
      cursor := before
      session := session }
  simpa [frameRetainedFrontier, sourceProductFrontier, opened] using
    PLeaTTa.PrologBodyFailureResourceTransitionBridge.RejectedPullsN.sourceProductContextStepsN
      pulls outer frame.callerScope opened frame.callerRest

/-! ## Source anti-vacuity witness -/

private def crossedRejectedReference : VersionedClause :=
  { id := 0
    clause :=
      { predicate := "ranked"
        arguments := [.integer 2]
        body := [] }
    created := 0 }

private def crossedRejectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 2)
    body := [] }

private def crossedRejectedBranch : ClauseBranch :=
  preparedBranchOf 0 [.integer 1] [] 0 crossedRejectedReference

private def crossedRejectedCursor : PreparedCursor :=
  { callGeneration := 0
    predicate := "ranked"
    arguments := [.integer 1]
    bindings := []
    reservationStart := 0
    remaining := [crossedRejectedBranch]
    reservedUntil := 0 }

private def crossedRejectedFinish : PreparedCursor :=
  crossedRejectedCursor.advance crossedRejectedBranch []

private def crossedRejectedResource : RetainedAlternativeSegment :=
  { argsv := []
    args := []
    res := .gnd (.int 1)
    rest := []
    binding := []
    qterm := .sym "query"
    barrier := 0
    counter := 0
    alts := []
    finalCounter := 0 }

private def crossedRejectedFrame : ActiveProductFrame :=
  { callerScope := 0
    predicateScope := 1
    retained := .clauses 1 crossedRejectedCursor
    callerRest := [] }

private theorem crossedRejectedCandidateAgreement :
    CandidateClauseAgrees "ranked" crossedRejectedReference
      crossedRejectedExecutable := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact ⟨[], .integer 2, rfl, .nil, .integer 2⟩
  · intro name
    simp [crossedRejectedReference, crossedRejectedExecutable,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables,
      goalsVariables]

private theorem crossedRejectedSupported :
    SupportedPreparedCandidateAgrees 0 "ranked" [.integer 1] []
      crossedRejectedBranch crossedRejectedExecutable := by
  refine .intro crossedRejectedReference 0 crossedRejectedExecutable
    crossedRejectedCandidateAgreement ?_ ?_
  · intro left right leftMember rightMember
    simp [crossedRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        crossedRejectedCandidateAgreement.body
    have proofEq :
        crossedRejectedCandidateAgreement.body =
          (CompilerAdequacy.GoalsAgree.nil : CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem crossedRejectedWellFormed :
    crossedRejectedCursor.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .cons 0 crossedRejectedBranch [] 0 (by decide) (by decide) (.nil 0)
  · intro index member
    simp [crossedRejectedCursor, termsVariables, termVariables,
      substitutionVariables] at member
  · intro branch member
    simp [crossedRejectedCursor] at member
    subst branch
    rfl
  · intro branch member
    simp [crossedRejectedCursor] at member
    subst branch
    intro source index targetMember
    simpa [crossedRejectedBranch, preparedBranchOf] using
      crossedRejectedReference.clause.freshCopy_target_range 0 targetMember

private theorem crossedRejectedQuery :
    RepresentativeNormalizedCallAgrees [] crossedRejectedCursor []
      (.gnd (.int 1)) := by
  apply NormalizedCallAgrees.representative
  constructor
  simpa [crossedRejectedCursor] using
    (AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 1)
      AlphaTermsAgree.nil)

private theorem crossedRejectedHead :
    NormalizedHeadAgrees crossedRejectedBranch [] (.gnd (.int 1))
      crossedRejectedExecutable :=
  supportedPreparedCandidate_normalizedHeadAgrees
    (query :=
      (⟨by
        simpa [crossedRejectedCursor] using
          (AlphaTermsAgree.cons
            (AlphaTermAgrees.integer (alpha := []) 1)
            AlphaTermsAgree.nil)⟩ :
        NormalizedCallAgrees [] crossedRejectedCursor []
          (.gnd (.int 1))))
    crossedRejectedWellFormed
    (by simp [crossedRejectedCursor])
    crossedRejectedSupported
    (by rfl)

private theorem crossedRejectedClash :
    ¬ ∃ result, HeadResolution crossedRejectedBranch result :=
  crossedRejectedHead.no_headResolution_of_rejected (by rfl)

private theorem crossedRejectedOwnership :
    crossedRejectedResource.Owns [] crossedRejectedCursor := by
  refine ⟨[crossedRejectedExecutable], crossedRejectedWellFormed,
    ?_, rfl, ?_, ?_, ?_⟩
  · simpa [crossedRejectedResource] using crossedRejectedQuery
  · exact .cons crossedRejectedSupported .nil
  · intro clause member
    simp [crossedRejectedExecutable] at member
    subst clause
    rfl
  · have rejected :
        resolutionClauseRetained [] (.gnd (.int 1))
          crossedRejectedExecutable = false := by
      rfl
    have rejectedAfterSubst :
        resolutionClauseRetained []
          (PLeaTTa.subst [] (.gnd (.int 1)))
          crossedRejectedExecutable = false := by
      simpa using rejected
    simpa [crossedRejectedResource] using
      (ResolutionScan.skipped crossedRejectedExecutable [] 0 0 []
        rejectedAfterSubst (ResolutionScan.nil 0))

private theorem crossedRejectedPull :
    RejectedPullsN 1 crossedRejectedCursor crossedRejectedFinish := by
  simpa [crossedRejectedFinish] using
    (RejectedPullsN.succ 0 crossedRejectedCursor crossedRejectedBranch []
      crossedRejectedFinish (by rfl) crossedRejectedClash
      (.zero crossedRejectedFinish))

/-- The recursive source catch-up relation has a genuine nonempty inhabitant:
one owned source occurrence is conservatively rejected, its executable bank
is empty, and the resulting cursor is exhausted.

This is the discriminator for the case an empty executable resource still
contains ranked source work; the `cons` branch is therefore not vacuous. -/
theorem one_rejected_crossed_frame_is_inhabited :
    ∃ resource frame cursor finish,
      cursor.remaining.length = 1 ∧
      resource.alts = [] ∧
      finish.remaining = [] ∧
      RejectedPullsN 1 cursor finish ∧
      resource.Owns [] cursor ∧
      CrossedEmptyResourceFramesAgrees []
        [resource] [frame] 1 := by
  refine ⟨crossedRejectedResource, crossedRejectedFrame,
    crossedRejectedCursor, crossedRejectedFinish, ?_, rfl, ?_,
    crossedRejectedPull, crossedRejectedOwnership, ?_⟩
  · rfl
  · rfl
  · exact
      .cons crossedRejectedResource [] crossedRejectedFrame []
        crossedRejectedCursor crossedRejectedFinish 1 0
        (by rfl) crossedRejectedOwnership (by rfl) crossedRejectedPull
        (by rfl) .nil

private def partitionLiveBranch : ClauseBranch :=
  preparedBranchOf 0 [.integer 2] [] 0 crossedRejectedReference

private def partitionLiveCursor : PreparedCursor :=
  { callGeneration := 0
    predicate := "ranked"
    arguments := [.integer 2]
    bindings := []
    reservationStart := 0
    remaining := [partitionLiveBranch]
    reservedUntil := 0 }

private def partitionLiveAlt : PLeaTTa.Alt :=
  resolutionAlt [] [] (.gnd (.int 2)) [] [] (.sym "query") 2 0
    crossedRejectedExecutable

private def partitionLiveGoals : List PLeaTTa.Goal :=
  match partitionLiveAlt with
  | .br goals _ => goals
  | .barrier => []

private theorem partitionLiveAlt_shape :
    partitionLiveAlt = .br partitionLiveGoals [] := by
  rfl

private def partitionLiveResource : RetainedAlternativeSegment :=
  { argsv := []
    args := []
    res := .gnd (.int 2)
    rest := []
    binding := []
    qterm := .sym "query"
    barrier := 2
    counter := 0
    alts := [partitionLiveAlt]
    finalCounter := 1 }

private def partitionLiveFrame : ActiveProductFrame :=
  { callerScope := 3
    predicateScope := 2
    retained := .clauses 2 partitionLiveCursor
    callerRest := [] }

private theorem partitionLiveSupported :
    SupportedPreparedCandidateAgrees 0 "ranked" [.integer 2] []
      partitionLiveBranch crossedRejectedExecutable := by
  refine .intro crossedRejectedReference 0 crossedRejectedExecutable
    crossedRejectedCandidateAgreement ?_ ?_
  · intro left right leftMember rightMember
    simp [crossedRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        crossedRejectedCandidateAgreement.body
    have proofEq :
        crossedRejectedCandidateAgreement.body =
          (CompilerAdequacy.GoalsAgree.nil :
            CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem partitionLiveWellFormed :
    partitionLiveCursor.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .cons 0 partitionLiveBranch [] 0 (by decide) (by decide) (.nil 0)
  · intro index member
    simp [partitionLiveCursor, termsVariables, termVariables,
      substitutionVariables] at member
  · intro branch member
    simp [partitionLiveCursor] at member
    subst branch
    rfl
  · intro branch member
    simp [partitionLiveCursor] at member
    subst branch
    intro source index targetMember
    simpa [partitionLiveBranch, preparedBranchOf] using
      crossedRejectedReference.clause.freshCopy_target_range 0 targetMember

private theorem partitionLiveQuery :
    RepresentativeNormalizedCallAgrees [] partitionLiveCursor []
      (.gnd (.int 2)) := by
  apply NormalizedCallAgrees.representative
  constructor
  simpa [partitionLiveCursor] using
    (AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 2)
      AlphaTermsAgree.nil)

private theorem partitionLiveOwnership :
    partitionLiveResource.Owns [] partitionLiveCursor := by
  refine ⟨[crossedRejectedExecutable], partitionLiveWellFormed,
    ?_, rfl, ?_, ?_, ?_⟩
  · simpa [partitionLiveResource] using partitionLiveQuery
  · exact .cons partitionLiveSupported .nil
  · intro clause member
    simp [crossedRejectedExecutable] at member
    subst clause
    rfl
  · have retained :
        resolutionClauseRetained [] (.gnd (.int 2))
          crossedRejectedExecutable = true := by
      rfl
    simpa [partitionLiveResource, partitionLiveAlt] using
      (ResolutionScan.retained crossedRejectedExecutable [] 0 1 []
        (by simpa using retained) (ResolutionScan.nil 1))

private theorem oneCrossedPartitionWork :
    CrossedEmptyResourceFramesAgrees []
      [crossedRejectedResource] [crossedRejectedFrame] 1 := by
  exact
    .cons crossedRejectedResource [] crossedRejectedFrame []
      crossedRejectedCursor crossedRejectedFinish 1 0
      (by rfl) crossedRejectedOwnership (by rfl) crossedRejectedPull
      (by rfl) .nil

private theorem twoCrossedPartitionWork :
    CrossedEmptyResourceFramesAgrees []
      [crossedRejectedResource, crossedRejectedResource]
      [crossedRejectedFrame, crossedRejectedFrame] 2 := by
  exact
    .cons crossedRejectedResource [crossedRejectedResource]
      crossedRejectedFrame [crossedRejectedFrame]
      crossedRejectedCursor crossedRejectedFinish 1 1
      (by rfl) crossedRejectedOwnership (by rfl) crossedRejectedPull
      (by rfl) oneCrossedPartitionWork

private def partitionWitnessSegment (barrier : Nat) : ControlSegment :=
  { barrier := barrier
    references := []
    executables := [] }

/-- The first-live catch-up partition is substantively inhabited.

Two outer frames each carry one genuine conservatively rejected source
occurrence and an empty executable bank.  The third frame owns one real
retained `resolutionAlt`.  Thus both recursive crossed work and the
surviving-head fields are simultaneously satisfiable. -/
theorem two_crossed_then_live_partition_is_inhabited :
    ∃ partition :
        OuterResourceCatchupPartition []
          [partitionWitnessSegment 0, partitionWitnessSegment 1,
            partitionWitnessSegment 2]
          [crossedRejectedResource, crossedRejectedResource,
            partitionLiveResource]
          [crossedRejectedFrame, crossedRejectedFrame, partitionLiveFrame],
      partition.crossedResources.length = 2 ∧
        partition.rejectionSteps = 2 ∧
        partition.first.alts ≠ [] := by
  let partition :
      OuterResourceCatchupPartition []
        [partitionWitnessSegment 0, partitionWitnessSegment 1,
          partitionWitnessSegment 2]
        [crossedRejectedResource, crossedRejectedResource,
          partitionLiveResource]
        [crossedRejectedFrame, crossedRejectedFrame, partitionLiveFrame] :=
    { crossedSegments :=
        [partitionWitnessSegment 0, partitionWitnessSegment 1]
      firstSegment := partitionWitnessSegment 2
      survivingSegments := []
      crossedResources :=
        [crossedRejectedResource, crossedRejectedResource]
      first := partitionLiveResource
      survivingResources := []
      crossedFrames := [crossedRejectedFrame, crossedRejectedFrame]
      firstFrame := partitionLiveFrame
      survivingContext := []
      firstCursor := partitionLiveCursor
      rejectionSteps := 2
      goals := partitionLiveGoals
      binding := []
      tail := []
      segmentsEq := rfl
      resourcesEq := rfl
      contextEq := rfl
      crossedSegmentDepth := rfl
      crossedWork := twoCrossedPartitionWork
      firstRetainedShape := rfl
      firstOwnership := partitionLiveOwnership
      firstHead := by
        simpa [partitionLiveResource] using partitionLiveAlt_shape }
  exact
    ⟨partition, rfl, rfl, by simp [partition, partitionLiveResource]⟩

/-- The all-terminal sibling partition is also substantively inhabited.

The same two ranked rejected frames exhaust completely and the arbitrary
base bank is definitionally terminal. -/
theorem two_crossed_then_terminal_partition_is_inhabited :
    ∃ partition :
        TerminalOuterResourceCatchupPartition []
          [partitionWitnessSegment 0, partitionWitnessSegment 1]
          [crossedRejectedResource, crossedRejectedResource]
          [crossedRejectedFrame, crossedRejectedFrame] [],
      partition.rejectionSteps = 2 := by
  let partition :
      TerminalOuterResourceCatchupPartition []
        [partitionWitnessSegment 0, partitionWitnessSegment 1]
        [crossedRejectedResource, crossedRejectedResource]
        [crossedRejectedFrame, crossedRejectedFrame] [] :=
    { rejectionSteps := 2
      segmentDepth := rfl
      crossedWork := twoCrossedPartitionWork
      baseTerminal := rfl }
  exact ⟨partition, rfl⟩

/-! ## Recursive chronology anti-vacuity -/

private def chronologyBranch (seed : Nat) : ClauseBranch :=
  preparedBranchOf 0 [.integer 2] [] seed crossedRejectedReference

@[simp] private theorem chronologyBranch_firstFresh (seed : Nat) :
    (chronologyBranch seed).firstFresh = seed := by
  simp [chronologyBranch, preparedBranchOf, LocalClause.freshCopy,
    crossedRejectedReference, LocalClause.generatedCeiling,
    LocalClause.variables, termsVariables, termVariables, goalsVariables,
    variablesGeneratedCeiling, buildFreshening]

@[simp] private theorem chronologyBranch_nextFresh (seed : Nat) :
    (chronologyBranch seed).nextFresh = seed := by
  simp [chronologyBranch, preparedBranchOf, LocalClause.freshCopy,
    crossedRejectedReference, LocalClause.generatedCeiling,
    LocalClause.variables, termsVariables, termVariables, goalsVariables,
    variablesGeneratedCeiling, buildFreshening]

private def chronologyCursor (seed : Nat) : PreparedCursor :=
  { callGeneration := 0
    predicate := "ranked"
    arguments := [.integer 2]
    bindings := []
    reservationStart := seed
    remaining := [chronologyBranch seed]
    reservedUntil := (chronologyBranch seed).nextFresh }

private def chronologyAlt
    (barrier counter : Nat) : PLeaTTa.Alt :=
  resolutionAlt [] [] (.gnd (.int 2)) [] [] (.sym "query") barrier counter
    crossedRejectedExecutable

private def chronologyResource
    (barrier counter : Nat) : RetainedAlternativeSegment :=
  { argsv := []
    args := []
    res := .gnd (.int 2)
    rest := []
    binding := []
    qterm := .sym "query"
    barrier := barrier
    counter := counter
    alts := [chronologyAlt barrier counter]
    finalCounter := counter + 1 }

private def chronologySegment (barrier : Nat) : ControlSegment :=
  { barrier := barrier
    references := []
    executables := [] }

private def chronologyFrame
    (predicateScope callerScope : CutScopeId) (seed : Nat) :
    ActiveProductFrame :=
  { callerScope := callerScope
    predicateScope := predicateScope
    retained := .clauses predicateScope (chronologyCursor seed)
    callerRest := [] }

private theorem chronologySupported (seed : Nat) :
    SupportedPreparedCandidateAgrees 0 "ranked" [.integer 2] []
      (chronologyBranch seed) crossedRejectedExecutable := by
  refine .intro crossedRejectedReference seed crossedRejectedExecutable
    crossedRejectedCandidateAgreement ?_ ?_
  · intro left right leftMember rightMember
    simp [crossedRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        crossedRejectedCandidateAgreement.body
    have proofEq :
        crossedRejectedCandidateAgreement.body =
          (CompilerAdequacy.GoalsAgree.nil :
            CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem chronologyWellFormed (seed : Nat) :
    (chronologyCursor seed).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      .cons seed (chronologyBranch seed) []
        (chronologyBranch seed).nextFresh
        (by
          change
            seed ≤
              (crossedRejectedReference.clause.freshCopy seed).firstFresh
          exact
            crossedRejectedReference.clause.freshCopy_first_ge_seed seed)
        (by
          change
            (crossedRejectedReference.clause.freshCopy seed).firstFresh ≤
              (crossedRejectedReference.clause.freshCopy seed).nextFresh
          rw [LocalClause.freshCopy_next]
          omega)
        (.nil (chronologyBranch seed).nextFresh)
  · intro index member
    simp [chronologyCursor, termsVariables, termVariables,
      substitutionVariables] at member
  · intro branch member
    simp [chronologyCursor] at member
    subst branch
    rfl
  · intro branch member
    simp [chronologyCursor] at member
    subst branch
    intro source index targetMember
    simpa [chronologyBranch, preparedBranchOf] using
      crossedRejectedReference.clause.freshCopy_target_range seed targetMember

private theorem chronologyQuery (seed : Nat) :
    RepresentativeNormalizedCallAgrees [] (chronologyCursor seed) []
      (.gnd (.int 2)) := by
  apply NormalizedCallAgrees.representative
  constructor
  simpa [chronologyCursor] using
    (AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 2)
      AlphaTermsAgree.nil)

private theorem chronologyOwnership
    (seed barrier counter : Nat) :
    (chronologyResource barrier counter).Owns []
      (chronologyCursor seed) := by
  refine ⟨[crossedRejectedExecutable], chronologyWellFormed seed,
    ?_, rfl, ?_, ?_, ?_⟩
  · simpa [chronologyResource] using chronologyQuery seed
  · exact .cons (chronologySupported seed) .nil
  · intro clause member
    simp [crossedRejectedExecutable] at member
    subst clause
    rfl
  · have retained :
        resolutionClauseRetained [] (.gnd (.int 2))
          crossedRejectedExecutable = true := by
      rfl
    simpa [chronologyResource, chronologyAlt] using
      (ResolutionScan.retained crossedRejectedExecutable [] counter
        (counter + 1) [] (by simpa using retained)
        (ResolutionScan.nil (counter + 1)))

private def emptyRuntimeTopological :
    PLeaTTa.SubstTopological [] := by
  refine
    { order := []
      nodup := by simp
      domain := ?_
      decreases := ?_ }
  · intro name
    simp [Metta.Subst.lookup]
  · intro source value dependency lookup
    simp [Metta.Subst.lookup] at lookup

private theorem emptyTaskData :
    TaskDataAgrees [] [] [] [] [] [] := by
  refine
    { alphaShared := ?_
      canonicalWellFormed := TreeSubstitution.wellFormed_nil
      bindingShape := rfl
      valuation := ?_ }
  · constructor <;> intro <;> simp_all
  · refine
      ⟨[], TreeSubstitutionVariants.refl [],
        TreeSubstitutionTopological.nil, ?_, ⟨emptyRuntimeTopological⟩, ?_⟩
    · intro entry member
      simp at member
    · intro identity name member
      simp at member

private theorem chronologyCallerAgrees (barrier : Nat) :
    (chronologySegment barrier).Agrees [] := by
  exact .nil

private theorem chronologyCallControl (barrier : Nat) :
    NormalizedAlphaGoalsAgree [] barrier
      [.call "ranked" [.integer 2]]
      [.call "ranked" [] (.gnd (.int 2))] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.integer (alpha := []) 2))
      .nil

private def chronologySnapshot
    (seed resourceBarrier counter callerBarrier : Nat)
    (outer : List ControlSegment)
    (outerControl : ControlSpineAgrees [] outer)
    (outerExecutables : flattenExecutables outer = []) :
    RetainedCallPayloadSnapshot [] []
      (chronologyResource resourceBarrier counter)
      (chronologyCursor seed) (chronologySegment callerBarrier) outer := by
  have supported :
      AlphaTermsSupported [] [] [.integer 2] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  have payload :
      TaskSpinePayloadAgrees [] [] [] [] [] []
        ({ barrier := callerBarrier
           references := [.call "ranked" [.integer 2]]
           executables := [.call "ranked" [] (.gnd (.int 2))] } ::
         outer) :=
    ⟨emptyTaskData,
      .cons (chronologyCallControl callerBarrier) outerControl⟩
  refine
    { snapshotAlpha := []
      canonical := []
      referenceBase := []
      referencePayload := [.integer 2]
      alphaIncluded := ?_
      allocationGap := ?_
      cursorArguments := rfl
      residualRepresentative := []
      cumulative := ?_
      materialized := ?_
      queryReferenceBelow := ?_
      queryExecutableLive := ?_
      queryExecutableBelow := ?_
      resourceRest := ?_
      payload := ?_ }
  · intro pair member
    simp at member
  · constructor <;> intro <;> simp_all
  · refine
      ⟨TreeSubstitutionVariants.refl [], TreeSubstitutionTopological.nil,
        ?_, ⟨emptyRuntimeTopological⟩, ?_⟩
    · intro entry member
      simp at member
    · intro identity name member
      simp at member
  · refine
      ⟨TreeSubstitutionVariants.refl [], ?_, ?_, ?_⟩
    · intro entry member
      simp at member
    · intro entry member
      simp at member
    · have leaves :
          List.Forall₂ (CanonicalRuntimeAgrees [])
            [.node (.integer 2) []] [.gnd (.int 2)] :=
        .cons (CanonicalRuntimeAgrees.integer (alpha := []) 2) .nil
      simpa [chronologyResource, chronologyCursor, TreeSubstitution.apply,
        Term.denote] using leaves
  · intro index member
    simp at member
  · intro name member
    simp at member
  · simp only [chronologyResource]
    unfold resolutionOccupiedVars
    simp [Metta.Atom.vars, specializationGoalsVars,
      resolutionSeedHighWaterNames]
  · simp [chronologyResource, chronologySegment, outerExecutables]
  · simpa [chronologyCursor, chronologyResource, chronologySegment] using
      payload

private def chronologyOrderedZipper :
    SourceControlResourcePayloadContextAgrees [] [] (.sym "query") 30
      [chronologySegment 20, chronologySegment 10, chronologySegment 0]
      [chronologyResource 30 6, chronologyResource 20 4,
        chronologyResource 10 2]
      3
      [chronologyFrame 3 2 6, chronologyFrame 2 1 4,
        chronologyFrame 1 0 2]
      0 :=
  .cons 30 3 2 0 (chronologySegment 20)
    [chronologySegment 10, chronologySegment 0]
    (chronologyResource 30 6)
    [chronologyResource 20 4, chronologyResource 10 2]
    (chronologyCursor 6)
    [chronologyFrame 2 1 4, chronologyFrame 1 0 2]
    (chronologyCallerAgrees 20) (by rfl) (by rfl) (by rfl)
    (chronologyOwnership 6 30 6)
    (chronologySnapshot 6 30 6 20
      [chronologySegment 10, chronologySegment 0]
      (.cons (chronologyCallerAgrees 10)
        (.cons (chronologyCallerAgrees 0) .nil))
      rfl)
    (.cons 20 2 1 0 (chronologySegment 10)
      [chronologySegment 0]
      (chronologyResource 20 4) [chronologyResource 10 2]
      (chronologyCursor 4) [chronologyFrame 1 0 2]
      (chronologyCallerAgrees 10) (by rfl) (by rfl) (by rfl)
      (chronologyOwnership 4 20 4)
      (chronologySnapshot 4 20 4 10 [chronologySegment 0]
        (.cons (chronologyCallerAgrees 0) .nil) rfl)
      (.cons 10 1 0 0 (chronologySegment 0) []
        (chronologyResource 10 2) [] (chronologyCursor 2) []
        (chronologyCallerAgrees 0) (by rfl) (by rfl) (by rfl)
        (chronologyOwnership 2 10 2)
        (chronologySnapshot 2 10 2 0 [] .nil rfl)
        (.nil 0 0)))

private def chronologySwappedZipper :
    SourceControlResourcePayloadContextAgrees [] [] (.sym "query") 30
      [chronologySegment 20, chronologySegment 10, chronologySegment 0]
      [chronologyResource 30 6, chronologyResource 20 2,
        chronologyResource 10 4]
      3
      [chronologyFrame 3 2 6, chronologyFrame 2 1 2,
        chronologyFrame 1 0 4]
      0 :=
  .cons 30 3 2 0 (chronologySegment 20)
    [chronologySegment 10, chronologySegment 0]
    (chronologyResource 30 6)
    [chronologyResource 20 2, chronologyResource 10 4]
    (chronologyCursor 6)
    [chronologyFrame 2 1 2, chronologyFrame 1 0 4]
    (chronologyCallerAgrees 20) (by rfl) (by rfl) (by rfl)
    (chronologyOwnership 6 30 6)
    (chronologySnapshot 6 30 6 20
      [chronologySegment 10, chronologySegment 0]
      (.cons (chronologyCallerAgrees 10)
        (.cons (chronologyCallerAgrees 0) .nil))
      rfl)
    (.cons 20 2 1 0 (chronologySegment 10)
      [chronologySegment 0]
      (chronologyResource 20 2) [chronologyResource 10 4]
      (chronologyCursor 2) [chronologyFrame 1 0 4]
      (chronologyCallerAgrees 10) (by rfl) (by rfl) (by rfl)
      (chronologyOwnership 2 20 2)
      (chronologySnapshot 2 20 2 10 [chronologySegment 0]
        (.cons (chronologyCallerAgrees 0) .nil) rfl)
      (.cons 10 1 0 0 (chronologySegment 0) []
        (chronologyResource 10 4) [] (chronologyCursor 4) []
        (chronologyCallerAgrees 0) (by rfl) (by rfl) (by rfl)
        (chronologyOwnership 4 10 4)
        (chronologySnapshot 4 10 4 0 [] .nil rfl)
        (.nil 0 0)))

/-- Recursive allocation chronology is inhabited below the first surviving
cell, not merely at the head.

All three cells are real retained local calls.  The source reservations are
`6 > 4 > 2` and the executable alternative-bank intervals are
`[6,7) > [4,5) > [2,3)`, so both recursive `ActivationOrdered` obligations
carry substantive strict separation. -/
theorem three_cell_activation_order_is_inhabited :
    ActivationOrdered chronologyOrderedZipper ∧
      ActivationOrdered
        (SourceControlResourcePayloadContextAgrees.tail
          chronologyOrderedZipper) := by
  have ordered : ActivationOrdered chronologyOrderedZipper := by
    simp [chronologyOrderedZipper, ActivationOrdered,
      SourceControlResourcePayloadContextAgrees.endpointsBelow,
      chronologyCursor, chronologyResource]
  exact
    ⟨ordered,
      ActivationOrdered.tail chronologyOrderedZipper ordered⟩

/-- Swapping the two older real cells leaves the zipper structurally valid
but violates chronology at the recursive tail.

The head still dominates both older cells, so a head-only invariant would
accept this zipper.  `ActivationOrdered` rejects it because the cell at seed
`2` cannot dominate the surviving cell whose reservation and executable
bank end above `4`. -/
theorem adjacent_surviving_cell_swap_breaks_activation_order :
    ¬ ActivationOrdered chronologySwappedZipper := by
  simp [chronologySwappedZipper, ActivationOrdered,
    SourceControlResourcePayloadContextAgrees.endpointsBelow,
    chronologyCursor, chronologyResource]

/-! ## Typed alignment suffixes -/

/-- Dropping an exact number of inner-to-outer zipper cells preserves a
fully typed source/control/resource suffix.

The new current barrier and cut scope are returned explicitly because each
discarded control segment advances both indices.  The query term and final
outer scope are unchanged. -/
theorem SourceControlResourceContextAgrees.dropAlignedPrefix
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer)
    (count : Nat) (within : count ≤ segments.length) :
    ∃ nextBarrier nextInner,
      SourceControlResourceContextAgrees alpha qterm nextBarrier
        (segments.drop count) (resources.drop count) nextInner
        (context.drop count) outer := by
  induction count generalizing currentBarrier segments resources inner
      context with
  | zero =>
      exact ⟨currentBarrier, inner, by simpa using agreement⟩
  | succ count inductionHypothesis =>
      cases agreement with
      | nil currentBarrier scope =>
          simp at within
      | cons currentBarrier currentScope nextScope outerScope segment
          segments resource resources cursor context segmentAgrees
          resourceRest resourceQuery resourceBarrier resourceOwnership
          outerAgrees =>
          have withinTail : count ≤ segments.length := by
            simpa using Nat.le_of_succ_le_succ within
          obtain ⟨nextBarrier, nextInner, suffix⟩ :=
            inductionHypothesis outerAgrees withinTail
          exact ⟨nextBarrier, nextInner, by simpa using suffix⟩

/-- The first-live partition plus the original typed zipper exposes the
literal aligned suffix beginning at `firstFrame`.

This theorem is the guard against treating
`OuterResourceCatchupPartition` as a standalone alignment certificate. -/
theorem OuterResourceCatchupPartition.alignedSuffix
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    {qterm : Atom} {currentBarrier : Nat}
    {inner outer : CutScopeId}
    (alignment :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer) :
    ∃ suffixBarrier,
      SourceControlResourceContextAgrees alpha qterm suffixBarrier
        (partition.firstSegment :: partition.survivingSegments)
        (partition.first :: partition.survivingResources)
        partition.firstFrame.predicateScope
        (partition.firstFrame :: partition.survivingContext) outer := by
  let count := partition.crossedResources.length
  have crossedFrameLength :
      partition.crossedFrames.length = count := by
    dsimp [count]
    exact partition.crossedWork.length_eq.symm
  have crossedSegmentLength :
      partition.crossedSegments.length = count := by
    dsimp [count]
    exact partition.crossedSegmentDepth
  have within : count ≤ segments.length := by
    rw [partition.segmentsEq]
    simp [count, crossedSegmentLength]
  obtain ⟨suffixBarrier, suffixInner, suffix⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.SourceControlResourceContextAgrees.dropAlignedPrefix
      alignment count within
  have segmentsDrop :
      segments.drop count =
        partition.firstSegment :: partition.survivingSegments := by
    calc
      segments.drop count =
          (partition.crossedSegments ++
            partition.firstSegment :: partition.survivingSegments).drop
              count :=
        congrArg (List.drop count) partition.segmentsEq
      _ = partition.firstSegment :: partition.survivingSegments := by
        rw [← crossedSegmentLength]
        simp
  have resourcesDrop :
      resources.drop count =
        partition.first :: partition.survivingResources := by
    calc
      resources.drop count =
          (partition.crossedResources ++
            partition.first :: partition.survivingResources).drop count :=
        congrArg (List.drop count) partition.resourcesEq
      _ = partition.first :: partition.survivingResources := by
        simp [count]
  have contextDrop :
      context.drop count =
        partition.firstFrame :: partition.survivingContext := by
    calc
      context.drop count =
          (partition.crossedFrames ++
            partition.firstFrame :: partition.survivingContext).drop count :=
        congrArg (List.drop count) partition.contextEq
      _ = partition.firstFrame :: partition.survivingContext := by
        rw [← crossedFrameLength]
        simp
  rw [segmentsDrop, resourcesDrop, contextDrop] at suffix
  have head :=
    PLeaTTa.PrologSpinedSourceActivationBridge.SourceControlContextAgrees.head_shape
      (PLeaTTa.PrologProductResourceContextBridge.SourceControlResourceContextAgrees.control
        suffix)
  exact ⟨suffixBarrier, by simpa [head.1] using suffix⟩

private theorem stepsN_one
    {start finish : State} {events : List Observation}
    (step : Transition start events finish) :
    StepsN 1 start events finish := by
  simpa using
    (StepsN.succ 0 start finish finish events [] step (.zero finish))

/-! ## Exact ranked catch-up -/

/-- Cross an exact ranked prefix of empty outer predicate resources and
promote the first nonempty resource's source cursor.

For `k` crossed frames, the source performs every stored rejection step plus
exactly `k + 1` frame promotions: one into each crossed cursor and one final
promotion into `destination`.  Every completion is consumed by an enclosing
choice, so the complete public observation sequence is exactly empty. -/
theorem CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame
    {alpha : List (LogicVar × String)}
    {resources : List RetainedAlternativeSegment}
    {frames : ActiveProductContext} {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha resources frames rejectionSteps)
    (session : Session) (focus : Search)
    (focusCompleted :
      RawStep session focus [.completed] .none session
        (.terminal .completed))
    (destination : ActiveProductFrame)
    (surviving : ActiveProductContext)
    (destinationCursor : PreparedCursor)
    (destinationShape :
      destination.retained =
        .clauses destination.predicateScope destinationCursor) :
    StepsN (rejectionSteps + frames.length + 1)
      (.running session
        (ActiveProductContext.plug
          (frames ++ destination :: surviving) focus))
      []
      (.running session
        (ActiveProductContext.plug surviving
          (frameRetainedFrontier destination destinationCursor))) := by
  induction agreement generalizing focus destination surviving with
  | nil =>
      have promoted :=
        ActiveProductContext.promoteCompleted surviving destination session
          focus destinationCursor destinationShape focusCompleted
      simpa using stepsN_one promoted
  | cons resource resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail
      inductionHypothesis =>
      let continuation := frames ++ destination :: surviving
      have promoted :
          StepsN 1
            (.running session
              (ActiveProductContext.plug
                ((frame :: frames) ++ destination :: surviving) focus))
            []
            (.running session
              (ActiveProductContext.plug continuation
                (frameRetainedFrontier frame cursor))) := by
        have step :=
          ActiveProductContext.promoteCompleted continuation frame session
            focus cursor retainedShape focusCompleted
        simpa [continuation] using stepsN_one step
      have rejected :
          StepsN count
            (.running session
              (ActiveProductContext.plug continuation
                (frameRetainedFrontier frame cursor)))
            []
            (.running session
              (ActiveProductContext.plug continuation
                (frameRetainedFrontier frame finish))) :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
          pulls continuation frame session
      have finishCompleted :
          RawStep session (frameRetainedFrontier frame finish)
            [.completed] .none session (.terminal .completed) :=
        frameRetainedFrontier_exhausted session frame finish finishEmpty
      have rest :=
        inductionHypothesis (frameRetainedFrontier frame finish)
          finishCompleted destination surviving destinationShape
      have combined := StepsN.trans promoted (StepsN.trans rejected rest)
      simpa [continuation, List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using combined

/-- Cross every ranked empty outer predicate resource and terminate.

The same exact `rejectionSteps + frames.length + 1` count applies.  Unlike
the first-live case, there is no enclosing choice left to consume the final
predicate completion, so the ordered observation trace is exactly the
singleton `[.completed]`. -/
theorem CrossedEmptyResourceFramesAgrees.sourceCatchupTerminal
    {alpha : List (LogicVar × String)}
    {resources : List RetainedAlternativeSegment}
    {frames : ActiveProductContext} {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha resources frames rejectionSteps)
    (session : Session) (focus : Search)
    (focusCompleted :
      RawStep session focus [.completed] .none session
        (.terminal .completed)) :
    StepsN (rejectionSteps + frames.length + 1)
      (.running session (ActiveProductContext.plug frames focus))
      [.completed]
      (.terminal session .completed) := by
  induction agreement generalizing focus with
  | nil =>
      have transition :
          Transition (.running session focus) [.completed]
            (.terminal session .completed) :=
        .ordinary _ _ _ _ _ focusCompleted
      simpa using stepsN_one transition
  | cons resource resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail
      inductionHypothesis =>
      have promoted :
          StepsN 1
            (.running session
              (ActiveProductContext.plug (frame :: frames) focus))
            []
            (.running session
              (ActiveProductContext.plug frames
                (frameRetainedFrontier frame cursor))) := by
        have step :=
          ActiveProductContext.promoteCompleted frames frame session focus
            cursor retainedShape focusCompleted
        simpa using stepsN_one step
      have rejected :
          StepsN count
            (.running session
              (ActiveProductContext.plug frames
                (frameRetainedFrontier frame cursor)))
            []
            (.running session
              (ActiveProductContext.plug frames
                (frameRetainedFrontier frame finish))) :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
          pulls frames frame session
      have finishCompleted :
          RawStep session (frameRetainedFrontier frame finish)
            [.completed] .none session (.terminal .completed) :=
        frameRetainedFrontier_exhausted session frame finish finishEmpty
      have rest :=
        inductionHypothesis (frameRetainedFrontier frame finish)
          finishCompleted
      have combined := StepsN.trans promoted (StepsN.trans rejected rest)
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using combined

/-! ## First-live source/executable composition -/

/-- Exact source state after ranked catch-up has exposed the first live
outer predicate cursor. -/
def firstLiveSourceFrontier
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    Search :=
  ActiveProductContext.plug partition.survivingContext
    (frameRetainedFrontier partition.firstFrame partition.firstCursor)

/-- Exact executable state which the original eager `pull` has already
reached while the source is at `firstLiveSourceFrontier`.

Every field not named here is inherited from the predecessor configuration.
The first live marker remains in `alts`; only the crossed empty markers have
been removed from the barrier cache. -/
def firstLiveExecutableConf
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (pending : DemandDrivenCallStep.PendingCall)
    (predecessor : OpenConf)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (baseAlts : List PLeaTTa.Alt) : PLeaTTa.Conf :=
  { predecessor.toConf with
    cur := some (partition.goals, partition.binding)
    alts :=
      partition.tail ++ PLeaTTa.Alt.barrier ::
        flattenOwnedAlts partition.survivingResources baseAlts
    barriers :=
      popBarrierCacheN partition.crossedResources.length
        pending.outer.barriers }

/-- Fully composed first-live phase after an exhausted active predicate.

The partition is not treated as an alignment certificate: `suffixAlignment`
is derived from the original full source/control/resource zipper and retained
as an explicit field. -/
structure SpinedFirstLiveOuterResourceFrontierRelates
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
    (source : Search) (successor : OpenConf) : Prop where
  persistent :
    SessionRelatesPersistent freshFrontier opened.session
      successor.persistent
  queryTerm : successor.control.qterm = qterm
  frames : successor.frames = pending.frames
  suffixAlignment :
    SourceControlResourceContextAgrees alpha qterm suffixBarrier
      (partition.firstSegment :: partition.survivingSegments)
      (partition.first :: partition.survivingResources)
      partition.firstFrame.predicateScope
      (partition.firstFrame :: partition.survivingContext) outerScope
  sourceShape : source = firstLiveSourceFrontier partition
  executableExact :
    successor.toConf =
      firstLiveExecutableConf pending predecessor partition baseAlts

/-- Execute the exact source catch-up corresponding to one eager executable
pull which crosses a ranked empty prefix and installs the first live branch.

The executable does not step again: `successor` is the already-reached
body-failure successor.  Only the independent source consumes the hidden
finite prefix. -/
theorem SpinedExhaustedPostFailureOffsetRelates.catchupFirstLive
    {freshFrontier : FreshFrontierRelation}
    {alpha : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    (agreement :
      SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        segments qterm cursor active resources callerScope outerScope context
        baseAlts predecessor source successor)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    ∃ suffixBarrier,
      StepsN
          (partition.rejectionSteps +
            partition.crossedFrames.length + 1)
          (.running opened.session source)
          []
          (.running opened.session
            (firstLiveSourceFrontier partition)) ∧
        SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
          pending qterm outerScope suffixBarrier segments resources context
          baseAlts predecessor partition (firstLiveSourceFrontier partition)
          successor := by
  have focusCompleted :
      RawStep opened.session
        (sourceProductFrontier callerScope opened cursor callerReferences)
        [.completed] .none opened.session (.terminal .completed) :=
    sourceProductFrontier_exhausted callerScope opened cursor
      callerReferences agreement.exhausted.cursorEmpty
  have ranked :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame
      partition.crossedWork opened.session
      (sourceProductFrontier callerScope opened cursor callerReferences)
      focusCompleted partition.firstFrame partition.survivingContext
      partition.firstCursor partition.firstRetainedShape
  have sourceStart :
      source =
        ActiveProductContext.plug
          (partition.crossedFrames ++
            partition.firstFrame :: partition.survivingContext)
          (sourceProductFrontier callerScope opened cursor
            callerReferences) := by
    calc
      source =
          ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened cursor
              callerReferences) :=
        agreement.sourceShape
      _ =
          ActiveProductContext.plug
            (partition.crossedFrames ++
              partition.firstFrame :: partition.survivingContext)
            (sourceProductFrontier callerScope opened cursor
              callerReferences) :=
        congrArg
          (fun frames =>
            ActiveProductContext.plug frames
              (sourceProductFrontier callerScope opened cursor
                callerReferences))
          partition.contextEq
  have sourceSteps :
      StepsN
        (partition.rejectionSteps +
          partition.crossedFrames.length + 1)
        (.running opened.session source)
        []
        (.running opened.session
          (firstLiveSourceFrontier partition)) := by
    rw [sourceStart]
    simpa [firstLiveSourceFrontier] using ranked
  obtain ⟨suffixBarrier, suffixAlignment⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.OuterResourceCatchupPartition.alignedSuffix
      partition agreement.outerAlignment
  have prefixEmpty :
      ∀ resource ∈ partition.crossedResources, resource.alts = [] :=
    partition.crossedWork.all_empty
  let baseConf : PLeaTTa.Conf :=
    { predecessor.toConf with
      barriers := pending.outer.barriers }
  have exactPull :=
    pull_flattenOwnedAlts_first_nonempty_exact baseConf
      partition.crossedResources partition.first
      partition.survivingResources baseAlts partition.goals
      partition.binding partition.tail prefixEmpty partition.firstHead
  have bankRewrite :
      PLeaTTa.pull
          { predecessor.toConf with
            cur := none
            alts := flattenOwnedAlts resources baseAlts
            barriers := pending.outer.barriers } =
        PLeaTTa.pull
          { predecessor.toConf with
            cur := none
            alts :=
              flattenOwnedAlts
                (partition.crossedResources ++
                  partition.first :: partition.survivingResources)
                baseAlts
            barriers := pending.outer.barriers } :=
    congrArg
      (fun alts =>
        PLeaTTa.pull
          { predecessor.toConf with
            cur := none
            alts := alts
            barriers := pending.outer.barriers })
      (congrArg (fun items => flattenOwnedAlts items baseAlts)
        partition.resourcesEq)
  have executableExact :
      successor.toConf =
        firstLiveExecutableConf pending predecessor partition baseAlts := by
    calc
      successor.toConf =
          PLeaTTa.pull
            { predecessor.toConf with
              cur := none
              alts := flattenOwnedAlts resources baseAlts
              barriers := pending.outer.barriers } :=
        agreement.successorExact
      _ =
          PLeaTTa.pull
            { predecessor.toConf with
              cur := none
              alts :=
                flattenOwnedAlts
                  (partition.crossedResources ++
                    partition.first :: partition.survivingResources)
                  baseAlts
              barriers := pending.outer.barriers } :=
        bankRewrite
      _ =
          firstLiveExecutableConf pending predecessor partition baseAlts := by
        simpa [baseConf, firstLiveExecutableConf] using exactPull
  exact
    ⟨suffixBarrier, sourceSteps,
      ⟨agreement.persistent, agreement.queryTerm, agreement.frames,
        suffixAlignment, rfl, executableExact⟩⟩

/-! ## All-terminal source/executable composition -/

/-- Exact executable core after every local resource and the arbitrary base
bank have produced no branch.

The cache result is intentionally taken from the tracked traversal of the
base after the exact local-marker prefix.  The base may itself contain
markers, so replacing this field with only `resources.length` pops would be
incorrect. -/
def terminalOuterExecutableConf
    (pending : DemandDrivenCallStep.PendingCall)
    (predecessor : OpenConf)
    (resources : List RetainedAlternativeSegment)
    (baseAlts : List PLeaTTa.Alt) : PLeaTTa.Conf :=
  let outcome :=
    PLeaTTa.pullAuxTracked
      (popBarrierCacheN resources.length pending.outer.barriers) baseAlts
  { predecessor.toConf with
    cur := none
    alts := []
    barriers := outcome.2 }

/-- Fully composed local-core terminal phase.

`coreTerminal` is deliberately the sealed core predicate.  Fine executable
frames are preserved and may still need their own exit transition, so this
relation does not claim `DemandDrivenStep.Terminal successor`. -/
structure SpinedTerminalOuterResourceCatchupRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (callerBarrier : Nat)
    (callerScope outerScope : CutScopeId)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        baseAlts)
    (successor : OpenConf) : Prop where
  persistent :
    SessionRelatesPersistent freshFrontier opened.session
      successor.persistent
  queryTerm : successor.control.qterm = qterm
  frames : successor.frames = pending.frames
  originalAlignment :
    SourceControlResourceContextAgrees alpha qterm callerBarrier segments
      resources callerScope context outerScope
  executableExact :
    successor.toConf =
      terminalOuterExecutableConf pending predecessor resources baseAlts
  coreTerminal : PLeaTTa.Terminal successor.toConf

/-- Execute all hidden source work when the eager executable pull reaches no
branch at all.

The source finishes with one visible completion.  The executable does not
step again; its exact terminal core is the successor already reached by the
body-failure transition. -/
theorem SpinedExhaustedPostFailureOffsetRelates.catchupTerminal
    {freshFrontier : FreshFrontierRelation}
    {alpha : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    (agreement :
      SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        segments qterm cursor active resources callerScope outerScope context
        baseAlts predecessor source successor)
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        baseAlts) :
    StepsN
        (partition.rejectionSteps + context.length + 1)
        (.running opened.session source)
        [.completed]
        (.terminal opened.session .completed) ∧
      SpinedTerminalOuterResourceCatchupRelates freshFrontier alpha opened
        pending qterm callerBarrier callerScope outerScope segments resources
        context baseAlts predecessor partition successor := by
  have focusCompleted :
      RawStep opened.session
        (sourceProductFrontier callerScope opened cursor callerReferences)
        [.completed] .none opened.session (.terminal .completed) :=
    sourceProductFrontier_exhausted callerScope opened cursor
      callerReferences agreement.exhausted.cursorEmpty
  have ranked :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupTerminal
      partition.crossedWork opened.session
      (sourceProductFrontier callerScope opened cursor callerReferences)
      focusCompleted
  have sourceSteps :
      StepsN
        (partition.rejectionSteps + context.length + 1)
        (.running opened.session source)
        [.completed]
        (.terminal opened.session .completed) := by
    rw [agreement.sourceShape]
    exact ranked
  have allEmpty :
      ∀ resource ∈ resources, resource.alts = [] :=
    partition.crossedWork.all_empty
  have trackedPrefix :=
    pullAuxTracked_flattenOwnedAlts_all_empty pending.outer.barriers
      resources baseAlts allEmpty
  let baseOutcome :=
    PLeaTTa.pullAuxTracked
      (popBarrierCacheN resources.length pending.outer.barriers) baseAlts
  have baseNone : baseOutcome.1 = none := by
    dsimp [baseOutcome]
    rw [PLeaTTa.pullAuxTracked_fst, partition.baseTerminal]
  have pullExact :
      PLeaTTa.pull
          { predecessor.toConf with
            cur := none
            alts := flattenOwnedAlts resources baseAlts
            barriers := pending.outer.barriers } =
        terminalOuterExecutableConf pending predecessor resources
          baseAlts := by
    unfold PLeaTTa.pull
    rw [trackedPrefix]
    unfold terminalOuterExecutableConf
    dsimp only
    rw [baseNone]
  have executableExact :
      successor.toConf =
        terminalOuterExecutableConf pending predecessor resources
          baseAlts :=
    agreement.successorExact.trans pullExact
  have coreTerminal : PLeaTTa.Terminal successor.toConf := by
    rw [executableExact]
    exact ⟨rfl, rfl⟩
  exact
    ⟨sourceSteps,
      ⟨agreement.persistent, agreement.queryTerm, agreement.frames,
        agreement.outerAlignment, executableExact, coreTerminal⟩⟩

/-! ## Automatic three-way catch-up -/

/-- Exhaustive result after classifying the local resource spine and the
arbitrary older executable base.

The base-live constructor intentionally carries no source transition.  That
older bank is outside the locally owned resource zipper, so its source
correspondence remains an explicit boundary rather than being inferred from
an executable answer. -/
inductive ExhaustedPostFailureCatchupResult
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (callerBarrier : Nat)
    (callerScope outerScope : CutScopeId)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (source : Search) (successor : OpenConf) : Prop where
  | firstLive
      (partition :
        OuterResourceCatchupPartition alpha segments resources context)
      (suffixBarrier : Nat)
      (sourceSteps :
        StepsN
          (partition.rejectionSteps +
            partition.crossedFrames.length + 1)
          (.running opened.session source)
          []
          (.running opened.session
            (firstLiveSourceFrontier partition)))
      (relation :
        SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
          pending qterm outerScope suffixBarrier segments resources context
          baseAlts predecessor partition (firstLiveSourceFrontier partition)
          successor) :
      ExhaustedPostFailureCatchupResult freshFrontier alpha opened pending
        qterm callerBarrier callerScope outerScope segments resources context
        baseAlts predecessor source successor
  | baseLive
      (partition :
        BaseLiveOuterResourceCatchupPartition alpha segments resources context
          baseAlts) :
      ExhaustedPostFailureCatchupResult freshFrontier alpha opened pending
        qterm callerBarrier callerScope outerScope segments resources context
        baseAlts predecessor source successor
  | terminal
      (partition :
        TerminalOuterResourceCatchupPartition alpha segments resources context
          baseAlts)
      (sourceSteps :
        StepsN
          (partition.rejectionSteps + context.length + 1)
          (.running opened.session source)
          [.completed]
          (.terminal opened.session .completed))
      (relation :
        SpinedTerminalOuterResourceCatchupRelates freshFrontier alpha opened
          pending qterm callerBarrier callerScope outerScope segments resources
          context baseAlts predecessor partition successor) :
      ExhaustedPostFailureCatchupResult freshFrontier alpha opened pending
        qterm callerBarrier callerScope outerScope segments resources context
        baseAlts predecessor source successor

/-- Automatically classify and execute every locally owned catch-up case.

No caller supplies a hand-built partition.  The local-live and terminal
branches immediately consume the generated partition through the existing
exact source/executable catch-up proofs; a live arbitrary base is returned as
the explicit uncomposed boundary. -/
theorem SpinedExhaustedPostFailureOffsetRelates.catchupClassified
    {freshFrontier : FreshFrontierRelation}
    {alpha : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    (agreement :
      SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        segments qterm cursor active resources callerScope outerScope context
        baseAlts predecessor source successor) :
    ExhaustedPostFailureCatchupResult freshFrontier alpha opened pending qterm
      callerBarrier callerScope outerScope segments resources context baseAlts
      predecessor source successor := by
  cases
      PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge.SourceControlResourceContextAgrees.classifyCatchup
        agreement.outerAlignment baseAlts with
  | firstLive partition =>
      obtain ⟨suffixBarrier, sourceSteps, relation⟩ :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.SpinedExhaustedPostFailureOffsetRelates.catchupFirstLive
          agreement partition
      exact .firstLive partition suffixBarrier sourceSteps relation
  | baseLive partition =>
      exact .baseLive partition
  | terminal partition =>
      obtain ⟨sourceSteps, relation⟩ :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.SpinedExhaustedPostFailureOffsetRelates.catchupTerminal
          agreement partition
      exact .terminal partition sourceSteps relation

end PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge
