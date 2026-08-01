-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetainedPayloadActivationBridge
Purpose: Reactivate one retained local-clause payload from the actual current
  source cursor and fine executable configuration, without reconstructing a
  historical call-entry state.
Trusted boundary: none
Main exports:
  ConfBelowResolutionCounter.resolutionOccupied_of_selectedEquality,
  SelectedHeadActivationChronology,
  SelectedHeadActivationChronology.restoreSnapshot,
  RetainedCallPayloadSnapshot.activateSelectedHead
-/
import PLeaTTa.Proofs.PrologRetainedPayloadCatchupBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceActivationBridge

namespace PLeaTTa.PrologRetainedPayloadActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeActivationBridge
open PrologRepresentativeTaskActivationBridge
open PrologRetainedPayloadCatchupBridge
open PrologRetainedPayloadSnapshotBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
The executable eager pull has already replaced the retained call with a
clause-head equality.  Therefore reactivation must use the current equality
configuration as its machine predecessor.  A historical `PendingCall` would
restore stale world, counter, frames, or alternatives after nested execution.

The frozen snapshot supplies only logical payload data.  Current persistent
state and all backtrackable machine ownership remain in the actual
`OpenConf`.
-/

/-! ## Current-state resolver high-water -/

/-- The selected full-head equality contains every old call variable needed
by the clause-copy resolver input.

The copied clause contributes additional freshly allocated names, but the
resolver's *input* high-water is over the raw caller arguments/result,
continuation, carried binding, and observable query.  All are visibly present
in the current configuration; no call-entry configuration is required. -/
theorem ConfBelowResolutionCounter.resolutionOccupied_of_selectedEquality
    {conf : PLeaTTa.Conf}
    (below : ConfBelowResolutionCounter conf)
    (args : List Atom) (res : Atom) (copied : PLeaTTa.Clause)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (current :
      conf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ rest,
            binding)) :
    resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) res rest binding conf.qterm) ≤
      conf.counter := by
  apply Nat.le_trans
    (resolutionSeedHighWaterNames_le_of_subset (right := resolutionLiveVars conf)
      ?_)
  exact below
  intro name member
  unfold resolutionOccupiedVars at member
  simp only [List.mem_append] at member
  rcases member with
      ((((substituted | result) | continuation) | carried) | query)
  · rcases substAtomList_vars_origin binding args name substituted with
      raw | fromBinding
    · have rawWitness : ∃ atom ∈ args, name ∈ atom.vars :=
        List.mem_flatMap.mp raw
      simp [resolutionLiveVars, current, PLeaTTa.specializationGoalsVars,
        PLeaTTa.specializationGoalVars, Metta.Atom.vars, rawWitness]
    · have bindingWitness :
          ∃ source value, (source, value) ∈ binding ∧
            (name = source ∨ name ∈ value.vars) := by
        simpa [resolutionSubstVars, List.mem_flatMap] using fromBinding
      simp [resolutionLiveVars, current, PLeaTTa.specializationGoalsVars,
        PLeaTTa.specializationGoalVars, resolutionSubstVars, bindingWitness]
  · simp [resolutionLiveVars, current, PLeaTTa.specializationGoalsVars,
      PLeaTTa.specializationGoalVars, Metta.Atom.vars, result]
  · simp [resolutionLiveVars, current, PLeaTTa.specializationGoalsVars,
      PLeaTTa.specializationGoalVars, continuation]
  · simp [resolutionLiveVars, current, PLeaTTa.specializationGoalsVars,
      PLeaTTa.specializationGoalVars, resolutionSubstVars, carried]
  · simp [resolutionLiveVars, current, query]

/-! ## Entry-free selected-head activation -/

/-- The two independent chronology facts intentionally weakened when a
retained head is pulled eagerly.

The dependent `snapshot` is already indexed by the consumed executable
resource and the one-head-advanced source cursor.  Its immutable payload is
still exact, but its source/query lower bounds and executable allocation-gap
floor have advanced.  Reactivating the selected head needs the corresponding
pre-pull bounds.  The old source query bound follows from the retained gap,
alpha inclusion, and the consumed snapshot's advanced bound.  Keeping the
independent bounds in one token is strictly weaker than
retaining a historical machine state: no world, database, frame, alternative
bank, or live allocator occurs here. -/
structure SelectedHeadActivationChronology
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {branchTail : List ClauseBranch}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment} {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support
        (afterPulledHead resource remainingAlts)
        (finish.advance branch branchTail) caller outer) : Prop where
  allocationGap :
    AlphaAllocationGap currentAlpha finish.reservationStart
      finish.reservedUntil resource.counter resource.finalCounter
  queryExecutableBelow :
    resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (resource.args.map (PLeaTTa.subst resource.binding))
          resource.res resource.rest resource.binding resource.qterm) ≤
      resource.counter

namespace SelectedHeadActivationChronology

/-- Consume one exact retained head while keeping the stronger chronology
needed to activate that same head.

The returned token and consumed snapshot are definitionally produced from
one pre-pull snapshot; no independent existential can pair bounds from one
payload with logical data from another. -/
def ofBeforePull
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment} {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource finish caller
        outer)
    (offset :
      PulledHeadOffsetAgrees currentAlpha finish branch clause branchTail
        copied resource remainingAlts) :
    SelectedHeadActivationChronology
      (RetainedCallPayloadSnapshot.afterPulledHead remainingAlts
        (RetainedCallPayloadSnapshot.transportCursor
          ((CursorCallContext.refl finish).advance branch branchTail)
          (RetainedCallPayloadSnapshot.advance_reservationStart_le
            offset.cursorWellFormed offset.cursorRemaining)
          rfl snapshot)) :=
  { allocationGap := snapshot.allocationGap
    queryExecutableBelow := snapshot.queryExecutableBelow }

/-- Counted conservative rejections followed by one eager retained-head pull
produce the exact consumed snapshot and its activation chronology together. -/
def ofRejectedPullsAndBeforePull
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before finish : PreparedCursor}
    {count : Nat}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment} {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer)
    (beforeWellFormed : before.WellFormed)
    (pulls : RejectedPullsN count before finish)
    (offset :
      PulledHeadOffsetAgrees currentAlpha finish branch clause branchTail
        copied resource remainingAlts) :
    SelectedHeadActivationChronology
      (RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead snapshot
        beforeWellFormed pulls offset) := by
  exact
    ofBeforePull
      (RetainedCallPayloadSnapshot.afterRejectedPulls snapshot beforeWellFormed
        pulls)
      offset

/-- Recover the immutable logical snapshot immediately before the eager head
pull.

This construction is sound only because `chronology` supplies the exact
strong bounds which the consumed snapshot deliberately no longer contains.
All payload fields are inherited from `snapshot`; operational state is absent
from both the premise and conclusion. -/
def restoreSnapshot
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment} {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support
        (afterPulledHead resource remainingAlts)
        (finish.advance branch branchTail) caller outer)
    (chronology : SelectedHeadActivationChronology snapshot)
    (offset :
      PulledHeadOffsetAgrees currentAlpha finish branch clause branchTail
        copied resource remainingAlts) :
    RetainedCallPayloadSnapshot currentAlpha support resource finish caller
      outer := by
  refine
    { snapshotAlpha := snapshot.snapshotAlpha
      canonical := snapshot.canonical
      referenceBase := snapshot.referenceBase
      referencePayload := snapshot.referencePayload
      alphaIncluded := snapshot.alphaIncluded
      allocationGap := chronology.allocationGap
      cursorArguments := ?_
      residualRepresentative := snapshot.residualRepresentative
      cumulative := by
        simpa [afterPulledHead] using snapshot.cumulative
      materialized := by
        simpa [PreparedCursor.advance, afterPulledHead] using
          snapshot.materialized
      queryReferenceBelow := ?_
      queryExecutableBelow := chronology.queryExecutableBelow
      resourceRest := ?_
      payload := ?_ }
  · simpa [PreparedCursor.advance] using snapshot.cursorArguments
  · intro index member
    rcases List.mem_map.mp member with
      ⟨pair, pairMember, pairIdentity⟩
    have currentMember :
        .generated index ∈ currentAlpha.map Prod.fst := by
      exact List.mem_map.mpr
        ⟨pair, snapshot.alphaIncluded pair pairMember, pairIdentity⟩
    rcases chronology.allocationGap.1 index currentMember with below | above
    · exact below
    · have advancedBelow := snapshot.queryReferenceBelow index member
      have branchMember : branch ∈ finish.remaining := by
        rw [offset.cursorRemaining]
        simp
      have advancedStartLe :
          (finish.advance branch branchTail).reservationStart ≤
            finish.reservedUntil := by
        simpa [PreparedCursor.advance] using
          offset.cursorWellFormed.1.member_next_le_final branchMember
      omega
  · simpa [afterPulledHead] using snapshot.resourceRest
  · simpa [PreparedCursor.advance, afterPulledHead] using snapshot.payload

end SelectedHeadActivationChronology

/-- Activate the retained head using only its frozen payload and the actual
current source/executable states.

No `OpenedCall`, call-entry `OpenConf`, or `PendingCall` occurs in the
statement.  The copied-clause seed is justified by the snapshot's exact
old-seed bound; persistent state, frames, alternatives, and the current
counter come exclusively from `state`. -/
theorem RetainedCallPayloadSnapshot.activateSelectedHead
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment} {outer : List ControlSegment}
    {scope : CutScopeId} {session : Session}
    {state : OpenConf} {independentResult : Substitution}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource finish caller
        outer)
    (offset :
      PulledHeadOffsetAgrees currentAlpha finish branch clause branchTail
        copied resource remainingAlts)
    (currentHead :
      state.control.cur =
        some
          (PLeaTTa.Goal.eq
                (.expr (resource.args ++ [resource.res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ resource.rest,
            resource.binding))
    (currentQuery : state.control.qterm = resource.qterm)
    (currentShared : SharedRuntimeAlpha currentAlpha)
    (currentPersistent :
      SessionRelatesPersistent (AlphaFreshFrontier currentAlpha) session
        state.persistent)
    (cursorDominated :
      finish.reservedUntil ≤ session.resolver.nextFresh)
    (resourceDominated :
      resource.finalCounter ≤ state.persistent.counter)
    (below : ConfBelowResolutionCounter state.toConf)
    (live :
      AlphaRuntimeNamesLive support
        (copied.body ++ resource.rest) resource.qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ representative nextAlpha sourceCanonical flattened installed,
      SharedRuntimeAlpha nextAlpha ∧
      (∀ pair, pair ∈ currentAlpha → pair ∈ nextAlpha) ∧
      AlphaExtendsAbove currentAlpha nextAlpha branch.firstFresh
        resource.counter ∧
      AlphaFreshFrontier nextAlpha session.resolver.nextFresh
        state.persistent.counter ∧
      independentResult =
        TreeSubstitution.reify
            (sourceCanonical ++ snapshot.canonical) ++
          snapshot.referenceBase ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      RawStep session (.clauses scope finish) [] .none session
        (.running
          (.choice scope
            (.task scope branch.body independentResult)
            (.clauses scope (finish.advance branch branchTail)))) ∧
      PLeaTTa.Step prog gt state.toConf
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).toConf ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready
          (unifySuccessor state (copied.body ++ resource.rest)
            installed)) ∧
      AlphaCumulativeResidualVariantAgreesOnWith
        nextAlpha support (sourceCanonical ++ snapshot.canonical)
        snapshot.referenceBase
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          resource.qterm installed)
        (flattened ++ representative) ∧
      TaskPayloadAgrees nextAlpha support resource.barrier
        (sourceCanonical ++ snapshot.canonical) snapshot.referenceBase
        independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          resource.qterm installed)
        branch.body copied.body ∧
      Nonempty (RetainedCallPayloadSnapshot nextAlpha support
        (afterPulledHead resource remainingAlts)
        (finish.advance branch branchTail) caller outer) ∧
      ConfBelowResolutionCounter
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).toConf ∧
      (unifySuccessor state (copied.body ++ resource.rest)
          installed).persistent = state.persistent ∧
      (unifySuccessor state (copied.body ++ resource.rest)
          installed).frames = state.frames ∧
      (unifySuccessor state (copied.body ++ resource.rest)
          installed).control.alts = state.control.alts := by
  obtain ⟨representative, oldCumulative, query⟩ :=
    snapshot.representative
  have cursorBindingShape :
      finish.bindings =
        TreeSubstitution.reify snapshot.canonical ++
          snapshot.referenceBase :=
    snapshot.sourceBindingShape
  have member : branch ∈ finish.remaining := by
    rw [offset.cursorRemaining]
    simp
  have arity : clause.params.length = resource.args.length := by
    calc
      clause.params.length = resource.argsv.length := offset.arity
      _ = (resource.args.map
            (PLeaTTa.subst resource.binding)).length :=
        congrArg List.length offset.substitutedArgs
      _ = resource.args.length := List.length_map ..
  have copiedExact :
      copied =
        PLeaTTa.freshenResolutionClause
          (resource.args.map (PLeaTTa.subst resource.binding))
          resource.args resource.res resource.rest resource.binding
          resource.qterm resource.counter resource.barrier clause := by
    simpa only [offset.substitutedArgs] using offset.copiedExact
  have exactLive :
      AlphaRuntimeNamesLive support
        ((PLeaTTa.freshenResolutionClause
            (resource.args.map (PLeaTTa.subst resource.binding))
            resource.args resource.res resource.rest resource.binding
            resource.qterm resource.counter resource.barrier clause).body ++
          resource.rest)
        resource.qterm := by
    rw [← copiedExact]
    exact live
  have referenceEnd :
      branch.nextFresh ≤ session.resolver.nextFresh := by
    exact Nat.le_trans
      (offset.cursorWellFormed.1.member_next_le_final member)
      cursorDominated
  have seedReserved :
      resource.counter + 1 ≤ resource.finalCounter := by
    rcases offset.tailOwnership with
      ⟨_callStart, _position, tailOwnership⟩
    rcases tailOwnership.scan with
      ⟨_candidates, _wellFormed, _query, _substitutedArgs, _supported,
        _arities, scan⟩
    have scanExact := scan.counter_exact
    simpa only [afterPulledHead_counter, afterPulledHead_finalCounter] using
      (show
        (afterPulledHead resource remainingAlts).counter ≤
          (afterPulledHead resource remainingAlts).finalCounter by
        omega)
  have executableEnd :
      resource.counter + 1 ≤ state.persistent.counter :=
    Nat.le_trans seedReserved resourceDominated
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, generated, installed,
      nextShared, alphaIncluded, extensionAbove, freshFrontier, allocationGap,
      independentShape,
      sourceOrdered, _generatedExact, installedExact, _generatedAgreement,
      successorCumulative, successorTask, _materializedHeads⟩ :=
    PLeaTTa.PrologRepresentativeTaskActivationBridge.SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution_extension
      oldCumulative query cursorBindingShape
      snapshot.callPayload.canonicalWellFormed offset.cursorWellFormed member
      offset.supported arity snapshot.alphaIncluded currentShared
      snapshot.queryReferenceBelow snapshot.queryExecutableBelow
      currentPersistent.fresh referenceEnd executableEnd
      snapshot.allocationGap seedReserved exactLive resolved
  have sourceStep :
      RawStep session (.clauses scope finish) [] .none session
        (.running
          (.choice scope
            (.task scope branch.body independentResult)
            (.clauses scope (finish.advance branch branchTail)))) := by
    have pulled :
        LocalPull finish
          (.reply (branch.enter independentResult)
            (finish.advance branch branchTail)) :=
      .matched finish branch branchTail independentResult
        offset.cursorRemaining resolved
    simpa [ClauseBranch.enter] using
      (matched_clause_splices_body_first scope session pulled)
  have currentConf :
      state.toConf.cur =
        some
          (PLeaTTa.Goal.eq
                (.expr (resource.args ++ [resource.res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ resource.rest,
            resource.binding) := by
    simpa [OpenConf.toConf, Control.toConf] using currentHead
  have installedCopied :
      PLeaTTa.unifyB resource.binding
          (.expr (resource.args ++ [resource.res]))
          (.expr (copied.params ++ [copied.result])) =
        some installed := by
    simpa only [copiedExact] using installedExact
  have sealedStep :
      PLeaTTa.Step prog gt state.toConf
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).toConf := by
    simpa [unifySuccessor] using
      (PLeaTTa.Step.eq_ok state.toConf
        (.expr (resource.args ++ [resource.res]))
        (.expr (copied.params ++ [copied.result]))
        (copied.body ++ resource.rest) resource.binding installed
        currentConf installedCopied)
  have fineStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready
          (unifySuccessor state (copied.body ++ resource.rest)
            installed)) := by
    exact
      executable_unify_step state
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.equality
        (.expr (resource.args ++ [resource.res]))
        (.expr (copied.params ++ [copied.result]))
        (copied.body ++ resource.rest) resource.binding installed
        (by simpa
          [NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
            currentHead)
        installedCopied
  have cumulativeCopied :
      AlphaCumulativeResidualVariantAgreesOnWith
        nextAlpha support (sourceCanonical ++ snapshot.canonical)
        snapshot.referenceBase
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          resource.qterm installed)
        (flattened ++ representative) := by
    simpa only [copiedExact] using successorCumulative
  have taskCopied :
      TaskPayloadAgrees nextAlpha support resource.barrier
        (sourceCanonical ++ snapshot.canonical) snapshot.referenceBase
        independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          resource.qterm installed)
        branch.body copied.body := by
    simpa only [copiedExact] using successorTask
  have advancedContext :
      CursorCallContext (finish.advance branch branchTail)
        finish.callGeneration finish.predicate finish.arguments
        finish.bindings :=
    (CursorCallContext.refl finish).advance branch branchTail
  have snapshotAtAdvanced :
      RetainedCallPayloadSnapshot currentAlpha support resource
        (finish.advance branch branchTail) caller outer :=
    RetainedCallPayloadSnapshot.transportCursor advancedContext
      (RetainedCallPayloadSnapshot.advance_reservationStart_le
        offset.cursorWellFormed offset.cursorRemaining)
      rfl
      snapshot
  have consumedSnapshot :
      RetainedCallPayloadSnapshot currentAlpha support
        (afterPulledHead resource remainingAlts)
        (finish.advance branch branchTail) caller outer :=
    RetainedCallPayloadSnapshot.afterPulledHead remainingAlts
      snapshotAtAdvanced
  have nextSnapshot :
      RetainedCallPayloadSnapshot nextAlpha support
        (afterPulledHead resource remainingAlts)
        (finish.advance branch branchTail) caller outer :=
    consumedSnapshot.mono alphaIncluded (by
      simpa [PreparedCursor.advance, afterPulledHead] using allocationGap)
  have successorBelow :
      ConfBelowResolutionCounter
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).toConf :=
    sealedStep.preserves_belowResolutionCounter below
  have cumulativeAtStateQuery :
      AlphaCumulativeResidualVariantAgreesOnWith
        nextAlpha support (sourceCanonical ++ snapshot.canonical)
        snapshot.referenceBase
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        (flattened ++ representative) := by
    simpa [currentQuery] using cumulativeCopied
  have taskAtStateQuery :
      TaskPayloadAgrees nextAlpha support resource.barrier
        (sourceCanonical ++ snapshot.canonical) snapshot.referenceBase
        independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        branch.body copied.body := by
    simpa [currentQuery] using taskCopied
  refine
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      nextShared, alphaIncluded, extensionAbove, freshFrontier,
      independentShape,
      sourceOrdered, sourceStep, sealedStep, fineStep, cumulativeCopied,
      taskCopied, ⟨nextSnapshot⟩, successorBelow, ?_, ?_, ?_⟩
  · exact unifySuccessor_persistent state _ installed
  · rfl
  · rfl

/-! ## Anti-vacuity: the two chronology fields are independent -/

/-- An allocation gap constrains only names represented in the alpha graph;
it does not bound every runtime name currently occupied by the selected
resource.

Here the graph's historical compact seed `1` lies below executable floor `2`,
so the allocation gap holds.  The actual result atom contains compact seed
`2`, whose high-water is `3`, so the independent occupied-runtime bound at
floor `2` fails. -/
theorem allocationGap_does_not_bound_occupiedRuntime :
    AlphaAllocationGap
        [(.source "x", "x" ++ resolutionCompactSuffix 1)]
        0 0 2 3 ∧
      ¬ resolutionSeedHighWaterNames
          (resolutionOccupiedVars []
            (.var ("x" ++ resolutionCompactSuffix 2))
            [] [] (.sym "query")) ≤
        2 := by
  constructor
  · constructor
    · intro index member
      simp at member
    · intro name member
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
      subst name
      rw [resolutionSeedHighWaterName_append_compact]
      exact Or.inl (Nat.le_refl 2)
  · intro bounded
    have occupied :
        "x" ++ resolutionCompactSuffix 2 ∈
          resolutionOccupiedVars []
            (.var ("x" ++ resolutionCompactSuffix 2))
            [] [] (.sym "query") := by
      unfold resolutionOccupiedVars
      simp [PLeaTTa.specializationGoalsVars, Metta.Atom.vars]
    have nameBound :=
      (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ 2).mp bounded
        ("x" ++ resolutionCompactSuffix 2) occupied
    rw [resolutionSeedHighWaterName_append_compact] at nameBound
    omega

end PLeaTTa.PrologRetainedPayloadActivationBridge
