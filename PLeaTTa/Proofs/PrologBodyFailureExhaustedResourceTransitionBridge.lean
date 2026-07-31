-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologBodyFailureExhaustedResourceTransitionBridge
Purpose: Preserve exact resource ownership when primitive body failure
  exhausts the active local predicate.
Trusted boundary: none
Main exports:
  pullAux_flattenOwnedAlts_first_nonempty,
  flattenOwnedAlts_first_nonempty_barrierCount,
  ExhaustedCursorOffsetAgrees
-/
import PLeaTTa.Proofs.PrologBodyFailureResourceTransitionBridge

namespace PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PLeaTTa.PrologBooleanAliasSafety
open PrologActivationMacro
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureBacktrackingBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologHeadFailureContinuationBridge
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologPrefilterScanBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedCursorOwnershipBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
When the active local predicate has no retained executable alternative, the
single executable `pull` skips its marker and may continue across arbitrarily
many empty outer predicate regions.  The independent source has not performed
that unwinding yet: it still contains the exhausted `.clauses` cursor.

This module first characterizes the actual executable list traversal.  It
then records the source/executable phase offset explicitly.  A later
finite-prefix catch-up theorem will consume the same maximal empty-prefix
partition; no theorem here equates one executable pull with one source step.
-/

/-! ## Exact pull across a maximal empty resource prefix -/

/-- The real executable `pullAux` skips exactly the markers belonging to an
explicit empty resource prefix, then selects the first branch of the first
nonempty resource.

The theorem is about `PLeaTTa.pullAux` itself.  It does not introduce a
parallel traversal or classify an answer after the fact. -/
theorem pullAux_flattenOwnedAlts_first_nonempty
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    PLeaTTa.pullAux
        (flattenOwnedAlts (emptyPrefix ++ first :: rest) base) =
      some
        ((goals, binding),
          tail ++ PLeaTTa.Alt.barrier :: flattenOwnedAlts rest base) := by
  induction emptyPrefix with
  | nil =>
      rw [List.nil_append, flattenOwnedAlts_cons, firstHead]
      rfl
  | cons resource resources inductionHypothesis =>
      have headEmpty : resource.alts = [] :=
        prefixEmpty resource (by simp)
      have tailEmpty :
          ∀ item ∈ resources, item.alts = [] := by
        intro item member
        exact prefixEmpty item (by simp [member])
      rw [List.cons_append, flattenOwnedAlts_cons, headEmpty]
      exact inductionHypothesis tailEmpty

/-- A successful `pullAux` result fixes the concrete machine pull's current
branch and remaining alternative bank.  The barrier cache may change, but it
cannot change either of these two fields. -/
theorem pull_cur_alts_of_pullAux_some
    (conf : PLeaTTa.Conf)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (rest : List PLeaTTa.Alt)
    (outcome :
      PLeaTTa.pullAux conf.alts = some ((goals, binding), rest)) :
    (PLeaTTa.pull conf).cur = some (goals, binding) ∧
      (PLeaTTa.pull conf).alts = rest := by
  unfold PLeaTTa.pull
  generalize trackedEq :
    PLeaTTa.pullAuxTracked conf.barriers conf.alts = tracked
  rcases tracked with ⟨branch, cache⟩
  have branchEq :=
    PLeaTTa.pullAuxTracked_fst conf.barriers conf.alts
  rw [trackedEq, outcome] at branchEq
  change branch = some ((goals, binding), rest) at branchEq
  subst branch
  exact ⟨rfl, rfl⟩

/-- The maximal-prefix characterization determines the actual pulled branch
and exact post-pull alternative suffix, not merely the auxiliary outcome. -/
theorem pull_flattenOwnedAlts_first_nonempty_cur_alts
    (conf : PLeaTTa.Conf)
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (restResources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    let before :=
      { conf with
        cur := none
        alts :=
          flattenOwnedAlts
            (emptyPrefix ++ first :: restResources) base }
    (PLeaTTa.pull before).cur = some (goals, binding) ∧
      (PLeaTTa.pull before).alts =
        tail ++ PLeaTTa.Alt.barrier ::
          flattenOwnedAlts restResources base := by
  dsimp only
  apply pull_cur_alts_of_pullAux_some
  simpa using
    pullAux_flattenOwnedAlts_first_nonempty emptyPrefix first restResources
      base goals binding tail prefixEmpty firstHead

/-- A first nonempty outer resource rules out the terminal pull outcome. -/
theorem pullAux_flattenOwnedAlts_first_nonempty_not_terminal
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    PLeaTTa.pullAux
        (flattenOwnedAlts (emptyPrefix ++ first :: rest) base) ≠ none := by
  rw [pullAux_flattenOwnedAlts_first_nonempty emptyPrefix first rest base
    goals binding tail prefixEmpty firstHead]
  simp

/-- If every local resource bank is empty, the real executable traversal
crosses exactly their markers and continues with the arbitrary base bank. -/
theorem pullAux_flattenOwnedAlts_all_empty
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (allEmpty : ∀ resource ∈ resources, resource.alts = []) :
    PLeaTTa.pullAux (flattenOwnedAlts resources base) =
      PLeaTTa.pullAux base := by
  induction resources with
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
      exact inductionHypothesis tailEmpty

/-- All empty local resources over a terminal base produce the genuine
terminal `pullAux` outcome. -/
theorem pullAux_flattenOwnedAlts_all_empty_terminal
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (allEmpty : ∀ resource ∈ resources, resource.alts = [])
    (baseTerminal : PLeaTTa.pullAux base = none) :
    PLeaTTa.pullAux (flattenOwnedAlts resources base) = none := by
  rw [pullAux_flattenOwnedAlts_all_empty resources base allEmpty]
  exact baseTerminal

/-- Pulling through a maximal empty prefix preserves the first nonempty
resource's marker.  The executable barrier-count drop is therefore exactly
the number of skipped empty resource descriptors, not one more. -/
theorem flattenOwnedAlts_first_nonempty_barrierCount
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    PLeaTTa.barrierCount
        (flattenOwnedAlts (emptyPrefix ++ first :: rest) base) =
      PLeaTTa.barrierCount
          (tail ++ PLeaTTa.Alt.barrier :: flattenOwnedAlts rest base) +
        emptyPrefix.length := by
  induction emptyPrefix with
  | nil =>
      simp [firstHead]
  | cons resource resources inductionHypothesis =>
      have headEmpty : resource.alts = [] :=
        prefixEmpty resource (by simp)
      have tailEmpty :
          ∀ item ∈ resources, item.alts = [] := by
        intro item member
        exact prefixEmpty item (by simp [member])
      simp only [List.cons_append, flattenOwnedAlts_cons,
        headEmpty, List.nil_append, PLeaTTa.barrierCount_cons_barrier,
        List.length_cons]
      rw [inductionHypothesis tailEmpty]
      omega

/-- Dropping the first nonempty resource descriptor together with the empty
prefix removes one marker too many.  This is the negative guard for
descriptor/marker linearity. -/
theorem dropping_first_nonempty_marker_is_rejected
    (emptyPrefix : List RetainedAlternativeSegment)
    (first : RetainedAlternativeSegment)
    (rest : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (prefixEmpty : ∀ resource ∈ emptyPrefix, resource.alts = [])
    (firstHead : first.alts = .br goals binding :: tail) :
    PLeaTTa.barrierCount
        (flattenOwnedAlts (emptyPrefix ++ first :: rest) base) ≠
      PLeaTTa.barrierCount
          (tail ++ flattenOwnedAlts rest base) +
        emptyPrefix.length := by
  have exactCount :=
    flattenOwnedAlts_first_nonempty_barrierCount emptyPrefix first rest base
      goals binding tail prefixEmpty firstHead
  intro wrong
  have markerAdds :
      PLeaTTa.barrierCount
          (tail ++ PLeaTTa.Alt.barrier :: flattenOwnedAlts rest base) =
        PLeaTTa.barrierCount (tail ++ flattenOwnedAlts rest base) + 1 := by
    simp only [PLeaTTa.barrierCount_append,
      PLeaTTa.barrierCount_cons_barrier]
    omega
  omega

/-! ## Inhabitation guard -/

private def emptyPullWitnessResource : RetainedAlternativeSegment :=
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

private def livePullWitnessResource : RetainedAlternativeSegment :=
  { emptyPullWitnessResource with
    barrier := 2
    alts := [.br [.call "witness" [] (.sym "result")] []] }

/-- A concrete two-frame bank crosses one empty resource and lands on the
first branch of the next resource.  Thus the nontrivial prefix case above is
inhabited. -/
theorem two_frame_empty_then_live_pull_witness :
    PLeaTTa.pullAux
        (flattenOwnedAlts
          [emptyPullWitnessResource, livePullWitnessResource] []) =
      some
        (([.call "witness" [] (.sym "result")], []),
          [PLeaTTa.Alt.barrier]) := by
  rfl

/-- The sibling terminal branch is inhabited: two empty local resources over
an empty base produce no executable branch. -/
theorem two_empty_frames_terminal_pull_witness :
    PLeaTTa.pullAux
        (flattenOwnedAlts
          [emptyPullWitnessResource, emptyPullWitnessResource] []) =
      none := by
  rfl

/-! ## Explicit exhausted-cursor phase offset -/

/-- Exact proof that the source cursor is exhausted while its executable
predicate resource has no alternative left.

The full ownership relation remains present, so emptiness cannot hide a
different query, occurrence list, counter, continuation, or barrier. -/
structure ExhaustedCursorOffsetAgrees
    (alpha : List (LogicVar × String))
    (cursor : PreparedCursor)
    (resource : RetainedAlternativeSegment) : Prop where
  cursorEmpty : cursor.remaining = []
  altsEmpty : resource.alts = []
  counterExact : resource.finalCounter = resource.counter
  ownership : resource.Owns alpha cursor

/-- Empty-cursor and retained-head offsets are disjoint phases. -/
theorem ExhaustedCursorOffsetAgrees.not_pulledHead
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {resource : RetainedAlternativeSegment}
    (exhausted : ExhaustedCursorOffsetAgrees alpha cursor resource)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch) (copied : PLeaTTa.Clause)
    (remainingAlts : List PLeaTTa.Alt) :
    ¬ PulledHeadOffsetAgrees alpha cursor branch clause branchTail copied
      resource remainingAlts := by
  intro retained
  have remaining := retained.cursorRemaining
  rw [exhausted.cursorEmpty] at remaining
  simp at remaining

/-- Empty executable readiness is genuine exhaustion on both occurrence
banks, with no hidden fresh-counter advance. -/
theorem representativeSupportedReady_exhausted_shape_of_alts_empty
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List PLeaTTa.Alt}
    (ready :
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter)
    (empty : alts = []) :
    branches = [] ∧ clauses = [] ∧ finalCounter = counter := by
  cases ready <;> simp_all

/-- Fully indexed state immediately after executable failure has crossed the
exhausted active predicate marker while the source still owns that
predicate's empty cursor.

`successorExact` deliberately stops at the real `pull` over the untouched
outer bank.  That pull may already have crossed more outer resource markers;
the relation does not guess a post-pull resource suffix before the general
catch-up theorem partitions it. -/
structure SpinedExhaustedPostFailureOffsetRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (cursor : PreparedCursor)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (source : Search) (successor : OpenConf) : Prop where
  persistent :
    SessionRelatesPersistent freshFrontier opened.session
      successor.persistent
  queryTerm : successor.control.qterm = qterm
  frames : successor.frames = pending.frames
  exhausted : ExhaustedCursorOffsetAgrees alpha cursor active
  activeRest :
    active.rest = callerExecutables ++ flattenExecutables outer
  activeQuery : active.qterm = qterm
  activeBarrier : active.barrier = bodyBarrier
  bodyBarrierTag :
    bodyBarrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  outerAlignment :
    SourceControlResourceContextAgrees alpha qterm callerBarrier outer
      resources callerScope context outerScope
  suspendedOuterAlts :
    pending.outer.alts = flattenOwnedAlts resources baseAlts
  predecessorAlts :
    predecessor.control.alts =
      flattenOwnedAlts (active :: resources) baseAlts
  predecessorBarriers :
    predecessor.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  successorExact :
    successor.toConf =
      PLeaTTa.pull
        { predecessor.toConf with
          cur := none
          alts := flattenOwnedAlts resources baseAlts
          barriers := pending.outer.barriers }
  sourceShape :
    source =
      ActiveProductContext.plug context
        (sourceProductFrontier callerScope opened cursor callerReferences)

/-! ## Exhausted-offset producer -/

/-- Primitive failure with an empty active executable suffix reaches the
exact exhausted-cursor offset.

The complete remaining source occurrence list is the maximal conservative
rejection prefix.  The source performs one wrapped body-failure transition
plus one present silent step per rejected occurrence.  The executable
performs one real equality-failure transition whose internal `pull` has
already crossed the active predicate marker. -/
theorem SpinedActiveProductResourceRelates.afterUnifyFailureExhausted
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyRest callerReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {left right : Term}
    (agreement :
      SpinedActiveProductResourceRelates freshFrontier alpha support canonical
        referenceBase opened pending finish selected selectedTail altTail
        bodyBarrier callerBarrier (.unify left right :: bodyRest)
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result)
    (empty : active.alts = []) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (_pulls :
          RejectedPullsN count (finish.advance selected selectedTail) next),
      selectedTail = skippedBranches ∧
      candidates = skippedClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      (∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false) ∧
      next.remaining = [] ∧
      StepsN (count + 1)
        (.running opened.session source)
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        outer qterm next active resources callerScope outerScope context
        baseAlts state
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state) := by
  let advanced := finish.advance selected selectedTail
  have advancedRemaining : advanced.remaining = selectedTail := by
    simp [advanced, PreparedCursor.advance]
  rcases agreement.resourceStack.activeOwnership with
    ⟨candidates, advancedWellFormed, advancedQuery, substitutedArgs,
      supportedCandidates, candidateArities, candidateScan⟩
  obtain
    ⟨count, skippedBranches, skippedClauses, next,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, nextRemaining, nextContext, ready⟩ :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.ResolutionScan.decomposeRepresentativeRejectedPrefix
      candidateScan supportedCandidates advancedQuery advancedWellFormed
      (.refl advanced) (.refl advanced) advancedRemaining
      (fun _branch member => member) candidateArities
  have readyShape :
      readyBranches = [] ∧ readyClauses = [] :=
    let shape :=
      representativeSupportedReady_exhausted_shape_of_alts_empty ready empty
    ⟨shape.1, shape.2.1⟩
  have readyBranchesEmpty : readyBranches = [] := readyShape.1
  have readyClausesEmpty : readyClauses = [] := readyShape.2
  have selectedTailEq : selectedTail = skippedBranches := by
    calc
      selectedTail = advanced.remaining := advancedRemaining.symm
      _ = skippedBranches ++ readyBranches := branchesEq
      _ = skippedBranches := by rw [readyBranchesEmpty, List.append_nil]
  have candidatesEq : candidates = skippedClauses := by
    calc
      candidates = skippedClauses ++ readyClauses := clausesEq
      _ = skippedClauses := by rw [readyClausesEmpty, List.append_nil]
  have retainedCountZero :
      retainedClauseCount active.argsv
        (PLeaTTa.subst active.binding active.res) candidates = 0 := by
    have lengthExact := candidateScan.length_exact
    rw [empty] at lengthExact
    simpa using lengthExact.symm
  have counterExact : active.finalCounter = active.counter := by
    have exact := candidateScan.counter_exact
    rw [retainedCountZero] at exact
    simpa using exact
  have skippedRejected :
      ∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false := by
    have skippedCountZero :
        retainedClauseCount active.argsv
          (PLeaTTa.subst active.binding active.res) skippedClauses = 0 := by
      simpa [candidatesEq] using retainedCountZero
    have skippedFilterEmpty :
        skippedClauses.filter
            (resolutionClauseRetained active.argsv
              (PLeaTTa.subst active.binding active.res)) = [] := by
      exact List.length_eq_zero_iff.mp skippedCountZero
    intro clause member
    cases retained :
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause with
    | false =>
        rfl
    | true =>
        have filteredMember :
            clause ∈
              skippedClauses.filter
                (resolutionClauseRetained active.argsv
                  (PLeaTTa.subst active.binding active.res)) := by
          simp [member, retained]
        rw [skippedFilterEmpty] at filteredMember
        simp at filteredMember

  have firstFocus :
      RawStep opened.session
        (activeSourceProduct callerScope opened finish selected selectedTail
          current (.unify left right :: bodyRest) callerReferences)
        [] .none opened.session
        (.running
          (sourceProductFrontier callerScope opened advanced
            callerReferences)) :=
    activeSourceProduct_unifyFailure callerScope opened finish selected
      selectedTail current left right bodyRest callerReferences clash
  have firstLifted :
      RawStep opened.session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish selected selectedTail
            current (.unify left right :: bodyRest) callerReferences))
        [] .none opened.session
        (.running
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) :=
    ActiveProductContext.liftProgress context firstFocus
      (by simp [Trace.AnswerFree])
  have firstTransition :
      Transition
        (.running opened.session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) :=
    .ordinary _ _ _ _ _ firstLifted
  have firstSteps :
      StepsN 1
        (.running opened.session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) := by
    simpa using
      (StepsN.succ 0
        (.running opened.session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        [] [] firstTransition (.zero _))
  have tailSteps :
      StepsN count
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) :=
    PLeaTTa.PrologBodyFailureResourceTransitionBridge.RejectedPullsN.sourceProductContextStepsN
      pulls context callerScope opened callerReferences
  have sourceSteps :
      StepsN (count + 1)
        (.running opened.session source)
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) := by
    rw [agreement.sourceShape]
    simpa [Nat.add_comm] using StepsN.trans firstSteps tailSteps

  rcases agreement.control.ready with
    ⟨persistentAgreement, currentControl, currentQuery, payload⟩
  have bodyPayload := payload.headPayload
  rcases bodyPayload.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      bodyShape, leftAgreement, rightAgreement, _tailControl⟩
  have flattenedControl :
      state.control.cur =
        some
          (bodyExecutables ++
            (callerExecutables ++ flattenExecutables outer),
            runtime) := by
    simpa [flattenExecutables, ControlSegment.executableGoals] using
      currentControl
  have bodyShape' :
      bodyExecutables =
        spelling.goal executableLeft executableRight ::
          bodyExecutableTail := by
    simpa using bodyShape
  have executableHead :
      state.control.cur =
        some
          (spelling.goal executableLeft executableRight ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) := by
    calc
      state.control.cur =
          some
            (bodyExecutables ++
              (callerExecutables ++ flattenExecutables outer),
              runtime) :=
        flattenedControl
      _ =
          some
            ((spelling.goal executableLeft executableRight ::
                bodyExecutableTail) ++
              (callerExecutables ++ flattenExecutables outer),
              runtime) := by rw [bodyShape']
      _ =
          some
            (spelling.goal executableLeft executableRight ::
              (bodyExecutableTail ++
                (callerExecutables ++ flattenExecutables outer)),
              runtime) := by rfl
  have aliasSafe :
      CurrentUnifyOperandsAliasSafe current left right :=
    CurrentUnifyOperandsAliasSafe.of_booleanAliasSafe
      currentSafe leftAliasSafe rightAliasSafe
  have strict :=
    bodyPayload.strictUnifyOperands_of_currentAliasSafe
      leftAgreement rightAgreement leftSupported rightSupported aliasSafe
  have failed :
      PLeaTTa.unifyB runtime executableLeft executableRight = none :=
    bodyPayload.unifyB_eq_none_of_no_resolution strict clash
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) :=
    executable_unify_failure_step state spelling executableLeft
      executableRight
      (bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer))
      runtime executableHead failed

  have nextWellFormed : next.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      pulls advancedWellFormed
  have queryAtNext :
      RepresentativeNormalizedCallAgrees alpha next active.argsv
        (PLeaTTa.subst active.binding active.res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      nextContext (.refl advanced) advancedQuery
  have nextRemainingEmpty : next.remaining = [] :=
    nextRemaining.trans readyBranchesEmpty
  have nextOwnership : active.Owns alpha next := by
    refine
      ⟨[], nextWellFormed, queryAtNext, substitutedArgs, ?_, ?_, ?_⟩
    · rw [nextRemainingEmpty]
      exact .nil
    · intro clause member
      simp at member
    · simpa [empty, counterExact] using
        (ResolutionScan.nil active.counter :
          ResolutionScan active.argsv active.args active.res active.rest
            active.binding active.qterm active.barrier [] active.counter []
            active.counter)
  have exhausted :
      ExhaustedCursorOffsetAgrees alpha next active :=
    ⟨nextRemainingEmpty, empty, counterExact, nextOwnership⟩

  have predecessorAlts :
      state.control.alts =
        flattenOwnedAlts (active :: resources) baseAlts :=
    agreement.resourceStack.actualAlts
  have activeAlts :
      state.toConf.alts =
        PLeaTTa.Alt.barrier :: pending.outer.alts := by
    change state.control.alts =
      PLeaTTa.Alt.barrier :: pending.outer.alts
    calc
      state.control.alts =
          flattenOwnedAlts (active :: resources) baseAlts :=
        predecessorAlts
      _ =
          active.alts ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts resources baseAlts := rfl
      _ =
          PLeaTTa.Alt.barrier ::
            flattenOwnedAlts resources baseAlts := by rw [empty, List.nil_append]
      _ =
          PLeaTTa.Alt.barrier :: pending.outer.alts := by
        rw [agreement.resourceStack.suspendedOuterAlts]
  have activeBarriers :
      state.toConf.barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers := by
    change state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
    exact agreement.control.retainedBarriers
  let resumedBase : PLeaTTa.Conf :=
    { state.toConf with barriers := pending.outer.barriers }
  have activeConf :
      { state.toConf with cur := none } =
        { resumedBase with
          cur := none
          alts := PLeaTTa.Alt.barrier :: pending.outer.alts
          barriers := PLeaTTa.pushBarrierCache resumedBase.barriers } := by
    apply PLeaTTa.Conf.ext <;>
      simp [resumedBase, activeAlts, activeBarriers]
  have successorOuter :
      (unifyFailureSuccessor state).toConf =
        PLeaTTa.pull
          { state.toConf with
            cur := none
            alts := pending.outer.alts
            barriers := pending.outer.barriers } := by
    calc
      (unifyFailureSuccessor state).toConf =
          PLeaTTa.pull { state.toConf with cur := none } := by
            rfl
      _ =
          PLeaTTa.pull
            { resumedBase with
              cur := none
              alts := PLeaTTa.Alt.barrier :: pending.outer.alts
              barriers := PLeaTTa.pushBarrierCache resumedBase.barriers } := by
            rw [activeConf]
      _ =
          PLeaTTa.pull
            { resumedBase with
              cur := none
              alts := pending.outer.alts } := by
            exact PLeaTTa.pull_barrier resumedBase pending.outer.alts
      _ =
          PLeaTTa.pull
            { state.toConf with
              cur := none
              alts := pending.outer.alts
              barriers := pending.outer.barriers } := by
            rfl
  have successorExact :
      (unifyFailureSuccessor state).toConf =
        PLeaTTa.pull
          { state.toConf with
            cur := none
            alts := flattenOwnedAlts resources baseAlts
            barriers := pending.outer.barriers } := by
    rw [successorOuter, agreement.resourceStack.suspendedOuterAlts]
  have successorPersistent :
      SessionRelatesPersistent freshFrontier opened.session
        (unifyFailureSuccessor state).persistent := by
    rw [unifyFailureSuccessor_persistent]
    exact persistentAgreement
  have successorQuery :
      (unifyFailureSuccessor state).control.qterm = qterm := by
    change
      (PLeaTTa.pull { state.toConf with cur := none }).qterm = qterm
    rw [pull_qterm]
    exact currentQuery
  have successorFrames :
      (unifyFailureSuccessor state).frames = pending.frames := by
    simpa [unifyFailureSuccessor] using agreement.control.frames
  have post :
      SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        outer qterm next active resources callerScope outerScope context
        baseAlts state
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state) :=
    ⟨successorPersistent, successorQuery, successorFrames, exhausted,
      agreement.resourceStack.activeRest,
      agreement.resourceStack.activeQuery,
      agreement.resourceStack.activeBarrier,
      agreement.control.bodyBarrierTag,
      agreement.resourceStack.outerAlignment,
      agreement.resourceStack.suspendedOuterAlts, predecessorAlts,
      activeBarriers, successorExact, rfl⟩
  exact
    ⟨count, skippedBranches, skippedClauses, candidates, next,
      pulls, selectedTailEq, candidatesEq, branchCount, clauseCount,
      skippedRejected, nextRemainingEmpty, sourceSteps, executableStep, post⟩

/-! ## Catch-up interface fixed before its implementation -/

/-- Ranked evidence for source work hidden by executable traversal across
empty local resource banks.

An empty executable bank does not imply an empty source cursor: it may own
arbitrarily many conservatively rejected clause occurrences.  Every
constructor therefore stores the exact `RejectedPullsN` count required to
empty that frame.  `rejectionSteps` is the sum of those counts; later source
step accounting can use it together with the number of crossed frames rather
than an unconstrained existential. -/
inductive CrossedEmptyResourceFramesAgrees
    (alpha : List (LogicVar × String)) :
    List RetainedAlternativeSegment → ActiveProductContext → Nat → Prop where
  | nil :
      CrossedEmptyResourceFramesAgrees alpha [] [] 0
  | cons (resource : RetainedAlternativeSegment)
      (resources : List RetainedAlternativeSegment)
      (frame : ActiveProductFrame) (frames : ActiveProductContext)
      (cursor finish : PreparedCursor) (count tailCount : Nat)
      (retainedShape :
        frame.retained = .clauses frame.predicateScope cursor)
      (ownership : resource.Owns alpha cursor)
      (empty : resource.alts = [])
      (pulls : RejectedPullsN count cursor finish)
      (finishEmpty : finish.remaining = [])
      (tail :
        CrossedEmptyResourceFramesAgrees alpha resources frames tailCount) :
      CrossedEmptyResourceFramesAgrees alpha
        (resource :: resources) (frame :: frames) (count + tailCount)

/-- Crossed source frames and executable resources are paired one-for-one. -/
theorem CrossedEmptyResourceFramesAgrees.length_eq
    {alpha : List (LogicVar × String)}
    {resources : List RetainedAlternativeSegment}
    {frames : ActiveProductContext} {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha resources frames
        rejectionSteps) :
    resources.length = frames.length := by
  induction agreement with
  | nil =>
      rfl
  | cons resource resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail
      inductionHypothesis =>
      simp [inductionHypothesis]

/-- Every descriptor in a ranked crossed prefix has an empty executable
bank; this is the maximality fact consumed by the real pull theorem. -/
theorem CrossedEmptyResourceFramesAgrees.all_empty
    {alpha : List (LogicVar × String)}
    {resources : List RetainedAlternativeSegment}
    {frames : ActiveProductContext} {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha resources frames
        rejectionSteps) :
    ∀ resource ∈ resources, resource.alts = [] := by
  induction agreement with
  | nil =>
      simp
  | cons resource resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail
      inductionHypothesis =>
      intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact empty
      · exact inductionHypothesis item member

/-- Structural partition for catch-up when executable pull lands in the first
nonempty outer local resource.

The first surviving resource, source frame, and control segment are named
explicitly.  Crossed resources and frames carry ranked rejection work; the
control-segment split is forced at the same depth.  The full
`SourceControlResourceContextAgrees` certificate remains an input of the
future catch-up theorem and will tie these literal sublists to their typed
scopes and barriers. -/
structure OuterResourceCatchupPartition
    (alpha : List (LogicVar × String))
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext) where
  crossedSegments : List ControlSegment
  firstSegment : ControlSegment
  survivingSegments : List ControlSegment
  crossedResources : List RetainedAlternativeSegment
  first : RetainedAlternativeSegment
  survivingResources : List RetainedAlternativeSegment
  crossedFrames : ActiveProductContext
  firstFrame : ActiveProductFrame
  survivingContext : ActiveProductContext
  firstCursor : PreparedCursor
  rejectionSteps : Nat
  goals : List PLeaTTa.Goal
  binding : Subst
  tail : List PLeaTTa.Alt
  segmentsEq :
    segments =
      crossedSegments ++ (firstSegment :: survivingSegments)
  resourcesEq :
    resources =
      crossedResources ++ (first :: survivingResources)
  contextEq :
    context = crossedFrames ++ (firstFrame :: survivingContext)
  crossedSegmentDepth :
    crossedSegments.length = crossedResources.length
  crossedWork :
    CrossedEmptyResourceFramesAgrees alpha crossedResources crossedFrames
      rejectionSteps
  firstRetainedShape :
    firstFrame.retained = .clauses firstFrame.predicateScope firstCursor
  firstOwnership : first.Owns alpha firstCursor
  firstHead : first.alts = .br goals binding :: tail

/-- Structural sibling for terminal catch-up.

All local frames/resources are crossed with an exact ranked rejection count,
all control segments occur at the same depth, and the arbitrary base bank
itself has no branch.  Consequently a later terminal theorem cannot finish
while leaving a residual local source frame. -/
structure TerminalOuterResourceCatchupPartition
    (alpha : List (LogicVar × String))
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (base : List PLeaTTa.Alt) where
  rejectionSteps : Nat
  segmentDepth : segments.length = resources.length
  crossedWork :
    CrossedEmptyResourceFramesAgrees alpha resources context rejectionSteps
  baseTerminal : PLeaTTa.pullAux base = none

end PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge
