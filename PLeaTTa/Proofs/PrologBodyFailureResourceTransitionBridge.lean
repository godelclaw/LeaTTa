-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologBodyFailureResourceTransitionBridge
Purpose: Preserve exact retained-cursor/executable-alternative ownership
  through primitive failure inside an entered local clause body.
Trusted boundary: none
Main exports:
  RetainedAlternativeSegment.afterPulledHead,
  PulledHeadOffsetAgrees,
  SpinedPostFailureFrontierResourceRelatesAt,
  SpinedPostFailureFrontierResourceRelates,
  RejectedPullsN.path_unique,
  RejectedPullsN.sourceProductContextStepsNAt,
  SpinedActiveProductResourceRelatesAt.afterUnifyFailureRetained
-/
import PLeaTTa.Proofs.PrologBodyFailureBacktrackingBridge
import PLeaTTa.Proofs.PrologProductResourceTransitionBridge

namespace PLeaTTa.PrologBodyFailureResourceTransitionBridge

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
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologHeadFailureContinuationBridge
open PrologOrdinaryStepBridge
open PrologProductSchedulingBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeCallPrefilterBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedCursorOwnershipBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCallFrontierBridge
open PrologSupportedCursorAlternativeBridge
open PrologPrefilterScanBridge

/-!
After a failed equality the executable `pull` is one phase ahead of the
independent cursor:

* the source is still at `next.remaining = selected :: tail`;
* the executable has installed `selected` in `cur`; and
* only the alternatives for `tail` remain in the executable bank.

This offset must not be represented by `SpinedActiveProductResourceRelates`.
That relation means the source has already selected the head and therefore
contains the advanced cursor as a live right branch.  The structures below
make the intermediate phase explicit.  The later source activation is the
transition which promotes the offset resource into a live active resource.
-/

/-! ## A structurally stable retained suffix -/

/-- Consume the executable alternative for one retained head.

Every call-level datum is inherited literally.  Only the scan counter advances
and the exact remaining alternative suffix changes.  In particular the
predicate barrier cannot be retagged during backtracking. -/
def afterPulledHead
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    RetainedAlternativeSegment :=
  { resource with
    counter := resource.counter + 1
    alts := remainingAlts }

@[simp] theorem afterPulledHead_argsv
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).argsv = resource.argsv := rfl

@[simp] theorem afterPulledHead_args
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).args = resource.args := rfl

@[simp] theorem afterPulledHead_res
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).res = resource.res := rfl

@[simp] theorem afterPulledHead_rest
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).rest = resource.rest := rfl

@[simp] theorem afterPulledHead_binding
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).binding = resource.binding := rfl

@[simp] theorem afterPulledHead_qterm
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).qterm = resource.qterm := rfl

@[simp] theorem afterPulledHead_barrier
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).barrier = resource.barrier := rfl

@[simp] theorem afterPulledHead_counter
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).counter =
      resource.counter + 1 := rfl

@[simp] theorem afterPulledHead_alts
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).alts = remainingAlts := rfl

@[simp] theorem afterPulledHead_finalCounter
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) :
    (afterPulledHead resource remainingAlts).finalCounter =
      resource.finalCounter := rfl

/-! ## The executable-ahead cursor offset -/

/-- Exact relation between an unadvanced source cursor and the executable
state after its retained head alternative has already been pulled.

`tailOwnership` is deliberately indexed through `cursor.advance`.  It is not
presented as an independently live source resource: `cursorRemaining` records
that the actual source cursor still contains `branch` at its head. -/
structure PulledHeadOffsetAgrees
    (alpha : List (LogicVar × String))
    (cursor : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) : Prop where
  cursorRemaining : cursor.remaining = branch :: branchTail
  cursorWellFormed : cursor.WellFormed
  query :
    RepresentativeNormalizedCallAgrees alpha cursor resource.argsv
      (PLeaTTa.subst resource.binding resource.res)
  substitutedArgs :
    resource.argsv = resource.args.map (PLeaTTa.subst resource.binding)
  supported :
    SupportedPreparedCandidateAgrees cursor.callGeneration cursor.predicate
      cursor.arguments cursor.bindings branch clause
  arity : clause.params.length = resource.argsv.length
  retained :
    resolutionClauseRetained resource.argsv
      (PLeaTTa.subst resource.binding resource.res) clause = true
  priorAlts :
    resource.alts =
      resolutionAlt resource.argsv resource.args resource.res resource.rest
        resource.binding resource.qterm resource.barrier resource.counter
        clause :: remainingAlts
  copiedExact :
    copied =
      PLeaTTa.freshenResolutionClause resource.argsv resource.args
        resource.res resource.rest resource.binding resource.qterm
        resource.counter resource.barrier clause
  tailOwnership :
    (afterPulledHead resource remainingAlts).Owns alpha
      (cursor.advance branch branchTail)

/-! ## Anti-vacuity guards for the offset phase -/

/-- The offset descriptor consumes exactly one executable alternative.

This rules out pairing an unadvanced source head with an unchanged or
off-by-one executable bank. -/
theorem PulledHeadOffsetAgrees.consumes_exactly_one
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch}
    {copied : PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    (agreement :
      PulledHeadOffsetAgrees alpha cursor branch clause branchTail copied
        resource remainingAlts) :
    resource.alts.length =
      (afterPulledHead resource remainingAlts).alts.length + 1 := by
  rw [agreement.priorAlts]
  simp [afterPulledHead]

/-- Retagging the predicate barrier cannot masquerade as pulling one head. -/
theorem wrong_retagged_afterPulledHead_is_rejected
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt) (differentBarrier : Nat)
    (different : differentBarrier ≠ resource.barrier) :
    ({ afterPulledHead resource remainingAlts with
        barrier := differentBarrier } : RetainedAlternativeSegment) ≠
      afterPulledHead resource remainingAlts := by
  intro equality
  have barrierEquality :=
    congrArg (fun item : RetainedAlternativeSegment => item.barrier) equality
  exact different (by simpa using barrierEquality)

/-- Installing a focus beneath an already-entered product stack is
injective.  Outer control therefore cannot hide a phase mismatch at the
innermost predicate. -/
theorem ActiveProductContext.plug_injective
    (context : ActiveProductContext) :
    Function.Injective (ActiveProductContext.plug context) := by
  induction context with
  | nil =>
      intro left right equality
      exact equality
  | cons frame outer inductionHypothesis =>
      intro left right equality
      have wrapped :
          ActiveProductFrame.wrap frame left =
            ActiveProductFrame.wrap frame right :=
        inductionHypothesis equality
      simpa [ActiveProductFrame.wrap] using wrapped

/-- A source cursor frontier and an active clause body are different phases,
even beneath an arbitrary stack of older local calls. -/
theorem post_failure_frontier_is_not_active
    (context : ActiveProductContext)
    (callerScope : CutScopeId) (opened : OpenedCall)
    (cursor finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (body referenceRest : List PeTTaSpec.PrologCore.Goal) :
    ActiveProductContext.plug context
        (sourceProductFrontier callerScope opened cursor referenceRest) ≠
      ActiveProductContext.plug context
        (activeSourceProduct callerScope opened finish branch branchTail
          current body referenceRest) := by
  intro equality
  have focusEquality :=
    ActiveProductContext.plug_injective context equality
  simp [sourceProductFrontier, activeSourceProduct] at focusEquality

/-! ## Exact post-failure phase relations -/

/-- Control facts after executable failure has pulled the next retained head
while the independent source is still at its unadvanced cursor.

The executable head prefix is kept outside the caller spine: no source body
region exists until the next source activation. -/
structure SpinedPostFailureFrontierRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (state : OpenConf) : Prop where
  persistent :
    SessionRelatesPersistent freshFrontier session state.persistent
  sessionAdvanced :
    SessionHighWatersExtend opened.session session
  callerSpine :
    ControlSpineAgrees alpha
      ({ barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } :: outer)
  current :
    state.control.cur =
      some
        (PLeaTTa.Goal.eq
            (.expr (resource.args ++ [resource.res]))
            (.expr (copied.params ++ [copied.result])) ::
          copied.body ++ resource.rest,
          resource.binding)
  resourceRest :
    resource.rest = callerExecutables ++ flattenExecutables outer
  queryTerm : state.control.qterm = qterm
  resourceQuery : resource.qterm = qterm
  resourceBarrier : resource.barrier = bodyBarrier
  bodyBarrierTag :
    bodyBarrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  retainedAlts :
    state.control.alts =
      remainingAlts ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedBarriers :
    state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  frames : state.frames = pending.frames

/-- Exact opener-session specialization of the post-failure control phase. -/
abbrev SpinedPostFailureFrontierRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (state : OpenConf) : Prop :=
  SpinedPostFailureFrontierRelatesAt freshFrontier alpha opened
    opened.session pending bodyBarrier callerBarrier callerReferences
    callerExecutables outer qterm copied resource remainingAlts state

/-- A post-failure frontier cannot be reindexed below the call-opening fresh
high-water.  The retained cursor was allocated at that historical frontier. -/
theorem SpinedPostFailureFrontierRelatesAt.rejectsFreshRegression
    {freshFrontier : FreshFrontierRelation}
    {alpha : List (LogicVar × String)}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom}
    {copied : PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    {state : OpenConf}
    (agreement :
      SpinedPostFailureFrontierRelatesAt freshFrontier alpha opened session
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        outer qterm copied resource remainingAlts state)
    (regressed :
      session.resolver.nextFresh < opened.session.resolver.nextFresh) :
    False :=
  SessionHighWatersExtend.rejects_fresh_regression regressed
    agreement.sessionAdvanced

/-- Resource-stack facts in the executable-ahead post-failure phase.

The innermost descriptor is an offset descriptor: it owns the alternatives
after the already-pulled head, while `offset.cursorRemaining` keeps the actual
source cursor unadvanced. -/
structure PostFailureFrontierResourceStackAgrees
    (alpha : List (LogicVar × String)) (qterm : Atom)
    (bodyBarrier callerBarrier : Nat)
    (pending : DemandDrivenCallStep.PendingCall)
    (cursor : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (outer : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (state : OpenConf) : Prop where
  offset :
    PulledHeadOffsetAgrees alpha cursor branch clause branchTail
      copied resource remainingAlts
  resourceBarrier : resource.barrier = bodyBarrier
  outerAlignment :
    SourceControlResourceContextAgrees alpha qterm callerBarrier outer
      resources callerScope context outerScope
  suspendedOuterAlts :
    pending.outer.alts = flattenOwnedAlts resources baseAlts
  actualAlts :
    state.control.alts =
      flattenOwnedAlts
        (afterPulledHead resource remainingAlts :: resources) baseAlts

/-- Fully composed retained post-failure frontier.

The literal source term makes the phase observable: the source still contains
`.clauses cursor`, whereas the executable has already installed `branch` in
its current goal prefix. -/
structure SpinedPostFailureFrontierResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha : List (LogicVar × String))
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (cursor : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf) : Prop where
  control :
    SpinedPostFailureFrontierRelatesAt freshFrontier alpha opened session pending
      bodyBarrier callerBarrier callerReferences callerExecutables outer qterm
      copied resource remainingAlts state
  resourceStack :
    PostFailureFrontierResourceStackAgrees alpha qterm bodyBarrier
      callerBarrier pending cursor branch clause branchTail copied resource
      remainingAlts outer resources callerScope outerScope context baseAlts
      state
  sourceShape :
    source =
      ActiveProductContext.plug context
        (sourceProductFrontier callerScope opened cursor callerReferences)

/-- Exact opener-session specialization of the retained post-failure
frontier. -/
abbrev SpinedPostFailureFrontierResourceRelates
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
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf) : Prop :=
  SpinedPostFailureFrontierResourceRelatesAt freshFrontier alpha opened
    opened.session pending bodyBarrier callerBarrier callerReferences
    callerExecutables outer qterm cursor branch clause branchTail copied
    resource remainingAlts resources callerScope outerScope context baseAlts
    source state

/-! ## Exact source-prefix lifting -/

/-- A fixed rejected-pull count and starting cursor determine the exact
ending cursor.

Each successor must consume the unique head/tail decomposition of the current
remaining list.  Thus the path witness exported by the retained-failure
producer is reusable compositional evidence, not a choice among alternate
endpoint-equal scans. -/
theorem RejectedPullsN.path_unique
    {count : Nat} {before after after' : PreparedCursor}
    (left : RejectedPullsN count before after)
    (right : RejectedPullsN count before after') :
    after = after' := by
  induction left generalizing after' with
  | zero cursor =>
      cases right
      rfl
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      cases right with
      | succ _ _ branch' branches' finish' remaining' clash' tail' =>
          have sameHead :
              branch :: branches = branch' :: branches' :=
            remaining.symm.trans remaining'
          rcases List.cons.inj sameHead with ⟨rfl, rfl⟩
          exact inductionHypothesis tail'

/-- Exactly counted conservative cursor rejections lift through both the
current predicate product and every older active source frame.

Every source-only rejection remains a present transition.  The observation
sequence stays exactly empty; no stuttering quotient is used. -/
theorem RejectedPullsN.sourceProductContextStepsNAt
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (context : ActiveProductContext)
    (callerScope : CutScopeId) (opened : OpenedCall)
    (session : Session)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    StepsN count
      (.running session
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened before referenceRest)))
      []
      (.running session
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened after referenceRest))) := by
  induction pulls with
  | zero cursor =>
      exact .zero _
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have pulled :
          LocalPull cursor (.silent (cursor.advance branch branches)) :=
        .rejected cursor branch branches remaining clash
      have leaf :
          RawStep session (.clauses opened.scope cursor) [] .none
            session
            (.running
              (.clauses opened.scope (cursor.advance branch branches))) := by
        simpa [localPullEvents, localPullTarget] using
          (RawStep.clausesPull opened.scope cursor
            (.silent (cursor.advance branch branches)) session pulled)
      have boundary :
          RawStep session
            (.cutBoundary opened.scope (.clauses opened.scope cursor))
            [] .none session
            (.running
              (.cutBoundary opened.scope
                (.clauses opened.scope
                  (cursor.advance branch branches)))) :=
        .cutBoundaryProgress opened.scope _ _ [] session
          session leaf
      have wrapped :
          RawStep session
            (sourceProductFrontier callerScope opened cursor referenceRest)
            [] .none session
            (.running
              (sourceProductFrontier callerScope opened
                (cursor.advance branch branches) referenceRest)) := by
        exact
          .productProgress callerScope _ _ referenceRest [] .none
            session session boundary
            (by simp [Trace.AnswerFree])
      have lifted :
          RawStep session
            (ActiveProductContext.plug context
              (sourceProductFrontier callerScope opened cursor referenceRest))
            [] .none session
            (.running
              (ActiveProductContext.plug context
                (sourceProductFrontier callerScope opened
                  (cursor.advance branch branches) referenceRest))) :=
        ActiveProductContext.liftProgress context wrapped
          (by simp [Trace.AnswerFree])
      have first :
          Transition
            (.running session
              (ActiveProductContext.plug context
                (sourceProductFrontier callerScope opened cursor
                  referenceRest)))
            []
            (.running session
              (ActiveProductContext.plug context
                (sourceProductFrontier callerScope opened
                  (cursor.advance branch branches) referenceRest))) :=
        .ordinary _ _ _ _ _ lifted
      simpa using
        (StepsN.succ count
          (.running session
            (ActiveProductContext.plug context
              (sourceProductFrontier callerScope opened cursor referenceRest)))
          (.running session
            (ActiveProductContext.plug context
              (sourceProductFrontier callerScope opened
                (cursor.advance branch branches) referenceRest)))
          (.running session
            (ActiveProductContext.plug context
              (sourceProductFrontier callerScope opened finish referenceRest)))
          [] [] first inductionHypothesis)

/-- Backward-compatible opener-session specialization of the exact rejected
source prefix. -/
theorem RejectedPullsN.sourceProductContextStepsN
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (context : ActiveProductContext)
    (callerScope : CutScopeId) (opened : OpenedCall)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    StepsN count
      (.running opened.session
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened before referenceRest)))
      []
      (.running opened.session
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened after referenceRest))) :=
  PLeaTTa.PrologBodyFailureResourceTransitionBridge.RejectedPullsN.sourceProductContextStepsNAt
    pulls context callerScope opened opened.session referenceRest

/-! ## Retained body-failure transition -/

/-- Primitive failure inside the selected body reaches the exact
executable-ahead retained frontier.

The source takes one body-failure transition plus the exactly counted
conservative rejected prefix.  The executable takes one real equality-failure
transition whose eager `pull` installs the next retained clause.  The theorem
constructs the offset resource directly from the predecessor resource's owned
`ResolutionScan`; it does not replay call entry or invent a pending call. -/
theorem SpinedActiveProductResourceRelatesAt.afterUnifyFailureRetained
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
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
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish selected
        selectedTail altTail bodyBarrier callerBarrier
        (.unify left right :: bodyRest) bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result)
    (nonempty : active.alts ≠ []) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (nextBranch : ClauseBranch) (nextClause : PLeaTTa.Clause)
        (nextBranchTail : List ClauseBranch)
        (nextClauseTail : List PLeaTTa.Clause)
        (nextAltTail : List PLeaTTa.Alt)
        (nextCopied : PLeaTTa.Clause),
      selectedTail = skippedBranches ++ (nextBranch :: nextBranchTail) ∧
      candidates = skippedClauses ++ (nextClause :: nextClauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      (∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false) ∧
      RejectedPullsN count (finish.advance selected selectedTail) next ∧
      StepsN (count + 1)
        (.running session source)
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      SpinedPostFailureFrontierResourceRelatesAt freshFrontier alpha opened
        session pending bodyBarrier callerBarrier callerReferences
        callerExecutables outer qterm next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail resources callerScope outerScope context
        baseAlts
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
  have readyNonempty : readyBranches ≠ [] :=
    ready.branches_nonempty_of_alts_nonempty nonempty
  obtain
    ⟨nextBranch, nextClause, nextBranchTail, nextClauseTail, nextAltTail,
      readyBranchesEq, readyClausesEq, priorAlts, nextSupported, nextArity,
      nextRetained, tailSupported, tailScan⟩ :=
    ready.retained_shape readyNonempty
  let nextCopied :=
    PLeaTTa.freshenResolutionClause active.argsv active.args active.res
      active.rest active.binding active.qterm active.counter active.barrier
      nextClause
  have selectedTailEq :
      selectedTail = skippedBranches ++ (nextBranch :: nextBranchTail) := by
    calc
      selectedTail = advanced.remaining := advancedRemaining.symm
      _ = skippedBranches ++ readyBranches := branchesEq
      _ = skippedBranches ++ (nextBranch :: nextBranchTail) := by
        rw [readyBranchesEq]
  have candidatesEq :
      candidates = skippedClauses ++ (nextClause :: nextClauseTail) := by
    rw [clausesEq, readyClausesEq]
  have skippedRejected :
      ∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false := by
    have fullLength := candidateScan.length_exact
    have tailLength := tailScan.length_exact
    have skippedCountZero :
        retainedClauseCount active.argsv
          (PLeaTTa.subst active.binding active.res) skippedClauses = 0 := by
      rw [priorAlts, candidatesEq] at fullLength
      simp [retainedClauseCount, nextRetained] at fullLength tailLength
      unfold retainedClauseCount
      omega
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
      RawStep session
        (activeSourceProduct callerScope opened finish selected selectedTail
          current (.unify left right :: bodyRest) callerReferences)
        [] .none session
        (.running
          (sourceProductFrontier callerScope opened advanced
            callerReferences)) :=
    activeSourceProduct_unifyFailureAt callerScope opened session finish
      selected selectedTail current left right bodyRest callerReferences clash
  have firstLifted :
      RawStep session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish selected selectedTail
            current (.unify left right :: bodyRest) callerReferences))
        [] .none session
        (.running
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) :=
    ActiveProductContext.liftProgress context firstFocus
      (by simp [Trace.AnswerFree])
  have firstTransition :
      Transition
        (.running session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) :=
    .ordinary _ _ _ _ _ firstLifted
  have firstSteps :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
        (.running session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences))) := by
    simpa using
      (StepsN.succ 0
        (.running session
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish selected
              selectedTail current (.unify left right :: bodyRest)
              callerReferences)))
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        [] [] firstTransition (.zero _))
  have tailSteps :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened advanced
              callerReferences)))
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) :=
    PLeaTTa.PrologBodyFailureResourceTransitionBridge.RejectedPullsN.sourceProductContextStepsNAt
      pulls context callerScope opened session callerReferences
  have sourceSteps :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
        (.running session source)
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) := by
    rw [agreement.sourceShape]
    simpa [Nat.add_comm] using
      PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans firstSteps tailSteps

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
  have nextRemainingHead :
      next.remaining = nextBranch :: nextBranchTail :=
    nextRemaining.trans readyBranchesEq
  have nextAdvancedContext :
      CursorCallContext (next.advance nextBranch nextBranchTail)
        advanced.callGeneration advanced.predicate
        advanced.arguments advanced.bindings :=
    nextContext.advance nextBranch nextBranchTail
  have nextAdvancedWellFormed :
      (next.advance nextBranch nextBranchTail).WellFormed :=
    next.advance_wellFormed nextWellFormed nextRemainingHead
  have queryAtNextAdvanced :
      RepresentativeNormalizedCallAgrees alpha
        (next.advance nextBranch nextBranchTail) active.argsv
        (PLeaTTa.subst active.binding active.res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      nextAdvancedContext nextContext queryAtNext
  have tailArities :
      ∀ candidate, candidate ∈ nextClauseTail →
        candidate.params.length = active.argsv.length := by
    intro candidate member
    apply candidateArities candidate
    rw [candidatesEq]
    simp [member]
  have tailOwnership :
      (afterPulledHead active nextAltTail).Owns alpha
        (next.advance nextBranch nextBranchTail) := by
    have tailSupportedAtAdvanced :
        List.Forall₂
          (SupportedPreparedCandidateAgrees
            (next.advance nextBranch nextBranchTail).callGeneration
            (next.advance nextBranch nextBranchTail).predicate
            (next.advance nextBranch nextBranchTail).arguments
            (next.advance nextBranch nextBranchTail).bindings)
          (next.advance nextBranch nextBranchTail).remaining
          nextClauseTail := by
      have transported :
          List.Forall₂
            (SupportedPreparedCandidateAgrees
              (next.advance nextBranch nextBranchTail).callGeneration
              (next.advance nextBranch nextBranchTail).predicate
              (next.advance nextBranch nextBranchTail).arguments
              (next.advance nextBranch nextBranchTail).bindings)
            nextBranchTail nextClauseTail :=
        tailSupported.imp
          (fun _branch _clause supported =>
            nextAdvancedContext.supportedPreparedCandidate supported)
      simpa [PreparedCursor.advance] using transported
    exact
      ⟨nextClauseTail, nextAdvancedWellFormed, queryAtNextAdvanced,
        substitutedArgs, tailSupportedAtAdvanced, tailArities, tailScan⟩
  have nextSupportedAtCursor :
      SupportedPreparedCandidateAgrees next.callGeneration next.predicate
        next.arguments next.bindings nextBranch nextClause :=
    nextContext.supportedPreparedCandidate nextSupported
  have offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause
        nextBranchTail nextCopied active nextAltTail :=
    ⟨nextRemainingHead, nextWellFormed, queryAtNext, substitutedArgs,
      nextSupportedAtCursor, nextArity, nextRetained, priorAlts, rfl,
      tailOwnership⟩

  have activeBank :
      state.control.alts =
        resolutionAlt active.argsv active.args active.res active.rest
            active.binding active.qterm active.barrier active.counter
            nextClause ::
          (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts) := by
    calc
      state.control.alts =
          flattenOwnedAlts (active :: resources) baseAlts :=
        agreement.resourceStack.actualAlts
      _ =
          active.alts ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts resources baseAlts := rfl
      _ =
          active.alts ++ PLeaTTa.Alt.barrier :: pending.outer.alts := by
        rw [agreement.resourceStack.suspendedOuterAlts]
      _ =
          (resolutionAlt active.argsv active.args active.res active.rest
              active.binding active.qterm active.barrier active.counter
              nextClause :: nextAltTail) ++
            PLeaTTa.Alt.barrier :: pending.outer.alts := by
        rw [priorAlts]
      _ =
          resolutionAlt active.argsv active.args active.res active.rest
              active.binding active.qterm active.barrier active.counter
              nextClause ::
            (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts) := by
        rfl
  have activeBranchBank :
      state.control.alts =
        .br
            (PLeaTTa.Goal.eq
                (.expr (active.args ++ [active.res]))
                (.expr (nextCopied.params ++ [nextCopied.result])) ::
              nextCopied.body ++ active.rest)
            active.binding ::
          (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts) := by
    simpa [resolutionAlt, nextCopied] using activeBank
  have successorConf :
      (unifyFailureSuccessor state).toConf =
        { state.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq
                  (.expr (active.args ++ [active.res]))
                  (.expr (nextCopied.params ++ [nextCopied.result])) ::
                nextCopied.body ++ active.rest,
                active.binding)
          alts :=
            nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts } :=
    unifyFailureSuccessor_toConf_of_alts_branch state
      (PLeaTTa.Goal.eq
          (.expr (active.args ++ [active.res]))
          (.expr (nextCopied.params ++ [nextCopied.result])) ::
        nextCopied.body ++ active.rest)
      active.binding
      (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts)
      activeBranchBank
  have successorCur :
      (unifyFailureSuccessor state).control.cur =
        some
          (PLeaTTa.Goal.eq
              (.expr (active.args ++ [active.res]))
              (.expr (nextCopied.params ++ [nextCopied.result])) ::
            nextCopied.body ++ active.rest,
            active.binding) := by
    have field := congrArg (fun conf : PLeaTTa.Conf => conf.cur) successorConf
    simpa [OpenConf.toConf, Control.toConf] using field
  have successorAlts :
      (unifyFailureSuccessor state).control.alts =
        nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts := by
    have field := congrArg (fun conf : PLeaTTa.Conf => conf.alts) successorConf
    simpa [OpenConf.toConf, Control.toConf] using field
  have successorQueryFromState :
      (unifyFailureSuccessor state).control.qterm = state.control.qterm := by
    have field :=
      congrArg (fun conf : PLeaTTa.Conf => conf.qterm) successorConf
    simpa [OpenConf.toConf, Control.toConf] using field
  have successorBarriers :
      (unifyFailureSuccessor state).control.barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers := by
    have field :=
      congrArg (fun conf : PLeaTTa.Conf => conf.barriers) successorConf
    have unchanged :
        (unifyFailureSuccessor state).control.barriers =
          state.control.barriers := by
      simpa [OpenConf.toConf, Control.toConf] using field
    exact unchanged.trans agreement.control.retainedBarriers
  have successorFrames :
      (unifyFailureSuccessor state).frames = pending.frames := by
    simpa [unifyFailureSuccessor] using agreement.control.frames
  have successorPersistent :
      SessionRelatesPersistent freshFrontier session
        (unifyFailureSuccessor state).persistent := by
    rw [unifyFailureSuccessor_persistent]
    exact persistentAgreement
  have postControl :
      SpinedPostFailureFrontierRelatesAt freshFrontier alpha opened session
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        outer qterm nextCopied active nextAltTail
        (unifyFailureSuccessor state) := by
    refine
      ⟨successorPersistent, agreement.control.sessionAdvanced,
        payload.control.tail, successorCur,
        agreement.resourceStack.activeRest,
        successorQueryFromState.trans currentQuery,
        agreement.resourceStack.activeQuery,
        agreement.resourceStack.activeBarrier,
        agreement.control.bodyBarrierTag,
        successorAlts, successorBarriers, successorFrames⟩
  have successorExactBank :
      (unifyFailureSuccessor state).control.alts =
        flattenOwnedAlts
          (afterPulledHead active nextAltTail :: resources) baseAlts := by
    calc
      (unifyFailureSuccessor state).control.alts =
          nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts :=
        successorAlts
      _ =
          nextAltTail ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts resources baseAlts := by
        rw [agreement.resourceStack.suspendedOuterAlts]
      _ =
          flattenOwnedAlts
            (afterPulledHead active nextAltTail :: resources) baseAlts := by
        rfl
  have postResource :
      PostFailureFrontierResourceStackAgrees alpha qterm bodyBarrier
        callerBarrier pending next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail outer resources callerScope outerScope
        context baseAlts (unifyFailureSuccessor state) :=
    ⟨offset, agreement.resourceStack.activeBarrier,
      agreement.resourceStack.outerAlignment,
      agreement.resourceStack.suspendedOuterAlts, successorExactBank⟩
  have post :
      SpinedPostFailureFrontierResourceRelatesAt freshFrontier alpha opened
        session pending bodyBarrier callerBarrier callerReferences
        callerExecutables outer qterm next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail resources callerScope outerScope context
        baseAlts
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state) :=
    ⟨postControl, postResource, rfl⟩
  exact
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      selectedTailEq, candidatesEq, branchCount, clauseCount, skippedRejected,
      pulls, sourceSteps, executableStep, post⟩

/-- Backward-compatible opener-session projection of retained body failure.

The current-session theorem additionally exposes the exact rejected-pull proof
object.  This specialization preserves the historical API while discarding
only that new witness. -/
theorem SpinedActiveProductResourceRelates.afterUnifyFailureRetained
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
    (nonempty : active.alts ≠ []) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (nextBranch : ClauseBranch) (nextClause : PLeaTTa.Clause)
        (nextBranchTail : List ClauseBranch)
        (nextClauseTail : List PLeaTTa.Clause)
        (nextAltTail : List PLeaTTa.Alt)
        (nextCopied : PLeaTTa.Clause),
      selectedTail = skippedBranches ++ (nextBranch :: nextBranchTail) ∧
      candidates = skippedClauses ++ (nextClause :: nextClauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      (∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false) ∧
      StepsN (count + 1)
        (.running opened.session source)
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      SpinedPostFailureFrontierResourceRelates freshFrontier alpha opened
        pending bodyBarrier callerBarrier callerReferences callerExecutables
        outer qterm next nextBranch nextClause nextBranchTail nextCopied active
        nextAltTail resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state) := by
  rcases
      PLeaTTa.PrologBodyFailureResourceTransitionBridge.SpinedActiveProductResourceRelatesAt.afterUnifyFailureRetained
        agreement leftSupported rightSupported currentSafe leftAliasSafe
        rightAliasSafe clash nonempty with
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      selectedTailEq, candidatesEq, branchCount, clauseCount, skippedRejected,
      _pulls, sourceSteps, executableStep, post⟩
  exact
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      selectedTailEq, candidatesEq, branchCount, clauseCount, skippedRejected,
      sourceSteps, executableStep, post⟩

end PLeaTTa.PrologBodyFailureResourceTransitionBridge
