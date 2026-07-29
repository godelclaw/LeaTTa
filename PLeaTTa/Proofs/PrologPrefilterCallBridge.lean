-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPrefilterCallBridge
Purpose: Derive the conservative prefilter scan from one actual prepared
  local-call candidate bank.
Trusted boundary: none
Main exports:
  VisibleEncodingSupported,
  DatabaseRelatesWorld.prepareCall_resolveAlts_prefilter
-/
import PLeaTTa.Proofs.PrologCallPayloadBridge
import PLeaTTa.Proofs.PrologCallStepBridge

namespace PLeaTTa.PrologPrefilterCallBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open CompilerAdequacy
open OpenBindingAgreement
open PrologStateBridge
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologPrefilterBridge
open PrologPrefilterScanBridge
open PrologCallStepBridge
open DemandDrivenStep
open DemandDrivenCallStep

/-!
The executable variable-name projection is not globally injective: a source
variable may deliberately use one of the generated-name spellings.  The
supported-source condition is therefore carried on the exact call-start
snapshot, rather than hidden in a global theorem or inferred from the
executable scan.
-/

/-- Every occurrence in one immutable call-start snapshot has an injective
finite source-variable encoding.  This is deliberately list-local: it neither
asserts that all strings are globally collision-free nor quantifies over
clauses invisible to this call. -/
def VisibleEncodingSupported (entries : List VersionedClause) : Prop :=
  ∀ entry, entry ∈ entries →
    EncodingInjectiveOn entry.clause.variables

/-- Eager reservation transports the supported-source certificate alongside
the exact source-ordered candidate occurrence relation. -/
theorem reserveVisible_supported_candidates
    (callGeneration : Generation) (predicate : String)
    (arguments : List Term) (bindings : Substitution)
    (freshSeed : Nat)
    {references : List VersionedClause}
    {executables : List PLeaTTa.Clause}
    (agreement :
      List.Forall₂ (CandidateClauseAgrees predicate)
        references executables)
    (supported : VisibleEncodingSupported references) :
    List.Forall₂
      (SupportedPreparedCandidateAgrees callGeneration predicate
        arguments bindings)
      (reserveVisible callGeneration arguments bindings freshSeed
        references).1
      executables := by
  induction agreement generalizing freshSeed with
  | nil =>
      exact .nil
  | @cons reference executable references executables head tail
      inductionHypothesis =>
      simp only [reserveVisible]
      exact .cons
        (.intro reference freshSeed executable head
          (supported reference (by simp)))
        (inductionHypothesis
          (reference.clause.freshCopy freshSeed).nextFresh
          (by
            intro later laterMember
            exact supported later (by simp [laterMember])))

/-- Every candidate returned by the enabled coherent executable index has
the selected input arity.  This is derived from the indexed definition rather
than added to the occurrence relation as a forgeable field. -/
theorem resolutionCandidates_member_arity
    (world : PWorld) (predicate : String) (inputArity : Nat)
    (coherent : world.ClauseIndexCoherent)
    (ready : world.clauseIndexReady = true)
    {clause : PLeaTTa.Clause}
    (member :
      clause ∈ world.resolutionCandidates predicate inputArity) :
    clause.params.length = inputArity := by
  have filtered :
      clause ∈
        (world.clausesOf predicate).filter fun candidate =>
          candidate.params.length == inputArity := by
    rw [world.resolutionCandidates_eq predicate inputArity coherent] at member
    simpa [ready] using member
  have arityTest :
      clause.params.length == inputArity := (List.mem_filter.mp filtered).2
  simpa using arityTest

/-- Membership-parametric worker for the exact cursor spine. -/
private theorem supportedCandidates_normalizedHeads_of_subset
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {branches : List ClauseBranch} {candidates : List PLeaTTa.Clause}
    (query : NormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (subset : ∀ branch, branch ∈ branches → branch ∈ cursor.remaining)
    (spine :
      List.Forall₂
        (SupportedPreparedCandidateAgrees cursor.callGeneration
          cursor.predicate cursor.arguments cursor.bindings)
        branches candidates)
    (arities :
      ∀ clause, clause ∈ candidates →
        clause.params.length = argsv.length) :
    List.Forall₂
      (fun branch clause =>
        NormalizedHeadAgrees branch argsv resv clause)
      branches candidates := by
  induction spine with
  | nil =>
      exact .nil
  | @cons branch clause branches clauses head tail inductionHypothesis =>
      exact .cons
        (supportedPreparedCandidate_normalizedHeadAgrees
          query wellFormed (subset branch (by simp)) head
          (arities clause (by simp)))
        (inductionHypothesis
          (by
            intro later laterMember
            exact subset later (by simp [laterMember]))
          (by
            intro later laterMember
            exact arities later (by simp [laterMember])))

/-- A supported prepared occurrence spine plus the real cursor invariant and
the selected executable arities yields the exact normalized-head relation
pointwise. -/
theorem supportedCandidates_normalizedHeads
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {candidates : List PLeaTTa.Clause}
    (query : NormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (spine :
      List.Forall₂
        (SupportedPreparedCandidateAgrees cursor.callGeneration
          cursor.predicate cursor.arguments cursor.bindings)
        cursor.remaining candidates)
    (arities :
      ∀ clause, clause ∈ candidates →
        clause.params.length = argsv.length) :
    List.Forall₂
      (fun branch clause =>
        NormalizedHeadAgrees branch argsv resv clause)
      cursor.remaining candidates := by
  exact supportedCandidates_normalizedHeads_of_subset
    query wellFormed (fun _ member => member) spine arities

/-- The concrete independent call opener and the concrete executable
`resolveAlts` scan satisfy the complete prefilter-bank relation.

The sole supported-source premise is the finite encoding certificate on the
actual immutable snapshot.  `query` is the still-independent caller-payload
relation; no clause decision or unifier result appears in it. -/
theorem prepareCall_resolveAlts_prefilter
    {session : LocalSession} {world : PWorld}
    (database : DatabaseRelatesWorld session.database world)
    (ready : world.clauseIndexReady = true)
    (request : CallRequest)
    (queryAlpha : List (LogicVar × String))
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier counter : Nat)
    (arity : request.arguments.length = args.length + 1)
    (query :
      NormalizedCallAgrees queryAlpha
        (prepareCall session request).1 argsv
        (PLeaTTa.subst binding res))
    (supported :
      VisibleEncodingSupported
        (session.database.visibleClausesAt session.database.generation
          request.predicate request.arguments.length)) :
    PreparedPrefilterBankRelates
      (prepareCall session request).1
      argsv args res rest binding qterm barrier
      (world.resolutionCandidates request.predicate args.length)
      counter
      (resolveAlts
        (world.resolutionCandidates request.predicate args.length)
        argsv args res rest binding qterm barrier counter).1
      (resolveAlts
        (world.resolutionCandidates request.predicate args.length)
        argsv args res rest binding qterm barrier counter).2 := by
  have queryLength :=
    PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.length_eq query.arguments
  have requestLength : request.arguments.length = argsv.length + 1 := by
    simpa only [prepareCall, Substitution.applyTerms_length,
      List.length_append, List.length_singleton] using queryLength
  have argsvLength : argsv.length = args.length := by
    omega
  have bank :=
    PrologCallEntryBridge.DatabaseRelatesWorld.prepareCall_resolveAlts
      database ready request argsv args res rest binding qterm barrier counter
      arity
  have candidates :=
    PrologCallEntryBridge.DatabaseRelatesWorld.currentResolutionCandidates
      database ready request.predicate args.length
  have supportedAtSelectedArity :
      VisibleEncodingSupported
        (session.database.visibleClausesAt session.database.generation
          request.predicate (args.length + 1)) := by
    simpa only [arity] using supported
  have supportedSpine :=
    reserveVisible_supported_candidates
      session.database.generation request.predicate request.arguments
      request.bindings (max session.nextFresh request.generatedCeiling)
      candidates supportedAtSelectedArity
  have preparedSpine :
      List.Forall₂
        (SupportedPreparedCandidateAgrees
          (prepareCall session request).1.callGeneration
          (prepareCall session request).1.predicate
          (prepareCall session request).1.arguments
          (prepareCall session request).1.bindings)
        (prepareCall session request).1.remaining
        (world.resolutionCandidates request.predicate args.length) := by
    simpa only [prepareCall, arity] using supportedSpine
  constructor
  · exact bank
  · exact supportedCandidates_normalizedHeads query
      (prepareCall_wellFormed session request) preparedSpine
      (by
        intro clause member
        rw [argsvLength]
        have filtered :
            clause ∈
              (world.clausesOf request.predicate).filter fun candidate =>
                candidate.params.length == args.length := by
          rw [world.resolutionCandidates_eq request.predicate args.length
            database.clauseIndex] at member
          simpa [ready] using member
        have arityTest :
            clause.params.length == args.length :=
          (List.mem_filter.mp filtered).2
        simpa using arityTest)

/-- Consequently the actual call-entry bank has a source-ranked conservative
scan: every executable skip is one independently certified silent rejection,
while retained false positives remain available for the later ordered-MGU
step. -/
theorem prepareCall_conservativeResolutionScan
    {session : LocalSession} {world : PWorld}
    (database : DatabaseRelatesWorld session.database world)
    (ready : world.clauseIndexReady = true)
    (request : CallRequest)
    (queryAlpha : List (LogicVar × String))
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier counter : Nat)
    (arity : request.arguments.length = args.length + 1)
    (query :
      NormalizedCallAgrees queryAlpha
        (prepareCall session request).1 argsv
        (PLeaTTa.subst binding res))
    (supported :
      VisibleEncodingSupported
        (session.database.visibleClausesAt session.database.generation
          request.predicate request.arguments.length)) :
    ConservativeResolutionScan argsv (PLeaTTa.subst binding res)
      (prepareCall session request).1.remaining
      (world.resolutionCandidates request.predicate args.length) :=
  preparedPrefilterScan
    (prepareCall_resolveAlts_prefilter
      database ready request queryAlpha argsv args res rest binding qterm
      barrier counter arity query supported)

/-! ## Actual fine call-entry state -/

/-- The paired post-entry states carry both the exact control/ownership bank
and the independently derived conservative prefilter alignment.  No
successful head MGU is asserted for a retained candidate. -/
structure CallEntryPrefilterRelates
    (opened : OpenedCall) (before : OpenConf) (pending : PendingCall)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier startCounter : Nat) : Prop where
  entry :
    CallEntryBankRelates opened before pending argsv args res rest binding
      qterm barrier startCounter
  prefilter :
    PreparedPrefilterBankRelates opened.cursor argsv args res rest binding
      qterm barrier
      (pending.persistent.world.resolutionCandidates
        opened.cursor.predicate args.length)
      startCounter pending.branches pending.persistent.counter

/-- The strengthened post-entry relation exposes the exact ranked decision
alignment without recomputing the executable filter. -/
theorem CallEntryPrefilterRelates.rankedScan
    {opened : OpenedCall} {before : OpenConf} {pending : PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      CallEntryPrefilterRelates opened before pending argsv args res rest
        binding qterm barrier startCounter) :
    ConservativeResolutionScan argsv (PLeaTTa.subst binding res)
      opened.cursor.remaining
      (pending.persistent.world.resolutionCandidates
        opened.cursor.predicate args.length) :=
  preparedPrefilterScan agreement.prefilter

/-- The concrete opener and concrete pending package satisfy the strengthened
post-entry relation.  The proof reuses the already-checked entry theorem and
rewrites the independent prefilter theorem by the actual `resolveAlts`
equation; it does not re-run or assume a second scan. -/
theorem openedFor_pendingCallOf_prefilter_relates
    {session : Session} {state : OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (predicate : String)
    (referenceArguments : List Term)
    (referenceBindings : Substitution)
    (queryAlpha : List (LogicVar × String))
    (args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referenceArguments.length = args.length + 1)
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.persistent.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.control.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter))
    (query :
      NormalizedCallAgrees queryAlpha
        (openedFor session predicate referenceArguments
          referenceBindings).cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res))
    (supported :
      VisibleEncodingSupported
        (session.resolver.database.visibleClausesAt
          session.resolver.database.generation predicate
          referenceArguments.length)) :
    CallEntryPrefilterRelates
      (openedFor session predicate referenceArguments referenceBindings)
      state (pendingCallOf state branches finalCounter)
      (args.map (PLeaTTa.subst binding)) args res rest binding
      state.control.qterm (barrierDepth state.toConf + 1)
      state.toConf.counter := by
  constructor
  · exact openedFor_pendingCallOf_relates database ready predicate
      referenceArguments referenceBindings args res rest binding
      branches finalCounter arity head scanned
  · have complete :=
      prepareCall_resolveAlts_prefilter
        database ready
        (requestFor predicate referenceArguments referenceBindings)
        queryAlpha (args.map (PLeaTTa.subst binding)) args res rest binding
        state.control.qterm (barrierDepth state.toConf + 1)
        state.toConf.counter arity query supported
    simp only [requestFor] at complete
    rw [scanned] at complete
    simpa [openedFor, openLocalCall, requestFor, prepareCall, pendingCallOf]
      using complete

/-- Exact paired call-entry transitions, strengthened through the real
prefilter bank.  A skipped executable occurrence is already known here to be
one silent independent rejection; retained occurrences remain pending for
the ordered-MGU payload proof. -/
theorem taskCall_callEnter_prefilter_correspondence
    {prog : Prog} {gt : Metta.GroundingTable}
    {session : Session} {state : OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (scope : CutScopeId) (predicate : String)
    (referenceArguments : List Term)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings : Substitution)
    (queryAlpha : List (LogicVar × String))
    (args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referenceArguments.length = args.length + 1)
    (notThrow : ¬ BuiltinThrowCall predicate referenceArguments)
    (nonempty :
      session.resolver.database.visibleClausesAt
        session.resolver.database.generation predicate
          referenceArguments.length ≠ [])
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.toConf.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter))
    (query :
      NormalizedCallAgrees queryAlpha
        (openedFor session predicate referenceArguments
          referenceBindings).cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res))
    (supported :
      VisibleEncodingSupported
        (session.resolver.database.visibleClausesAt
          session.resolver.database.generation predicate
          referenceArguments.length)) :
    RawStep session
        (.task scope
          (.call predicate referenceArguments :: referenceRest)
          referenceBindings)
        [.opened
          (requestFor predicate referenceArguments referenceBindings)]
        .none
        (openedFor session predicate referenceArguments
          referenceBindings).session
        (.running
          (.product scope
            (.cutBoundary
              (openedFor session predicate referenceArguments
                referenceBindings).scope
              (.clauses
                (openedFor session predicate referenceArguments
                  referenceBindings).scope
                (openedFor session predicate referenceArguments
                  referenceBindings).cursor))
            referenceRest)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.callPending (pendingCallOf state branches finalCounter)) ∧
      CallEntryPrefilterRelates
        (openedFor session predicate referenceArguments referenceBindings)
        state (pendingCallOf state branches finalCounter)
        (args.map (PLeaTTa.subst binding)) args res rest binding
        state.control.qterm (barrierDepth state.toConf + 1)
        state.persistent.counter := by
  have paired :=
    taskCall_callEnter_bank_correspondence (prog := prog) (gt := gt)
      database ready scope predicate referenceArguments referenceRest
      referenceBindings args res rest binding branches finalCounter arity
      notThrow nonempty head scanned
  exact ⟨paired.1, paired.2.1,
    openedFor_pendingCallOf_prefilter_relates database ready predicate
      referenceArguments referenceBindings queryAlpha args res rest binding
      branches finalCounter arity head scanned query supported⟩

/-! ### Anti-vacuity: supported source is a real restriction -/

private def collidingVisibleClause (index : Nat) : VersionedClause :=
  { id := 0
    clause :=
      { predicate := "collision"
        arguments :=
          [.variable (.source (generatedExecutableName index)),
           .variable (.generated index)]
        body := [] }
    created := 0 }

/-- The call-local support premise rejects the parser-permitted collision
between a source spelling and the corresponding generated executable name.
Thus the supported-source hypothesis cannot be discharged by `simp` for an
arbitrary snapshot. -/
theorem colliding_snapshot_not_supported (index : Nat) :
    ¬ VisibleEncodingSupported [collidingVisibleClause index] := by
  intro supported
  have injective :
      EncodingInjectiveOn
        (collidingVisibleClause index).clause.variables :=
    supported (collidingVisibleClause index) (by simp)
  change
    EncodingInjectiveOn
      [.source (generatedExecutableName index), .generated index]
    at injective
  exact source_generated_pair_not_injective index injective

end PLeaTTa.PrologPrefilterCallBridge
