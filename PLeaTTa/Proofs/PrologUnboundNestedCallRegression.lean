-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologUnboundNestedCallRegression
Purpose: Exercise the representative-preserving nested-call bridge on a
  reachable non-ground p(Z) :- q(Z) prefix.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyBridge

namespace PLeaTTa.PrologUnboundNestedCallRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open OpenBindingAgreement
open PrologAlphaFreshFrontierBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-! ## A genuinely open source program -/

def queryIdentity : LogicVar := .source "z"

def clauseIdentity : LogicVar := .source "x"

def queryTerm : Term := .variable queryIdentity

def queryAtom : Atom := .var "z"

def pReferenceClause : LocalClause :=
  { predicate := "p"
    arguments := [.variable clauseIdentity]
    body := [.call "q" [.variable clauseIdentity]] }

def qReferenceClause : LocalClause :=
  { predicate := "q"
    arguments := [.variable clauseIdentity]
    body := [] }

def pExecutableClause : PLeaTTa.Clause :=
  { params := []
    result := .var "x"
    body := [.call "q" [] (.var "x")] }

def qExecutableClause : PLeaTTa.Clause :=
  { params := []
    result := .var "x"
    body := [] }

def referenceDatabase : Database :=
  (Database.empty.assertz pReferenceClause).assertz qReferenceClause

def executableWorld : PWorld :=
  ((default : PWorld).reindexClauses.appendProgClause
      ("p", pExecutableClause)).appendProgClause
      ("q", qExecutableClause)

def rootAlpha : List (LogicVar × String) := [(queryIdentity, "z")]

private def emptyRuntimeTopological : PLeaTTa.SubstTopological [] := by
  refine
    { order := []
      nodup := by simp
      domain := ?_
      decreases := ?_ }
  · intro name
    simp [Metta.Subst.lookup]
  · intro source value dependency lookup
    simp [Metta.Subst.lookup] at lookup

private theorem rootShared : SharedRuntimeAlpha rootAlpha := by
  constructor <;> intro <;> simp_all [rootAlpha]

private theorem rootValuation :
    AlphaCumulativeResidualVariantAgreesOn rootAlpha rootAlpha [] [] [] := by
  refine
    ⟨[], TreeSubstitutionVariants.refl [],
      TreeSubstitutionTopological.nil, ?_, ⟨emptyRuntimeTopological⟩, ?_⟩
  · intro entry member
    simp at member
  · intro identity name member
    simp only [rootAlpha, List.mem_singleton] at member
    have identityEq : identity = queryIdentity := congrArg Prod.fst member
    have nameEq : name = "z" := congrArg Prod.snd member
    subst identity
    subst name
    simpa [Substitution.denote, TreeSubstitution.apply, queryIdentity] using
      (PrologPrefilterBridge.CanonicalRuntimeAgrees.variable
        (alpha := rootAlpha) (by simp [rootAlpha, queryIdentity]))

private theorem rootTaskData :
    TaskDataAgrees rootAlpha rootAlpha [] [] [] [] :=
  ⟨rootShared, TreeSubstitution.wellFormed_nil, rfl, rootValuation⟩

private theorem rootControl (barrier : Nat) :
    NormalizedAlphaGoalsAgree rootAlpha barrier
      [.call "p" [queryTerm]] [.call "p" [] queryAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.variable (by simp [rootAlpha, queryIdentity])))
      .nil

private theorem rootPayload (barrier : Nat) :
    TaskPayloadAgrees rootAlpha rootAlpha barrier [] [] [] []
      [.call "p" [queryTerm]] [.call "p" [] queryAtom] :=
  rootTaskData.withControl (rootControl barrier)

private theorem rootPayloadSupported :
    AlphaTermsSupported rootAlpha rootAlpha [queryTerm] := by
  intro term member
  simp only [List.mem_singleton] at member
  subst term
  intro name linked
  exact linked

/-! ## Source/executable clause correspondence -/

private def variableDefinedCallHeadAgrees (predicate : String) :
    CompilerAdequacy.GoalAgrees
      (.call predicate [.variable clauseIdentity])
      (.call predicate [] (.var "x")) :=
  .definedCall CompilerAdequacy.TermsAgree.nil
    (CompilerAdequacy.TermAgrees.sourceVariable "x")

private def variableDefinedCallGoalsAgrees (predicate : String) :
    CompilerAdequacy.GoalsAgree
      [.call predicate [.variable clauseIdentity]]
      [.call predicate [] (.var "x")] :=
  .cons (variableDefinedCallHeadAgrees predicate) .nil

private theorem variableDefinedCallHeadSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalAgreesSupported
      [clauseIdentity] [clauseIdentity]
      (variableDefinedCallHeadAgrees predicate) := by
  unfold variableDefinedCallHeadAgrees
  refine
    @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.definedCall
      [clauseIdentity] [clauseIdentity] predicate predicate []
      (.variable clauseIdentity) [] (.var "x")
      CompilerAdequacy.TermsAgree.nil
      (CompilerAdequacy.TermAgrees.sourceVariable "x") ?_ ?_
  · simp [CompilerGoalSubstitutionAdequacy.TermsAgreeSupported,
      CompilerSubstitutionAdequacy.termsVariablesIn]
  · simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
      CompilerSubstitutionAdequacy.termVariablesIn, clauseIdentity]

private theorem variableDefinedCallGoalsSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
      [clauseIdentity] [clauseIdentity]
      (variableDefinedCallGoalsAgrees predicate) := by
  unfold variableDefinedCallGoalsAgrees
  exact .cons (variableDefinedCallHeadSupported predicate) .nil

private theorem pClauseAgrees :
    LocalClauseAgrees pReferenceClause ("p", pExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := ?_
      support := ?_ }
  · exact
      ⟨[], .variable clauseIdentity, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · exact variableDefinedCallGoalsAgrees "q"
  · intro name
    simp [pReferenceClause, pExecutableClause, clauseIdentity,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables,
      OpenBindingAgreement.logicVarExecutableName]

private theorem qClauseAgrees :
    LocalClauseAgrees qReferenceClause ("q", qExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], .variable clauseIdentity, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · intro name
    simp [qReferenceClause, qExecutableClause, clauseIdentity,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables,
      OpenBindingAgreement.logicVarExecutableName]

private theorem emptyDatabaseRelatesIndexedWorld :
    DatabaseRelatesWorld Database.empty
      ((default : PWorld).reindexClauses) := by
  refine
    { reachable := DatabaseActions.DatabaseReachable.empty
      liveClauses := ?_
      clauseIndex := PWorld.reindexClauses_coherent _ }
  exact .nil

theorem referenceDatabase_relates_executableWorld :
    DatabaseRelatesWorld referenceDatabase executableWorld := by
  have p := emptyDatabaseRelatesIndexedWorld.assertz pClauseAgrees
  have q := p.assertz qClauseAgrees
  simpa [referenceDatabase, executableWorld] using q

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have p := PWorld.appendProgClause_coherent _ ("p", pExecutableClause) root
  have q := PWorld.appendProgClause_coherent _ ("q", qExecutableClause) p
  simpa [executableWorld] using q

private theorem pResolutionCandidates :
    executableWorld.resolutionCandidates "p" 0 = [pExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, pExecutableClause, emptyClauses]

private theorem qResolutionCandidates :
    executableWorld.resolutionCandidates "q" 0 = [qExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, qExecutableClause, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [Database.empty.allocate pReferenceClause] := by
  rfl

private theorem qVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "q" 1 =
      [(Database.empty.assertz pReferenceClause).allocate qReferenceClause] := by
  rfl

private theorem pCandidateBank :
    SupportedCandidateBank "p"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1)
      (executableWorld.resolutionCandidates "p" 0) := by
  rw [pVisibleClauses, pResolutionCandidates]
  let head : CandidateClauseAgrees "p"
      (Database.empty.allocate pReferenceClause) pExecutableClause := by
    change LocalClauseAgrees pReferenceClause ("p", pExecutableClause)
    exact pClauseAgrees
  have encoding :
      EncodingInjectiveOn
        (Database.empty.allocate pReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, Database.allocate, pReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, clauseIdentity]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate pReferenceClause).clause.variables
        (Database.empty.allocate pReferenceClause).clause.variables
        head.body := by
    change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        [clauseIdentity] [clauseIdentity] head.body
    have bodyEq : head.body = variableDefinedCallGoalsAgrees "q" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact variableDefinedCallGoalsSupported "q"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

/-! ## Exact root entry and retained occurrence -/

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "p" [] queryAtom], [])
        alts := []
        qterm := queryAtom } }

private def pScan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] queryAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf pScan.1 pScan.2

private theorem pEntry :
    RepresentativeSupportedCallEntryRelates rootAlpha
      (openedFor initialSession "p" [queryTerm] []) initialOpenConf pPending
      [] [] queryAtom [] [] queryAtom
      (barrierDepth initialOpenConf.toConf + 1)
      initialOpenConf.toConf.counter := by
  have database :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using
      referenceDatabase_relates_executableWorld
  have ready : initialOpenConf.persistent.world.clauseIndexReady = true := by
    rfl
  have scanned :
      resolveAlts
          (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
          [] [] queryAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = pScan := by
    rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (rootPayload (barrierDepth initialOpenConf.toConf + 1))
      rootPayloadSupported
      (openedFor initialSession "p" [queryTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "p" [queryTerm] [] rootAlpha [] queryAtom [] []
      pScan.1 pScan.2 (by rfl) (by rfl)
      (by
        calc
          _ = pScan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (pScan.1, pScan.2) := (Prod.eta pScan).symm) query pCandidateBank
  simpa [pPending, initialOpenConf] using constructed

private theorem initialBelow :
    ConfBelowResolutionCounter initialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, initialOpenConf, OpenConf.toConf, Control.toConf,
    specializationGoalsVars, specializationGoalVars, resolutionSubstVars,
    queryAtom, Metta.Atom.vars] at member
  subst name
  simp [resolutionSeedHighWaterName, terminalResolutionSeed?,
    terminalResolutionSeedRev, initialOpenConf, OpenConf.toConf,
    Control.toConf]

private def pCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] []
    initialOpenConf.control.qterm initialOpenConf.toConf.counter
    (barrierDepth initialOpenConf.toConf + 1) pExecutableClause

private def pAlt : PLeaTTa.Alt :=
  .br
    (.eq (.expr [queryAtom])
        (.expr (pCopied.params ++ [pCopied.result])) ::
      pCopied.body)
    []

private theorem pScanExact :
    pScan = ([pAlt], initialOpenConf.toConf.counter + 1) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 0) [] [] queryAtom
        [] [] queryAtom 1 0 =
      ([pAlt], 1)
  rw [pResolutionCandidates]
  simp [resolveAlts, pExecutableClause, queryAtom, pAlt, pCopied,
    initialOpenConf, OpenConf.toConf, Control.toConf, barrierDepth,
    PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList]

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

/-- The source clause variable is standardized apart to generated identity
zero before head unification. -/
private def pPreparedBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate pReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated 0))]
    headEquations := [(queryTerm, .variable (.generated 0))]
    body := [.call "q" [.variable (.generated 0)]]
    bindings := []
    firstFresh := 0
    nextFresh := 1 }

private theorem pOpenedRemaining :
    (openedFor initialSession "p" [queryTerm] []).cursor.remaining =
      [pPreparedBranch] := by
  rfl

def pSourceExtension : Substitution :=
  TreeSubstitution.reify
    [(queryIdentity, .variable (.generated 0))]

/-- Ordered source head resolution chooses the left-variable orientation
`Z ↦ generated 0`; the opposite MGU is semantically variant but is not the
ordered resolver's returned association list. -/
private theorem pPreparedBranch_resolves :
    HeadResolution pPreparedBranch pSourceExtension := by
  let extension : TreeSubstitution :=
    [(queryIdentity, .variable (.generated 0))]
  have computed :
      ComputesDenotationalMgu
        [(.variable queryIdentity, .variable (.generated 0))]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_left_variable queryIdentity
      (.variable (.generated 0)) (by
        intro equality
        cases equality) (by rfl)
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · simpa [pPreparedBranch, ClauseBranch.normalizedHeadEquations,
      extension, queryTerm] using computed
  · simp [pSourceExtension, extension, pPreparedBranch]

/-- The concrete singleton occurrence is the unique retained source and
executable clause; no rejected-prefix count is hidden in the witness. -/
private theorem pRetainedFrontier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish branch clause branchTail clauseTail altTail copied,
      branch = pPreparedBranch ∧
      branchTail = [] ∧
      clause = pExecutableClause ∧
      clauseTail = [] ∧
      copied = pCopied ∧
      RejectedPullsN 0
        (openedFor initialSession "p" [queryTerm] []).cursor finish ∧
      DemandDrivenCallStep.Step prog gt (.callPending pPending)
        (.ready pPending.pulled) ∧
      RepresentativeRetainedCallFrontier rootAlpha
        (openedFor initialSession "p" [queryTerm] []) initialOpenConf
        pPending finish branch clause branchTail clauseTail altTail copied
        [] [] queryAtom [] [] queryAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, sourceShape,
      executableShape, sourceCount, executableCount, pulls, _sourceSteps,
      executableStep, frontier⟩ :=
    RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
      (prog := prog) (gt := gt) pEntry initialBelow pScanNonempty
  change [pPreparedBranch] =
    skippedBranches ++ branch :: branchTail at sourceShape
  have executableCandidates :
      pPending.persistent.world.resolutionCandidates
          (openedFor initialSession "p" [queryTerm] []).cursor.predicate 0 =
        [pExecutableClause] := by
    simpa [pPending, initialOpenConf, openedFor, openLocalCall, requestFor,
      prepareCall] using pResolutionCandidates
  simp only [List.length_nil] at executableShape
  rw [executableCandidates] at executableShape
  have executableLengths := congrArg List.length executableShape
  simp only [List.length_cons, List.length_nil, List.length_append] at executableLengths
  have skippedClausesLength : skippedClauses.length = 0 := by omega
  have clauseTailLength : clauseTail.length = 0 := by omega
  have skippedClausesNil : skippedClauses = [] :=
    List.eq_nil_of_length_eq_zero skippedClausesLength
  have clauseTailNil : clauseTail = [] :=
    List.eq_nil_of_length_eq_zero clauseTailLength
  have countZero : count = 0 := by omega
  have clauseExact : clause = pExecutableClause := by
    subst skippedClauses
    subst clauseTail
    simpa using executableShape.symm
  have sourceLengths := congrArg List.length sourceShape
  simp only [List.length_cons, List.length_nil, List.length_append] at sourceLengths
  have skippedBranchesLength : skippedBranches.length = 0 := by omega
  have branchTailLength : branchTail.length = 0 := by omega
  have skippedBranchesNil : skippedBranches = [] :=
    List.eq_nil_of_length_eq_zero skippedBranchesLength
  have branchTailNil : branchTail = [] :=
    List.eq_nil_of_length_eq_zero branchTailLength
  have branchExact : branch = pPreparedBranch := by
    subst skippedBranches
    subst branchTail
    simpa using sourceShape.symm
  have copiedExact : copied = pCopied := by
    rw [frontier.copiedExact, clauseExact]
    rfl
  have pullsZero :
      RejectedPullsN 0
        (openedFor initialSession "p" [queryTerm] []).cursor finish := by
    simpa [countZero] using pulls
  exact
    ⟨finish, branch, clause, branchTail, clauseTail, altTail, copied,
      branchExact, branchTailNil, clauseExact, clauseTailNil, copiedExact,
      pullsZero, executableStep, frontier⟩

/-! ## Reachable materialized recursive head -/

private def rootScope : CutScopeId := 0

private theorem pCopied_body :
    pCopied.body = [.call "q" [] pCopied.result] := by
  rfl

/-- The actual open `p(Z)` call enters `p(X) :- q(X)` and exposes the next
`q` head through the representative-preserving materialized interface.

The final conjunct is the anti-vacuity hinge: the fresh source identity is
not in the caller's old support, so the legacy raw-support interface really
cannot justify this reachable next call. -/
theorem reachable_unbound_p_to_q_materialized
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (finish : PreparedCursor) (branch : ClauseBranch)
      (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
      (copied : PLeaTTa.Clause),
      ∃ representative nextAlpha sourceCanonical flattened installed,
        branch = pPreparedBranch ∧
        copied = pCopied ∧
        RepresentativeProductActivationCore prog gt rootAlpha rootAlpha [] []
          (openedFor initialSession "p" [queryTerm] []) pPending finish branch
          branchTail altTail copied [] [] queryAtom
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter rootScope pSourceExtension
          representative nextAlpha sourceCanonical flattened installed ∧
        StepsN 2
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          (.running
            (openedFor initialSession "p" [queryTerm] []).session
            (activatedSourceProduct rootScope
              (openedFor initialSession "p" [queryTerm] []) finish branch
              branchTail pSourceExtension [])) ∧
        DemandDrivenCallStep.StepsN prog gt 3
          (.ready initialOpenConf)
          (.ready
            (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
              pPending copied [] queryAtom installed)) ∧
        MaterializedCallAgreesWith nextAlpha pSourceExtension
          [.variable (.generated 0)] []
          (PLeaTTa.subst
            (PLeaTTa.trimFor copied.body queryAtom installed)
            copied.result)
          (flattened ++ representative) [] ∧
        ¬ AlphaTermsSupported nextAlpha rootAlpha
          [(.variable (.generated 0))] := by
  obtain
    ⟨finish, branch, clause, branchTail, clauseTail, altTail, copied,
      branchExact, branchTailNil, clauseExact, clauseTailNil, copiedExact,
      pulls, finePull, frontier⟩ :=
    pRetainedFrontier (prog := prog) (gt := gt)
  subst branch
  subst copied
  have resolved : HeadResolution pPreparedBranch pSourceExtension := by
    exact pPreparedBranch_resolves
  have preHeadPayload :
      TaskSpinePayloadAgrees rootAlpha rootAlpha [] [] [] []
        [{ barrier := 0
           references := [.call "p" [queryTerm]]
           executables := [.call "p" [] queryAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have preHeadTask :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.headPayload
      preHeadPayload
  obtain ⟨representative, oldCumulative, materializedAtOpen⟩ :=
    (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
      preHeadTask).materializedCallAgreesWith rootPayloadSupported
  have queryAtOpen :=
    materializedAtOpen.toRepresentativeNormalizedCallAgreesWith
      (openedFor initialSession "p" [queryTerm] []).cursor
      (by rfl) (by rfl)
  have referenceBelow :
      GeneratedBelow finish.reservationStart (rootAlpha.map Prod.fst) := by
    intro index member
    simp [rootAlpha, queryIdentity] at member
  have executableLive :
      ∀ name, name ∈ rootAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars [] queryAtom [] [] queryAtom := by
    intro name member
    simp only [rootAlpha, List.map_singleton, List.mem_singleton] at member
    subst name
    simp [resolutionOccupiedVars, queryAtom, Metta.Atom.vars]
  have live : AlphaRuntimeNamesLive rootAlpha (pCopied.body ++ []) queryAtom := by
    intro identity name member
    simp only [rootAlpha, List.mem_singleton] at member
    have identityEq : identity = queryIdentity := congrArg Prod.fst member
    have nameEq : name = "z" := congrArg Prod.snd member
    subst identity
    subst name
    change PLeaTTa.isTrimRoot (pCopied.body ++ []) queryAtom "z" = true
    exact PLeaTTa.isTrimRoot_qterm_mem _ queryAtom "z"
      (by simp [queryAtom, Metta.Atom.vars])
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, installed, activation⟩ :=
    RepresentativeRetainedCallFrontier.activate_spined_product_step_with
      (prog := prog) (gt := gt) (referencePayload := [queryTerm])
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (callerBarrier := 0) (callerScope := rootScope)
      pEntry frontier preHeadPayload oldCumulative queryAtOpen
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      referenceBelow executableLive live resolved
  have dispatch :=
    PrologCallEntryBridge.DatabaseRelatesWorld.callResolve_dispatch
      pEntry.entry.database pEntry.indexReady "p" 0
      (by
        have nonempty :
            referenceDatabase.visibleClausesAt referenceDatabase.generation
              "p" 1 ≠ [] := by
          rw [pVisibleClauses]
          simp
        simpa [openedFor, openLocalCall, initialSession] using nonempty)
  have scanned :
      resolveAlts
          (initialOpenConf.toConf.world.resolutionCandidates "p" 0)
          [] [] queryAtom [] [] initialOpenConf.toConf.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter =
        (pScan.1, pScan.2) := by
    change pScan = (pScan.1, pScan.2)
    exact (Prod.eta pScan).symm
  have finishExact :
      finish = (openedFor initialSession "p" [queryTerm] []).cursor := by
    cases pulls
    rfl
  have pNotThrow : ¬ BuiltinThrowCall "p" [queryTerm] := by
    simp [BuiltinThrowCall]
  have pNotDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [queryTerm] = none := by
    rfl
  have sourceEntryRaw :
      RawStep initialSession
        (.task rootScope [.call "p" [queryTerm]] [])
        [.opened (requestFor "p" [queryTerm] [])] .none
        (openedFor initialSession "p" [queryTerm] []).session
        (.running
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [queryTerm] [])
            (openedFor initialSession "p" [queryTerm] []).cursor [])) := by
    simpa [sourceProductFrontier] using
      (RawStep.taskCall rootScope "p" [queryTerm] [] [] initialSession
        pNotThrow pNotDatabase)
  have sourceEntryTransition :
      Transition
        (.running initialSession
          (.task rootScope [.call "p" [queryTerm]] []))
        [.opened (requestFor "p" [queryTerm] [])]
        (.running
          (openedFor initialSession "p" [queryTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [queryTerm] [])
            (openedFor initialSession "p" [queryTerm] []).cursor [])) := by
    exact Transition.ordinary _ _ _ _ _ sourceEntryRaw
  have sourceEntryTransitionFinish :
      Transition
        (.running initialSession
          (.task rootScope [.call "p" [queryTerm]] []))
        [.opened (requestFor "p" [queryTerm] [])]
        (.running
          (openedFor initialSession "p" [queryTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [queryTerm] []) finish [])) := by
    simpa [finishExact] using sourceEntryTransition
  have sourceActivationTransition :
      Transition
        (.running
          (openedFor initialSession "p" [queryTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [queryTerm] []) finish []))
        []
        (.running
          (openedFor initialSession "p" [queryTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [queryTerm] []) finish
            pPreparedBranch branchTail pSourceExtension [])) := by
    exact Transition.ordinary _ _ _ _ _ activation.sourceStep
  have rootSourceSteps :
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [queryTerm]] []))
        [.opened (requestFor "p" [queryTerm] [])]
        (.running
          (openedFor initialSession "p" [queryTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [queryTerm] []) finish
            pPreparedBranch branchTail pSourceExtension [])) := by
    simpa using
      StepsN.succ 1 _ _ _ _ _ sourceEntryTransitionFinish
        (StepsN.succ 0 _ _ _ _ _ sourceActivationTransition
          (StepsN.zero _))
  have fineEntry :
      DemandDrivenCallStep.Step prog gt (.ready initialOpenConf)
        (.callPending pPending) := by
    simpa [pPending] using
      (DemandDrivenCallStep.Step.callEnter initialOpenConf "p" [] queryAtom
        [] [] pScan.1 pScan.2 (by rfl) dispatch.1 dispatch.2 scanned)
  have rootFineSteps :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready initialOpenConf)
        (.ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pPending pCopied [] queryAtom installed)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 2 _ _ _ fineEntry
        (DemandDrivenCallStep.StepsN.succ 1 _ _ _ finePull
          (DemandDrivenCallStep.StepsN.succ 0 _ _ _
            activation.fineExecutableStep
            (DemandDrivenCallStep.StepsN.zero _)))
  have materialized :
      MaterializedCallAgreesWith nextAlpha pSourceExtension
        [.variable (.generated 0)] []
        (PLeaTTa.subst
          (PLeaTTa.trimFor pCopied.body queryAtom installed)
          pCopied.result)
        (flattened ++ representative) [] := by
    have exactHead := activation.materializedBodyHeads
      (by rfl)
      pCopied_body
    simpa using exactHead
  have rawUnsupported :
      ¬ AlphaTermsSupported nextAlpha rootAlpha
        [(.variable (.generated 0))] := by
    intro supported
    have linked :
        ∃ name, ((.generated 0 : LogicVar), name) ∈ nextAlpha := by
      have bodyControl :
          NormalizedAlphaGoalsAgree nextAlpha
            (barrierDepth initialOpenConf.toConf + 1)
            [.call "q" [.variable (.generated 0)]]
            [.call "q" [] pCopied.result] := by
        simpa [pPreparedBranch, pCopied_body] using
          activation.bodyPayload.control
      obtain
        ⟨referenceArguments, referenceResult, payloadShape, _arguments,
          result, _tail⟩ :=
        NormalizedAlphaGoalsAgree.localCallHead bodyControl
      have referenceArgumentsNil : referenceArguments = [] := by
        simpa using congrArg List.length payloadShape
      subst referenceArguments
      simp only [List.nil_append, List.singleton_inj] at payloadShape
      subst referenceResult
      obtain ⟨name, _runtimeShape, link⟩ :=
        PLeaTTa.PrologMguTopology.AlphaTermAgrees.source_variable_linked result
      exact ⟨name, link⟩
    obtain ⟨name, linked⟩ := linked
    have observed := supported (.variable (.generated 0)) (by simp)
    have mustBeOld := observed name linked
    simp [rootAlpha, queryIdentity] at mustBeOld
  exact
    ⟨finish, pPreparedBranch, branchTail, altTail, pCopied, representative,
      nextAlpha, sourceCanonical, flattened, installed, rfl,
      rfl, activation.toRepresentativeProductActivationCore,
      rootSourceSteps, rootFineSteps, materialized, rawUnsupported⟩

end PLeaTTa.PrologUnboundNestedCallRegression
