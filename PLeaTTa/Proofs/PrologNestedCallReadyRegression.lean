-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedCallReadyRegression
Purpose: Inhabit the state-indexed nested-call bridge with one concrete,
  source-ordered p -> q -> r local-resolution prefix.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyBridge

namespace PLeaTTa.PrologNestedCallReadyRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologMguTopology
open PrologMguVariant
open PrologMguBridge
open PrologOrdinaryStepBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open OpenBindingAgreement
open SourceControlResourcePayloadContextAgrees

/-! ## Ground source and executable program -/

def resultTerm : Term := .integer 7

def resultAtom : Atom := .gnd (.int 7)

def pReferenceClause : LocalClause :=
  { predicate := "p"
    arguments := [resultTerm]
    body := [.call "q" [resultTerm]] }

def qReferenceClause : LocalClause :=
  { predicate := "q"
    arguments := [resultTerm]
    body := [.call "r" [resultTerm]] }

def rReferenceClause : LocalClause :=
  { predicate := "r"
    arguments := [resultTerm]
    body := [] }

def pExecutableClause : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.call "q" [] resultAtom] }

def qExecutableClause : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.call "r" [] resultAtom] }

def rExecutableClause : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [] }

def referenceDatabase : Database :=
  ((Database.empty.assertz pReferenceClause).assertz qReferenceClause).assertz
    rReferenceClause

def executableWorld : PWorld :=
  (((default : PWorld).reindexClauses.appendProgClause
      ("p", pExecutableClause)).appendProgClause
      ("q", qExecutableClause)).appendProgClause
      ("r", rExecutableClause)

/-! ## Empty cumulative valuation and ground control -/

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
        TreeSubstitutionTopological.nil, ?_,
        ⟨emptyRuntimeTopological⟩, ?_⟩
    · intro entry member
      simp at member
    · intro identity name member
      simp at member

private theorem groundCallControl (barrier : Nat) (predicate : String) :
    NormalizedAlphaGoalsAgree [] barrier
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.integer (alpha := []) 7))
      .nil

private theorem groundCallPayload (barrier : Nat) (predicate : String) :
    TaskPayloadAgrees [] [] barrier [] [] [] []
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] :=
  emptyTaskData.withControl (groundCallControl barrier predicate)

private theorem groundPayloadSupported :
    AlphaTermsSupported [] [] [resultTerm] := by
  intro term member
  simp only [List.mem_singleton] at member
  subst term
  simp [resultTerm, AlphaTreeSupported, Term.denote,
    PrologMguOpenAgreement.TreeVariablesSatisfy,
    PrologMguOpenAgreement.TreesVariablesSatisfy]

/-! ## Exact database/world correspondence -/

private theorem pClauseAgrees :
    LocalClauseAgrees pReferenceClause ("p", pExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := ?_
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · exact
      .cons
        (.definedCall CompilerAdequacy.TermsAgree.nil
          (CompilerAdequacy.TermAgrees.integer 7))
        .nil
  · intro name
    simp [pReferenceClause, pExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem qClauseAgrees :
    LocalClauseAgrees qReferenceClause ("q", qExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := ?_
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · exact
      .cons
        (.definedCall CompilerAdequacy.TermsAgree.nil
          (CompilerAdequacy.TermAgrees.integer 7))
        .nil
  · intro name
    simp [qReferenceClause, qExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem rClauseAgrees :
    LocalClauseAgrees rReferenceClause ("r", rExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · intro name
    simp [rReferenceClause, rExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables]

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
  have r := q.assertz rClauseAgrees
  simpa [referenceDatabase, executableWorld] using r

/-! ## Concrete root runtime -/

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "p" [] resultAtom], [])
        alts := []
        qterm := resultAtom } }

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have p := PWorld.appendProgClause_coherent _ ("p", pExecutableClause) root
  have q := PWorld.appendProgClause_coherent _ ("q", qExecutableClause) p
  have r := PWorld.appendProgClause_coherent _ ("r", rExecutableClause) q
  simpa [executableWorld] using r

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

private theorem rResolutionCandidates :
    executableWorld.resolutionCandidates "r" 0 = [rExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, rExecutableClause, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [((Database.empty.allocate pReferenceClause))] := by
  rfl

private theorem qVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "q" 1 =
      [(((Database.empty.assertz pReferenceClause).allocate
        qReferenceClause))] := by
  rfl

private theorem rVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "r" 1 =
      [((((Database.empty.assertz pReferenceClause).assertz
        qReferenceClause).allocate rReferenceClause))] := by
  rfl

private def groundDefinedCallHeadAgrees (predicate : String) :
    CompilerAdequacy.GoalAgrees
      (.call predicate [resultTerm])
      (.call predicate [] resultAtom) :=
  .definedCall CompilerAdequacy.TermsAgree.nil
    (CompilerAdequacy.TermAgrees.integer 7)

private def groundDefinedCallGoalsAgrees (predicate : String) :
    CompilerAdequacy.GoalsAgree
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] :=
  .cons (groundDefinedCallHeadAgrees predicate) .nil

private theorem groundDefinedCallHeadSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalAgreesSupported [] []
      (groundDefinedCallHeadAgrees predicate) := by
  unfold groundDefinedCallHeadAgrees
  refine
    @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.definedCall
      [] [] predicate predicate [] resultTerm [] resultAtom
      CompilerAdequacy.TermsAgree.nil
      (CompilerAdequacy.TermAgrees.integer 7) ?_ ?_
  · simp [CompilerGoalSubstitutionAdequacy.TermsAgreeSupported,
      CompilerSubstitutionAdequacy.termsVariablesIn]
  · simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
      CompilerSubstitutionAdequacy.termVariablesIn, resultTerm]

private theorem groundDefinedCallGoalsSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      (groundDefinedCallGoalsAgrees predicate) := by
  unfold groundDefinedCallGoalsAgrees
  exact .cons (groundDefinedCallHeadSupported predicate) .nil

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
      goalVariables, resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate pReferenceClause).clause.variables
        (Database.empty.allocate pReferenceClause).clause.variables
        head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq : head.body = groundDefinedCallGoalsAgrees "q" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "q"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

private theorem qCandidateBank :
    SupportedCandidateBank "q"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "q" 1)
      (executableWorld.resolutionCandidates "q" 0) := by
  rw [qVisibleClauses, qResolutionCandidates]
  let previous := Database.empty.assertz pReferenceClause
  let head : CandidateClauseAgrees "q"
      (previous.allocate qReferenceClause) qExecutableClause := by
    change LocalClauseAgrees qReferenceClause ("q", qExecutableClause)
    exact qClauseAgrees
  have encoding :
      EncodingInjectiveOn (previous.allocate qReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, previous, Database.allocate, qReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (previous.allocate qReferenceClause).clause.variables
        (previous.allocate qReferenceClause).clause.variables head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq : head.body = groundDefinedCallGoalsAgrees "r" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "r"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

private theorem rCandidateBank :
    SupportedCandidateBank "r"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "r" 1)
      (executableWorld.resolutionCandidates "r" 0) := by
  rw [rVisibleClauses, rResolutionCandidates]
  let previous :=
    (Database.empty.assertz pReferenceClause).assertz qReferenceClause
  let head : CandidateClauseAgrees "r"
      (previous.allocate rReferenceClause) rExecutableClause := by
    change LocalClauseAgrees rReferenceClause ("r", rExecutableClause)
    exact rClauseAgrees
  have encoding :
      EncodingInjectiveOn (previous.allocate rReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, previous, Database.allocate, rReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (previous.allocate rReferenceClause).clause.variables
        (previous.allocate rReferenceClause).clause.variables head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq :
        head.body = (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

/-! ## Root `p` entry and activation -/

private def pScan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] resultAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf pScan.1 pScan.2

private theorem pEntry :
    RepresentativeSupportedCallEntryRelates []
      (openedFor initialSession "p" [resultTerm] []) initialOpenConf pPending
      [] [] resultAtom [] [] resultAtom
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
          [] [] resultAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = pScan := by
    rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (groundCallPayload (barrierDepth initialOpenConf.toConf + 1) "p")
      groundPayloadSupported
      (openedFor initialSession "p" [resultTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "p" [resultTerm] [] [] [] resultAtom [] []
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
    resultAtom, Metta.Atom.vars] at member

private def pCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] resultAtom [] []
    initialOpenConf.control.qterm initialOpenConf.toConf.counter
    (barrierDepth initialOpenConf.toConf + 1) pExecutableClause

private def pAlt : PLeaTTa.Alt :=
  .br
    (.eq (.expr [resultAtom])
        (.expr (pCopied.params ++ [pCopied.result])) ::
      pCopied.body)
    []

private theorem pScanExact :
    pScan = ([pAlt], initialOpenConf.toConf.counter + 1) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 0) [] [] resultAtom
        [] [] resultAtom 1 0 =
      ([pAlt], 1)
  rw [pResolutionCandidates]
  have argumentsMatch : PLeaTTa.prologMatchCompatList [] [] = true := rfl
  have resultMatch :
      PLeaTTa.prologMatchCompat
        (.gnd (.int 7)) (.gnd (.int 7)) = true := by
    rfl
  simp [resolveAlts, pExecutableClause, resultAtom, pAlt, pCopied,
    initialOpenConf, OpenConf.toConf, Control.toConf, barrierDepth,
    argumentsMatch, resultMatch]

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

/-! ## Exact retained source occurrence -/

/-- The literal standardized source occurrence opened for the ground `p/1`
call.  The clause has no variables, so eager standardization reserves the
empty interval `[0,0)` and leaves its head and body unchanged. -/
private def pPreparedBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate pReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "q" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem pOpenedRemaining :
    (openedFor initialSession "p" [resultTerm] []).cursor.remaining =
      [pPreparedBranch] := by
  rfl

private theorem pPreparedBranch_unifies :
    DenotationalUnifiesEquations []
      pPreparedBranch.normalizedHeadEquations := by
  intro equation member
  simp [pPreparedBranch, ClauseBranch.normalizedHeadEquations] at member
  subst equation
  rfl

/-- Reflexive ground head matching computes exactly the empty extension. -/
private theorem pPreparedBranch_resolves_empty :
    HeadResolution pPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [pPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [pPreparedBranch]

/-- The literal standardized source occurrence opened for the nested ground
`q/1` call. -/
private def qPreparedBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz pReferenceClause).allocate qReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "r" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem qPreparedBranch_resolves_empty :
    HeadResolution qPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [qPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [qPreparedBranch]

/-- The literal standardized source occurrence opened for the second nested
ground `r/1` call. -/
private def rPreparedBranch : ClauseBranch :=
  { sourceId :=
      (((Database.empty.assertz pReferenceClause).assertz qReferenceClause).allocate
        rReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem rPreparedBranch_resolves_empty :
    HeadResolution rPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [rPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [rPreparedBranch]

/-- The generic representative-frontier decomposition is non-vacuously
inhabited by the unique source and executable `p/1` occurrences.  In
particular, the maximal rejected prefix is exactly empty on both sides. -/
private theorem pRetainedFrontier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish branch clause branchTail clauseTail altTail copied,
      branch = pPreparedBranch ∧
      branchTail = [] ∧
      clause = pExecutableClause ∧
      clauseTail = [] ∧
      copied = pCopied ∧
      RejectedPullsN 0
        (openedFor initialSession "p" [resultTerm] []).cursor finish ∧
      StepsN 0
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (.clauses (openedFor initialSession "p" [resultTerm] []).scope
            (openedFor initialSession "p" [resultTerm] []).cursor)) []
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (.clauses (openedFor initialSession "p" [resultTerm] []).scope
            finish)) ∧
      DemandDrivenCallStep.Step prog gt (.callPending pPending)
        (.ready pPending.pulled) ∧
      RepresentativeRetainedCallFrontier []
        (openedFor initialSession "p" [resultTerm] []) initialOpenConf
        pPending finish branch clause branchTail clauseTail altTail copied
        [] [] resultAtom [] [] resultAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, sourceShape,
      executableShape, sourceCount, executableCount, pulls, sourceSteps,
      executableStep, frontier⟩ :=
    RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
      (prog := prog) (gt := gt) pEntry initialBelow pScanNonempty
  change [pPreparedBranch] =
    skippedBranches ++ branch :: branchTail at sourceShape
  have executableCandidates :
      pPending.persistent.world.resolutionCandidates
          (openedFor initialSession "p" [resultTerm] []).cursor.predicate
          0 =
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
        (openedFor initialSession "p" [resultTerm] []).cursor finish := by
    simpa [countZero] using pulls
  have sourceStepsZero :
      StepsN 0
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (.clauses (openedFor initialSession "p" [resultTerm] []).scope
            (openedFor initialSession "p" [resultTerm] []).cursor)) []
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (.clauses (openedFor initialSession "p" [resultTerm] []).scope
            finish)) := by
    simpa [countZero] using sourceSteps
  exact
    ⟨finish, branch, clause, branchTail, clauseTail, altTail, copied,
      branchExact, branchTailNil, clauseExact, clauseTailNil, copiedExact,
      pullsZero, sourceStepsZero, executableStep, frontier⟩

/-! ## Concrete root activation -/

private def rootScope : CutScopeId := 0

/-- The real `p/1` entry activates its unique clause and produces a literal
active carrier whose next source and executable goals are both `q(7)`. -/
private theorem pActive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : ActivePayloadState,
      state.index.bodyReferences = [.call "q" [resultTerm]] ∧
      state.index.bodyExecutables = [.call "q" [] resultAtom] ∧
      state.index.alpha = [] ∧
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.session.resolver.database = referenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = executableWorld ∧
      ConfBelowResolutionCounter state.index.openConf.toConf ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) state.fineState := by
  obtain
    ⟨finish, branch, clause, branchTail, clauseTail, altTail, copied,
      branchExact, branchTailNil, clauseExact, clauseTailNil, copiedExact,
      pulls, _sourceSteps, finePull, frontier⟩ :=
    pRetainedFrontier (prog := prog) (gt := gt)
  have unifies :
      DenotationalUnifiesEquations [] branch.normalizedHeadEquations := by
    simpa [branchExact] using pPreparedBranch_unifies
  obtain ⟨independentResult, resolved⟩ :=
    HeadResolution.exists_of_unifier [] unifies
  have exactResolution : HeadResolution branch [] := by
    simpa [branchExact] using pPreparedBranch_resolves_empty
  have independentResultEq : independentResult = [] :=
    HeadResolution.deterministic resolved exactResolution
  have preHeadPayload :
      TaskSpinePayloadAgrees [] [] [] [] [] []
        [{ barrier := 0
           references := [.call "p" [resultTerm]]
           executables := [.call "p" [] resultAtom] }] :=
    TaskSpinePayloadAgrees.singleton (groundCallPayload 0 "p")
  have referenceBelow : GeneratedBelow finish.reservationStart [] := by
    intro index member
    simp at member
  have executableLive :
      ∀ name, name ∈ ([] : List (LogicVar × String)).map Prod.snd →
        name ∈
          resolutionOccupiedVars [] resultAtom [] [] resultAtom := by
    intro name member
    simp at member
  have live : AlphaRuntimeNamesLive [] (copied.body ++ []) resultAtom := by
    intro identity name member
    simp at member
  obtain
    ⟨representative, nextAlpha, sourceCanonical, flattenedRepresentative,
      installed, activation⟩ :=
    RepresentativeRetainedCallFrontier.activate_spined_product_step
      (prog := prog) (gt := gt) (referencePayload := [resultTerm])
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (callerBarrier := 0) (callerScope := rootScope)
      pEntry frontier preHeadPayload groundPayloadSupported
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      referenceBelow executableLive live resolved
  let outerPayloads :
      SourceControlResourcePayloadContextAgrees [] [] resultAtom 0 [] []
        rootScope [] rootScope :=
    .nil 0 rootScope
  have outerEndpoints :
      endpointsBelow outerPayloads
        (openedFor initialSession "p" [resultTerm] []).cursor.reservationStart
        initialOpenConf.toConf.counter := by
    trivial
  have outerOrdered : ActivationOrdered outerPayloads := by
    trivial
  have sourceFresh :
      (openedFor initialSession "p" [resultTerm] []).session.resolver.nextFresh =
        (openedFor initialSession "p" [resultTerm] []).cursor.reservedUntil := by
    rfl
  have outerAlts : pPending.outer.alts = flattenOwnedAlts [] [] := by
    rfl
  obtain ⟨active, payloadContext, agreement, _outerExact⟩ :=
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
      (prog := prog) (gt := gt) (alpha := []) (support := [])
      (canonical := []) (referenceBase := []) (referenceBindings := [])
      (argsv := []) (args := []) (res := resultAtom)
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (binding := []) (qterm := resultAtom)
      (callerBarrier := 0) (callerScope := rootScope)
      (outerScope := rootScope) (resources := []) (context := [])
      frontier preHeadPayload groundPayloadSupported
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      referenceBelow executableLive activation sourceFresh outerPayloads
      outerEndpoints outerOrdered [] outerAlts
  have nextAlphaBelowFirst :
      GeneratedBelow branch.firstFresh (nextAlpha.map Prod.fst) := by
    simpa [branchExact, pPreparedBranch] using activation.selectionFresh.1
  have nextAlphaEq : nextAlpha = [] := by
    have exact :=
      activation.alphaExtension.eq_of_generatedBelow nextAlphaBelowFirst
    simpa using exact
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
          [] [] resultAtom [] [] initialOpenConf.toConf.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter =
        (pScan.1, pScan.2) := by
    change pScan = (pScan.1, pScan.2)
    exact (Prod.eta pScan).symm
  have sealedEntry :
      PLeaTTa.Step prog gt initialOpenConf.toConf pPending.pulled.toConf := by
    change
      PLeaTTa.Step prog gt initialOpenConf.toConf
        (DemandDrivenCallStep.FineConf.callPending pPending).toSealed
    simpa [pPending] using
      (DemandDrivenCallStep.callEnter_projects_to_sealed
          (prog := prog) (gt := gt) (state := initialOpenConf)
          (f := "p") (args := []) (res := resultAtom) (rest := [])
          (binding := []) (branches := pScan.1) (counter := pScan.2)
          (by rfl) dispatch.1 dispatch.2 scanned)
  have activeBelow :
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pPending copied [] resultAtom installed) :=
    activation.executableStep.preserves_belowResolutionCounter
      (sealedEntry.preserves_belowResolutionCounter initialBelow)
  have finishExact :
      finish =
        (openedFor initialSession "p" [resultTerm] []).cursor := by
    cases pulls
    rfl
  have pNotThrow : ¬ BuiltinThrowCall "p" [resultTerm] := by
    simp [BuiltinThrowCall]
  have pNotDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [resultTerm] = none := by
    rfl
  have sourceEntryRaw :
      RawStep initialSession
        (.task rootScope [.call "p" [resultTerm]] [])
        [.opened (requestFor "p" [resultTerm] [])] .none
        (openedFor initialSession "p" [resultTerm] []).session
        (.running
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [resultTerm] [])
            (openedFor initialSession "p" [resultTerm] []).cursor [])) := by
    simpa [sourceProductFrontier] using
      (RawStep.taskCall rootScope "p" [resultTerm] [] [] initialSession
        pNotThrow pNotDatabase)
  have sourceEntryTransition :
      Transition
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [resultTerm] [])
            (openedFor initialSession "p" [resultTerm] []).cursor [])) := by
    exact Transition.ordinary _ _ _ _ _ sourceEntryRaw
  have sourceEntryTransitionFinish :
      Transition
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [resultTerm] []) finish [])) := by
    simpa [finishExact] using sourceEntryTransition
  have sourceActivationRaw :
      RawStep
        (openedFor initialSession "p" [resultTerm] []).session
        (sourceProductFrontier rootScope
          (openedFor initialSession "p" [resultTerm] [])
          finish [])
        [] .none
        (openedFor initialSession "p" [resultTerm] []).session
        (.running
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [resultTerm] [])
            finish branch branchTail independentResult [])) := by
    exact activation.sourceStep
  have sourceActivationTransition :
      Transition
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (sourceProductFrontier rootScope
            (openedFor initialSession "p" [resultTerm] [])
            finish []))
        []
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [resultTerm] [])
            finish branch branchTail independentResult [])) := by
    exact Transition.ordinary _ _ _ _ _ sourceActivationRaw
  have rootSourceStepsRaw :
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        (.running
          (openedFor initialSession "p" [resultTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [resultTerm] [])
            finish branch branchTail independentResult [])) := by
    simpa using
      StepsN.succ 1 _ _ _ _ _ sourceEntryTransitionFinish
        (StepsN.succ 0 _ _ _ _ _ sourceActivationTransition
          (StepsN.zero _))
  have fineEntry :
      DemandDrivenCallStep.Step prog gt (.ready initialOpenConf)
        (.callPending pPending) := by
    simpa [pPending] using
      (DemandDrivenCallStep.Step.callEnter initialOpenConf "p" [] resultAtom
        [] [] pScan.1 pScan.2 (by rfl) dispatch.1 dispatch.2 scanned)
  have rootFineStepsRaw :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready initialOpenConf)
        (.ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pPending copied [] resultAtom installed)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 2 _ _ _ fineEntry
        (DemandDrivenCallStep.StepsN.succ 1 _ _ _ finePull
          (DemandDrivenCallStep.StepsN.succ 0 _ _ _
            activation.fineExecutableStep
            (DemandDrivenCallStep.StepsN.zero _)))
  let state := ActivePayloadState.ofAgreement agreement
  have stateSourceExact :
      state.sourceState =
        .running
          (openedFor initialSession "p" [resultTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [resultTerm] []) finish branch
            branchTail independentResult []) := by
    rfl
  have stateFineExact :
      state.fineState =
        .ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pPending copied [] resultAtom installed) := by
    rfl
  have rootSourceSteps :
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState := by
    rw [stateSourceExact]
    exact rootSourceStepsRaw
  have rootFineSteps :
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) state.fineState := by
    rw [stateFineExact]
    exact rootFineStepsRaw
  refine
    ⟨state, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rootSourceSteps,
      rootFineSteps⟩
  · change branch.body = [.call "q" [resultTerm]]
    simp [branchExact, pPreparedBranch]
  · change copied.body = [.call "q" [] resultAtom]
    simp [copiedExact, pCopied, pExecutableClause, resultAtom,
      PLeaTTa.freshenResolutionClause, PLeaTTa.renameGoalSuffix,
      PLeaTTa.renameAtomSuffix_gnd]
  · change nextAlpha = []
    exact nextAlphaEq
  · rfl
  · rfl
  · change independentResult = []
    exact independentResultEq
  · rfl
  · rfl
  · rfl
  · change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pPending copied [] resultAtom installed).world =
        executableWorld
    simpa [pPending, initialOpenConf] using activation.worldPreserved
  · change
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          pPending copied [] resultAtom installed).toConf
    simpa using activeBelow

/-! ## State-indexed nested `q/1` readiness -/

/-- The literal successor of the ground `p/1` activation is ready to enter
and select the unique ground `q/1` occurrence.  No payload, session, frontier,
or endpoint is supplied independently of that successor. -/
private theorem qReadyAfterP
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : ActivePayloadState, ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
      head.predicate = "q" ∧
      head.referencePayload = [resultTerm] ∧
      head.referenceRest = [] ∧
      head.arguments = [] ∧
      head.result = resultAtom ∧
      head.executableRest = [] ∧
      state.index.alpha = [] ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.session.resolver.database = referenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = executableWorld ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) state.fineState := by
  obtain
    ⟨state, referenceHead, executableHead, alphaNil, freshExact, supportNil,
      currentNil, qtermExact, databaseExact, nextFreshZero, worldExact,
      below, rootSourceSteps, rootFineSteps⟩ :=
    pActive (prog := prog) (gt := gt)
  let head : NestedCallHead state :=
    { predicate := "q"
      referencePayload := [resultTerm]
      referenceRest := []
      arguments := []
      result := resultAtom
      executableRest := []
      referenceHead := referenceHead
      executableHead := executableHead }
  have openedSingleton :
      (openedFor state.index.session "q" [resultTerm]
        state.index.current).cursor.remaining = [qPreparedBranch] := by
    rw [currentNil]
    change
      (prepareCall state.index.session.resolver
        (requestFor "q" [resultTerm] [])).1.remaining = [qPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [databaseExact, nextFreshZero]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).1 = [qPreparedBranch]
    rw [qVisibleClauses]
    rfl
  refine
    ⟨state, head, ?_, rfl, rfl, rfl, rfl, rfl, rfl, alphaNil, supportNil,
      currentNil, qtermExact, databaseExact, nextFreshZero, worldExact,
      rootSourceSteps, rootFineSteps⟩
  refine
    { exactFresh := freshExact
      indexReady := ?_
      below := below
      payloadSupported := ?_
      candidateSupported := ?_
      sourceNonempty := ?_
      scanNonempty := ?_
      queryExecutableLive := ?_
      selected := ?_
      notThrow := ?_
      notDatabase := ?_ }
  · rw [worldExact]
    rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported
  · change
      SupportedCandidateBank "q"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "q" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
    simpa [databaseExact, worldExact] using qCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "q" 1 ≠ []
    rw [databaseExact, qVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, qResolutionCandidates]
    have argumentsMatch : PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, qExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · intro name member
    rw [alphaNil] at member
    simp at member
  · intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    have finishNonempty : finish.remaining ≠ [] := by
      rw [frontier.finishRemaining]
      simp
    have pathExact :=
      _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
        openedSingleton pulls finishNonempty
    have branchExact : branch = qPreparedBranch := by
      have remaining := frontier.finishRemaining
      rw [pathExact.2, openedSingleton] at remaining
      exact (List.cons.inj remaining).1.symm
    refine ⟨[], ?_, ?_⟩
    · simpa [branchExact] using qPreparedBranch_resolves_empty
    · rw [supportNil]
      intro identity name member
      simp at member
  · simp [head, BuiltinThrowCall]
  · rfl

/-- Any literal active carrier with the preserved ground substrate and an
`r(7)` body head is ready for the unique local `r/1` occurrence. -/
private theorem rReadyFromGroundState
    (state : ActivePayloadState)
    (referenceHead :
      state.index.bodyReferences = [.call "r" [resultTerm]])
    (executableHead :
      state.index.bodyExecutables = [.call "r" [] resultAtom])
    (alphaNil : state.index.alpha = [])
    (freshExact :
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha)
    (supportNil : state.index.support = [])
    (currentNil : state.index.current = [])
    (databaseExact :
      state.index.session.resolver.database = referenceDatabase)
    (nextFreshZero : state.index.session.resolver.nextFresh = 0)
    (worldExact :
      state.index.openConf.persistent.world = executableWorld)
    (below : ConfBelowResolutionCounter state.index.openConf.toConf) :
    ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
        head.predicate = "r" ∧
        head.referencePayload = [resultTerm] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = resultAtom ∧
        head.executableRest = [] := by
  let head : NestedCallHead state :=
    { predicate := "r"
      referencePayload := [resultTerm]
      referenceRest := []
      arguments := []
      result := resultAtom
      executableRest := []
      referenceHead := referenceHead
      executableHead := executableHead }
  have openedSingleton :
      (openedFor state.index.session "r" [resultTerm]
        state.index.current).cursor.remaining = [rPreparedBranch] := by
    rw [currentNil]
    change
      (prepareCall state.index.session.resolver
        (requestFor "r" [resultTerm] [])).1.remaining = [rPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [databaseExact, nextFreshZero]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "r" 1)).1 = [rPreparedBranch]
    rw [rVisibleClauses]
    rfl
  refine ⟨head, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine
    { exactFresh := freshExact
      indexReady := ?_
      below := below
      payloadSupported := ?_
      candidateSupported := ?_
      sourceNonempty := ?_
      scanNonempty := ?_
      queryExecutableLive := ?_
      selected := ?_
      notThrow := ?_
      notDatabase := ?_ }
  · rw [worldExact]
    rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported
  · change
      SupportedCandidateBank "r"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "r" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
    simpa [databaseExact, worldExact] using rCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "r" 1 ≠ []
    rw [databaseExact, rVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, rResolutionCandidates]
    have argumentsMatch : PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, rExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · intro name member
    rw [alphaNil] at member
    simp at member
  · intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    have finishNonempty : finish.remaining ≠ [] := by
      rw [frontier.finishRemaining]
      simp
    have pathExact :=
      _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
        openedSingleton pulls finishNonempty
    have branchExact : branch = rPreparedBranch := by
      have remaining := frontier.finishRemaining
      rw [pathExact.2, openedSingleton] at remaining
      exact (List.cons.inj remaining).1.symm
    refine ⟨[], ?_, ?_⟩
    · simpa [branchExact] using rPreparedBranch_resolves_empty
    · rw [supportNil]
      intro identity name member
      simp at member
  · simp [head, BuiltinThrowCall]
  · rfl

/-! ## Literal depth-two successor -/

/-- The actual ground `q/1` push selected from the `p/1` successor produces
the literal carrier on which the unique ground `r/1` call is ready.  The
source pull path and executable candidate bank force the selected occurrences;
the successor facts then force its substitution, bodies, alpha graph,
persistent state, and sealed counter invariant. -/
theorem ground_p_q_r_two_nested_pushes
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : ActivePayloadState, ∃ qHead : NestedCallHead before,
      ∃ middle : ActivePayloadState,
        NestedCallReady before qHead ∧
          qHead.predicate = "q" ∧
          qHead.referencePayload = [resultTerm] ∧
          before.index.bodyReferences = [.call "q" [resultTerm]] ∧
          before.index.bodyExecutables = [.call "q" [] resultAtom] ∧
          StepsN 2
            (.running initialSession
              (.task rootScope [.call "p" [resultTerm]] []))
            [.opened (requestFor "p" [resultTerm] [])]
            before.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 3
            (.ready initialOpenConf) before.fineState ∧
          NestedCallPushCertificate prog gt 0
            (requestFor "q" [resultTerm] []) before middle ∧
          ∃ rHead : NestedCallHead middle, ∃ after : ActivePayloadState,
            NestedCallReady middle rHead ∧
              rHead.predicate = "r" ∧
              rHead.referencePayload = [resultTerm] ∧
              NestedCallPushCertificate prog gt 0
                (requestFor "r" [resultTerm] []) middle after := by
  obtain
    ⟨before, qHead, qReady, qPredicate, qPayload, qReferenceRest,
      qArguments, qResult, qExecutableRest, beforeAlphaNil,
      beforeSupportNil, beforeCurrentNil, beforeQterm, beforeDatabase,
      beforeNextFresh, beforeWorld, rootSourceSteps, rootFineSteps⟩ :=
    qReadyAfterP (prog := prog) (gt := gt)
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, qInstalled, middle, facts⟩ :=
    qReady.pushDetailed (prog := prog) (gt := gt)
  have openedSingleton :
      (openedFor before.index.session "q" [resultTerm]
        before.index.current).cursor.remaining = [qPreparedBranch] := by
    rw [beforeCurrentNil]
    change
      (prepareCall before.index.session.resolver
        (requestFor "q" [resultTerm] [])).1.remaining = [qPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).1 = [qPreparedBranch]
    rw [qVisibleClauses]
    rfl
  have finishNonempty : finish.remaining ≠ [] := by
    rw [facts.frontier.finishRemaining]
    simp
  have pullsConcrete :
      RejectedPullsN count
        (openedFor before.index.session "q" [resultTerm]
          before.index.current).cursor
        finish := by
    simpa [qPredicate, qPayload] using facts.pulls
  have pathExact :=
    _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton pullsConcrete finishNonempty
  have countZero : count = 0 := pathExact.1
  have branchExact : branch = qPreparedBranch := by
    have remaining := facts.frontier.finishRemaining
    rw [pathExact.2, openedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.executableSkipCount, countZero]
  have executableShape := facts.executableBank
  rw [qPredicate, qArguments, beforeWorld, skippedClausesNil] at executableShape
  simp only [List.length_nil] at executableShape
  rw [qResolutionCandidates] at executableShape
  have clauseExact : clause = qExecutableClause :=
    (List.cons.inj executableShape).1.symm
  have copiedBody : copied.body = [.call "r" [] resultAtom] := by
    rw [facts.frontier.copiedExact, clauseExact]
    simp [PLeaTTa.freshenResolutionClause, qExecutableClause, resultAtom,
      PLeaTTa.renameGoalSuffix, PLeaTTa.renameAtomSuffix_gnd]
  have middleReferences :
      middle.index.bodyReferences = [.call "r" [resultTerm]] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have middleExecutables :
      middle.index.bodyExecutables = [.call "r" [] resultAtom] := by
    rw [facts.bodyExecutables, copiedBody]
  have middleGeneratedBelow :
      GeneratedBelow branch.firstFresh (middle.index.alpha.map Prod.fst) := by
    simpa [branchExact, qPreparedBranch] using facts.selectionFresh.1
  have middleAlphaBefore : middle.index.alpha = before.index.alpha :=
    facts.alphaExtension.eq_of_generatedBelow middleGeneratedBelow
  have middleAlphaNil : middle.index.alpha = [] :=
    middleAlphaBefore.trans beforeAlphaNil
  have branchResolvesEmpty : HeadResolution branch [] := by
    simpa [branchExact] using qPreparedBranch_resolves_empty
  have middleCurrentNil : middle.index.current = [] :=
    HeadResolution.deterministic facts.resolution branchResolvesEmpty
  have middleSupportNil : middle.index.support = [] :=
    facts.supportPreserved.trans beforeSupportNil
  have middleDatabase :
      middle.index.session.resolver.database = referenceDatabase := by
    rw [facts.sessionExact]
    simpa [qPredicate, qPayload, beforeCurrentNil, openedFor, openLocalCall]
      using beforeDatabase
  have middleNextFresh : middle.index.session.resolver.nextFresh = 0 := by
    rw [facts.sessionExact]
    change
      (prepareCall before.index.session.resolver
        (requestFor qHead.predicate qHead.referencePayload
          before.index.current)).2.nextFresh = 0
    rw [qPredicate, qPayload, beforeCurrentNil]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).2 = 0
    rw [qVisibleClauses]
    rfl
  have middleWorld :
      middle.index.openConf.persistent.world = executableWorld :=
    facts.worldPreserved.trans beforeWorld
  obtain
    ⟨rHead, rReady, rPredicate, rPayload, rReferenceRest, rArguments,
      rResult, rExecutableRest⟩ :=
    rReadyFromGroundState middle middleReferences middleExecutables
      middleAlphaNil facts.freshFrontierExact middleSupportNil
      middleCurrentNil middleDatabase middleNextFresh middleWorld facts.below
  have qCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "q" [resultTerm] []) before middle := by
    simpa [countZero, qPredicate, qPayload, beforeCurrentNil] using
      facts.certificate
  have beforeReferences :
      before.index.bodyReferences = [.call "q" [resultTerm]] := by
    simpa [qPredicate, qPayload, qReferenceRest] using qHead.referenceHead
  have beforeExecutables :
      before.index.bodyExecutables = [.call "q" [] resultAtom] := by
    simpa [qPredicate, qArguments, qResult, qExecutableRest] using
      qHead.executableHead
  obtain
    ⟨rCount, rSkippedBranches, rSkippedClauses, rFinish, rBranch, rClause,
      rBranchTail, rClauseTail, rAltTail, rCopied, rInstalled, after,
      rFacts⟩ :=
    rReady.pushDetailed (prog := prog) (gt := gt)
  have rOpenedSingleton :
      (openedFor middle.index.session "r" [resultTerm]
        middle.index.current).cursor.remaining = [rPreparedBranch] := by
    rw [middleCurrentNil]
    change
      (prepareCall middle.index.session.resolver
        (requestFor "r" [resultTerm] [])).1.remaining = [rPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [middleDatabase, middleNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "r" 1)).1 = [rPreparedBranch]
    rw [rVisibleClauses]
    rfl
  have rFinishNonempty : rFinish.remaining ≠ [] := by
    rw [rFacts.frontier.finishRemaining]
    simp
  have rPullsConcrete :
      RejectedPullsN rCount
        (openedFor middle.index.session "r" [resultTerm]
          middle.index.current).cursor
        rFinish := by
    simpa [rPredicate, rPayload] using rFacts.pulls
  have rPathExact :=
    _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      rOpenedSingleton rPullsConcrete rFinishNonempty
  have rCountZero : rCount = 0 := rPathExact.1
  have rCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "r" [resultTerm] []) middle after := by
    simpa [rCountZero, rPredicate, rPayload, middleCurrentNil] using
      rFacts.certificate
  exact
    ⟨before, qHead, middle, qReady, qPredicate, qPayload,
      beforeReferences, beforeExecutables, rootSourceSteps, rootFineSteps,
      qCertificate, rHead, after, rReady, rPredicate, rPayload, rCertificate⟩

/-- The root activation and both dependent push certificates compose to one
exact finite prefix.  Source observations retain call order; the fine lane
retains all three install/pull/head-equality microsteps per call. -/
theorem ground_p_q_r_exact_prefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ after : ActivePayloadState,
      StepsN 6
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] []),
          .opened (requestFor "q" [resultTerm] []),
          .opened (requestFor "r" [resultTerm] [])]
        after.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 9
        (.ready initialOpenConf) after.fineState := by
  obtain
    ⟨before, qHead, middle, _qReady, _qPredicate, _qPayload,
      _beforeReferences, _beforeExecutables, rootSourceSteps, rootFineSteps,
      qCertificate, rHead, after, _rReady, _rPredicate, _rPayload,
      rCertificate⟩ :=
    ground_p_q_r_two_nested_pushes (prog := prog) (gt := gt)
  have sourceSteps :=
    StepsN.trans rootSourceSteps
      (StepsN.trans qCertificate.sourceSteps rCertificate.sourceSteps)
  have fineSteps :=
    DemandDrivenCallStep.StepsN.trans rootFineSteps
      (DemandDrivenCallStep.StepsN.trans qCertificate.fineSteps
        rCertificate.fineSteps)
  refine ⟨after, ?_, ?_⟩
  · simpa using sourceSteps
  · simpa using fineSteps

end PLeaTTa.PrologNestedCallReadyRegression
