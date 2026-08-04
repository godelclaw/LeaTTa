-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCommittedScheduledFirstLiveRegression
Purpose: Force the first-live committed-answer classifier arm on one
  source/fine-reachable nested cut execution.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologCommittedScheduledOuterCatchupBridge
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologPersistentFreeCommittedPayloadBridge
import PLeaTTa.Proofs.PrologRootCallReadyBridge

namespace PLeaTTa.PrologCommittedScheduledFirstLiveRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open OpenBindingAgreement
open PrologActivationMacro
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologCommittedScheduledOuterCatchupBridge
open PrologCommittedScheduledOuterCatchupBridge.RootClosedCommittedAnswerReady
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguTopology
open PrologMguVariant
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologPersistentFreeCommittedScheduledPayloadBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRootCallReadyBridge
open PrologStateBridge

/-! ## A two-level ground program with independent inner and outer siblings -/

def resultTerm : Term := .integer 7

def resultAtom : Atom := .gnd (.int 7)

def wrapperReference : LocalClause :=
  { predicate := "wrapcut"
    arguments := [resultTerm]
    body := [.call "cutg" [resultTerm]] }

def selectedCutReference : LocalClause :=
  { predicate := "cutg"
    arguments := [resultTerm]
    body := [.cut] }

def retainedCutReference : LocalClause :=
  { predicate := "cutg"
    arguments := [resultTerm]
    body := [] }

def wrapperExecutable : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.call "cutg" [] resultAtom] }

def selectedCutExecutable : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.cut] }

def retainedCutExecutable : PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [] }

def referenceDatabase : Database :=
  ((((Database.empty.assertz wrapperReference).assertz wrapperReference).assertz
      selectedCutReference).assertz retainedCutReference)

def executableWorld : PWorld :=
  (((((default : PWorld).reindexClauses.appendProgClause
      ("wrapcut", wrapperExecutable)).appendProgClause
      ("wrapcut", wrapperExecutable)).appendProgClause
      ("cutg", selectedCutExecutable)).appendProgClause
      ("cutg", retainedCutExecutable))

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

private theorem wrapperClauseAgrees :
    LocalClauseAgrees wrapperReference ("wrapcut", wrapperExecutable) := by
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
    simp [wrapperReference, wrapperExecutable, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem selectedCutClauseAgrees :
    LocalClauseAgrees selectedCutReference
      ("cutg", selectedCutExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .cons .cut .nil
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · intro name
    simp [selectedCutReference, selectedCutExecutable, resultTerm,
      resultAtom, LocalClause.variables, resolutionClauseVars,
      Metta.Atom.vars, specializationGoalsVars, specializationGoalVars,
      termsVariables, termVariables, goalsVariables, goalVariables]

private theorem retainedCutClauseAgrees :
    LocalClauseAgrees retainedCutReference
      ("cutg", retainedCutExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · intro name
    simp [retainedCutReference, retainedCutExecutable, resultTerm,
      resultAtom, LocalClause.variables, resolutionClauseVars,
      Metta.Atom.vars, specializationGoalsVars, termsVariables,
      termVariables, goalsVariables]

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
  have first := emptyDatabaseRelatesIndexedWorld.assertz wrapperClauseAgrees
  have second := first.assertz wrapperClauseAgrees
  have selected := second.assertz selectedCutClauseAgrees
  have retained := selected.assertz retainedCutClauseAgrees
  simpa [referenceDatabase, executableWorld] using retained

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have first :=
    PWorld.appendProgClause_coherent _ ("wrapcut", wrapperExecutable) root
  have second :=
    PWorld.appendProgClause_coherent _ ("wrapcut", wrapperExecutable) first
  have selected :=
    PWorld.appendProgClause_coherent _ ("cutg", selectedCutExecutable) second
  have retained :=
    PWorld.appendProgClause_coherent _ ("cutg", retainedCutExecutable) selected
  simpa [executableWorld] using retained

private theorem wrapperResolutionCandidates :
    executableWorld.resolutionCandidates "wrapcut" 0 =
      [wrapperExecutable, wrapperExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, wrapperExecutable, emptyClauses]

private theorem cutResolutionCandidates :
    executableWorld.resolutionCandidates "cutg" 0 =
      [selectedCutExecutable, retainedCutExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, selectedCutExecutable, retainedCutExecutable,
    emptyClauses]

private theorem wrapperVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation
        "wrapcut" 1 =
      [Database.empty.allocate wrapperReference,
        (Database.empty.assertz wrapperReference).allocate wrapperReference] := by
  rfl

private theorem cutVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation
        "cutg" 1 =
      [((Database.empty.assertz wrapperReference).assertz
          wrapperReference).allocate selectedCutReference,
        (((Database.empty.assertz wrapperReference).assertz
          wrapperReference).assertz selectedCutReference).allocate
            retainedCutReference] := by
  rfl

private theorem groundEncoding (clause : LocalClause)
    (vars : clause.variables = []) :
    EncodingInjectiveOn clause.variables := by
  rw [vars]
  simp [EncodingInjectiveOn]

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

private theorem wrapperCandidateBank :
    SupportedCandidateBank "wrapcut"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation
        "wrapcut" 1)
      (executableWorld.resolutionCandidates "wrapcut" 0) := by
  rw [wrapperVisibleClauses, wrapperResolutionCandidates]
  let first : CandidateClauseAgrees "wrapcut"
      (Database.empty.allocate wrapperReference) wrapperExecutable := by
    change LocalClauseAgrees wrapperReference ("wrapcut", wrapperExecutable)
    exact wrapperClauseAgrees
  let second : CandidateClauseAgrees "wrapcut"
      ((Database.empty.assertz wrapperReference).allocate wrapperReference)
      wrapperExecutable := by
    change LocalClauseAgrees wrapperReference ("wrapcut", wrapperExecutable)
    exact wrapperClauseAgrees
  have firstEncoding :
      EncodingInjectiveOn
        (Database.empty.allocate wrapperReference).clause.variables := by
    apply groundEncoding
    simp [Database.allocate, wrapperReference, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables,
      resultTerm]
  have secondEncoding :
      EncodingInjectiveOn
        ((Database.empty.assertz wrapperReference).allocate
          wrapperReference).clause.variables := by
    apply groundEncoding
    simp [Database.allocate, wrapperReference, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables,
      resultTerm]
  have firstBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate wrapperReference).clause.variables
        (Database.empty.allocate wrapperReference).clause.variables
        first.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      first.body
    have bodyEq : first.body = groundDefinedCallGoalsAgrees "cutg" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "cutg"
  have secondBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        ((Database.empty.assertz wrapperReference).allocate
          wrapperReference).clause.variables
        ((Database.empty.assertz wrapperReference).allocate
          wrapperReference).clause.variables second.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      second.body
    have bodyEq : second.body = first.body := Subsingleton.elim _ _
    rw [bodyEq]
    exact firstBody
  refine
    ⟨List.Forall₂.cons first (List.Forall₂.cons second .nil), ?_⟩
  exact
    .cons (head := first) firstEncoding firstBody
      (.cons (head := second) secondEncoding secondBody .nil)

private theorem cutCandidateBank :
    SupportedCandidateBank "cutg"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation
        "cutg" 1)
      (executableWorld.resolutionCandidates "cutg" 0) := by
  rw [cutVisibleClauses, cutResolutionCandidates]
  let selected : CandidateClauseAgrees "cutg"
      (((Database.empty.assertz wrapperReference).assertz
        wrapperReference).allocate selectedCutReference)
      selectedCutExecutable := by
    change LocalClauseAgrees selectedCutReference
      ("cutg", selectedCutExecutable)
    exact selectedCutClauseAgrees
  let retained : CandidateClauseAgrees "cutg"
      ((((Database.empty.assertz wrapperReference).assertz
        wrapperReference).assertz selectedCutReference).allocate
          retainedCutReference)
      retainedCutExecutable := by
    change LocalClauseAgrees retainedCutReference
      ("cutg", retainedCutExecutable)
    exact retainedCutClauseAgrees
  have selectedEncoding :
      EncodingInjectiveOn
        (((Database.empty.assertz wrapperReference).assertz
          wrapperReference).allocate selectedCutReference).clause.variables := by
    apply groundEncoding
    simp [Database.allocate, selectedCutReference, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables,
      resultTerm]
  have retainedEncoding :
      EncodingInjectiveOn
        ((((Database.empty.assertz wrapperReference).assertz
          wrapperReference).assertz selectedCutReference).allocate
            retainedCutReference).clause.variables := by
    apply groundEncoding
    simp [Database.allocate, retainedCutReference, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, resultTerm]
  have selectedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (((Database.empty.assertz wrapperReference).assertz
          wrapperReference).allocate selectedCutReference).clause.variables
        (((Database.empty.assertz wrapperReference).assertz
          wrapperReference).allocate selectedCutReference).clause.variables
        selected.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      selected.body
    have bodyEq : selected.body =
        (CompilerAdequacy.GoalsAgree.cons .cut .nil) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .cons .cut .nil
  have retainedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        ((((Database.empty.assertz wrapperReference).assertz
          wrapperReference).assertz selectedCutReference).allocate
            retainedCutReference).clause.variables
        ((((Database.empty.assertz wrapperReference).assertz
          wrapperReference).assertz selectedCutReference).allocate
            retainedCutReference).clause.variables retained.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      retained.body
    have bodyEq : retained.body =
        (CompilerAdequacy.GoalsAgree.nil : CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  refine
    ⟨List.Forall₂.cons selected (List.Forall₂.cons retained .nil), ?_⟩
  exact
    .cons (head := selected) selectedEncoding selectedBody
      (.cons (head := retained) retainedEncoding retainedBody .nil)

/-! ## Exact root wrapper activation -/

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "wrapcut" [] resultAtom], [])
        alts := []
        qterm := resultAtom } }

private def wrapperScan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "wrapcut" 0)
    [] [] resultAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def wrapperPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf wrapperScan.1
    wrapperScan.2

private theorem wrapperEntry :
    RepresentativeSupportedCallEntryRelates []
      (openedFor initialSession "wrapcut" [resultTerm] []) initialOpenConf
      wrapperPending [] [] resultAtom [] [] resultAtom
      (barrierDepth initialOpenConf.toConf + 1)
      initialOpenConf.toConf.counter := by
  have database :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using
      referenceDatabase_relates_executableWorld
  have ready : initialOpenConf.persistent.world.clauseIndexReady = true := rfl
  have scanned :
      resolveAlts
          (initialOpenConf.persistent.world.resolutionCandidates "wrapcut" 0)
          [] [] resultAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = wrapperScan := rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (groundCallPayload
        (barrierDepth initialOpenConf.toConf + 1) "wrapcut")
      groundPayloadSupported
      (openedFor initialSession "wrapcut" [resultTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "wrapcut" [resultTerm] [] [] [] resultAtom [] []
      wrapperScan.1 wrapperScan.2 (by rfl) (by rfl)
      (by
        calc
          _ = wrapperScan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (wrapperScan.1, wrapperScan.2) :=
            (Prod.eta wrapperScan).symm)
      query wrapperCandidateBank
  simpa [wrapperPending, initialOpenConf] using constructed

private theorem initialBelow :
    ConfBelowResolutionCounter initialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, initialOpenConf, OpenConf.toConf, Control.toConf,
    specializationGoalsVars, specializationGoalVars, resolutionSubstVars,
    resultAtom, Metta.Atom.vars] at member

private def wrapperCopiedAt (counter : Nat) : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] resultAtom [] []
    initialOpenConf.control.qterm counter
    (barrierDepth initialOpenConf.toConf + 1) wrapperExecutable

private def wrapperAltAt (counter : Nat) : PLeaTTa.Alt :=
  .br
    (.eq (.expr [resultAtom])
        (.expr
          ((wrapperCopiedAt counter).params ++
            [(wrapperCopiedAt counter).result])) ::
      (wrapperCopiedAt counter).body)
    []

private theorem wrapperScanExact :
    wrapperScan = ([wrapperAltAt 0, wrapperAltAt 1], 2) := by
  unfold wrapperScan
  change
    resolveAlts
        (executableWorld.resolutionCandidates "wrapcut" 0) [] [] resultAtom
        [] [] resultAtom 1 0 =
      ([wrapperAltAt 0, wrapperAltAt 1], 2)
  rw [wrapperResolutionCandidates]
  have argumentsMatch : PLeaTTa.prologMatchCompatList [] [] = true := rfl
  have resultMatch :
      PLeaTTa.prologMatchCompat
        (.gnd (.int 7)) (.gnd (.int 7)) = true := by
    rfl
  simp [resolveAlts, wrapperExecutable, resultAtom, wrapperAltAt,
    wrapperCopiedAt, initialOpenConf, OpenConf.toConf, Control.toConf,
    barrierDepth, argumentsMatch, resultMatch]

private theorem wrapperPendingPulledCur :
    wrapperPending.pulled.toConf.cur =
      some
        (.eq (.expr [resultAtom])
            (.expr
              ((wrapperCopiedAt 0).params ++
                [(wrapperCopiedAt 0).result])) ::
          (wrapperCopiedAt 0).body,
          []) := by
  rw [wrapperPending, wrapperScanExact]
  rfl

private theorem wrapperScanNonempty : wrapperPending.branches ≠ [] := by
  rw [wrapperPending, wrapperScanExact]
  exact List.cons_ne_nil _ _

private def wrapperFirstBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate wrapperReference).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "cutg" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def wrapperSecondBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz wrapperReference).allocate wrapperReference).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "cutg" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem wrapperOpenedRemaining :
    (openedFor initialSession "wrapcut" [resultTerm] []).cursor.remaining =
      [wrapperFirstBranch, wrapperSecondBranch] := by
  rfl

private theorem groundBranchResolves
    (branch : ClauseBranch)
    (normalized :
      branch.normalizedHeadEquations = [(resultTerm, resultTerm)])
    (bindings : branch.bindings = []) :
    HeadResolution branch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [normalized]
    simpa [denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [bindings]

private theorem wrapperFirstBranch_resolves_empty :
    HeadResolution wrapperFirstBranch [] := by
  apply groundBranchResolves wrapperFirstBranch
  · rfl
  · rfl

private theorem wrapperSecondBranch_resolves_empty :
    HeadResolution wrapperSecondBranch [] := by
  apply groundBranchResolves wrapperSecondBranch
  · rfl
  · rfl

private def selectedCutBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz wrapperReference).assertz
        wrapperReference).allocate selectedCutReference |>.id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.cut]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def retainedCutBranch : ClauseBranch :=
  { sourceId :=
      (((Database.empty.assertz wrapperReference).assertz
        wrapperReference).assertz selectedCutReference).allocate
          retainedCutReference |>.id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem selectedCutBranch_resolves_empty :
    HeadResolution selectedCutBranch [] := by
  apply groundBranchResolves selectedCutBranch
  · rfl
  · rfl

private theorem retainedCutBranch_resolves_empty :
    HeadResolution retainedCutBranch [] := by
  apply groundBranchResolves retainedCutBranch
  · rfl
  · rfl

/-- The first wrapper occurrence is selected by the real root resolver while
the duplicate remains as the exact live local resource. -/
private theorem wrapper_selected_reachable
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (finish : PreparedCursor)
        (representative sourceCanonical flattened : TreeSubstitution)
        (nextAlpha : List (LogicVar × String))
        (installed : Subst)
        (after : RepresentativeActivePayloadState),
      RepresentativeRootCallSuccessorFacts prog gt [] [] [] []
        initialSession initialOpenConf 0 "wrapcut" [resultTerm] [] []
        resultAtom [] wrapperScan.1 wrapperScan.2 0 0 [] [] finish
        wrapperFirstBranch wrapperExecutable [wrapperSecondBranch]
        [wrapperExecutable] [wrapperAltAt 1] (wrapperCopiedAt 0) []
        representative nextAlpha sourceCanonical flattened installed after ∧
      after.carrier.index.bodyReferences = [.call "cutg" [resultTerm]] ∧
      after.carrier.index.bodyExecutables = [.call "cutg" [] resultAtom] ∧
      after.carrier.index.alpha = [] ∧
      after.carrier.index.support = [] ∧
      after.carrier.index.current = [] ∧
      after.carrier.index.runtime = [] ∧
      after.carrier.index.active.alts = [wrapperAltAt 1] ∧
      after.carrier.index.resources = [] ∧
      after.carrier.index.baseAlts = [] ∧
      after.carrier.index.openConf.frames = [] := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier []) ExactControlFrontiers
        initialSession initialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [initialSession, initialOpenConf] using
        referenceDatabase_relates_executableWorld
    · simpa [initialSession, initialOpenConf] using
        (AlphaFreshFrontier.empty 0 0)
  have preHeadPayload :
      TaskSpinePayloadAgrees [] [] [] [] [] []
        [{ barrier := 0
           references := [.call "wrapcut" [resultTerm]]
           executables := [.call "wrapcut" [] resultAtom] }] :=
    TaskSpinePayloadAgrees.singleton (groundCallPayload 0 "wrapcut")
  have selected :
      ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
        {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
        {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
        {copied : PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor initialSession "wrapcut" [resultTerm] []).cursor
            finish →
          RepresentativeRetainedCallFrontier []
            (openedFor initialSession "wrapcut" [resultTerm] [])
            initialOpenConf wrapperPending finish branch clause branchTail
            clauseTail altTail copied [] [] resultAtom [] [] resultAtom
            (barrierDepth initialOpenConf.toConf + 1)
            initialOpenConf.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive [] copied.body resultAtom := by
    intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    cases pulls with
    | zero cursor =>
        have branchExact : branch = wrapperFirstBranch := by
          have exact :
              [wrapperFirstBranch, wrapperSecondBranch] =
                branch :: branchTail :=
            wrapperOpenedRemaining.symm.trans frontier.finishRemaining
          exact (List.cons.inj exact).1.symm
        refine ⟨[], ?_, ?_⟩
        · simpa [branchExact] using wrapperFirstBranch_resolves_empty
        · intro identity name member
          simp at member
    | succ count cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = wrapperFirstBranch := by
          have exact :
              [wrapperFirstBranch, wrapperSecondBranch] = first :: branches :=
            wrapperOpenedRemaining.symm.trans remaining
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            wrapperFirstBranch_resolves_empty⟩)
  have notThrow : ¬ BuiltinThrowCall "wrapcut" [resultTerm] := by
    simp [BuiltinThrowCall]
  have notDatabase :
      DatabaseActions.recognizeDatabaseAction "wrapcut" [resultTerm] = none :=
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, independentResult,
        representative, nextAlpha, sourceCanonical, flattened, installed,
        after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := 0) (callerBarrier := 0)
      wrapperEntry preHeadPayload groundPayloadSupported beforeSession
      (by rfl) (by rfl) initialBelow wrapperScanNonempty selected notThrow
      notDatabase
  have rejectsZero : rejects = 0 := by
    cases facts.pulls with
    | zero cursor => rfl
    | succ count cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = wrapperFirstBranch := by
          have exact :
              [wrapperFirstBranch, wrapperSecondBranch] = first :: branches :=
            wrapperOpenedRemaining.symm.trans remaining
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            wrapperFirstBranch_resolves_empty⟩)
  have skippedBranchesNil : skippedBranches = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.sourceSkipCount, rejectsZero]
  have sourceShape := facts.sourceBank
  rw [wrapperOpenedRemaining, skippedBranchesNil] at sourceShape
  have branchExact : branch = wrapperFirstBranch :=
    (List.cons.inj sourceShape).1.symm
  have branchTailExact : branchTail = [wrapperSecondBranch] :=
    (List.cons.inj sourceShape).2.symm
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.executableSkipCount, rejectsZero]
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "wrapcut" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [wrapperResolutionCandidates, skippedClausesNil] at executableShape
  have clauseExact : clause = wrapperExecutable :=
    (List.cons.inj executableShape).1.symm
  have clauseTailExact : clauseTail = [wrapperExecutable] :=
    (List.cons.inj executableShape).2.symm
  have copiedExact : copied = wrapperCopiedAt 0 := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have tailScan :
      ResolutionScan [] [] resultAtom [] [] resultAtom 1
        [wrapperExecutable] 1 altTail 2 := by
    simpa [wrapperPending, wrapperScanExact, initialOpenConf, OpenConf.toConf,
      Control.toConf, barrierDepth, clauseTailExact] using
      facts.frontier.tailScan
  have expectedTailScan :
      ResolutionScan [] [] resultAtom [] [] resultAtom 1
        [wrapperExecutable] 1 [wrapperAltAt 1] 2 :=
    .retained wrapperExecutable [] 1 2 []
      (by
        simp [resolutionClauseRetained, resultAtom, wrapperExecutable,
          PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
          PLeaTTa.prologMatchCompatList])
      (.nil 2)
  have altTailExact : altTail = [wrapperAltAt 1] :=
    (tailScan.deterministic expectedTailScan).1
  have exactResolution : HeadResolution branch [] := by
    simpa [branchExact] using wrapperFirstBranch_resolves_empty
  have currentExact : after.carrier.index.current = [] :=
    HeadResolution.deterministic facts.resolution exactResolution
  have alphaExact : after.carrier.index.alpha = [] := by
    have generatedBelow :
        GeneratedBelow branch.firstFresh
          (after.carrier.index.alpha.map Prod.fst) := by
      simpa [branchExact, wrapperFirstBranch] using facts.selectionFresh.1
    have exact := facts.alphaExtension.eq_of_generatedBelow generatedBelow
    simpa using exact
  have runtimeExact : after.carrier.index.runtime = [] := by
    obtain
      ⟨base, args, headResult, pulledExact, generated, generatedExact,
        generatedAgrees⟩ := facts.activation.headMgu
    change wrapperPending.pulled.toConf.cur = _ at pulledExact
    have pairExact :=
      Option.some.inj (wrapperPendingPulledCur.symm.trans pulledExact)
    have baseNil : base = [] := (congrArg Prod.snd pairExact).symm
    have goalsExact := congrArg Prod.fst pairExact
    rw [copiedExact] at goalsExact
    simp only [List.nil_append] at goalsExact
    have firstGoalExact := (List.cons.inj goalsExact).1
    have expressionExact :
        (.expr [resultAtom] : Atom) = .expr (args ++ [headResult]) := by
      injection firstGoalExact
    subst base
    have generatedNil : generated = [] := by
      have exact := generatedExact
      have mapSubstNil (atoms : List Atom) :
          atoms.map (PLeaTTa.subst []) = atoms := by
        induction atoms with
        | nil => rfl
        | cons atom atoms ih => simp [PLeaTTa.subst_nil, ih]
      rw [mapSubstNil, mapSubstNil] at exact
      rw [← expressionExact, copiedExact] at exact
      simpa [wrapperCopiedAt, wrapperExecutable, initialOpenConf, resultAtom,
        PLeaTTa.freshenResolutionClause, PLeaTTa.renameAtomSuffix_gnd,
        PLeaTTa.unifyTopExact_self] using exact
    have installedNil : installed = [] := by
      rw [generatedAgrees.installedShape, generatedNil]
      rfl
    have openConfExact :
        after.carrier.index.openConf =
          PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            wrapperPending copied [] initialOpenConf.control.qterm
              installed :=
      DemandDrivenCallStep.FineConf.ready.inj facts.fineStateExact
    have currentControl := after.carrier.agreement.core.control.ready.2.1
    rw [openConfExact] at currentControl
    have runtimeTrim :
        after.carrier.index.runtime =
          PLeaTTa.trimFor copied.body initialOpenConf.control.qterm
            installed := by
      simpa [facts.bodyExecutables, facts.callerExecutablesEmpty,
        facts.outerEmpty] using (Option.some.inj currentControl).symm
    rw [runtimeTrim, installedNil, copiedExact]
    simp [PLeaTTa.trimFor, PLeaTTa.trimSubst,
      PLeaTTa.filterLiveSubst]
  have independentResultNil : independentResult = [] :=
    facts.carrierCurrent.symm.trans currentExact
  subst rejects
  subst skippedBranches
  subst skippedClauses
  subst branch
  subst branchTail
  subst clause
  subst clauseTail
  subst copied
  subst altTail
  subst independentResult
  refine
    ⟨finish, representative, sourceCanonical, flattened, nextAlpha,
      installed, after, ?_, ?_, ?_, alphaExact, facts.supportPreserved,
      currentExact, runtimeExact, ?_, facts.resourcesEmpty,
      facts.baseAltsEmpty, facts.framesEmpty⟩
  · simpa [wrapperPending, DemandDrivenCallStep.pendingCallOf] using facts
  · rw [facts.bodyReferences]
    rfl
  · rw [facts.bodyExecutables]
    simp [wrapperCopiedAt, wrapperExecutable, resultAtom,
      PLeaTTa.freshenResolutionClause, PLeaTTa.renameGoalSuffix,
      PLeaTTa.renameAtomSuffix_gnd]
  · rw [facts.activeAltsExact]

/-! ## Exact nested cut activation -/

/-- Any representative ground wrapper successor with the literal `cutg(7)`
body is ready to enter the two-occurrence cut predicate. -/
private theorem cutReadyFromGroundWrapper
    (state : RepresentativeActivePayloadState)
    (referenceHead :
      state.carrier.index.bodyReferences = [.call "cutg" [resultTerm]])
    (executableHead :
      state.carrier.index.bodyExecutables = [.call "cutg" [] resultAtom])
    (freshExact :
      state.carrier.index.freshFrontier =
        AlphaFreshFrontier state.carrier.index.alpha)
    (supportNil : state.carrier.index.support = [])
    (currentNil : state.carrier.index.current = [])
    (runtimeNil : state.carrier.index.runtime = [])
    (databaseExact :
      state.carrier.index.session.resolver.database = referenceDatabase)
    (nextFreshZero : state.carrier.index.session.resolver.nextFresh = 0)
    (worldExact :
      state.carrier.index.openConf.persistent.world = executableWorld)
    (callerExecutablesEmpty :
      state.carrier.index.callerExecutables = [])
    (outerEmpty : state.carrier.index.outer = [])
    (below :
      ConfBelowResolutionCounter state.carrier.index.openConf.toConf)
    (materializedHeads :
      MaterializedLocalCallHeadsAgreeWith state.carrier.index.alpha
        state.carrier.index.current state.carrier.index.bodyReferences
        state.carrier.index.bodyExecutables state.carrier.index.runtime
        state.representative state.carrier.index.referenceBase) :
    ∃ head : NestedCallHead state.carrier,
      MaterializedNestedCallReady state head ∧
        head.predicate = "cutg" ∧
        head.referencePayload = [resultTerm] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = resultAtom ∧
        head.executableRest = [] := by
  let head : NestedCallHead state.carrier :=
    { predicate := "cutg"
      referencePayload := [resultTerm]
      referenceRest := []
      arguments := []
      result := resultAtom
      executableRest := []
      referenceHead := referenceHead
      executableHead := executableHead }
  have executableTailNil : head.executableTail = [] := by
    simp [NestedCallHead.executableTail, head, callerExecutablesEmpty,
      outerEmpty]
  have openedPair :
      (openedFor state.carrier.index.session "cutg" [resultTerm]
        state.carrier.index.current).cursor.remaining =
          [selectedCutBranch, retainedCutBranch] := by
    rw [currentNil]
    change
      (prepareCall state.carrier.index.session.resolver
        (requestFor "cutg" [resultTerm] [])).1.remaining =
          [selectedCutBranch, retainedCutBranch]
    simp only [prepareCall, requestFor]
    rw [databaseExact, nextFreshZero]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "cutg" 1)).1 = [selectedCutBranch, retainedCutBranch]
    rw [cutVisibleClauses]
    rfl
  refine ⟨head, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine
    { toNestedCallOperationalReady :=
        { exactFresh := freshExact
          indexReady := ?_
          below := below
          candidateSupported := ?_
          sourceNonempty := ?_
          scanNonempty := ?_
          selected := ?_
          notThrow := ?_
          notDatabase := ?_ }
      materialized := ?_ }
  · rw [worldExact]
    rfl
  · change
      SupportedCandidateBank "cutg"
        (state.carrier.index.session.resolver.database.visibleClausesAt
          state.carrier.index.session.resolver.database.generation "cutg" 1)
        (state.carrier.index.openConf.persistent.world.resolutionCandidates
          "cutg" 0)
    simpa [databaseExact, worldExact] using cutCandidateBank
  · change
      state.carrier.index.session.resolver.database.visibleClausesAt
        state.carrier.index.session.resolver.database.generation "cutg" 1 ≠ []
    rw [databaseExact, cutVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.carrier.index.openConf.persistent.world.resolutionCandidates
          "cutg" 0)
        [] [] resultAtom head.executableTail state.carrier.index.runtime
        state.carrier.index.openConf.toConf.qterm
        (barrierDepth state.carrier.index.openConf.toConf + 1)
        state.carrier.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, cutResolutionCandidates]
    have argumentsMatch : PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, selectedCutExecutable, retainedCutExecutable,
      resultAtom, argumentsMatch, resultMatch]
  · intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    cases pulls with
    | zero cursor =>
        have branchExact : branch = selectedCutBranch := by
          have exact :
              [selectedCutBranch, retainedCutBranch] = branch :: branchTail :=
            openedPair.symm.trans frontier.finishRemaining
          exact (List.cons.inj exact).1.symm
        refine ⟨[], ?_, ?_⟩
        · simpa [branchExact] using selectedCutBranch_resolves_empty
        · rw [supportNil]
          intro identity name member
          simp at member
    | succ count cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = selectedCutBranch := by
          have exact :
              [selectedCutBranch, retainedCutBranch] = first :: branches :=
            openedPair.symm.trans remaining
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            selectedCutBranch_resolves_empty⟩)
  · simp [head, BuiltinThrowCall]
  · rfl
  · simpa [head, runtimeNil, PLeaTTa.subst_nil] using
      materializedHeads head.referenceHead head.executableHead

/-- The literal wrapper/cut program reaches the selected cut clause with both
the cut-local sibling and the wrapper-local sibling genuinely live. -/
private theorem nested_cut_selected_reachable
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (root : RepresentativeActivePayloadState)
        (head : NestedCallHead root.carrier)
        (finish : PreparedCursor) (altTail : List PLeaTTa.Alt)
        (copied : PLeaTTa.Clause) (installed : Subst)
        (after : RepresentativeActivePayloadState),
      RepresentativeNestedCallSuccessorFacts prog gt root head 0 [] []
        finish selectedCutBranch selectedCutExecutable [retainedCutBranch]
        [retainedCutExecutable] altTail copied installed after ∧
      root.carrier.index.active.alts = [wrapperAltAt 1] ∧
      after.carrier.index.bodyReferences = [.cut] ∧
      after.carrier.index.bodyExecutables =
        [.cutAt after.carrier.index.bodyBarrier] ∧
      after.carrier.index.active.alts ≠ [] ∧
      after.carrier.index.resources = [root.carrier.index.active] ∧
      after.carrier.index.callerReferences = [] ∧
      after.carrier.index.callerExecutables = [] ∧
      (∀ segment ∈ after.carrier.index.outer, segment.references = []) ∧
      after.carrier.index.baseAlts = [] ∧
      after.carrier.index.openConf.frames = [] ∧
      PLeaTTa.BarrierCacheCoherent after.carrier.index.openConf.toConf ∧
      StepsN 4
        (.running initialSession
          (.task 0 [.call "wrapcut" [resultTerm]] []))
        [.opened (requestFor "wrapcut" [resultTerm] []),
          .opened (requestFor "cutg" [resultTerm] [])]
        after.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 6
        (.ready initialOpenConf) after.carrier.fineState := by
  obtain
    ⟨rootFinish, rootRepresentative, rootSourceCanonical, rootFlattened,
      rootNextAlpha, rootInstalled, root, rootFacts, rootReferences,
      rootExecutables, rootAlphaNil, rootSupportNil, rootCurrentNil,
      rootRuntimeNil, rootActiveAlts, rootResourcesEmpty, rootBaseAltsEmpty,
      rootFramesEmpty⟩ :=
    wrapper_selected_reachable (prog := prog) (gt := gt)
  have rootDatabase :
      root.carrier.index.session.resolver.database = referenceDatabase := by
    rw [rootFacts.sessionExact]
    rfl
  have rootNextFresh :
      root.carrier.index.session.resolver.nextFresh = 0 := by
    rw [rootFacts.sessionExact]
    rfl
  have rootWorld :
      root.carrier.index.openConf.persistent.world = executableWorld := by
    simpa [initialOpenConf] using rootFacts.worldPreserved
  obtain
    ⟨head, cutReady, headPredicate, headPayload, headReferenceRest,
      headArguments, headResult, headExecutableRest⟩ :=
    cutReadyFromGroundWrapper root rootReferences rootExecutables
      rootFacts.freshFrontierExact rootSupportNil rootCurrentNil
      rootRuntimeNil rootDatabase rootNextFresh rootWorld
      rootFacts.callerExecutablesEmpty rootFacts.outerEmpty rootFacts.below
      rootFacts.materializedBodyHeads
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
    cutReady.pushDetailed (prog := prog) (gt := gt)
  have openedPair :
      (openedFor root.carrier.index.session "cutg" [resultTerm]
        root.carrier.index.current).cursor.remaining =
          [selectedCutBranch, retainedCutBranch] := by
    rw [rootCurrentNil]
    change
      (prepareCall root.carrier.index.session.resolver
        (requestFor "cutg" [resultTerm] [])).1.remaining =
          [selectedCutBranch, retainedCutBranch]
    simp only [prepareCall, requestFor]
    rw [rootDatabase, rootNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "cutg" 1)).1 = [selectedCutBranch, retainedCutBranch]
    rw [cutVisibleClauses]
    rfl
  have countZero : count = 0 := by
    cases facts.pulls with
    | zero cursor => rfl
    | succ n cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = selectedCutBranch := by
          have exact :
              [selectedCutBranch, retainedCutBranch] = first :: branches :=
            openedPair.symm.trans (by simpa [headPredicate, headPayload] using remaining)
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            selectedCutBranch_resolves_empty⟩)
  have skippedBranchesNil : skippedBranches = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.sourceSkipCount, countZero]
  have sourceShape := facts.sourceBank
  rw [headPredicate, headPayload, openedPair, skippedBranchesNil] at sourceShape
  have branchExact : branch = selectedCutBranch :=
    (List.cons.inj sourceShape).1.symm
  have branchTailExact : branchTail = [retainedCutBranch] :=
    (List.cons.inj sourceShape).2.symm
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.executableSkipCount, countZero]
  have executableShape := facts.executableBank
  rw [headPredicate, headArguments, rootWorld, skippedClausesNil] at executableShape
  simp only [List.length_nil] at executableShape
  rw [cutResolutionCandidates] at executableShape
  have clauseExact : clause = selectedCutExecutable :=
    (List.cons.inj executableShape).1.symm
  have clauseTailExact : clauseTail = [retainedCutExecutable] :=
    (List.cons.inj executableShape).2.symm
  have tailLength : altTail.length = 1 := by
    have exact := facts.frontier.tailScan.length_exact
    rw [clauseTailExact] at exact
    simpa [headArguments, headResult, rootRuntimeNil, PLeaTTa.subst_nil,
      retainedClauseCount, resolutionClauseRetained, resultAtom,
      retainedCutExecutable, PLeaTTa.prologGroundIdentical,
      PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList] using exact
  have altTailNonempty : altTail ≠ [] := by
    intro empty
    rw [empty] at tailLength
    simp at tailLength
  have copiedBody :
      copied.body =
        [.cutAt (barrierDepth root.carrier.index.openConf.toConf + 1)] := by
    rw [facts.frontier.copiedExact, clauseExact]
    simp [PLeaTTa.freshenResolutionClause, selectedCutExecutable,
      PLeaTTa.renameGoalSuffix]
  have afterReferences : after.carrier.index.bodyReferences = [.cut] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have afterExecutablesKnown :
      after.carrier.index.bodyExecutables =
        [.cutAt (barrierDepth root.carrier.index.openConf.toConf + 1)] := by
    rw [facts.bodyExecutables, copiedBody]
  have activeReady := after.carrier.agreement.core.control.ready
  rw [afterReferences] at activeReady
  rcases activeReady with
    ⟨_persistent, _currentControl, _queryTerm, activePayload⟩
  have bodyPayload := activePayload.headPayload
  rcases bodyPayload.control.cutHead with
    ⟨executableTail, executableShapeAtCut, _tailControl⟩
  rw [afterExecutablesKnown] at executableShapeAtCut
  have bodyBarrierExact :
      after.carrier.index.bodyBarrier =
        barrierDepth root.carrier.index.openConf.toConf + 1 := by
    have headExact := (List.cons.inj executableShapeAtCut).1
    have same :
        barrierDepth root.carrier.index.openConf.toConf + 1 =
          after.carrier.index.bodyBarrier := by
      injection headExact
    exact same.symm
  have afterExecutables :
      after.carrier.index.bodyExecutables =
        [.cutAt after.carrier.index.bodyBarrier] := by
    simpa [bodyBarrierExact] using afterExecutablesKnown
  have afterResources :
      after.carrier.index.resources = [root.carrier.index.active] := by
    rw [facts.resourcesExact, rootResourcesEmpty]
  have afterCallerReferences :
      after.carrier.index.callerReferences = [] := by
    simpa [headReferenceRest] using facts.callerReferences
  have afterCallerExecutables :
      after.carrier.index.callerExecutables = [] := by
    simpa [headExecutableRest] using facts.callerExecutables
  have afterOuterAllEmpty :
      ∀ segment ∈ after.carrier.index.outer, segment.references = [] := by
    intro segment member
    rw [facts.outerSegments, rootFacts.callerReferencesEmpty,
      rootFacts.callerExecutablesEmpty, rootFacts.outerEmpty] at member
    simp only [List.mem_singleton] at member
    subst segment
    rfl
  have afterBaseAlts : after.carrier.index.baseAlts = [] :=
    facts.baseAltsPreserved.trans rootBaseAltsEmpty
  have afterFrames : after.carrier.index.openConf.frames = [] := by
    rw [facts.openConfExact,
      PrologRepresentativeStepActivationBridge.activatedOpenSuccessor_frames]
    simp [NestedCallHead.pending, DemandDrivenCallStep.pendingCallOf,
      rootFramesEmpty]
  have database :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using
      referenceDatabase_relates_executableWorld
  have sourceNonempty :
      initialSession.resolver.database.visibleClausesAt
        initialSession.resolver.database.generation "wrapcut" 1 ≠ [] := by
    simp [initialSession, wrapperVisibleClauses]
  have scanned :
      resolveAlts
          (initialOpenConf.toConf.world.resolutionCandidates "wrapcut" 0)
          [] [] resultAtom [] [] initialOpenConf.toConf.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter =
        (wrapperScan.1, wrapperScan.2) := by
    change wrapperScan = (wrapperScan.1, wrapperScan.2)
    exact (Prod.eta wrapperScan).symm
  obtain ⟨_sourceEntry, rootFineEntry, _entryAgain⟩ :=
    taskCall_callEnter_bank_correspondence
      (prog := prog) (gt := gt) (session := initialSession)
      (state := initialOpenConf) database wrapperEntry.indexReady 0 "wrapcut"
      [resultTerm] [] [] [] resultAtom [] [] wrapperScan.1 wrapperScan.2
      wrapperEntry.entry.arity (by simp [BuiltinThrowCall])
      (by simp [DatabaseActions.recognizeDatabaseAction]) sourceNonempty
      wrapperEntry.entry.callHead scanned
  have rootSealedEntry :
      PLeaTTa.Step prog gt initialOpenConf.toConf wrapperPending.pulled.toConf := by
    simpa [wrapperPending] using
      (DemandDrivenCallStep.Step.ready_callPending_projects_to_sealed
        rootFineEntry)
  have initialCoherent :
      PLeaTTa.BarrierCacheCoherent initialOpenConf.toConf := by
    simp [initialOpenConf, OpenConf.toConf, Control.toConf,
      PLeaTTa.BarrierCacheCoherent]
  have rootPulledCoherent :
      PLeaTTa.BarrierCacheCoherent wrapperPending.pulled.toConf :=
    rootSealedEntry.preserves_barrierCacheCoherent initialCoherent
  have rootActivatedCoherent :
      PLeaTTa.BarrierCacheCoherent root.carrier.index.openConf.toConf := by
    have exact :=
      rootFacts.activation.executableStep.preserves_barrierCacheCoherent
        rootPulledCoherent
    have openExact :
        root.carrier.index.openConf =
          PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            wrapperPending (wrapperCopiedAt 0) []
              initialOpenConf.control.qterm rootInstalled :=
      DemandDrivenCallStep.FineConf.ready.inj rootFacts.fineStateExact
    rw [openExact]
    simpa [wrapperPending, DemandDrivenCallStep.pendingCallOf] using exact
  have nestedSealedEntry :
      PLeaTTa.Step prog gt root.carrier.index.openConf.toConf
        head.pending.pulled.toConf :=
    DemandDrivenCallStep.Step.ready_callPending_projects_to_sealed
      cutReady.fineEntry
  have nestedPulledCoherent :
      PLeaTTa.BarrierCacheCoherent head.pending.pulled.toConf :=
    nestedSealedEntry.preserves_barrierCacheCoherent rootActivatedCoherent
  have afterCoherent :
      PLeaTTa.BarrierCacheCoherent after.carrier.index.openConf.toConf := by
    have exact :=
      facts.activationStep.preserves_barrierCacheCoherent
        nestedPulledCoherent
    rw [facts.openConfExact]
    simpa only [
      PrologRepresentativeStepActivationBridge.activatedOpenSuccessor_toConf]
      using exact
  have sourceAll := rootFacts.sourceSteps.trans facts.certificate.sourceSteps
  have fineAll := rootFacts.fineSteps.trans facts.certificate.fineSteps
  subst count
  subst skippedBranches
  subst skippedClauses
  subst branch
  subst branchTail
  subst clause
  subst clauseTail
  refine
    ⟨root, head, finish, altTail, copied, installed, after, ?_,
      rootActiveAlts, afterReferences, afterExecutables, ?_, afterResources,
      afterCallerReferences, afterCallerExecutables, afterOuterAllEmpty,
      afterBaseAlts, afterFrames, afterCoherent, ?_, ?_⟩
  · simpa [headPredicate, headPayload, headArguments] using facts
  · simpa [facts.activeAltsExact] using altTailNonempty
  · simpa [headPredicate, headPayload, rootCurrentNil, Nat.add_assoc] using
      sourceAll
  · norm_num at fineAll ⊢
    exact fineAll

/-! ## The reachable cut forces the first-live classifier arm -/

/-- A real two-level source program reaches a committed root answer whose
inner cut has pruned the inner sibling while the duplicate outer wrapper
remains live.  The exhaustive classifier is therefore forced into its
`firstLive` arm; terminal exhaustion is impossible. -/
theorem ground_wrapper_cut_forces_first_live
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (scheduled :
          RepresentativePersistentFreeCommittedScheduledPayloadState)
        (ready : RootClosedCommittedAnswerReady scheduled)
        (partition :
          OuterResourceCatchupPartition scheduled.carrier.index.alpha
            scheduled.carrier.index.outer scheduled.carrier.index.resources
            scheduled.carrier.index.context)
        (outerResource : RetainedAlternativeSegment),
      FirstLiveRelates prog gt ready partition ∧
      scheduled.carrier.index.resources = [outerResource] ∧
      outerResource.alts ≠ [] ∧
      partition.crossedResources = [] ∧
      partition.first = outerResource ∧
      partition.survivingResources = [] ∧
      (∀ terminalPartition :
          TerminalOuterResourceCatchupPartition
            scheduled.carrier.index.alpha scheduled.carrier.index.outer
            scheduled.carrier.index.resources scheduled.carrier.index.context
            [],
        ¬ TerminalRelates prog gt ready terminalPartition) ∧
      (∃ prunedToken : CursorToken,
        prunedToken.scope = scheduled.carrier.index.predicateScope ∧
        StepsN 6
          (.running initialSession
            (.task 0 [.call "wrapcut" [resultTerm]] []))
          [.opened (requestFor "wrapcut" [resultTerm] []),
            .opened (requestFor "cutg" [resultTerm] []),
            .pruned prunedToken]
          scheduled.carrier.sourceState) ∧
      DemandDrivenCallStep.StepsN prog gt 7
        (.ready initialOpenConf) scheduled.carrier.fineState := by
  obtain
    ⟨root, head, finish, altTail, copied, installed, after, facts,
      rootActiveAlts, afterReferences, afterExecutables, afterActiveNonempty,
      afterResources, afterCallerReferences, afterCallerExecutables,
      afterOuterAllEmpty, afterBaseAlts, afterFrames, afterCoherent,
      sourcePrefix, finePrefix⟩ :=
    nested_cut_selected_reachable (prog := prog) (gt := gt)
  let active :=
    RepresentativePersistentFreeActivePayloadState.ofLegacy after
  have activeReferences : active.carrier.index.bodyReferences = [.cut] := by
    change after.carrier.index.bodyReferences = [.cut]
    exact afterReferences
  have activeExecutables :
      active.carrier.index.bodyExecutables =
        [.cutAt active.carrier.index.bodyBarrier] := by
    change
      after.carrier.index.bodyExecutables =
        [.cutAt after.carrier.index.bodyBarrier]
    exact afterExecutables
  have activeCoherent :
      PLeaTTa.BarrierCacheCoherent active.carrier.index.openConf.toConf := by
    simpa [active] using afterCoherent
  let committed :=
    RepresentativePersistentFreeActivePayloadState.afterCut prog gt active
      [] [] activeReferences activeExecutables activeCoherent
  have committedReferenceEmpty :
      committed.carrier.index.bodyReferences = [] := by
    rfl
  have committedExecutableEmpty :
      committed.carrier.index.bodyExecutables = [] := by
    rfl
  let scheduled :=
    RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer prog gt
      committed committedReferenceEmpty committedExecutableEmpty
  have scheduledResources :
      scheduled.carrier.index.resources = [root.carrier.index.active] := by
    change active.carrier.index.resources = [root.carrier.index.active]
    change after.carrier.index.resources = [root.carrier.index.active]
    exact afterResources
  have scheduledCallerReferences :
      scheduled.carrier.index.callerReferences = [] := by
    change after.carrier.index.callerReferences = []
    exact afterCallerReferences
  have scheduledOuterAllEmpty :
      ∀ segment ∈ scheduled.carrier.index.outer,
        segment.references = [] := by
    change ∀ segment ∈ after.carrier.index.outer,
      segment.references = []
    exact afterOuterAllEmpty
  have scheduledBaseAlts : scheduled.carrier.index.baseAlts = [] := by
    change after.carrier.index.baseAlts = []
    exact afterBaseAlts
  have scheduledFrames : scheduled.carrier.index.openConf.frames = [] := by
    change
      (RepresentativePersistentFreeActivePayloadState.committedOpenConf active
        []).frames = []
    simpa [RepresentativePersistentFreeActivePayloadState.committedOpenConf,
      active, cutSuccessor] using afterFrames
  have cutFacts :=
    persistentFreeActive_afterCut (prog := prog) (gt := gt)
      (RepresentativePersistentFreeActivePayloadState.cutAgreement active [] []
        activeReferences activeExecutables)
      activeCoherent
  have sourcePrefixActive :
      StepsN 4
        (.running initialSession
          (.task 0 [.call "wrapcut" [resultTerm]] []))
        [.opened (requestFor "wrapcut" [resultTerm] []),
          .opened (requestFor "cutg" [resultTerm] [])]
        active.carrier.sourceState := by
    simpa [active] using sourcePrefix
  have cutSourceOne :
      StepsN 1 active.carrier.sourceState
        [.pruned
          (retainedCursorTokenAt active.carrier.index.predicateScope
            active.carrier.index.finish active.carrier.index.branch
            active.carrier.index.branchTail)]
        committed.carrier.sourceState := by
    have one :=
      PLeaTTa.PrologHeterogeneousPrefixBridge.CertifiedTransition.oneSourceStep
        cutFacts.2.1
    change
      StepsN 1 active.carrier.sourceState
        [.pruned
          (retainedCursorTokenAt active.carrier.index.predicateScope
            active.carrier.index.finish active.carrier.index.branch
            active.carrier.index.branchTail)]
        (RepresentativePersistentFreeActivePayloadState.afterCut prog gt
          active [] [] activeReferences activeExecutables
          activeCoherent).carrier.sourceState
    rw [RepresentativePersistentFreeActivePayloadState.afterCut_sourceState]
    simpa [PersistentFreeActivePayloadState.sourceState,
      RepresentativePersistentFreeActivePayloadState.committedSource] using
      one
  have bodySourceOne :
      StepsN 1 committed.carrier.sourceState []
        scheduled.carrier.sourceState := by
    have one :=
      PLeaTTa.PrologHeterogeneousPrefixBridge.CertifiedTransition.oneSourceStep
        (RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer_sourceStep
          prog gt committed committedReferenceEmpty committedExecutableEmpty)
    simpa [scheduled, PersistentFreeCommittedPayloadState.sourceState] using
      one
  have sourceAll := sourcePrefixActive.trans (cutSourceOne.trans bodySourceOne)
  have finePrefixActive :
      DemandDrivenCallStep.StepsN prog gt 6 (.ready initialOpenConf)
        active.carrier.fineState := by
    simpa [active] using finePrefix
  have cutFineOne :
      DemandDrivenCallStep.StepsN prog gt 1 active.carrier.fineState
        committed.carrier.fineState := by
    have one :=
      PLeaTTa.PrologHeterogeneousPrefixBridge.CertifiedTransition.oneFineStep
        cutFacts.2.2.1
    change
      DemandDrivenCallStep.StepsN prog gt 1 active.carrier.fineState
        (RepresentativePersistentFreeActivePayloadState.afterCut prog gt
          active [] [] activeReferences activeExecutables
          activeCoherent).carrier.fineState
    rw [RepresentativePersistentFreeActivePayloadState.afterCut_fineState]
    simpa [PersistentFreeActivePayloadState.fineState,
      RepresentativePersistentFreeActivePayloadState.committedOpenConf] using
      one
  have fineAll := finePrefixActive.trans cutFineOne
  let ready :=
    PrologCommittedScheduledOuterCatchupBridge.RepresentativePersistentFreeCommittedScheduledPayloadState.rootClosedAnswerReady
      scheduled scheduledCallerReferences scheduledOuterAllEmpty
        scheduledBaseAlts scheduledFrames
  have outerResourceNonempty : root.carrier.index.active.alts ≠ [] := by
    rw [rootActiveAlts]
    simp
  have noTerminal :
      ∀ terminalPartition :
          TerminalOuterResourceCatchupPartition
            scheduled.carrier.index.alpha scheduled.carrier.index.outer
            scheduled.carrier.index.resources scheduled.carrier.index.context
            [],
        ¬ TerminalRelates prog gt ready terminalPartition := by
    intro terminalPartition _relation
    have resourceEmpty : root.carrier.index.active.alts = [] :=
      terminalPartition.crossedWork.all_empty root.carrier.index.active (by
        rw [scheduledResources]
        simp)
    exact outerResourceNonempty resourceEmpty
  have classified := ready.classifyAndRelate (prog := prog) (gt := gt)
  cases classified with
  | firstLive partition relation =>
      have resourceShape :
          [root.carrier.index.active] =
            partition.crossedResources ++
              partition.first :: partition.survivingResources :=
        scheduledResources.symm.trans partition.resourcesEq
      have lengthShape := congrArg List.length resourceShape
      have crossedLength : partition.crossedResources.length = 0 := by
        simp only [List.length_cons, List.length_nil, List.length_append] at lengthShape
        omega
      have survivingLength : partition.survivingResources.length = 0 := by
        simp only [List.length_cons, List.length_nil, List.length_append] at lengthShape
        omega
      have crossedNil : partition.crossedResources = [] :=
        List.eq_nil_of_length_eq_zero crossedLength
      have survivingNil : partition.survivingResources = [] :=
        List.eq_nil_of_length_eq_zero survivingLength
      have firstExact : partition.first = root.carrier.index.active := by
        rw [crossedNil, survivingNil] at resourceShape
        exact (List.cons.inj resourceShape).1.symm
      refine
        ⟨scheduled, ready, partition, root.carrier.index.active, relation,
          scheduledResources, outerResourceNonempty, crossedNil, firstExact,
          survivingNil, noTerminal, ?_, ?_⟩
      · refine
          ⟨retainedCursorTokenAt active.carrier.index.predicateScope
              active.carrier.index.finish active.carrier.index.branch
              active.carrier.index.branchTail,
            ?_, ?_⟩
        · rfl
        simpa [Nat.add_assoc] using sourceAll
      · norm_num at fineAll ⊢
        simpa [scheduled] using fineAll
  | terminal partition relation =>
      exact False.elim (noTerminal partition relation)

end PLeaTTa.PrologCommittedScheduledFirstLiveRegression
