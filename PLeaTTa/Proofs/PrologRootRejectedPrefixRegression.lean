-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootRejectedPrefixRegression
Purpose: Exercise literal-root activation after two rigid source rejections,
  with one selected occurrence and one retained sibling.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootCallReadyBridge

namespace PLeaTTa.PrologRootRejectedPrefixRegression

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
open PrologCallPayloadBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologActivationMacro
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologRepresentativeCallFrontierBridge
open PrologRecursiveCallPayloadBridge
open PrologRootCallReadyBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-! ## Four source-ordered occurrences -/

def queryTerm : Term := .integer 0

def queryAtom : Atom := .gnd (.int 0)

def bodyTerm : Term := .integer 9

def bodyAtom : Atom := .gnd (.int 9)

def firstRejectedReference : LocalClause :=
  { predicate := "p"
    arguments := [.integer 1]
    body := [] }

def secondRejectedReference : LocalClause :=
  { predicate := "p"
    arguments := [.integer 2]
    body := [] }

def selectedReference : LocalClause :=
  { predicate := "p"
    arguments := [queryTerm]
    body := [.call "chosen" [bodyTerm]] }

def retainedReference : LocalClause :=
  { predicate := "p"
    arguments := [queryTerm]
    body := [.call "retained" [bodyTerm]] }

def firstRejectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 1)
    body := [] }

def secondRejectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 2)
    body := [] }

def selectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := queryAtom
    body := [.call "chosen" [] bodyAtom] }

def retainedExecutable : PLeaTTa.Clause :=
  { params := []
    result := queryAtom
    body := [.call "retained" [] bodyAtom] }

def firstVersion : VersionedClause :=
  Database.empty.allocate firstRejectedReference

def secondVersion : VersionedClause :=
  (Database.empty.assertz firstRejectedReference).allocate
    secondRejectedReference

def selectedVersion : VersionedClause :=
  ((Database.empty.assertz firstRejectedReference).assertz
    secondRejectedReference).allocate selectedReference

def retainedVersion : VersionedClause :=
  (((Database.empty.assertz firstRejectedReference).assertz
    secondRejectedReference).assertz selectedReference).allocate
      retainedReference

def referenceDatabase : Database :=
  (((Database.empty.assertz firstRejectedReference).assertz
    secondRejectedReference).assertz selectedReference).assertz
      retainedReference

def executableWorld : PWorld :=
  ((((default : PWorld).reindexClauses.appendProgClause
    ("p", firstRejectedExecutable)).appendProgClause
    ("p", secondRejectedExecutable)).appendProgClause
    ("p", selectedExecutable)).appendProgClause
    ("p", retainedExecutable)

/-! ## Empty valuation and ground payload -/

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

private theorem rootControl (barrier : Nat) :
    NormalizedAlphaGoalsAgree [] barrier
      [.call "p" [queryTerm]] [.call "p" [] queryAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.integer (alpha := []) 0))
      .nil

private theorem rootPayload (barrier : Nat) :
    TaskPayloadAgrees [] [] barrier [] [] [] []
      [.call "p" [queryTerm]] [.call "p" [] queryAtom] :=
  emptyTaskData.withControl (rootControl barrier)

private theorem rootPayloadSupported :
    AlphaTermsSupported [] [] [queryTerm] := by
  intro term member
  simp only [List.mem_singleton] at member
  subst term
  simp [queryTerm, AlphaTreeSupported, Term.denote,
    PrologMguOpenAgreement.TreeVariablesSatisfy,
    PrologMguOpenAgreement.TreesVariablesSatisfy]

private def groundBodyHeadAgrees (predicate : String) :
    CompilerAdequacy.GoalAgrees
      (.call predicate [bodyTerm]) (.call predicate [] bodyAtom) :=
  .definedCall CompilerAdequacy.TermsAgree.nil
    (CompilerAdequacy.TermAgrees.integer 9)

private def groundBodyAgrees (predicate : String) :
    CompilerAdequacy.GoalsAgree
      [.call predicate [bodyTerm]] [.call predicate [] bodyAtom] :=
  .cons (groundBodyHeadAgrees predicate) .nil

private theorem groundBodyHeadSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalAgreesSupported [] []
      (groundBodyHeadAgrees predicate) := by
  unfold groundBodyHeadAgrees
  refine
    @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.definedCall
      [] [] predicate predicate [] bodyTerm [] bodyAtom
      CompilerAdequacy.TermsAgree.nil
      (CompilerAdequacy.TermAgrees.integer 9) ?_ ?_
  · simp [CompilerGoalSubstitutionAdequacy.TermsAgreeSupported,
      CompilerSubstitutionAdequacy.termsVariablesIn]
  · simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
      CompilerSubstitutionAdequacy.termVariablesIn, bodyTerm]

private theorem groundBodySupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      (groundBodyAgrees predicate) := by
  exact .cons (groundBodyHeadSupported predicate) .nil

private theorem firstClauseAgrees :
    LocalClauseAgrees firstRejectedReference
      ("p", firstRejectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], .integer 1, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 1⟩
  · intro name
    simp [firstRejectedReference, firstRejectedExecutable,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables]

private theorem secondClauseAgrees :
    LocalClauseAgrees secondRejectedReference
      ("p", secondRejectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], .integer 2, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 2⟩
  · intro name
    simp [secondRejectedReference, secondRejectedExecutable,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables]

private theorem selectedClauseAgrees :
    LocalClauseAgrees selectedReference ("p", selectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := groundBodyAgrees "chosen"
      support := ?_ }
  · exact
      ⟨[], queryTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 0⟩
  · intro name
    simp [selectedReference, selectedExecutable, queryTerm, queryAtom,
      bodyTerm, bodyAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem retainedClauseAgrees :
    LocalClauseAgrees retainedReference ("p", retainedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := groundBodyAgrees "retained"
      support := ?_ }
  · exact
      ⟨[], queryTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 0⟩
  · intro name
    simp [retainedReference, retainedExecutable, queryTerm, queryAtom,
      bodyTerm, bodyAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

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
  have first := emptyDatabaseRelatesIndexedWorld.assertz firstClauseAgrees
  have second := first.assertz secondClauseAgrees
  have selected := second.assertz selectedClauseAgrees
  have retained := selected.assertz retainedClauseAgrees
  simpa [referenceDatabase, executableWorld] using retained

/-! ## Exact candidate bank and entry -/

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

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have first :=
    PWorld.appendProgClause_coherent _ ("p", firstRejectedExecutable) root
  have second :=
    PWorld.appendProgClause_coherent _ ("p", secondRejectedExecutable) first
  have selected :=
    PWorld.appendProgClause_coherent _ ("p", selectedExecutable) second
  have retained :=
    PWorld.appendProgClause_coherent _ ("p", retainedExecutable) selected
  simpa [executableWorld] using retained

private theorem pResolutionCandidates :
    executableWorld.resolutionCandidates "p" 0 =
      [firstRejectedExecutable, secondRejectedExecutable,
        selectedExecutable, retainedExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, firstRejectedExecutable, secondRejectedExecutable,
    selectedExecutable, retainedExecutable, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [firstVersion, secondVersion, selectedVersion, retainedVersion] := by
  rfl

private theorem pCandidateBank :
    SupportedCandidateBank "p"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1)
      (executableWorld.resolutionCandidates "p" 0) := by
  rw [pVisibleClauses, pResolutionCandidates]
  let firstHead : CandidateClauseAgrees "p" firstVersion
      firstRejectedExecutable := by
    change LocalClauseAgrees firstRejectedReference
      ("p", firstRejectedExecutable)
    exact firstClauseAgrees
  let secondHead : CandidateClauseAgrees "p" secondVersion
      secondRejectedExecutable := by
    change LocalClauseAgrees secondRejectedReference
      ("p", secondRejectedExecutable)
    exact secondClauseAgrees
  let selectedHead : CandidateClauseAgrees "p" selectedVersion
      selectedExecutable := by
    change LocalClauseAgrees selectedReference ("p", selectedExecutable)
    exact selectedClauseAgrees
  let retainedHead : CandidateClauseAgrees "p" retainedVersion
      retainedExecutable := by
    change LocalClauseAgrees retainedReference ("p", retainedExecutable)
    exact retainedClauseAgrees
  have firstEncoding : EncodingInjectiveOn firstVersion.clause.variables := by
    simp [EncodingInjectiveOn, firstVersion, Database.allocate,
      firstRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables]
  have secondEncoding : EncodingInjectiveOn secondVersion.clause.variables := by
    simp [EncodingInjectiveOn, secondVersion, Database.allocate,
      secondRejectedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables]
  have selectedEncoding :
      EncodingInjectiveOn selectedVersion.clause.variables := by
    simp [EncodingInjectiveOn, selectedVersion, Database.allocate,
      selectedReference, queryTerm, bodyTerm, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables]
  have retainedEncoding :
      EncodingInjectiveOn retainedVersion.clause.variables := by
    simp [EncodingInjectiveOn, retainedVersion, Database.allocate,
      retainedReference, queryTerm, bodyTerm, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables]
  have firstBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        firstVersion.clause.variables firstVersion.clause.variables
        firstHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      firstHead.body
    have bodyEq : firstHead.body =
        (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  have secondBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        secondVersion.clause.variables secondVersion.clause.variables
        secondHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      secondHead.body
    have bodyEq : secondHead.body =
        (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  have selectedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        selectedVersion.clause.variables selectedVersion.clause.variables
        selectedHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      selectedHead.body
    have bodyEq : selectedHead.body = groundBodyAgrees "chosen" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundBodySupported "chosen"
  have retainedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        retainedVersion.clause.variables retainedVersion.clause.variables
        retainedHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      retainedHead.body
    have bodyEq : retainedHead.body = groundBodyAgrees "retained" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundBodySupported "retained"
  refine
    ⟨List.Forall₂.cons firstHead
      (List.Forall₂.cons secondHead
        (List.Forall₂.cons selectedHead
          (List.Forall₂.cons retainedHead .nil))), ?_⟩
  exact
    .cons (head := firstHead) firstEncoding firstBody
      (.cons (head := secondHead) secondEncoding secondBody
        (.cons (head := selectedHead) selectedEncoding selectedBody
          (.cons (head := retainedHead) retainedEncoding retainedBody .nil)))

private def pScan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] queryAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf pScan.1 pScan.2

private theorem pEntry :
    RepresentativeSupportedCallEntryRelates []
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
      database ready "p" [queryTerm] [] [] [] queryAtom [] []
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

private def selectedCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] [] queryAtom 0 1
    selectedExecutable

private def retainedCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] [] queryAtom 1 1
    retainedExecutable

private def selectedAlt : PLeaTTa.Alt :=
  resolutionAlt [] [] queryAtom [] [] queryAtom 1 0 selectedExecutable

private def retainedAlt : PLeaTTa.Alt :=
  resolutionAlt [] [] queryAtom [] [] queryAtom 1 1 retainedExecutable

private theorem pScanExact : pScan = ([selectedAlt, retainedAlt], 2) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 0)
        [] [] queryAtom [] [] queryAtom 1 0 =
      ([selectedAlt, retainedAlt], 2)
  rw [pResolutionCandidates]
  rw [resolveAlts_eq_scanResolution]
  have scan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [firstRejectedExecutable, secondRejectedExecutable,
          selectedExecutable, retainedExecutable]
        0 [selectedAlt, retainedAlt] 2 :=
    .skipped firstRejectedExecutable
      [secondRejectedExecutable, selectedExecutable, retainedExecutable]
      0 2 [selectedAlt, retainedAlt]
      (by
        simp [resolutionClauseRetained, queryAtom, firstRejectedExecutable,
          PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
          PLeaTTa.prologMatchCompatList])
      (.skipped secondRejectedExecutable
        [selectedExecutable, retainedExecutable]
        0 2 [selectedAlt, retainedAlt]
        (by
          simp [resolutionClauseRetained, queryAtom,
            secondRejectedExecutable, PLeaTTa.prologGroundIdentical,
            PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList])
        (.retained selectedExecutable [retainedExecutable]
          0 2 [retainedAlt]
          (by
            simp [resolutionClauseRetained, queryAtom, selectedExecutable,
              PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
              PLeaTTa.prologMatchCompatList])
          (.retained retainedExecutable [] 1 2 []
            (by
              simp [resolutionClauseRetained, queryAtom, retainedExecutable,
                PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
                PLeaTTa.prologMatchCompatList])
            (.nil 2))))
  simpa [selectedAlt, retainedAlt] using scan.result_eq

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

private def firstPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 0 firstVersion

private def secondPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 0 secondVersion

private def selectedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 0 selectedVersion

private def retainedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 0 retainedVersion

private theorem pOpenedRemaining :
    (openedFor initialSession "p" [queryTerm] []).cursor.remaining =
      [firstPrepared, secondPrepared, selectedPrepared, retainedPrepared] := by
  rfl

private theorem firstRejected :
    ¬ ∃ result, HeadResolution firstPrepared result := by
  have agreement :
      NormalizedHeadAgrees firstPrepared [] queryAtom
        firstRejectedExecutable := by
    constructor
    · rfl
    · exact AlphaEquationsAgree.cons
        (AlphaTermAgrees.integer (alpha := []) 0)
        (AlphaTermAgrees.integer (alpha := []) 1)
        .nil
  have rejected :
      resolutionClauseRetained [] queryAtom firstRejectedExecutable = false :=
    rfl
  exact agreement.no_headResolution_of_rejected rejected

private theorem secondRejected :
    ¬ ∃ result, HeadResolution secondPrepared result := by
  have agreement :
      NormalizedHeadAgrees secondPrepared [] queryAtom
        secondRejectedExecutable := by
    constructor
    · rfl
    · exact AlphaEquationsAgree.cons
        (AlphaTermAgrees.integer (alpha := []) 0)
        (AlphaTermAgrees.integer (alpha := []) 2)
        .nil
  have rejected :
      resolutionClauseRetained [] queryAtom secondRejectedExecutable = false :=
    rfl
  exact agreement.no_headResolution_of_rejected rejected

private theorem selectedNormalized :
    selectedPrepared.normalizedHeadEquations = [(queryTerm, queryTerm)] := by
  rfl

private theorem retainedNormalized :
    retainedPrepared.normalizedHeadEquations = [(queryTerm, queryTerm)] := by
  rfl

private theorem firstNormalized :
    firstPrepared.normalizedHeadEquations =
      [(queryTerm, (.integer 1 : Term))] := by
  rfl

private theorem secondNormalized :
    secondPrepared.normalizedHeadEquations =
      [(queryTerm, (.integer 2 : Term))] := by
  rfl

private theorem selectedResolves : HeadResolution selectedPrepared [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [selectedNormalized]
    change OrderedTreeMgu [(Term.denote queryTerm, Term.denote queryTerm)] []
    exact OrderedTreeMgu.cons
      (Term.denote queryTerm) (Term.denote queryTerm) [] [] []
      (.reflexive (Term.denote queryTerm)) OrderedTreeMgu.nil
  · simp [selectedPrepared, preparedBranchOf]

private theorem retainedResolves : HeadResolution retainedPrepared [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [retainedNormalized]
    change OrderedTreeMgu [(Term.denote queryTerm, Term.denote queryTerm)] []
    exact OrderedTreeMgu.cons
      (Term.denote queryTerm) (Term.denote queryTerm) [] [] []
      (.reflexive (Term.denote queryTerm)) OrderedTreeMgu.nil
  · simp [retainedPrepared, preparedBranchOf]

private theorem firstPartnerRejected
    {cursor : PreparedCursor} {clause : PLeaTTa.Clause}
    {tail : List ClauseBranch}
    (context :
      CursorCallContext cursor referenceDatabase.generation "p"
        [queryTerm] [])
    (remaining : cursor.remaining = firstPrepared :: tail)
    (wellFormed : cursor.WellFormed)
    (supported :
      SupportedPreparedCandidateAgrees cursor.callGeneration cursor.predicate
        cursor.arguments cursor.bindings firstPrepared clause)
    (arity : clause.params.length = 0) :
    resolutionClauseRetained [] queryAtom clause = false := by
  have query : NormalizedCallAgrees [] cursor [] queryAtom := by
    constructor
    rw [context.arguments_eq, context.bindings_eq]
    exact AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 0) .nil
  have head : NormalizedHeadAgrees firstPrepared [] queryAtom clause :=
    supportedPreparedCandidate_normalizedHeadAgrees query wellFormed
      (by rw [remaining]; simp) supported arity
  rcases clause with ⟨params, result, body⟩
  simp only at arity
  have paramsNil : params = [] := List.eq_nil_of_length_eq_zero arity
  subst params
  have equations := head.equations
  rw [firstNormalized] at equations
  cases equations with
  | cons left right tail =>
      cases left
      cases right
      cases tail
      rfl

private theorem secondPartnerRejected
    {cursor : PreparedCursor} {clause : PLeaTTa.Clause}
    {tail : List ClauseBranch}
    (context :
      CursorCallContext cursor referenceDatabase.generation "p"
        [queryTerm] [])
    (remaining : cursor.remaining = secondPrepared :: tail)
    (wellFormed : cursor.WellFormed)
    (supported :
      SupportedPreparedCandidateAgrees cursor.callGeneration cursor.predicate
        cursor.arguments cursor.bindings secondPrepared clause)
    (arity : clause.params.length = 0) :
    resolutionClauseRetained [] queryAtom clause = false := by
  have query : NormalizedCallAgrees [] cursor [] queryAtom := by
    constructor
    rw [context.arguments_eq, context.bindings_eq]
    exact AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 0) .nil
  have head : NormalizedHeadAgrees secondPrepared [] queryAtom clause :=
    supportedPreparedCandidate_normalizedHeadAgrees query wellFormed
      (by rw [remaining]; simp) supported arity
  rcases clause with ⟨params, result, body⟩
  simp only at arity
  have paramsNil : params = [] := List.eq_nil_of_length_eq_zero arity
  subst params
  have equations := head.equations
  rw [secondNormalized] at equations
  cases equations with
  | cons left right tail =>
      cases left
      cases right
      cases tail
      rfl

private theorem selectedFrontierResolves :
    ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause},
      RejectedPullsN count
          (openedFor initialSession "p" [queryTerm] []).cursor finish →
        RepresentativeRetainedCallFrontier []
          (openedFor initialSession "p" [queryTerm] []) initialOpenConf
          pPending finish branch clause branchTail clauseTail altTail copied
          [] [] queryAtom [] [] queryAtom
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter →
        ∃ independentResult : Substitution,
          HeadResolution branch independentResult ∧
            AlphaRuntimeNamesLive [] copied.body queryAtom := by
  intro count finish branch clause branchTail clauseTail altTail copied
    pulls frontier
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [pOpenedRemaining] at shape
      have branchExact : branch = firstPrepared :=
        (List.cons.inj shape).1.symm
      subst branch
      have rejected :=
        firstPartnerRejected frontier.finishContext frontier.finishRemaining
          frontier.finishWellFormed frontier.supported (by
            simpa using frontier.arity)
      have retained :
          resolutionClauseRetained [] queryAtom clause = true := by
        simpa using frontier.retained
      rw [retained] at rejected
      contradiction
  | succ count cursor entered branches finish remaining clash tail =>
      rw [pOpenedRemaining] at remaining
      have enteredExact : entered = firstPrepared :=
        (List.cons.inj remaining).1.symm
      have branchesExact :
          branches = [secondPrepared, selectedPrepared, retainedPrepared] :=
        (List.cons.inj remaining).2.symm
      subst entered
      subst branches
      cases tail with
      | zero advanced =>
          have shape := frontier.finishRemaining
          simp [PreparedCursor.advance] at shape
          have branchExact : branch = secondPrepared :=
            shape.1.symm
          subst branch
          have rejected :=
            secondPartnerRejected frontier.finishContext
              frontier.finishRemaining frontier.finishWellFormed
              frontier.supported (by simpa using frontier.arity)
          have retained :
              resolutionClauseRetained [] queryAtom clause = true := by
            simpa using frontier.retained
          rw [retained] at rejected
          contradiction
      | succ tailCount cursor₂ entered₂ branches₂ finish₂ remaining₂ clash₂
          tail₂ =>
          simp [PreparedCursor.advance] at remaining₂
          have entered₂Exact : entered₂ = secondPrepared :=
            remaining₂.1.symm
          have branches₂Exact :
              branches₂ = [selectedPrepared, retainedPrepared] :=
            remaining₂.2.symm
          subst entered₂
          subst branches₂
          cases tail₂ with
          | zero advanced₂ =>
              have shape := frontier.finishRemaining
              simp [PreparedCursor.advance] at shape
              have branchExact : branch = selectedPrepared :=
                shape.1.symm
              subst branch
              refine ⟨[], selectedResolves, ?_⟩
              intro identity name member
              simp at member
          | succ remainingCount cursor₃ entered₃ branches₃ finish₃
              remaining₃ clash₃ tail₃ =>
              simp [PreparedCursor.advance] at remaining₃
              have entered₃Exact : entered₃ = selectedPrepared :=
                remaining₃.1.symm
              subst entered₃
              exact False.elim (clash₃ ⟨[], selectedResolves⟩)

private theorem selectedFrontierShape
    {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (pulls :
      RejectedPullsN count
        (openedFor initialSession "p" [queryTerm] []).cursor finish)
    (frontier :
      RepresentativeRetainedCallFrontier []
        (openedFor initialSession "p" [queryTerm] []) initialOpenConf
        pPending finish branch clause branchTail clauseTail altTail copied
        [] [] queryAtom [] [] queryAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter) :
    count = 2 ∧ branch = selectedPrepared ∧
      branchTail = [retainedPrepared] := by
  obtain ⟨result, resolved, _live⟩ :=
    selectedFrontierResolves pulls frontier
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [pOpenedRemaining] at shape
      have branchExact : branch = firstPrepared :=
        (List.cons.inj shape).1.symm
      subst branch
      exact False.elim (firstRejected ⟨result, resolved⟩)
  | succ count cursor entered branches finish remaining clash tail =>
      rw [pOpenedRemaining] at remaining
      have enteredExact : entered = firstPrepared :=
        (List.cons.inj remaining).1.symm
      have branchesExact :
          branches = [secondPrepared, selectedPrepared, retainedPrepared] :=
        (List.cons.inj remaining).2.symm
      subst entered
      subst branches
      cases tail with
      | zero advanced =>
          have shape := frontier.finishRemaining
          simp [PreparedCursor.advance] at shape
          have branchExact : branch = secondPrepared := shape.1.symm
          subst branch
          exact False.elim (secondRejected ⟨result, resolved⟩)
      | succ tailCount cursor₂ entered₂ branches₂ finish₂ remaining₂ clash₂
          tail₂ =>
          simp [PreparedCursor.advance] at remaining₂
          have entered₂Exact : entered₂ = secondPrepared :=
            remaining₂.1.symm
          have branches₂Exact :
              branches₂ = [selectedPrepared, retainedPrepared] :=
            remaining₂.2.symm
          subst entered₂
          subst branches₂
          cases tail₂ with
          | zero advanced₂ =>
              have shape := frontier.finishRemaining
              simp [PreparedCursor.advance] at shape
              exact ⟨rfl, shape.1.symm, shape.2.symm⟩
          | succ remainingCount cursor₃ entered₃ branches₃ finish₃
              remaining₃ clash₃ tail₃ =>
              simp [PreparedCursor.advance] at remaining₃
              have entered₃Exact : entered₃ = selectedPrepared :=
                remaining₃.1.symm
              subst entered₃
              exact False.elim (clash₃ ⟨[], selectedResolves⟩)

private def rootScope : CutScopeId := 0

/-- A literal root call crosses two real rigid-clash occurrences, activates
the first matching clause, and retains the duplicate matching sibling as a
live alternative.

The independent lane pays call-entry, two rejected pulls, and activation:
four exact transitions.  The fine executable lane prefilters the clashes and
pays entry, pull, and activation: three exact transitions.  Both paths end in
the same full session-related active carrier, whose retained-cursor ownership
is part of the returned activation certificate. -/
theorem two_rigid_rejections_then_selected_retained_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish representative nextAlpha sourceCanonical flattened installed
        after,
      RepresentativeRootCallSuccessorFacts prog gt [] [] [] []
        initialSession initialOpenConf rootScope "p" [queryTerm] []
        [] queryAtom [] pScan.1 pScan.2 0
        2 [firstPrepared, secondPrepared]
        [firstRejectedExecutable, secondRejectedExecutable]
        finish selectedPrepared selectedExecutable [retainedPrepared]
        [retainedExecutable] [retainedAlt] selectedCopied [] representative
        nextAlpha sourceCanonical flattened installed after ∧
      finish.remaining = [selectedPrepared, retainedPrepared] ∧
      after.carrier.index.bodyReferences = selectedReference.body ∧
      after.carrier.index.bodyExecutables = selectedCopied.body ∧
      StepsN 4
        (.running initialSession
          (.task rootScope [.call "p" [queryTerm]] []))
        [.opened (requestFor "p" [queryTerm] [])]
        after.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) after.carrier.fineState := by
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
           references := [.call "p" [queryTerm]]
           executables := [.call "p" [] queryAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have notThrow : ¬ BuiltinThrowCall "p" [queryTerm] := by
    simp [BuiltinThrowCall]
  have notDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [queryTerm] = none := by
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, independentResult,
        representative, nextAlpha, sourceCanonical, flattened, installed,
        after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      pEntry preHeadPayload rootPayloadSupported beforeSession (by rfl)
      (by rfl) initialBelow pScanNonempty selectedFrontierResolves notThrow
      notDatabase
  obtain ⟨rejectsExact, branchExact, branchTailExact⟩ :=
    selectedFrontierShape facts.pulls facts.frontier
  subst rejects
  subst branch
  subst branchTail
  have sourceShape := facts.sourceBank
  rw [pOpenedRemaining] at sourceShape
  have sourceAppend :
      [firstPrepared, secondPrepared] ++
          [selectedPrepared, retainedPrepared] =
        skippedBranches ++ [selectedPrepared, retainedPrepared] := by
    simpa using sourceShape
  have skippedBranchesExact :
      skippedBranches = [firstPrepared, secondPrepared] :=
    (List.append_cancel_right sourceAppend).symm
  subst skippedBranches
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "p" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [pResolutionCandidates] at executableShape
  have skippedClausesLength : skippedClauses.length = 2 := by
    simpa using facts.executableSkipCount
  have prefixShape := congrArg (List.take 2) executableShape
  have skippedClausesExact :
      skippedClauses = [firstRejectedExecutable, secondRejectedExecutable] := by
    simpa [skippedClausesLength] using prefixShape.symm
  subst skippedClauses
  have executableAppend :
      [firstRejectedExecutable, secondRejectedExecutable] ++
          [selectedExecutable, retainedExecutable] =
        [firstRejectedExecutable, secondRejectedExecutable] ++
          (clause :: clauseTail) := by
    simpa using executableShape
  have executableTail := List.append_cancel_left executableAppend
  have clauseExact : clause = selectedExecutable :=
    (List.cons.inj executableTail).1.symm
  have clauseTailExact : clauseTail = [retainedExecutable] :=
    (List.cons.inj executableTail).2.symm
  subst clause
  subst clauseTail
  have copiedExact : copied = selectedCopied := by
    rw [facts.frontier.copiedExact]
    rfl
  subst copied
  have tailScan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [retainedExecutable] 1 altTail 2 := by
    simpa [pPending, pScanExact, initialOpenConf, OpenConf.toConf,
      Control.toConf, barrierDepth] using facts.frontier.tailScan
  have expectedTailScan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [retainedExecutable] 1 [retainedAlt] 2 :=
    .retained retainedExecutable [] 1 2 []
      (by
        simp [resolutionClauseRetained, queryAtom, retainedExecutable,
          PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
          PLeaTTa.prologMatchCompatList])
      (.nil 2)
  have altTailExact : altTail = [retainedAlt] :=
    (tailScan.deterministic expectedTailScan).1
  subst altTail
  have selectedResolution : HeadResolution selectedPrepared independentResult := by
    rw [← facts.carrierCurrent]
    exact facts.resolution
  have independentResultExact : independentResult = [] :=
    HeadResolution.deterministic selectedResolution selectedResolves
  subst independentResult
  refine
    ⟨finish, representative, nextAlpha, sourceCanonical, flattened, installed,
      after, ?_, facts.frontier.finishRemaining, facts.bodyReferences,
      facts.bodyExecutables, ?_, facts.fineSteps⟩
  · simpa [pPending, DemandDrivenCallStep.pendingCallOf] using facts
  · simpa using facts.sourceSteps

end PLeaTTa.PrologRootRejectedPrefixRegression
