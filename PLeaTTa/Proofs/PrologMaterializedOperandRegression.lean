-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMaterializedOperandRegression
Purpose: Prove that fresh live operands can be interpreted without widening
  an immutable caller observation support.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootRejectedPrefixRegression

namespace PLeaTTa.PrologMaterializedOperandRegression

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologMguOpenAgreement
open PrologOrdinaryStepBridge
open PrologPrefilterBridge

/-- A fresh clause-local variable and a ground operand have exact
post-substitution readings even though the variable is deliberately absent
from the caller's empty observation support.  This separates materialized
execution availability from public payload observability. -/
theorem fresh_materialized_operands_need_no_payload_support :
    let identity : LogicVar := .generated 0
    let alpha : List (LogicVar × String) := [(identity, "_q0")]
    MaterializedOperandsAgreeWith alpha [] [] []
        [.variable identity, .integer 9]
        [.var "_q0", .gnd (.int 9)] ∧
      ¬ AlphaTreeSupported alpha [] (Term.denote (.variable identity)) := by
  dsimp
  constructor
  · refine ⟨.cons ?_ (.cons ?_ .nil)⟩
    · simpa [Substitution.denote, TreeSubstitution.apply, Term.denote,
          PLeaTTa.subst_nil] using
        (CanonicalRuntimeAgrees.variable
          (alpha := [((.generated 0 : LogicVar), "_q0")]) (by simp))
    · simpa [Substitution.denote, TreeSubstitution.apply, Term.denote,
          PLeaTTa.subst_nil] using
        (CanonicalRuntimeAgrees.integer
          (alpha := [((.generated 0 : LogicVar), "_q0")]) 9)
  · simp [AlphaTreeSupported, TreeVariablesSatisfy, Term.denote]

end PLeaTTa.PrologMaterializedOperandRegression

namespace PLeaTTa.PrologMaterializedOperandRegression.VariableCutCommit

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open OpenBindingAgreement
open PrologActivationMacro
open PrologAlphaFreshFrontierBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologPersistentFreeCommittedUnifyTransitionBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologRepresentativeCallFrontierBridge
open PrologRecursiveCallPayloadBridge
open PrologRootCallReadyBridge
open PrologScheduledSuccessPrefixBridge
open PrologStateBridge

/-! ## A non-ground cut clause whose equality operand is clause-local -/

def queryIdentity : LogicVar := .source "z"

def clauseIdentity : LogicVar := .source "x"

def queryTerm : Term := .variable queryIdentity

def clauseTerm : Term := .variable clauseIdentity

def valueTerm : Term := .integer 9

def queryAtom : Atom := .var "z"

def clauseAtom : Atom := .var "x"

def valueAtom : Atom := .gnd (.int 9)

def selectedReference : LocalClause :=
  { predicate := "cutv"
    arguments := [clauseTerm]
    body := [.cut, .conjunction [], .unify clauseTerm valueTerm] }

def retainedReference : LocalClause :=
  { predicate := "cutv"
    arguments := [clauseTerm]
    body := [] }

def selectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := clauseAtom
    body := [.cut, .eq clauseAtom valueAtom] }

def retainedExecutable : PLeaTTa.Clause :=
  { params := []
    result := clauseAtom
    body := [] }

def selectedVersion : VersionedClause :=
  Database.empty.allocate selectedReference

def retainedVersion : VersionedClause :=
  (Database.empty.assertz selectedReference).allocate retainedReference

def referenceDatabase : Database :=
  (Database.empty.assertz selectedReference).assertz retainedReference

def executableWorld : PWorld :=
  (((default : PWorld).reindexClauses.appendProgClause
    ("cutv", selectedExecutable)).appendProgClause
    ("cutv", retainedExecutable))

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
      (CanonicalRuntimeAgrees.variable
        (alpha := rootAlpha) (by simp [rootAlpha, queryIdentity]))

private theorem rootTaskData :
    TaskDataAgrees rootAlpha rootAlpha [] [] [] [] :=
  ⟨rootShared, TreeSubstitution.wellFormed_nil, rfl, rootValuation⟩

private theorem rootControl (barrier : Nat) :
    NormalizedAlphaGoalsAgree rootAlpha barrier
      [.call "cutv" [queryTerm]] [.call "cutv" [] queryAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.variable (by simp [rootAlpha, queryIdentity])))
      .nil

private theorem rootPayload (barrier : Nat) :
    TaskPayloadAgrees rootAlpha rootAlpha barrier [] [] [] []
      [.call "cutv" [queryTerm]] [.call "cutv" [] queryAtom] :=
  rootTaskData.withControl (rootControl barrier)

private theorem rootPayloadSupported :
    AlphaTermsSupported rootAlpha rootAlpha [queryTerm] := by
  intro term member
  simp only [List.mem_singleton] at member
  subst term
  intro name linked
  exact linked

private def selectedBodyAgreement :
    CompilerAdequacy.GoalsAgree selectedReference.body selectedExecutable.body :=
  .cons .cut
    (.conjunction .nil
      (.cons
        (.unify (CompilerAdequacy.TermAgrees.sourceVariable "x")
          (CompilerAdequacy.TermAgrees.integer 9))
        .nil))

private theorem selectedClauseAgrees :
    LocalClauseAgrees selectedReference ("cutv", selectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := selectedBodyAgreement
      support := ?_ }
  · exact
      ⟨[], clauseTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · intro name
    simp [selectedReference, selectedExecutable, clauseTerm, clauseAtom,
      valueTerm, valueAtom, clauseIdentity, LocalClause.variables,
      resolutionClauseVars, Metta.Atom.vars, specializationGoalsVars,
      specializationGoalVars, termsVariables, termVariables, goalsVariables,
      goalVariables, OpenBindingAgreement.logicVarExecutableName]

private theorem retainedClauseAgrees :
    LocalClauseAgrees retainedReference ("cutv", retainedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], clauseTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · intro name
    simp [retainedReference, retainedExecutable, clauseTerm, clauseAtom,
      clauseIdentity, LocalClause.variables, resolutionClauseVars,
      Metta.Atom.vars, specializationGoalsVars,
      termsVariables, termVariables, goalsVariables,
      OpenBindingAgreement.logicVarExecutableName]

private theorem emptyDatabaseRelatesIndexedWorld :
    DatabaseRelatesWorld Database.empty ((default : PWorld).reindexClauses) := by
  refine
    { reachable := DatabaseActions.DatabaseReachable.empty
      liveClauses := ?_
      clauseIndex := PWorld.reindexClauses_coherent _ }
  exact .nil

theorem referenceDatabase_relates_executableWorld :
    DatabaseRelatesWorld referenceDatabase executableWorld := by
  have selected := emptyDatabaseRelatesIndexedWorld.assertz selectedClauseAgrees
  have retained := selected.assertz retainedClauseAgrees
  simpa [referenceDatabase, executableWorld] using retained

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have selected :=
    PWorld.appendProgClause_coherent _ ("cutv", selectedExecutable) root
  have retained :=
    PWorld.appendProgClause_coherent _ ("cutv", retainedExecutable) selected
  simpa [executableWorld] using retained

private theorem resolutionCandidates :
    executableWorld.resolutionCandidates "cutv" 0 =
      [selectedExecutable, retainedExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, selectedExecutable, retainedExecutable, emptyClauses]

private theorem visibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "cutv" 1 =
      [selectedVersion, retainedVersion] := by
  rfl

private theorem selectedBodySupported :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
      selectedVersion.clause.variables selectedVersion.clause.variables
      selectedBodyAgreement := by
  change
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
      [clauseIdentity] [clauseIdentity] selectedBodyAgreement
  let unifyAgreement :
      CompilerAdequacy.GoalAgrees
        (.unify clauseTerm valueTerm) (.eq clauseAtom valueAtom) :=
    .unify (CompilerAdequacy.TermAgrees.sourceVariable "x")
      (CompilerAdequacy.TermAgrees.integer 9)
  have unifySupported :
      CompilerGoalSubstitutionAdequacy.GoalAgreesSupported
        [clauseIdentity] [clauseIdentity] unifyAgreement :=
    @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.unify
      [clauseIdentity] [clauseIdentity] clauseTerm valueTerm clauseAtom valueAtom
      (CompilerAdequacy.TermAgrees.sourceVariable "x")
      (CompilerAdequacy.TermAgrees.integer 9)
      (by simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
        CompilerSubstitutionAdequacy.termVariablesIn, clauseTerm,
        clauseIdentity])
      (by simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
        CompilerSubstitutionAdequacy.termVariablesIn, valueTerm])
  have bodyEq : selectedBodyAgreement =
      (CompilerAdequacy.GoalsAgree.cons CompilerAdequacy.GoalAgrees.cut
        (CompilerAdequacy.GoalsAgree.conjunction
          CompilerAdequacy.GoalsAgree.nil
          (CompilerAdequacy.GoalsAgree.cons unifyAgreement
            CompilerAdequacy.GoalsAgree.nil))) := Subsingleton.elim _ _
  rw [bodyEq]
  exact .cons .cut (.conjunction .nil (.cons unifySupported .nil))

private theorem candidateBank :
    SupportedCandidateBank "cutv"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation
        "cutv" 1)
      (executableWorld.resolutionCandidates "cutv" 0) := by
  rw [visibleClauses, resolutionCandidates]
  let selectedHead : CandidateClauseAgrees "cutv" selectedVersion
      selectedExecutable := by
    change LocalClauseAgrees selectedReference ("cutv", selectedExecutable)
    exact selectedClauseAgrees
  let retainedHead : CandidateClauseAgrees "cutv" retainedVersion
      retainedExecutable := by
    change LocalClauseAgrees retainedReference ("cutv", retainedExecutable)
    exact retainedClauseAgrees
  have selectedEncoding :
      EncodingInjectiveOn selectedVersion.clause.variables := by
    simp [EncodingInjectiveOn, selectedVersion, Database.allocate,
      selectedReference, clauseTerm, valueTerm, clauseIdentity, LocalClause.variables,
      termsVariables, termVariables, goalsVariables, goalVariables]
  have retainedEncoding :
      EncodingInjectiveOn retainedVersion.clause.variables := by
    simp [EncodingInjectiveOn, retainedVersion, Database.allocate,
      retainedReference, clauseTerm, clauseIdentity, LocalClause.variables,
      termsVariables, termVariables, goalsVariables]
  have retainedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        retainedVersion.clause.variables retainedVersion.clause.variables
        retainedHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
      [clauseIdentity] [clauseIdentity] retainedHead.body
    have bodyEq : retainedHead.body =
        (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  have selectedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        selectedVersion.clause.variables selectedVersion.clause.variables
        selectedHead.body := by
    have bodyEq : selectedHead.body = selectedBodyAgreement :=
      Subsingleton.elim _ _
    rw [bodyEq]
    simpa [selectedVersion, Database.allocate] using selectedBodySupported
  refine ⟨List.Forall₂.cons selectedHead
    (List.Forall₂.cons retainedHead .nil), ?_⟩
  exact
    .cons (head := selectedHead) selectedEncoding selectedBody
      (.cons (head := retainedHead) retainedEncoding retainedBody .nil)

/-! ## Exact root entry and occurrence selection -/

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "cutv" [] queryAtom], [])
        alts := []
        qterm := queryAtom } }

private def scan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "cutv" 0)
    [] [] queryAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf scan.1 scan.2

private theorem entry :
    RepresentativeSupportedCallEntryRelates rootAlpha
      (openedFor initialSession "cutv" [queryTerm] []) initialOpenConf pending
      [] [] queryAtom [] [] queryAtom
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
          (initialOpenConf.persistent.world.resolutionCandidates "cutv" 0)
          [] [] queryAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = scan := rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (rootPayload (barrierDepth initialOpenConf.toConf + 1))
      rootPayloadSupported
      (openedFor initialSession "cutv" [queryTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "cutv" [queryTerm] [] rootAlpha [] queryAtom [] []
      scan.1 scan.2 (by rfl) (by rfl)
      (by
        calc
          _ = scan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (scan.1, scan.2) := (Prod.eta scan).symm) query candidateBank
  simpa [pending, initialOpenConf] using constructed

private theorem initialBelow :
    ConfBelowResolutionCounter initialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, initialOpenConf, OpenConf.toConf, Control.toConf,
    specializationGoalsVars, specializationGoalVars, resolutionSubstVars,
    queryAtom, Metta.Atom.vars] at member
  subst name
  simp [resolutionSeedHighWaterName, terminalResolutionSeed?,
    terminalResolutionSeedRev, initialOpenConf, OpenConf.toConf, Control.toConf]

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

theorem selectedCopied_body_exact :
    selectedCopied.body =
      [.cutAt 1, .eq selectedCopied.result valueAtom] := by
  simp [selectedCopied, selectedExecutable, valueAtom,
    PLeaTTa.freshenResolutionClause, PLeaTTa.renameGoalSuffix,
    PLeaTTa.renameAtomSuffix]

theorem retainedAlt_is_branch :
    ∃ goals binding, retainedAlt = .br goals binding := by
  exact ⟨_, _, rfl⟩

private theorem scanExact : scan = ([selectedAlt, retainedAlt], 2) := by
  unfold scan
  change
    resolveAlts (executableWorld.resolutionCandidates "cutv" 0)
        [] [] queryAtom [] [] queryAtom 1 0 =
      ([selectedAlt, retainedAlt], 2)
  rw [resolutionCandidates, resolveAlts_eq_scanResolution]
  have exactScan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [selectedExecutable, retainedExecutable] 0
        [selectedAlt, retainedAlt] 2 :=
    .retained selectedExecutable [retainedExecutable] 0 2 _
      (by
        simp [resolutionClauseRetained, queryAtom, selectedExecutable,
          PLeaTTa.prologMatchCompat,
          PLeaTTa.prologMatchCompatList])
      (.retained retainedExecutable [] 1 2 []
        (by
          simp [resolutionClauseRetained, queryAtom, retainedExecutable,
            PLeaTTa.prologMatchCompat,
            PLeaTTa.prologMatchCompatList])
        (.nil 2))
  simpa [selectedAlt, retainedAlt] using exactScan.result_eq

private theorem scanNonempty : pending.branches ≠ [] := by
  rw [pending, scanExact]
  exact List.cons_ne_nil _ _

private def selectedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 0
    selectedVersion

private def retainedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation [queryTerm] [] 1
    retainedVersion

private theorem openedRemaining :
    (openedFor initialSession "cutv" [queryTerm] []).cursor.remaining =
      [selectedPrepared, retainedPrepared] := by
  rfl

private theorem selectedNormalized :
    selectedPrepared.normalizedHeadEquations =
      [(queryTerm, .variable (.generated 0))] := by
  rfl

def selectedSourceExtension : Substitution :=
  TreeSubstitution.reify
    [(queryIdentity, .variable (.generated 0))]

private theorem selectedResolves :
    HeadResolution selectedPrepared selectedSourceExtension := by
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
  · simpa [selectedNormalized, extension, queryTerm] using computed
  · simp [selectedSourceExtension, extension, selectedPrepared,
      selectedVersion, Database.allocate, preparedBranchOf]

private theorem selectedFrontierResolves :
    ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause},
      RejectedPullsN count
          (openedFor initialSession "cutv" [queryTerm] []).cursor finish →
        RepresentativeRetainedCallFrontier rootAlpha
          (openedFor initialSession "cutv" [queryTerm] []) initialOpenConf
          pending finish branch clause branchTail clauseTail altTail copied
          [] [] queryAtom [] [] queryAtom
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter →
        ∃ independentResult : Substitution,
          HeadResolution branch independentResult ∧
            AlphaRuntimeNamesLive rootAlpha copied.body queryAtom := by
  intro count finish branch clause branchTail clauseTail altTail copied
    pulls frontier
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [openedRemaining] at shape
      have branchExact : branch = selectedPrepared :=
        (List.cons.inj shape).1.symm
      subst branch
      refine ⟨selectedSourceExtension, selectedResolves, ?_⟩
      intro identity name member
      simp only [rootAlpha, List.mem_singleton] at member
      have nameExact : name = "z" := congrArg Prod.snd member
      subst name
      exact PLeaTTa.isTrimRoot_qterm_mem copied.body queryAtom "z"
        (by simp [queryAtom, Metta.Atom.vars])
  | succ count cursor entered branches finish remaining clash tail =>
      rw [openedRemaining] at remaining
      have enteredExact : entered = selectedPrepared :=
        (List.cons.inj remaining).1.symm
      subst entered
      exact False.elim (clash ⟨selectedSourceExtension, selectedResolves⟩)

private theorem selectedFrontierShape
    {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (pulls :
      RejectedPullsN count
        (openedFor initialSession "cutv" [queryTerm] []).cursor finish)
    (frontier :
      RepresentativeRetainedCallFrontier rootAlpha
        (openedFor initialSession "cutv" [queryTerm] []) initialOpenConf
        pending finish branch clause branchTail clauseTail altTail copied
        [] [] queryAtom [] [] queryAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter) :
    count = 0 ∧ branch = selectedPrepared ∧
      branchTail = [retainedPrepared] := by
  obtain ⟨result, resolved, _live⟩ :=
    selectedFrontierResolves pulls frontier
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [openedRemaining] at shape
      exact ⟨rfl, (List.cons.inj shape).1.symm,
        (List.cons.inj shape).2.symm⟩
  | succ count cursor entered branches finish remaining clash tail =>
      rw [openedRemaining] at remaining
      have enteredExact : entered = selectedPrepared :=
        (List.cons.inj remaining).1.symm
      subst entered
      exact False.elim (clash ⟨selectedSourceExtension, selectedResolves⟩)

private def rootScope : CutScopeId := 0

/-- A literal non-ground root call selects the first clause occurrence while
retaining the second.  The returned activation package contains the
whole-body materialization certificate; no caller supplies an operand
support proof. -/
theorem root_variable_cut_selected_retained_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish representative nextAlpha sourceCanonical flattened installed
        after,
      RepresentativeRootCallSuccessorFacts prog gt rootAlpha rootAlpha [] []
        initialSession initialOpenConf rootScope "cutv" [queryTerm] []
        [] queryAtom [] scan.1 scan.2 0
        0 [] [] finish selectedPrepared selectedExecutable
        [retainedPrepared] [retainedExecutable] [retainedAlt] selectedCopied
        selectedSourceExtension representative nextAlpha sourceCanonical
        flattened installed after ∧
      finish.remaining = [selectedPrepared, retainedPrepared] ∧
      after.carrier.index.bodyReferences = selectedPrepared.body ∧
      after.carrier.index.bodyExecutables = selectedCopied.body ∧
      after.carrier.index.support = rootAlpha ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [.opened (requestFor "cutv" [queryTerm] [])]
        after.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) after.carrier.fineState := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier rootAlpha)
        ExactControlFrontiers initialSession initialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [initialSession, initialOpenConf] using
        referenceDatabase_relates_executableWorld
    · simp [AlphaFreshFrontier, GeneratedBelow, rootAlpha, queryIdentity,
        resolutionSeedHighWaterNames, resolutionSeedHighWaterName,
        terminalResolutionSeed?, terminalResolutionSeedRev,
        initialSession, initialOpenConf]
  have preHeadPayload :
      TaskSpinePayloadAgrees rootAlpha rootAlpha [] [] [] []
        [{ barrier := 0
           references := [.call "cutv" [queryTerm]]
           executables := [.call "cutv" [] queryAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have notThrow : ¬ BuiltinThrowCall "cutv" [queryTerm] := by
    simp [BuiltinThrowCall]
  have notDatabase :
      DatabaseActions.recognizeDatabaseAction "cutv" [queryTerm] = none := rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, independentResult,
        representative, nextAlpha, sourceCanonical, flattened, installed,
        after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      entry preHeadPayload rootPayloadSupported beforeSession (by rfl)
      (by rfl) initialBelow scanNonempty selectedFrontierResolves notThrow
      notDatabase
  obtain ⟨rejectsExact, branchExact, branchTailExact⟩ :=
    selectedFrontierShape facts.pulls facts.frontier
  subst rejects
  subst branch
  subst branchTail
  have skippedBranchesNil : skippedBranches = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using facts.sourceSkipCount
  subst skippedBranches
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using facts.executableSkipCount
  subst skippedClauses
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "cutv" 0 =
      clause :: clauseTail at executableShape
  rw [resolutionCandidates] at executableShape
  have clauseExact : clause = selectedExecutable :=
    (List.cons.inj executableShape).1.symm
  have clauseTailExact : clauseTail = [retainedExecutable] :=
    (List.cons.inj executableShape).2.symm
  subst clause
  subst clauseTail
  have copiedExact : copied = selectedCopied := by
    rw [facts.frontier.copiedExact]
    rfl
  subst copied
  have tailScan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [retainedExecutable] 1 altTail 2 := by
    simpa [pending, scanExact, initialOpenConf, OpenConf.toConf,
      Control.toConf, barrierDepth, Metta.Subst.apply, Metta.Subst.lookup] using
      facts.frontier.tailScan
  have expectedTailScan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [retainedExecutable] 1 [retainedAlt] 2 :=
    .retained retainedExecutable [] 1 2 []
      (by
        simp [resolutionClauseRetained, queryAtom, retainedExecutable,
          PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList])
      (.nil 2)
  have altTailExact : altTail = [retainedAlt] :=
    (tailScan.deterministic expectedTailScan).1
  subst altTail
  have selectedResolution :
      HeadResolution selectedPrepared independentResult := by
    rw [← facts.carrierCurrent]
    exact facts.resolution
  have independentResultExact :
      independentResult = selectedSourceExtension :=
    HeadResolution.deterministic selectedResolution selectedResolves
  subst independentResult
  refine
    ⟨finish, representative, nextAlpha, sourceCanonical, flattened, installed,
      after, ?_, facts.frontier.finishRemaining, facts.bodyReferences,
      facts.bodyExecutables, facts.supportPreserved, ?_, facts.fineSteps⟩
  · simpa [pending, DemandDrivenCallStep.pendingCallOf] using facts
  · simpa using facts.sourceSteps

theorem selectedPrepared_body_exact :
    selectedPrepared.body =
      [.cut, .conjunction [],
        .unify (.variable (.generated 0)) valueTerm] := by
  rfl

/-- The source-only conjunction wrapper following the cut is one genuine
administrative step. -/
def afterCutAdministrative :
    AdministrativeStepsN 1
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm]
      [.unify (.variable (.generated 0)) valueTerm] :=
  .succ 0 _ _ _
    (.conjunction [] [.unify (.variable (.generated 0)) valueTerm])
    (.zero [.unify (.variable (.generated 0)) valueTerm])

/-- Exact non-ground execution through root activation, cut, and the
compiler-erased conjunction wrapper.  The retained occurrence is visibly
pruned, while the committed carrier keeps the whole-body materialization
needed by the following equality. -/
theorem root_variable_cut_then_committed_unify_ready
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (active : MaterializedRepresentativePersistentFreeActivePayloadState)
        (before : MaterializedRepresentativePersistentFreeCommittedPayloadState),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] ∧
      before.carrier.carrier.index.support = rootAlpha ∧
      before.carrier.carrier.index.current = selectedSourceExtension ∧
      before.carrier.carrier.index.openConf.control.qterm = queryAtom ∧
      ¬ AlphaTreeSupported before.carrier.carrier.index.alpha
          before.carrier.carrier.index.support
          (Term.denote (.variable (.generated 0))) ∧
      StepsN 4
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [ .opened (requestFor "cutv" [queryTerm] []),
          .pruned
            (PrologActivatedProductStepBridge.retainedCursorTokenAt
              active.carrier.carrier.index.predicateScope
              active.carrier.carrier.index.finish
              active.carrier.carrier.index.branch
              active.carrier.carrier.index.branchTail) ]
        before.carrier.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 4
        (.ready initialOpenConf) before.carrier.carrier.fineState := by
  obtain
      ⟨finish, representative, nextAlpha, sourceCanonical, flattened,
        installed, legacy, facts, finishRemaining, bodyReferences,
        bodyExecutables, supportPreserved, rootSource, rootFine⟩ :=
    root_variable_cut_selected_retained_exact (prog := prog) (gt := gt)
  let active := facts.toMaterializedPersistentFreeActive
  have referenceHead :
      active.carrier.carrier.index.bodyReferences =
        [.cut, .conjunction [],
          .unify (.variable (.generated 0)) valueTerm] := by
    change legacy.carrier.index.bodyReferences =
      [.cut, .conjunction [],
        .unify (.variable (.generated 0)) valueTerm]
    calc
      legacy.carrier.index.bodyReferences = selectedPrepared.body :=
        bodyReferences
      _ = _ := selectedPrepared_body_exact
  have executableKnown :
      active.carrier.carrier.index.bodyExecutables =
        [.cutAt 1, .eq selectedCopied.result valueAtom] := by
    change legacy.carrier.index.bodyExecutables =
      [.cutAt 1, .eq selectedCopied.result valueAtom]
    calc
      legacy.carrier.index.bodyExecutables = selectedCopied.body :=
        bodyExecutables
      _ = _ := selectedCopied_body_exact
  have activeReady := active.carrier.carrier.agreement.ready
  rw [referenceHead] at activeReady
  rcases activeReady with
    ⟨_persistent, _currentControl, _queryTerm, activePayload⟩
  have bodyPayload := activePayload.headPayload
  rcases bodyPayload.control.cutHead with
    ⟨executableTail, executableShape, _tailControl⟩
  rw [executableKnown] at executableShape
  have barrierExact : active.carrier.carrier.index.bodyBarrier = 1 := by
    have headExact := (List.cons.inj executableShape).1
    have same : 1 = active.carrier.carrier.index.bodyBarrier := by
      injection headExact
    exact same.symm
  have executableHead :
      active.carrier.carrier.index.bodyExecutables =
        [.cutAt active.carrier.carrier.index.bodyBarrier,
          .eq selectedCopied.result valueAtom] := by
    simpa [barrierExact] using executableKnown
  have activeAlts :
      active.carrier.carrier.index.active.alts = [retainedAlt] := by
    change legacy.carrier.index.active.alts = [retainedAlt]
    exact facts.activeAltsExact
  have database :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using
      referenceDatabase_relates_executableWorld
  have sourceNonempty :
      initialSession.resolver.database.visibleClausesAt
        initialSession.resolver.database.generation "cutv" 1 ≠ [] := by
    simp [initialSession, visibleClauses]
  have scanned :
      resolveAlts
          (initialOpenConf.toConf.world.resolutionCandidates "cutv" 0)
          [] [] queryAtom [] [] initialOpenConf.toConf.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter =
        (scan.1, scan.2) := by
    change scan = (scan.1, scan.2)
    exact (Prod.eta scan).symm
  obtain ⟨_sourceEntry, fineEntry, _entryAgain⟩ :=
    taskCall_callEnter_bank_correspondence
      (prog := prog) (gt := gt) (session := initialSession)
      (state := initialOpenConf) database entry.indexReady rootScope "cutv"
      [queryTerm] [] [] [] queryAtom [] [] scan.1 scan.2 entry.entry.arity
      (by simp [BuiltinThrowCall])
      (by simp [DatabaseActions.recognizeDatabaseAction]) sourceNonempty
      entry.entry.callHead scanned
  have sealedEntry :
      PLeaTTa.Step prog gt initialOpenConf.toConf pending.pulled.toConf := by
    simpa [pending] using
      (PrologNestedCallReadyBridge.DemandDrivenCallStep.Step.ready_callPending_projects_to_sealed
        fineEntry)
  have initialCoherent :
      PLeaTTa.BarrierCacheCoherent initialOpenConf.toConf := by
    simp [initialOpenConf, OpenConf.toConf, Control.toConf,
      PLeaTTa.BarrierCacheCoherent]
  have pulledCoherent :
      PLeaTTa.BarrierCacheCoherent pending.pulled.toConf :=
    sealedEntry.preserves_barrierCacheCoherent initialCoherent
  have activatedCoherent :
      PLeaTTa.BarrierCacheCoherent
        (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pending selectedCopied [] initialOpenConf.control.qterm installed) :=
    facts.activation.executableStep.preserves_barrierCacheCoherent
      pulledCoherent
  have activeOpenExact :
      active.carrier.carrier.index.openConf =
        PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          pending selectedCopied [] initialOpenConf.control.qterm installed := by
    have wrapped :
        active.carrier.carrier.fineState =
          DemandDrivenCallStep.FineConf.ready
            (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
              pending selectedCopied [] initialOpenConf.control.qterm
                installed) := by
      have exported :
          active.carrier.carrier.fineState = legacy.carrier.fineState := by
        change facts.toPersistentFreeActive.carrier.fineState =
          legacy.carrier.fineState
        exact facts.toPersistentFreeActive_fineState
      exact exported.trans facts.fineStateExact
    change
      DemandDrivenCallStep.FineConf.ready active.carrier.carrier.index.openConf =
        DemandDrivenCallStep.FineConf.ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending selectedCopied [] initialOpenConf.control.qterm installed)
        at wrapped
    injection wrapped
  have coherent :
      PLeaTTa.BarrierCacheCoherent
        active.carrier.carrier.index.openConf.toConf := by
    rw [activeOpenExact]
    simpa only [
      PrologRepresentativeStepActivationBridge.activatedOpenSuccessor_toConf]
      using activatedCoherent
  let committed :=
    RepresentativePersistentFreeActivePayloadState.afterCutMaterialized
      prog gt active
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm]
      [.eq selectedCopied.result valueAtom] referenceHead executableHead coherent
  let before :=
    committed.afterAdministrative afterCutAdministrative
  have localPrefix :=
    PrologScheduledSuccessPrefixBridge.GlobalCertifiedPrefix.activeCutThenCommittedAdministrative
      (prog := prog) (gt := gt) active.carrier
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm]
      [.eq selectedCopied.result valueAtom] referenceHead executableHead coherent
      (by omega) afterCutAdministrative
  have sourceAll := rootSource.trans localPrefix.sourceSteps
  have fineAll := rootFine.trans localPrefix.fineSteps
  have beforeReference :
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] := by
    simp [before, committed,
      MaterializedRepresentativePersistentFreeCommittedPayloadState.afterAdministrative,
      RepresentativePersistentFreeCommittedPayloadState.afterAdministrative]
  have beforeSupport :
      before.carrier.carrier.index.support = rootAlpha := by
    change active.carrier.carrier.index.support = rootAlpha
    change legacy.carrier.index.support = rootAlpha
    exact supportPreserved
  have beforeCurrent :
      before.carrier.carrier.index.current = selectedSourceExtension := by
    change active.carrier.carrier.index.current = selectedSourceExtension
    change legacy.carrier.index.current = selectedSourceExtension
    exact facts.carrierCurrent
  have beforeQterm :
      before.carrier.carrier.index.openConf.control.qterm = queryAtom := by
    change active.carrier.carrier.index.openConf.control.qterm = queryAtom
    exact _queryTerm.trans (by
      change legacy.carrier.index.qterm = queryAtom
      simpa [initialOpenConf] using facts.qtermPreserved)
  have unsupported :
      ¬ AlphaTreeSupported before.carrier.carrier.index.alpha
          before.carrier.carrier.index.support
          (Term.denote (.variable (.generated 0))) := by
    have current := before.materializedUnifyGoals
    rw [beforeReference] at current
    obtain
      ⟨spelling, executableLeft, executableRight, executableTail,
        executableShape, leftAgreement, _rightAgreement, _tail, _operands⟩ :=
      current.unifyHeadReady
    obtain ⟨name, _runtimeShape, linked⟩ :=
      PLeaTTa.PrologMguTopology.AlphaTermAgrees.source_variable_linked
        leftAgreement
    intro supported
    have observed := supported
    simp only [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy] at observed
    have old := observed name linked
    rw [beforeSupport] at old
    simp [rootAlpha, queryIdentity] at old
  refine ⟨active, before, activeAlts, beforeReference, beforeSupport,
    beforeCurrent, beforeQterm, unsupported, ?_, ?_⟩
  · simpa [active, committed, before,
      RepresentativePersistentFreeActivePayloadState.afterCutMaterialized,
      MaterializedRepresentativePersistentFreeCommittedPayloadState.afterAdministrative,
      GlobalTransitionSchedule.sourceCost,
      GlobalTransitionSchedule.sourceEvents,
      PrologScheduledSuccessPrefixBridge.GlobalTransitionKind.sourceCost,
      PrologScheduledSuccessPrefixBridge.GlobalTransitionKind.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverTransitionKind.sourceCost,
      PrologFailureRebasePrefixBridge.ResolverTransitionKind.sourceEvents,
      PrologHeterogeneousPrefixBridge.TransitionKind.sourceCost,
      PrologHeterogeneousPrefixBridge.TransitionKind.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using sourceAll
  · simpa [active, committed, before,
      RepresentativePersistentFreeActivePayloadState.afterCutMaterialized,
      MaterializedRepresentativePersistentFreeCommittedPayloadState.afterAdministrative,
      GlobalTransitionSchedule.fineCost,
      PrologScheduledSuccessPrefixBridge.GlobalTransitionKind.fineCost,
      PrologFailureRebasePrefixBridge.ResolverTransitionKind.fineCost,
      PrologHeterogeneousPrefixBridge.TransitionKind.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using fineAll

def finalSourceResult : Substitution :=
  TreeSubstitution.reify
      [((.generated 0 : LogicVar), Term.denote valueTerm)] ++
    selectedSourceExtension

theorem selectedBodyResolves :
    UnifyResolution selectedSourceExtension
      (.variable (.generated 0)) valueTerm finalSourceResult := by
  let extension : TreeSubstitution :=
    [((.generated 0 : LogicVar), Term.denote valueTerm)]
  have computed :
      ComputesDenotationalMgu
        [(.variable (.generated 0), valueTerm)]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_left_variable (.generated 0)
      valueTerm (by
        intro equality
        cases equality) (by rfl)
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · have leftUnchanged :
        selectedSourceExtension.applyTerm (.variable (.generated 0)) =
          .variable (.generated 0) := by
      simp [selectedSourceExtension, queryIdentity, TreeSubstitution.reify,
        Tree.reify, Term.instantiateOne]
    rw [leftUnchanged]
    simpa [selectedSourceExtension, extension, valueTerm] using computed
  · rfl

theorem finalSourceResult_answers_query :
    finalSourceResult.applyTerm queryTerm = valueTerm := by
  simp [finalSourceResult, selectedSourceExtension, queryTerm, queryIdentity,
    valueTerm, Substitution.applyTerm, TreeSubstitution.reify, Tree.reify,
    Term.denote, Term.instantiateOne]

/-- End-to-end discriminator for the materialized-operand repair.

The selected clause introduces a fresh local variable, commits past a retained
matching sibling, crosses a compiler-erased conjunction, and then unifies that
fresh variable with `9`.  The variable is proved absent from immutable caller
support at the equality state, so the legacy support-derived producer cannot
justify this transition.  The whole-body activation certificate does justify
it, and the original public query variable becomes exactly `9`. -/
theorem root_variable_cut_then_materialized_unify_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (active : MaterializedRepresentativePersistentFreeActivePayloadState)
        (before : MaterializedRepresentativePersistentFreeCommittedPayloadState)
        (after : RepresentativePersistentFreeCommittedPayloadState)
        (bodyExecutableTail : List PLeaTTa.Goal)
        (sourceExtension executableExtension : TreeSubstitution)
        (generated installed : Subst),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] ∧
      ¬ AlphaTreeSupported before.carrier.carrier.index.alpha
          before.carrier.carrier.index.support
          (Term.denote (.variable (.generated 0))) ∧
      RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
        before.carrier after (.variable (.generated 0)) valueTerm
        finalSourceResult [] bodyExecutableTail sourceExtension
        executableExtension generated installed ∧
      StepsN 5
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [ .opened (requestFor "cutv" [queryTerm] []),
          .pruned
            (PrologActivatedProductStepBridge.retainedCursorTokenAt
              active.carrier.carrier.index.predicateScope
              active.carrier.carrier.index.finish
              active.carrier.carrier.index.branch
              active.carrier.carrier.index.branchTail) ]
        after.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 5
        (.ready initialOpenConf) after.carrier.fineState ∧
      before.carrier.carrier.fineState ≠ after.carrier.fineState ∧
      after.carrier.index.current.applyTerm queryTerm = valueTerm ∧
      after.carrier.index.bodyReferences = [] := by
  obtain
      ⟨active, before, activeAlts, beforeReference, beforeSupport,
        beforeCurrent, beforeQterm, unsupported, rootSource, rootFine⟩ :=
    root_variable_cut_then_committed_unify_ready
      (prog := prog) (gt := gt)
  have continuationLive :
      ReadyUnifyContinuationLive before.carrier.carrier.index.support
        before.carrier.carrier.index.openConf := by
    intro executableHead rest runtime current identity name linked
    rw [beforeSupport] at linked
    simp only [rootAlpha, List.mem_singleton] at linked
    have nameExact : name = "z" := congrArg Prod.snd linked
    subst name
    rw [beforeQterm]
    exact PLeaTTa.isTrimRoot_qterm_mem rest queryAtom "z"
      (by simp [queryAtom, Metta.Atom.vars])
  have resolved :
      UnifyResolution before.carrier.carrier.index.current
        (.variable (.generated 0)) valueTerm finalSourceResult := by
    rw [beforeCurrent]
    exact selectedBodyResolves
  obtain
      ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
        installed, after, facts⟩ :=
    MaterializedRepresentativePersistentFreeCommittedPayloadState.exists_afterUnifySuccess
      before (prog := prog) (gt := gt) (bodyRest := []) beforeReference
      continuationLive resolved
  let edge :
      GlobalCertifiedTransition prog gt
        (.committedUnify (CommittedUnifyTransitionLabel.of facts))
        (.ordinary (.committed before.carrier))
        (.ordinary (.committed after)) :=
    .committedUnify facts
  have sourceAll := rootSource.trans edge.sourceSteps
  have fineAll := rootFine.trans edge.fineSteps
  have afterCurrent :
      after.carrier.index.current = finalSourceResult := by
    rw [facts.afterIndexExact]
    rfl
  have queryAnswer :
      after.carrier.index.current.applyTerm queryTerm = valueTerm := by
    rw [afterCurrent]
    exact finalSourceResult_answers_query
  have afterBody : after.carrier.index.bodyReferences = [] := by
    rw [facts.afterIndexExact]
    rfl
  refine
    ⟨active, before, after, bodyExecutableTail, sourceExtension,
      executableExtension, generated, installed, activeAlts, beforeReference,
      unsupported, facts, ?_, ?_, facts.fineState_ne, queryAnswer, afterBody⟩
  · simpa [GlobalTransitionKind.sourceCost,
      GlobalTransitionKind.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using
      sourceAll
  · simpa [GlobalTransitionKind.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using
      fineAll

end PLeaTTa.PrologMaterializedOperandRegression.VariableCutCommit
