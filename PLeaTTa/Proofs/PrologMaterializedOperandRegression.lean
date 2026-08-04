-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMaterializedOperandRegression
Purpose: Prove that fresh live operands can be interpreted without widening
  an immutable caller observation support.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootRejectedPrefixRegression
import PLeaTTa.Proofs.PrologMaterializedGlobalPrefixBridge
import PLeaTTa.Proofs.PrologCommittedScheduledTerminalBridge

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
open PrologCommittedScheduledTerminalBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologMaterializedGlobalPrefixBridge
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologPersistentFreeCommittedScheduledPayloadBridge
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
    body :=
      [.cut, .conjunction [], .unify clauseTerm valueTerm,
        .unify clauseTerm valueTerm] }

def retainedReference : LocalClause :=
  { predicate := "cutv"
    arguments := [clauseTerm]
    body := [] }

def selectedExecutable : PLeaTTa.Clause :=
  { params := []
    result := clauseAtom
    body := [.cut, .eq clauseAtom valueAtom, .eq clauseAtom valueAtom] }

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
        (.cons
          (.unify (CompilerAdequacy.TermAgrees.sourceVariable "x")
            (CompilerAdequacy.TermAgrees.integer 9))
          .nil)))

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
            (CompilerAdequacy.GoalsAgree.cons unifyAgreement
              CompilerAdequacy.GoalsAgree.nil)))) := Subsingleton.elim _ _
  rw [bodyEq]
  exact
    .cons .cut
      (.conjunction .nil
        (.cons unifySupported (.cons unifySupported .nil)))

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
      [.cutAt 1, .eq selectedCopied.result valueAtom,
        .eq selectedCopied.result valueAtom] := by
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
        .unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm] := by
  rfl

/-- The source-only conjunction wrapper following the cut is one genuine
administrative step. -/
def afterCutAdministrative :
    AdministrativeStepsN 1
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm]
      [.unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm] :=
  .succ 0 _ _ _
    (.conjunction []
      [.unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm])
    (.zero
      [.unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm])

/-- Exact non-ground execution through root activation, cut, and the
compiler-erased conjunction wrapper.  The retained occurrence is visibly
pruned, while the committed carrier keeps the whole-body materialization
needed by the following equality. -/
theorem root_variable_cut_then_committed_unify_ready
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (active : MaterializedRepresentativePersistentFreeActivePayloadState)
        (before : MaterializedRepresentativePersistentFreeCommittedPayloadState),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      before.carrier.carrier.index.openConf.control.alts = [] ∧
      before.carrier.carrier.index.callerReferences = [] ∧
      before.carrier.carrier.index.callerExecutables = [] ∧
      before.carrier.carrier.index.outer = [] ∧
      before.carrier.carrier.index.resources = [] ∧
      before.carrier.carrier.index.context = [] ∧
      before.carrier.carrier.index.baseAlts = [] ∧
      before.carrier.carrier.index.openConf.frames = [] ∧
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm,
          .unify (.variable (.generated 0)) valueTerm] ∧
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
        (.ready initialOpenConf) before.carrier.carrier.fineState ∧
      Nonempty
        (MaterializedGlobalCertifiedPrefix prog gt
          [ .resolver
              (.forward
                (.cut
                  (PrologActivatedProductStepBridge.retainedCursorTokenAt
                    active.carrier.carrier.index.predicateScope
                    active.carrier.carrier.index.finish
                    active.carrier.carrier.index.branch
                    active.carrier.carrier.index.branchTail))),
            .committedAdministrative 1 ]
          (.ordinary (.active active.carrier))
          (.ordinary (.committed before.carrier))) := by
  obtain
      ⟨finish, representative, nextAlpha, sourceCanonical, flattened,
        installed, legacy, facts, finishRemaining, bodyReferences,
        bodyExecutables, supportPreserved, rootSource, rootFine⟩ :=
    root_variable_cut_selected_retained_exact (prog := prog) (gt := gt)
  let active := facts.toMaterializedPersistentFreeActive
  have referenceHead :
      active.carrier.carrier.index.bodyReferences =
        [.cut, .conjunction [],
          .unify (.variable (.generated 0)) valueTerm,
          .unify (.variable (.generated 0)) valueTerm] := by
    change legacy.carrier.index.bodyReferences =
      [.cut, .conjunction [],
        .unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm]
    calc
      legacy.carrier.index.bodyReferences = selectedPrepared.body :=
        bodyReferences
      _ = _ := selectedPrepared_body_exact
  have executableKnown :
      active.carrier.carrier.index.bodyExecutables =
        [.cutAt 1, .eq selectedCopied.result valueAtom,
          .eq selectedCopied.result valueAtom] := by
    change legacy.carrier.index.bodyExecutables =
      [.cutAt 1, .eq selectedCopied.result valueAtom,
        .eq selectedCopied.result valueAtom]
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
          .eq selectedCopied.result valueAtom,
          .eq selectedCopied.result valueAtom] := by
    simpa [barrierExact] using executableKnown
  have activeAlts :
      active.carrier.carrier.index.active.alts = [retainedAlt] := by
    change legacy.carrier.index.active.alts = [retainedAlt]
    exact facts.activeAltsExact
  have activeResources :
      active.carrier.carrier.index.resources = [] := by
    change legacy.carrier.index.resources = []
    exact facts.resourcesEmpty
  have activeBaseAlts :
      active.carrier.carrier.index.baseAlts = [] := by
    change legacy.carrier.index.baseAlts = []
    exact facts.baseAltsEmpty
  have activeCallerReferences :
      active.carrier.carrier.index.callerReferences = [] := by
    change legacy.carrier.index.callerReferences = []
    exact facts.callerReferencesEmpty
  have activeCallerExecutables :
      active.carrier.carrier.index.callerExecutables = [] := by
    change legacy.carrier.index.callerExecutables = []
    exact facts.callerExecutablesEmpty
  have activeOuter : active.carrier.carrier.index.outer = [] := by
    change legacy.carrier.index.outer = []
    exact facts.outerEmpty
  have activeContext : active.carrier.carrier.index.context = [] := by
    change legacy.carrier.index.context = []
    exact facts.contextEmpty
  have activeFrames : active.carrier.carrier.index.openConf.frames = [] := by
    change legacy.carrier.index.openConf.frames = []
    exact facts.framesEmpty
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
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm]
      [.eq selectedCopied.result valueAtom,
        .eq selectedCopied.result valueAtom]
      referenceHead executableHead coherent
  let before :=
    committed.afterAdministrative afterCutAdministrative
  have cutPrefix :=
    MaterializedGlobalCertifiedPrefix.activeCut
      (prog := prog) (gt := gt) active
      [.conjunction [], .unify (.variable (.generated 0)) valueTerm,
        .unify (.variable (.generated 0)) valueTerm]
      [.eq selectedCopied.result valueAtom,
        .eq selectedCopied.result valueAtom]
      referenceHead executableHead coherent
  have administrativePrefix :=
    MaterializedGlobalCertifiedPrefix.committedAdministrative
      (prog := prog) (gt := gt) committed (by omega)
      afterCutAdministrative
  have localPrefix := cutPrefix.append administrativePrefix
  have sourceAll := rootSource.trans localPrefix.sourceSteps
  have fineAll := rootFine.trans localPrefix.fineSteps
  have beforeReference :
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm,
          .unify (.variable (.generated 0)) valueTerm] := by
    simp [before, committed,
      MaterializedRepresentativePersistentFreeCommittedPayloadState.afterAdministrative,
      RepresentativePersistentFreeCommittedPayloadState.afterAdministrative]
  have beforeAlts :
      before.carrier.carrier.index.openConf.control.alts = [] := by
    change committed.carrier.carrier.index.openConf.control.alts = []
    rw [show committed.carrier.carrier.index.openConf.control.alts =
        PrologProductResourceContextBridge.flattenOwnedAlts
          active.carrier.carrier.index.resources
          active.carrier.carrier.index.baseAlts from
      RepresentativePersistentFreeActivePayloadState.afterCut_alts_exact
        prog gt active.carrier
          [.conjunction [], .unify (.variable (.generated 0)) valueTerm,
            .unify (.variable (.generated 0)) valueTerm]
          [.eq selectedCopied.result valueAtom,
            .eq selectedCopied.result valueAtom]
          referenceHead executableHead coherent]
    simp [activeResources, activeBaseAlts]
  have beforeCallerReferences :
      before.carrier.carrier.index.callerReferences = [] := by
    change active.carrier.carrier.index.callerReferences = []
    exact activeCallerReferences
  have beforeCallerExecutables :
      before.carrier.carrier.index.callerExecutables = [] := by
    change active.carrier.carrier.index.callerExecutables = []
    exact activeCallerExecutables
  have beforeOuter : before.carrier.carrier.index.outer = [] := by
    change active.carrier.carrier.index.outer = []
    exact activeOuter
  have beforeResources : before.carrier.carrier.index.resources = [] := by
    change active.carrier.carrier.index.resources = []
    exact activeResources
  have beforeContext : before.carrier.carrier.index.context = [] := by
    change active.carrier.carrier.index.context = []
    exact activeContext
  have beforeBaseAlts : before.carrier.carrier.index.baseAlts = [] := by
    change active.carrier.carrier.index.baseAlts = []
    exact activeBaseAlts
  have beforeFrames :
      before.carrier.carrier.index.openConf.frames = [] := by
    change committed.carrier.carrier.index.openConf.frames = []
    change
      (RepresentativePersistentFreeActivePayloadState.committedOpenConf
        active.carrier
        [.eq selectedCopied.result valueAtom,
          .eq selectedCopied.result valueAtom]).frames = []
    simpa [RepresentativePersistentFreeActivePayloadState.committedOpenConf,
      cutSuccessor, OpenConf.stepOpen, OpenConf.ofConfWith]
      using activeFrames
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
  refine
    ⟨active, before, activeAlts, beforeAlts, beforeCallerReferences,
      beforeCallerExecutables, beforeOuter, beforeResources, beforeContext,
      beforeBaseAlts, beforeFrames, beforeReference, beforeSupport,
      beforeCurrent, beforeQterm, unsupported, ?_, ?_, ⟨localPrefix⟩⟩
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

/-- The first equality changes the clause-local operand observed by the
second equality from a fresh variable to the concrete value `9`. -/
theorem finalSourceResult_materializes_clause_variable :
    finalSourceResult.applyTerm (.variable (.generated 0)) = valueTerm := by
  simp [finalSourceResult, selectedSourceExtension, queryIdentity, valueTerm,
    Substitution.applyTerm, TreeSubstitution.reify, Tree.reify, Term.denote,
    Term.instantiateOne]

/-- The second source equality is a real subsequent resolution under the
binding installed by the first, rather than a replay against the old
activation substitution. -/
theorem selectedBodyResolvesAgain :
    UnifyResolution finalSourceResult
      (.variable (.generated 0)) valueTerm finalSourceResult := by
  refine ⟨TreeSubstitution.reify [], ?_, ?_⟩
  have rightUnchanged : finalSourceResult.applyTerm valueTerm = valueTerm := by
    simp [valueTerm]
  rw [finalSourceResult_materializes_clause_variable, rightUnchanged]
  have reflexive :
      OrderedTreeMgu (denoteEquations [(valueTerm, valueTerm)]) [] := by
    simpa [denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote valueTerm) (Term.denote valueTerm)
        [] [] [] (.reflexive (Term.denote valueTerm)) OrderedTreeMgu.nil)
  exact reflexive.computesReified
  rfl

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
        (after : MaterializedRepresentativePersistentFreeCommittedPayloadState)
        (bodyExecutableTail : List PLeaTTa.Goal)
        (sourceExtension executableExtension : TreeSubstitution)
        (generated installed : Subst)
        (facts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            before.carrier after.carrier (.variable (.generated 0)) valueTerm
            finalSourceResult
            [.unify (.variable (.generated 0)) valueTerm]
            bodyExecutableTail sourceExtension executableExtension generated
            installed),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm,
          .unify (.variable (.generated 0)) valueTerm] ∧
      ¬ AlphaTreeSupported before.carrier.carrier.index.alpha
          before.carrier.carrier.index.support
          (Term.denote (.variable (.generated 0))) ∧
      Nonempty
        (MaterializedGlobalCertifiedPrefix prog gt
          [ .resolver
              (.forward
                (.cut
                  (PrologActivatedProductStepBridge.retainedCursorTokenAt
                    active.carrier.carrier.index.predicateScope
                    active.carrier.carrier.index.finish
                    active.carrier.carrier.index.branch
                    active.carrier.carrier.index.branchTail))),
            .committedAdministrative 1,
            .committedUnify (CommittedUnifyTransitionLabel.of facts) ]
          (.ordinary (.active active.carrier))
          (.ordinary (.committed after.carrier))) ∧
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
        after.carrier.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 5
        (.ready initialOpenConf) after.carrier.carrier.fineState ∧
      before.carrier.carrier.fineState ≠ after.carrier.carrier.fineState ∧
      after.carrier.carrier.index.support = rootAlpha ∧
      after.carrier.carrier.index.openConf.control.alts = [] ∧
      after.carrier.carrier.index.callerReferences = [] ∧
      after.carrier.carrier.index.callerExecutables = [] ∧
      after.carrier.carrier.index.outer = [] ∧
      after.carrier.carrier.index.resources = [] ∧
      after.carrier.carrier.index.context = [] ∧
      after.carrier.carrier.index.baseAlts = [] ∧
      after.carrier.carrier.index.openConf.frames = [] ∧
      after.carrier.carrier.index.openConf.control.qterm = queryAtom ∧
      after.carrier.carrier.index.current = finalSourceResult ∧
      after.carrier.carrier.index.current.applyTerm queryTerm = valueTerm ∧
      after.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] := by
  obtain
      ⟨active, before, activeAlts, beforeAlts, beforeCallerReferences,
        beforeCallerExecutables, beforeOuter, beforeResources, beforeContext,
        beforeBaseAlts, beforeFrames, beforeReference, beforeSupport,
        beforeCurrent, beforeQterm, unsupported, rootSource, remaining⟩ :=
    root_variable_cut_then_committed_unify_ready
      (prog := prog) (gt := gt)
  obtain ⟨rootFine, ⟨localPrefix⟩⟩ := remaining
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
        installed, after, facts, ⟨unifyPrefix⟩⟩ :=
    MaterializedGlobalCertifiedPrefix.exists_committedUnify
      before (prog := prog) (gt := gt)
      (bodyRest := [.unify (.variable (.generated 0)) valueTerm])
      beforeReference continuationLive resolved
  have combinedPrefix := localPrefix.append unifyPrefix
  have sourceAll := rootSource.trans unifyPrefix.sourceSteps
  have fineAll := rootFine.trans unifyPrefix.fineSteps
  have afterCurrent :
      after.carrier.carrier.index.current = finalSourceResult := by
    rw [facts.afterIndexExact]
    rfl
  have queryAnswer :
      after.carrier.carrier.index.current.applyTerm queryTerm = valueTerm := by
    rw [afterCurrent]
    exact finalSourceResult_answers_query
  have afterSupport : after.carrier.carrier.index.support = rootAlpha := by
    rw [facts.afterIndexExact]
    exact beforeSupport
  have afterAlts :
      after.carrier.carrier.index.openConf.control.alts = [] := by
    rw [facts.afterIndexExact]
    exact beforeAlts
  have afterCallerReferences :
      after.carrier.carrier.index.callerReferences = [] := by
    rw [facts.afterIndexExact]
    exact beforeCallerReferences
  have afterCallerExecutables :
      after.carrier.carrier.index.callerExecutables = [] := by
    rw [facts.afterIndexExact]
    exact beforeCallerExecutables
  have afterOuter : after.carrier.carrier.index.outer = [] := by
    rw [facts.afterIndexExact]
    exact beforeOuter
  have afterResources : after.carrier.carrier.index.resources = [] := by
    rw [facts.afterIndexExact]
    exact beforeResources
  have afterContext : after.carrier.carrier.index.context = [] := by
    rw [facts.afterIndexExact]
    exact beforeContext
  have afterBaseAlts : after.carrier.carrier.index.baseAlts = [] := by
    rw [facts.afterIndexExact]
    exact beforeBaseAlts
  have afterFrames : after.carrier.carrier.index.openConf.frames = [] := by
    rw [facts.afterIndexExact]
    simpa [RepresentativePersistentFreeCommittedPayloadState.unifyIndex,
      RepresentativePersistentFreeCommittedPayloadState.unifyOpenConf]
      using beforeFrames
  have afterQterm :
      after.carrier.carrier.index.openConf.control.qterm = queryAtom := by
    rw [facts.afterIndexExact]
    exact beforeQterm
  have afterBody :
      after.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] := by
    rw [facts.afterIndexExact]
    rfl
  refine
    ⟨active, before, after, bodyExecutableTail, sourceExtension,
      executableExtension, generated, installed, facts, activeAlts,
      beforeReference, unsupported, ⟨combinedPrefix⟩, ?_, ?_, facts.fineState_ne,
      afterSupport, afterAlts, afterCallerReferences, afterCallerExecutables,
      afterOuter, afterResources, afterContext, afterBaseAlts, afterFrames,
      afterQterm, afterCurrent, queryAnswer, afterBody⟩
  · simpa [GlobalTransitionKind.sourceCost,
      GlobalTransitionKind.sourceEvents,
      GlobalTransitionSchedule.sourceCost,
      GlobalTransitionSchedule.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using
      sourceAll
  · simpa [GlobalTransitionKind.fineCost,
      GlobalTransitionSchedule.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using
      fineAll

/-- One literal invariant-carrying prefix consumes both equalities in the
selected clause.

The second equality is evaluated after the first has changed generated
operand `0` into `9`; it therefore cannot be justified by replaying the
activation substitution or by retaining only a one-step materialization
certificate.  Its resolution is reflexive under that inherited binding, so
this witness establishes dependent materialization across two equality
transitions but does not claim two nonempty MGU extensions.  Both source and
fine executions advance once more, while the same public query remains
exactly `9`. -/
theorem root_variable_cut_then_two_materialized_unifies_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (active : MaterializedRepresentativePersistentFreeActivePayloadState)
        (before first second :
          MaterializedRepresentativePersistentFreeCommittedPayloadState)
        (firstExecutableTail secondExecutableTail : List PLeaTTa.Goal)
        (firstSourceExtension firstExecutableExtension : TreeSubstitution)
        (secondSourceExtension secondExecutableExtension : TreeSubstitution)
        (firstGenerated firstInstalled secondGenerated secondInstalled :
          Subst)
        (firstFacts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            before.carrier first.carrier (.variable (.generated 0)) valueTerm
            finalSourceResult
            [.unify (.variable (.generated 0)) valueTerm]
            firstExecutableTail firstSourceExtension firstExecutableExtension
            firstGenerated firstInstalled)
        (secondFacts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            first.carrier second.carrier (.variable (.generated 0)) valueTerm
            finalSourceResult [] secondExecutableTail secondSourceExtension
            secondExecutableExtension secondGenerated secondInstalled),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      before.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm,
          .unify (.variable (.generated 0)) valueTerm] ∧
      first.carrier.carrier.index.bodyReferences =
        [.unify (.variable (.generated 0)) valueTerm] ∧
      first.carrier.carrier.index.current.applyTerm
          (.variable (.generated 0)) = valueTerm ∧
      Nonempty
        (MaterializedGlobalCertifiedPrefix prog gt
          [ .resolver
              (.forward
                (.cut
                  (PrologActivatedProductStepBridge.retainedCursorTokenAt
                    active.carrier.carrier.index.predicateScope
                    active.carrier.carrier.index.finish
                    active.carrier.carrier.index.branch
                    active.carrier.carrier.index.branchTail))),
            .committedAdministrative 1,
            .committedUnify (CommittedUnifyTransitionLabel.of firstFacts),
            .committedUnify (CommittedUnifyTransitionLabel.of secondFacts) ]
          (.ordinary (.active active.carrier))
          (.ordinary (.committed second.carrier))) ∧
      StepsN 6
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [ .opened (requestFor "cutv" [queryTerm] []),
          .pruned
            (PrologActivatedProductStepBridge.retainedCursorTokenAt
              active.carrier.carrier.index.predicateScope
              active.carrier.carrier.index.finish
              active.carrier.carrier.index.branch
              active.carrier.carrier.index.branchTail) ]
        second.carrier.carrier.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 6
        (.ready initialOpenConf) second.carrier.carrier.fineState ∧
      before.carrier.carrier.fineState ≠ first.carrier.carrier.fineState ∧
      first.carrier.carrier.fineState ≠ second.carrier.carrier.fineState ∧
      second.carrier.carrier.index.openConf.control.alts = [] ∧
      second.carrier.carrier.index.callerReferences = [] ∧
      second.carrier.carrier.index.callerExecutables = [] ∧
      second.carrier.carrier.index.outer = [] ∧
      second.carrier.carrier.index.resources = [] ∧
      second.carrier.carrier.index.context = [] ∧
      second.carrier.carrier.index.baseAlts = [] ∧
      second.carrier.carrier.index.openConf.frames = [] ∧
      second.carrier.carrier.index.current = finalSourceResult ∧
      second.carrier.carrier.index.current.applyTerm queryTerm = valueTerm ∧
      second.carrier.carrier.index.bodyReferences = [] := by
  obtain
      ⟨active, before, first, firstExecutableTail, firstSourceExtension,
        firstExecutableExtension, firstGenerated, firstInstalled, firstFacts,
        activeAlts, beforeBody, _unsupported, firstPrefixNonempty, sourceOne,
        fineOne, firstFineNe, firstSupport, firstAlts, firstCallerReferences,
        firstCallerExecutables, firstOuter, firstResources, firstContext,
        firstBaseAlts, firstFrames, firstQterm, firstCurrent, _firstQuery,
        firstBody⟩ :=
    root_variable_cut_then_materialized_unify_exact
      (prog := prog) (gt := gt)
  obtain ⟨firstPrefix⟩ := firstPrefixNonempty
  have continuationLive :
      ReadyUnifyContinuationLive first.carrier.carrier.index.support
        first.carrier.carrier.index.openConf := by
    intro executableHead rest runtime current identity name linked
    rw [firstSupport] at linked
    simp only [rootAlpha, List.mem_singleton] at linked
    have nameExact : name = "z" := congrArg Prod.snd linked
    subst name
    rw [firstQterm]
    exact PLeaTTa.isTrimRoot_qterm_mem rest queryAtom "z"
      (by simp [queryAtom, Metta.Atom.vars])
  have resolved :
      UnifyResolution first.carrier.carrier.index.current
        (.variable (.generated 0)) valueTerm finalSourceResult := by
    rw [firstCurrent]
    exact selectedBodyResolvesAgain
  obtain
      ⟨secondExecutableTail, secondSourceExtension,
        secondExecutableExtension, secondGenerated, secondInstalled, second,
        secondFacts, ⟨secondPrefix⟩⟩ :=
    MaterializedGlobalCertifiedPrefix.exists_committedUnify
      first (prog := prog) (gt := gt) (bodyRest := []) firstBody
      continuationLive resolved
  have combinedPrefix := firstPrefix.append secondPrefix
  have sourceAll := sourceOne.trans secondPrefix.sourceSteps
  have fineAll := fineOne.trans secondPrefix.fineSteps
  have firstOperand :
      first.carrier.carrier.index.current.applyTerm
          (.variable (.generated 0)) = valueTerm := by
    rw [firstCurrent]
    exact finalSourceResult_materializes_clause_variable
  have secondCurrent :
      second.carrier.carrier.index.current = finalSourceResult := by
    rw [secondFacts.afterIndexExact]
    rfl
  have secondAlts :
      second.carrier.carrier.index.openConf.control.alts = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstAlts
  have secondCallerReferences :
      second.carrier.carrier.index.callerReferences = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstCallerReferences
  have secondCallerExecutables :
      second.carrier.carrier.index.callerExecutables = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstCallerExecutables
  have secondOuter : second.carrier.carrier.index.outer = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstOuter
  have secondResources : second.carrier.carrier.index.resources = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstResources
  have secondContext : second.carrier.carrier.index.context = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstContext
  have secondBaseAlts : second.carrier.carrier.index.baseAlts = [] := by
    rw [secondFacts.afterIndexExact]
    exact firstBaseAlts
  have secondFrames : second.carrier.carrier.index.openConf.frames = [] := by
    rw [secondFacts.afterIndexExact]
    simpa [RepresentativePersistentFreeCommittedPayloadState.unifyIndex,
      RepresentativePersistentFreeCommittedPayloadState.unifyOpenConf]
      using firstFrames
  have secondQuery :
      second.carrier.carrier.index.current.applyTerm queryTerm = valueTerm := by
    rw [secondCurrent]
    exact finalSourceResult_answers_query
  have secondBody : second.carrier.carrier.index.bodyReferences = [] := by
    rw [secondFacts.afterIndexExact]
    rfl
  refine
    ⟨active, before, first, second, firstExecutableTail, secondExecutableTail,
      firstSourceExtension, firstExecutableExtension, secondSourceExtension,
      secondExecutableExtension, firstGenerated, firstInstalled,
      secondGenerated, secondInstalled, firstFacts, secondFacts, activeAlts,
      beforeBody, firstBody, firstOperand, ⟨combinedPrefix⟩, ?_, ?_,
      firstFineNe, secondFacts.fineState_ne, secondAlts,
      secondCallerReferences, secondCallerExecutables, secondOuter,
      secondResources, secondContext, secondBaseAlts, secondFrames,
      secondCurrent, secondQuery, secondBody⟩
  · simpa [GlobalTransitionKind.sourceCost,
      GlobalTransitionKind.sourceEvents,
      GlobalTransitionSchedule.sourceCost,
      GlobalTransitionSchedule.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using
      sourceAll
  · simpa [GlobalTransitionKind.fineCost,
      GlobalTransitionSchedule.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using
      fineAll

/-- Reachable exact discriminator for the post-cut body-answer seam.

After the retained sibling is visibly pruned and both materialized equalities
run, the successful clause body contributes one private source transition and
no fine transition: the fine machine already exposes the flattened caller
continuation.  The post-answer executable bank remains literally empty and is
also tied to the same dependent outer-resource suffix, so this witness rejects
both a fabricated fine step and resurrection of the consumed cursor. -/
theorem root_variable_cut_then_body_answer_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (active : MaterializedRepresentativePersistentFreeActivePayloadState)
        (before first second :
          MaterializedRepresentativePersistentFreeCommittedPayloadState)
        (firstExecutableTail secondExecutableTail : List PLeaTTa.Goal)
        (firstSourceExtension firstExecutableExtension : TreeSubstitution)
        (secondSourceExtension secondExecutableExtension : TreeSubstitution)
        (firstGenerated firstInstalled secondGenerated secondInstalled :
          Subst)
        (firstFacts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            before.carrier first.carrier (.variable (.generated 0)) valueTerm
            finalSourceResult
            [.unify (.variable (.generated 0)) valueTerm]
            firstExecutableTail firstSourceExtension firstExecutableExtension
            firstGenerated firstInstalled)
        (secondFacts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            first.carrier second.carrier (.variable (.generated 0)) valueTerm
            finalSourceResult [] secondExecutableTail secondSourceExtension
            secondExecutableExtension secondGenerated secondInstalled)
        (after : RepresentativePersistentFreeCommittedScheduledPayloadState)
        (ready : RootCommittedScheduledAnswerReady after),
      active.carrier.carrier.index.active.alts = [retainedAlt] ∧
      second.carrier.carrier.index.bodyReferences = [] ∧
      second.carrier.carrier.index.bodyExecutables = [] ∧
      Nonempty
        (MaterializedGlobalCertifiedPrefix prog gt
          [ .resolver
              (.forward
                (.cut
                  (PrologActivatedProductStepBridge.retainedCursorTokenAt
                    active.carrier.carrier.index.predicateScope
                    active.carrier.carrier.index.finish
                    active.carrier.carrier.index.branch
                    active.carrier.carrier.index.branchTail))),
            .committedAdministrative 1,
            .committedUnify (CommittedUnifyTransitionLabel.of firstFacts),
            .committedUnify (CommittedUnifyTransitionLabel.of secondFacts),
            .committedBodyAnswer ]
          (.ordinary (.active active.carrier))
          (.ordinary (.committedScheduled after))) ∧
      StepsN 7
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
      DemandDrivenCallStep.StepsN prog gt 6
        (.ready initialOpenConf) after.carrier.fineState ∧
      after.carrier.index.openConf.control.alts = [] ∧
      after.carrier.index.openConf.control.alts =
        PrologProductResourceContextBridge.flattenOwnedAlts
          second.carrier.carrier.index.resources
          second.carrier.carrier.index.baseAlts ∧
      after.carrier.cellIdentities = second.carrier.carrier.cellIdentities ∧
      after.carrier.index.current.applyTerm queryTerm = valueTerm ∧
      RootCommittedScheduledTerminalRelates prog gt after ready ∧
      StepsN 10
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [ .opened (requestFor "cutv" [queryTerm] []),
          .pruned
            (PrologActivatedProductStepBridge.retainedCursorTokenAt
              active.carrier.carrier.index.predicateScope
              active.carrier.carrier.index.finish
              active.carrier.carrier.index.branch
              active.carrier.carrier.index.branchTail),
          .answer after.carrier.index.current,
          .completed ]
        (.terminal after.carrier.index.session .completed) ∧
      DemandDrivenCallStep.StepsN prog gt 7
        (.ready initialOpenConf)
        (.ready
          (privateAnswerTarget after.carrier.index.openConf
            after.carrier.index.runtime)) ∧
      DemandDrivenStep.Terminal
        (privateAnswerTarget after.carrier.index.openConf
          after.carrier.index.runtime) := by
  obtain
      ⟨active, before, first, second, firstExecutableTail,
        secondExecutableTail, firstSourceExtension, firstExecutableExtension,
        secondSourceExtension, secondExecutableExtension, firstGenerated,
        firstInstalled, secondGenerated, secondInstalled, firstFacts,
        secondFacts, activeAlts, _beforeBody, _firstBody, _firstOperand,
        ⟨priorPrefix⟩, sourceSix, fineSix, _firstFineNe, _secondFineNe,
        secondAlts, secondCallerReferences, secondCallerExecutables,
        secondOuter, secondResources, secondContext, secondBaseAlts,
        secondFrames, _secondCurrent, secondQuery, secondBody⟩ :=
    root_variable_cut_then_two_materialized_unifies_exact
      (prog := prog) (gt := gt)
  have secondExecutableEmpty :
      second.carrier.carrier.index.bodyExecutables = [] :=
    NormalizedAlphaGoalsAgree.executables_eq_nil_of_references_eq_nil
      second.materializedUnifyGoals.toNormalized secondBody
  have secondExecutableTailEmpty : secondExecutableTail = [] := by
    rw [secondFacts.afterIndexExact] at secondExecutableEmpty
    exact secondExecutableEmpty
  have firstCallerExecutables :
      first.carrier.carrier.index.callerExecutables = [] := by
    rw [secondFacts.afterIndexExact] at secondCallerExecutables
    exact secondCallerExecutables
  have firstOuter : first.carrier.carrier.index.outer = [] := by
    rw [secondFacts.afterIndexExact] at secondOuter
    exact secondOuter
  have firstQtermIndex :
      first.carrier.carrier.index.openConf.control.qterm =
        first.carrier.carrier.index.qterm :=
    first.carrier.carrier.agreement.ready.2.2.1
  have secondFineHead :
      second.carrier.carrier.index.openConf.toConf.cur =
        some ([], second.carrier.carrier.index.runtime) := by
    rw [secondFacts.afterIndexExact]
    simp [RepresentativePersistentFreeCommittedPayloadState.unifyIndex,
      RepresentativePersistentFreeCommittedPayloadState.unifyOpenConf,
      RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail,
      secondExecutableTailEmpty, firstCallerExecutables, firstOuter,
      firstQtermIndex, OpenConf.toConf, Control.toConf]
  let after :=
    RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer
      prog gt second.carrier secondBody secondExecutableEmpty
  have answerPrefix :=
    MaterializedGlobalCertifiedPrefix.committedBodyAnswer
      (prog := prog) (gt := gt) second secondBody secondExecutableEmpty
  have combinedPrefix := priorPrefix.append answerPrefix
  have sourceSeven := sourceSix.trans answerPrefix.sourceSteps
  have fineStillSix := fineSix.trans answerPrefix.fineSteps
  have afterAlts : after.carrier.index.openConf.control.alts = [] := by
    change second.carrier.carrier.index.openConf.control.alts = []
    exact secondAlts
  have afterActualAlts :
      after.carrier.index.openConf.control.alts =
        PrologProductResourceContextBridge.flattenOwnedAlts
          second.carrier.carrier.index.resources
          second.carrier.carrier.index.baseAlts := by
    exact
      RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer_actualAlts
        prog gt second.carrier secondBody secondExecutableEmpty
  have afterCells :
      after.carrier.cellIdentities = second.carrier.carrier.cellIdentities := by
    exact
      RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer_cellIdentities
        prog gt second.carrier secondBody secondExecutableEmpty
  have afterQuery :
      after.carrier.index.current.applyTerm queryTerm = valueTerm := by
    change second.carrier.carrier.index.current.applyTerm queryTerm = valueTerm
    exact secondQuery
  let ready : RootCommittedScheduledAnswerReady after :=
    { callerReferencesEmpty := by
        change second.carrier.carrier.index.callerReferences = []
        exact secondCallerReferences
      contextEmpty := by
        change second.carrier.carrier.index.context = []
        exact secondContext
      resourcesEmpty := by
        change second.carrier.carrier.index.resources = []
        exact secondResources
      baseAltsEmpty := by
        change second.carrier.carrier.index.baseAlts = []
        exact secondBaseAlts
      fineHead := by
        change second.carrier.carrier.index.openConf.toConf.cur =
          some ([], second.carrier.carrier.index.runtime)
        exact secondFineHead
      rootFrames := by
        change second.carrier.carrier.index.openConf.frames = []
        exact secondFrames }
  have terminal :
      RootCommittedScheduledTerminalRelates prog gt after ready :=
    RootCommittedScheduledAnswerReady.complete ready
  have sourceTenRaw := sourceSeven.trans terminal.sourceRun
  have sourceTen :
      StepsN 10
        (.running initialSession
          (.task rootScope [.call "cutv" [queryTerm]] []))
        [ .opened (requestFor "cutv" [queryTerm] []),
          .pruned
            (PrologActivatedProductStepBridge.retainedCursorTokenAt
              active.carrier.carrier.index.predicateScope
              active.carrier.carrier.index.finish
              active.carrier.carrier.index.branch
              active.carrier.carrier.index.branchTail),
          .answer after.carrier.index.current,
          .completed ]
        (.terminal after.carrier.index.session .completed) := by
    simpa [after, GlobalTransitionKind.sourceCost,
      GlobalTransitionKind.sourceEvents,
      GlobalTransitionSchedule.sourceCost,
      GlobalTransitionSchedule.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using
      sourceTenRaw
  have fineSevenRaw := fineStillSix.trans terminal.fineRun
  have fineSeven :
      DemandDrivenCallStep.StepsN prog gt 7
        (.ready initialOpenConf)
        (.ready
          (privateAnswerTarget after.carrier.index.openConf
            after.carrier.index.runtime)) := by
    simpa [after, GlobalTransitionKind.fineCost,
      GlobalTransitionSchedule.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using
      fineSevenRaw
  refine
    ⟨active, before, first, second, firstExecutableTail,
      secondExecutableTail, firstSourceExtension, firstExecutableExtension,
      secondSourceExtension, secondExecutableExtension, firstGenerated,
      firstInstalled, secondGenerated, secondInstalled, firstFacts,
      secondFacts, after, ready, activeAlts, secondBody, secondExecutableEmpty,
      ⟨combinedPrefix⟩, ?_, ?_, afterAlts, afterActualAlts, afterCells,
      afterQuery, terminal, sourceTen, fineSeven, terminal.fineTerminal⟩
  · simpa [after, GlobalTransitionKind.sourceCost,
      GlobalTransitionKind.sourceEvents,
      GlobalTransitionSchedule.sourceCost,
      GlobalTransitionSchedule.sourceEvents,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.sourceState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.sourceState] using
      sourceSeven
  · simpa [after, GlobalTransitionKind.fineCost,
      GlobalTransitionSchedule.fineCost,
      PrologFailureRebasePrefixBridge.ResolverPhaseState.fineState,
      PrologHeterogeneousPrefixBridge.ProductPhaseState.fineState] using
      fineStillSix

end PLeaTTa.PrologMaterializedOperandRegression.VariableCutCommit
