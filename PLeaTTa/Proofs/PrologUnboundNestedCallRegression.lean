-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologUnboundNestedCallRegression
Purpose: Exercise the representative-preserving nested-call bridge on a
  reachable non-ground p(Z) :- q(Z) prefix.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallPrefixInductionBridge

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
open PrologCurrentSessionPayloadBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologNestedCallChainBridge
open PrologNestedCallPrefixInductionBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRootCallReadyBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open SourceControlResourcePayloadContextAgrees

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
      clauseIdentity]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (previous.allocate qReferenceClause).clause.variables
        (previous.allocate qReferenceClause).clause.variables head.body := by
    change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [clauseIdentity]
        [clauseIdentity] head.body
    have bodyEq :
        head.body = (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
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

/-- Opening the reached `q(generated 0)` call reserves a second, disjoint
copy of the stored clause variable. -/
private def qPreparedBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz pReferenceClause).allocate qReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated 1))]
    headEquations :=
      [(.variable (.generated 0), .variable (.generated 1))]
    body := []
    bindings := pSourceExtension
    firstFresh := 1
    nextFresh := 2 }

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

def qSourceExtension : Substitution :=
  TreeSubstitution.reify
      [((.generated 0 : LogicVar), .variable (.generated 1))] ++
    pSourceExtension

/-- The second ordered MGU preserves the first activation's binding while
linking the reached argument to the independently freshened `q` clause head. -/
private theorem qPreparedBranch_resolves :
    HeadResolution qPreparedBranch qSourceExtension := by
  let extension : TreeSubstitution :=
    [((.generated 0 : LogicVar), .variable (.generated 1))]
  have computed :
      ComputesDenotationalMgu
        [(.variable (.generated 0), .variable (.generated 1))]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_left_variable (.generated 0)
      (.variable (.generated 1)) (by
        intro equality
        injection equality with identityEquality
        injection identityEquality with indexEquality
        omega) (by rfl)
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · have normalized :
        qPreparedBranch.normalizedHeadEquations =
          [(.variable (.generated 0), .variable (.generated 1))] := by
      rfl
    rw [normalized]
    exact computed
  · simp [qSourceExtension, extension, qPreparedBranch]

/-! ## Reachable materialized recursive head -/

private def rootScope : CutScopeId := 0

private theorem pCopied_body :
    pCopied.body = [.call "q" [] pCopied.result] := by
  rfl

/-- The representative-preserving root activation factored through the
generic literal-root certificate.  The concrete singleton clause identities
and zero rejected-prefix cost are recovered from its returned banks. -/
theorem reachable_unbound_p_to_q_materialized
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (finish : PreparedCursor) (branch : ClauseBranch)
      (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
      (copied : PLeaTTa.Clause),
      ∃ representative nextAlpha sourceCanonical flattened installed,
        branch = pPreparedBranch ∧
        copied = pCopied ∧
        RepresentativeRetainedCallFrontier rootAlpha
          (openedFor initialSession "p" [queryTerm] []) initialOpenConf
          pPending finish branch pExecutableClause branchTail [] altTail copied
          [] [] queryAtom [] [] queryAtom
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter ∧
        AlphaCumulativeResidualVariantAgreesOnWith rootAlpha rootAlpha [] [] []
          representative ∧
        MaterializedCallAgreesWith rootAlpha [] [queryTerm] [] queryAtom
          representative [] ∧
        SpinedRepresentativeProductActivation prog gt rootAlpha rootAlpha [] []
          (openedFor initialSession "p" [queryTerm] []) pPending finish branch
          branchTail altTail copied [] [] [] queryAtom
          (barrierDepth initialOpenConf.toConf + 1)
          0 initialOpenConf.toConf.counter rootScope pSourceExtension
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
           references := [.call "p" [queryTerm]]
           executables := [.call "p" [] queryAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have selected :
      ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
        {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
        {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
        {copied : PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor initialSession "p" [queryTerm] []).cursor finish →
          RepresentativeRetainedCallFrontier rootAlpha
            (openedFor initialSession "p" [queryTerm] []) initialOpenConf
            pPending finish branch clause branchTail clauseTail altTail copied
            [] [] queryAtom [] [] queryAtom
            (barrierDepth initialOpenConf.toConf + 1)
            initialOpenConf.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive rootAlpha copied.body queryAtom := by
    intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    have finishNonempty : finish.remaining ≠ [] := by
      rw [frontier.finishRemaining]
      simp
    obtain ⟨_countZero, finishExact⟩ :=
      PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
        pOpenedRemaining pulls finishNonempty
    subst finish
    have branchExact : branch = pPreparedBranch := by
      have exact :
          pPreparedBranch :: [] = branch :: branchTail := by
        simpa [pOpenedRemaining] using frontier.finishRemaining
      exact (List.cons.inj exact).1.symm
    refine ⟨pSourceExtension, ?_, ?_⟩
    · simpa [branchExact] using pPreparedBranch_resolves
    · intro identity name member
      simp only [rootAlpha, List.mem_singleton] at member
      have nameExact : name = "z" := congrArg Prod.snd member
      subst name
      exact PLeaTTa.isTrimRoot_qterm_mem copied.body queryAtom "z"
        (by simp [queryAtom, Metta.Atom.vars])
  have pNotThrow : ¬ BuiltinThrowCall "p" [queryTerm] := by
    simp [BuiltinThrowCall]
  have pNotDatabase :
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
      (by rfl) initialBelow pScanNonempty selected pNotThrow pNotDatabase
  have sourceShape := facts.sourceBank
  rw [pOpenedRemaining] at sourceShape
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
  have rejectsZero : rejects = 0 := by
    rw [← facts.sourceSkipCount]
    exact skippedBranchesLength
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "p" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [pResolutionCandidates] at executableShape
  have executableLengths := congrArg List.length executableShape
  simp only [List.length_cons, List.length_nil, List.length_append] at executableLengths
  have skippedClausesLength : skippedClauses.length = 0 := by omega
  have clauseTailLength : clauseTail.length = 0 := by omega
  have skippedClausesNil : skippedClauses = [] :=
    List.eq_nil_of_length_eq_zero skippedClausesLength
  have clauseTailNil : clauseTail = [] :=
    List.eq_nil_of_length_eq_zero clauseTailLength
  have clauseExact : clause = pExecutableClause := by
    subst skippedClauses
    subst clauseTail
    simpa using executableShape.symm
  have copiedExact : copied = pCopied := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have selectedResolution : HeadResolution branch independentResult := by
    rw [← facts.carrierCurrent]
    exact facts.resolution
  have independentResultExact : independentResult = pSourceExtension :=
    HeadResolution.deterministic selectedResolution
      (by simpa [branchExact] using pPreparedBranch_resolves)
  subst branch
  subst branchTail
  subst clause
  subst clauseTail
  subst copied
  subst independentResult
  have materialized :
      MaterializedCallAgreesWith nextAlpha pSourceExtension
        [.variable (.generated 0)] []
        (PLeaTTa.subst
          (PLeaTTa.trimFor pCopied.body queryAtom installed)
          pCopied.result)
        (flattened ++ representative) [] := by
    have exactHead := facts.activation.materializedBodyHeads
      (by rfl) pCopied_body
    simpa [initialOpenConf] using exactHead
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
          facts.activation.bodyPayload.control
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
  refine
    ⟨finish, pPreparedBranch, [], altTail, pCopied, representative,
      nextAlpha, sourceCanonical, flattened, installed, rfl, rfl, ?_,
      facts.oldCumulative, (by simpa using facts.materializedAtOpen),
      facts.activation, ?_, ?_,
      materialized, rawUnsupported⟩
  · exact facts.frontier
  · rw [← facts.sourceStateExact]
    simpa [rejectsZero] using facts.sourceSteps
  · have fineSteps := facts.fineSteps
    rw [facts.fineStateExact] at fineSteps
    have pendingExact :
        DemandDrivenCallStep.pendingCallOf initialOpenConf pPending.branches
          pScan.2 = pPending := by
      rfl
    rw [pendingExact] at fineSteps
    exact fineSteps

/-! ## Literal readiness of the reached `q/1` call -/

/-- The exact post-`p` successor is a representative-indexed carrier whose
reached `q(generated 0)` head is materially and operationally ready.

The source cursor for that call is the singleton occurrence reserved in the
disjoint interval `[1, 2)`.  The root source and fine prefixes end at this
same carrier, so no shape-compatible state can be substituted between the
first and second activations. -/
private theorem qMaterializedReadyAfterP
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : RepresentativeActivePayloadState,
      ∃ head : NestedCallHead state.carrier,
        MaterializedNestedCallReady state head ∧
        head.predicate = "q" ∧
        head.referencePayload = [(.variable (.generated 0) : Term)] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = pCopied.result ∧
        head.executableRest = [] ∧
        state.carrier.index.current = pSourceExtension ∧
        state.carrier.index.session.resolver.database = referenceDatabase ∧
        state.carrier.index.openConf.persistent.world = executableWorld ∧
        (openedFor state.carrier.index.session head.predicate
            head.referencePayload state.carrier.index.current).cursor.remaining =
          [qPreparedBranch] ∧
        state.carrier.index.session.resolver.nextFresh = 1 ∧
        state.carrier.index.openConf.persistent.counter = 1 ∧
        StepsN 2
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          state.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 3
          (.ready initialOpenConf) state.carrier.fineState := by
  obtain
    ⟨finish, branch, branchTail, altTail, copied, representative, nextAlpha,
      sourceCanonical, flattened, installed, branchExact, copiedExact,
      frontier, oldCumulative, materializedAtOpen, activation, rootSourceSteps,
      rootFineSteps, materialized, _rawUnsupported⟩ :=
    reachable_unbound_p_to_q_materialized (prog := prog) (gt := gt)
  subst branch
  subst copied
  have preHeadPayload :
      TaskSpinePayloadAgrees rootAlpha rootAlpha [] [] [] []
        [{ barrier := 0
           references := [.call "p" [queryTerm]]
           executables := [.call "p" [] queryAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have referenceBelow :
      GeneratedBelow finish.reservationStart (rootAlpha.map Prod.fst) := by
    intro index member
    simp [rootAlpha, queryIdentity] at member
  let outerPayloads :
      SourceControlResourcePayloadContextAgrees rootAlpha rootAlpha queryAtom
        0 [] [] rootScope [] rootScope :=
    .nil 0 rootScope
  have outerEndpoints :
      endpointsBelow outerPayloads
        (openedFor initialSession "p" [queryTerm] []).cursor.reservationStart
        initialOpenConf.toConf.counter := by
    trivial
  have outerOrdered : ActivationOrdered outerPayloads := by
    trivial
  have sourceFresh :
      (openedFor initialSession "p" [queryTerm] []).session.resolver.nextFresh =
        (openedFor initialSession "p" [queryTerm] []).cursor.reservedUntil := by
    rfl
  have outerAlts : pPending.outer.alts = flattenOwnedAlts [] [] := by
    rfl
  obtain ⟨active, payloadContext, agreement, _outerExact⟩ :=
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
      (prog := prog) (gt := gt) (alpha := rootAlpha) (support := rootAlpha)
      (canonical := []) (referenceBase := []) (referenceBindings := [])
      (argsv := []) (args := []) (res := queryAtom)
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (binding := []) (qterm := queryAtom)
      (callerBarrier := 0) (callerScope := rootScope)
      (outerScope := rootScope) (resources := []) (context := [])
      frontier preHeadPayload oldCumulative
      (by simpa using materializedAtOpen)
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      referenceBelow activation sourceFresh outerPayloads outerEndpoints
      outerOrdered [] outerAlts
  let carrier := ActivePayloadState.ofAgreement agreement
  have carrierCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
        carrier.index.support carrier.index.canonical
        carrier.index.referenceBase carrier.index.runtime
        (flattened ++ representative) := by
    change
      AlphaCumulativeResidualVariantAgreesOnWith nextAlpha rootAlpha
        (sourceCanonical ++ []) []
        (PLeaTTa.trimFor (pCopied.body ++ ([] ++ flattenExecutables []))
          queryAtom installed)
        (flattened ++ representative)
    exact activation.cumulative
  let state : RepresentativeActivePayloadState :=
    { carrier := carrier
      representative := flattened ++ representative
      cumulative := carrierCumulative }
  let head : NestedCallHead state.carrier :=
    { predicate := "q"
      referencePayload := [(.variable (.generated 0) : Term)]
      referenceRest := []
      arguments := []
      result := pCopied.result
      executableRest := []
      referenceHead := by rfl
      executableHead := by exact pCopied_body }
  have databaseExact :
      state.carrier.index.session.resolver.database = referenceDatabase := by
    rfl
  have nextFreshOne :
      state.carrier.index.session.resolver.nextFresh = 1 := by
    rfl
  have supportExact : state.carrier.index.support = rootAlpha := by
    rfl
  have currentExact : state.carrier.index.current = pSourceExtension := by
    rfl
  have qtermExact : state.carrier.index.qterm = queryAtom := by
    rfl
  have worldExact :
      state.carrier.index.openConf.persistent.world = executableWorld := by
    change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pPending pCopied [] queryAtom installed).world = executableWorld
    simpa [pPending, initialOpenConf] using activation.worldPreserved
  have counterOne :
      state.carrier.index.openConf.persistent.counter = 1 := by
    change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pPending pCopied [] queryAtom installed).counter = 1
    simp [pPending, pScanExact, initialOpenConf, OpenConf.toConf,
      Control.toConf]
  have openedSingleton :
      (openedFor state.carrier.index.session "q"
        [(.variable (.generated 0) : Term)]
        state.carrier.index.current).cursor.remaining = [qPreparedBranch] := by
    rw [currentExact]
    change
      (prepareCall state.carrier.index.session.resolver
        (requestFor "q" [(.variable (.generated 0) : Term)]
          pSourceExtension)).1.remaining = [qPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [databaseExact, nextFreshOne]
    change
      (reserveVisible referenceDatabase.generation
        [(.variable (.generated 0) : Term)] pSourceExtension 1
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).1 = [qPreparedBranch]
    rw [qVisibleClauses]
    rfl
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
  have sealedEntry :
      PLeaTTa.Step prog gt initialOpenConf.toConf pPending.pulled.toConf := by
    change
      PLeaTTa.Step prog gt initialOpenConf.toConf
        (DemandDrivenCallStep.FineConf.callPending pPending).toSealed
    simpa [pPending] using
      (DemandDrivenCallStep.callEnter_projects_to_sealed
        (prog := prog) (gt := gt) (state := initialOpenConf)
        (f := "p") (args := []) (res := queryAtom) (rest := [])
        (binding := []) (branches := pScan.1) (counter := pScan.2)
        (by rfl) dispatch.1 dispatch.2 scanned)
  have activeBelow : ConfBelowResolutionCounter state.carrier.index.openConf.toConf := by
    change
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pPending pCopied [] queryAtom installed)
    exact activation.executableStep.preserves_belowResolutionCounter
      (sealedEntry.preserves_belowResolutionCounter initialBelow)
  have sourceExact :
      state.carrier.sourceState =
        .running
          (openedFor initialSession "p" [queryTerm] []).session
          (activatedSourceProduct rootScope
            (openedFor initialSession "p" [queryTerm] []) finish
            pPreparedBranch branchTail pSourceExtension []) := by
    rfl
  have fineExact :
      state.carrier.fineState =
        .ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pPending pCopied [] queryAtom installed) := by
    rfl
  have exactFresh :
      state.carrier.index.freshFrontier =
        AlphaFreshFrontier state.carrier.index.alpha := by
    rfl
  have operational : NestedCallOperationalReady state.carrier head := by
    refine
      { exactFresh := exactFresh
        indexReady := ?_
        below := activeBelow
        candidateSupported := ?_
        sourceNonempty := ?_
        scanNonempty := ?_
        selected := ?_
        notThrow := ?_
        notDatabase := ?_ }
    · rw [worldExact]
      rfl
    · change
        SupportedCandidateBank "q"
          (state.carrier.index.session.resolver.database.visibleClausesAt
            state.carrier.index.session.resolver.database.generation "q" 1)
          (state.carrier.index.openConf.persistent.world.resolutionCandidates
            "q" 0)
      simpa [databaseExact, worldExact] using qCandidateBank
    · change
        state.carrier.index.session.resolver.database.visibleClausesAt
          state.carrier.index.session.resolver.database.generation "q" 1 ≠ []
      rw [databaseExact, qVisibleClauses]
      simp
    · have executableTailNil : head.executableTail = [] := by
        rfl
      unfold NestedCallHead.scan
      rw [executableTailNil]
      simp only [head, List.length_nil, List.map_nil]
      change
        (resolveAlts
          (state.carrier.index.openConf.persistent.world.resolutionCandidates
            "q" 0)
          [] [] pCopied.result []
          state.carrier.index.runtime state.carrier.index.openConf.toConf.qterm
          (barrierDepth state.carrier.index.openConf.toConf + 1)
          state.carrier.index.openConf.toConf.counter).1 ≠ []
      rw [worldExact, qResolutionCandidates]
      have resultMatch :
          PLeaTTa.prologMatchCompat
              (PLeaTTa.subst state.carrier.index.runtime pCopied.result)
              (.var "x") = true := by
        generalize
          PLeaTTa.subst state.carrier.index.runtime pCopied.result = result
        cases result <;> rfl
      simp [resolveAlts, qExecutableClause, resultMatch,
        PLeaTTa.prologMatchCompatList]
    · intro count finish' branch' clause branchTail' clauseTail altTail
        copied pulls frontier'
      have finishNonempty : finish'.remaining ≠ [] := by
        rw [frontier'.finishRemaining]
        simp
      have pathExact :=
        _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
          openedSingleton pulls finishNonempty
      have branchExact' : branch' = qPreparedBranch := by
        have remaining := frontier'.finishRemaining
        rw [pathExact.2, openedSingleton] at remaining
        exact (List.cons.inj remaining).1.symm
      refine ⟨qSourceExtension, ?_, ?_⟩
      · simpa [branchExact'] using qPreparedBranch_resolves
      · rw [supportExact, qtermExact]
        intro identity name member
        simp only [rootAlpha, List.mem_singleton] at member
        have identityEq : identity = queryIdentity := congrArg Prod.fst member
        have nameEq : name = "z" := congrArg Prod.snd member
        subst identity
        subst name
        exact PLeaTTa.isTrimRoot_qterm_mem _ queryAtom "z"
          (by simp [queryAtom, Metta.Atom.vars])
    · simp [head, BuiltinThrowCall]
    · rfl
  have ready : MaterializedNestedCallReady state head := by
    refine
      { toNestedCallOperationalReady := operational
        materialized := ?_ }
    change
      MaterializedCallAgreesWith nextAlpha pSourceExtension
        [(.variable (.generated 0) : Term)] []
        (PLeaTTa.subst
          (PLeaTTa.trimFor pCopied.body queryAtom installed) pCopied.result)
        (flattened ++ representative) []
    exact materialized
  refine
    ⟨state, head, ready, rfl, rfl, rfl, rfl, rfl, rfl, currentExact,
      databaseExact, worldExact, ?_, nextFreshOne, counterOne, ?_, ?_⟩
  · simpa [head] using openedSingleton
  · rw [sourceExact]
    exact rootSourceSteps
  · rw [fineExact]
    exact rootFineSteps

/-- The rooted non-ground `p(Z) :- q(Z)` execution reaches and activates the
second local clause with exact finite-prefix accounting.

The two independent source clause copies consume disjoint intervals
`[0, 1)` and `[1, 2)`.  The final source substitution is the ordered
composition `Z ↦ generated 0 ↦ generated 1`; the executable alpha frontier
is simultaneously valid at counter two.  Both lanes share the same literal
middle and final representative carriers. -/
theorem reachable_unbound_p_q_exact_prefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before after : RepresentativeActivePayloadState,
      StepsN 2
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          before.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 3
          (.ready initialOpenConf) before.carrier.fineState ∧
        before.carrier.index.session.resolver.nextFresh = 1 ∧
        AlphaFreshFrontier before.carrier.index.alpha 1 1 ∧
        StepsN 4
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] []),
            .opened
              (requestFor "q" [(.variable (.generated 0) : Term)]
                pSourceExtension)]
          after.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 6
          (.ready initialOpenConf) after.carrier.fineState ∧
        after.carrier.index.current = qSourceExtension ∧
        after.carrier.index.session.resolver.nextFresh = 2 ∧
        AlphaFreshFrontier after.carrier.index.alpha 2 2 ∧
        AlphaExtendsAbove before.carrier.index.alpha
          after.carrier.index.alpha 1 1 ∧
        (∃ extension : TreeSubstitution,
          after.representative = extension ++ before.representative) ∧
        NestedCallPushes prog gt
          [(0,
            requestFor "q" [(.variable (.generated 0) : Term)]
              pSourceExtension)]
          before after := by
  obtain
    ⟨before, head, ready, qPredicate, qPayload, qReferenceRest, qArguments,
      qResult, qExecutableRest, beforeCurrent, beforeDatabase, _beforeWorld,
      openedSingleton, beforeNextFresh, beforeCounter, rootSourceSteps,
      rootFineSteps⟩ :=
    qMaterializedReadyAfterP (prog := prog) (gt := gt)
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  have finishNonempty : finish.remaining ≠ [] := by
    rw [facts.frontier.finishRemaining]
    simp
  have pathExact :=
    _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton facts.pulls finishNonempty
  have countZero : count = 0 := pathExact.1
  have branchExact : branch = qPreparedBranch := by
    have remaining := facts.frontier.finishRemaining
    rw [pathExact.2, openedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have afterCurrent : after.carrier.index.current = qSourceExtension := by
    have exactResolution : HeadResolution branch qSourceExtension := by
      simpa [branchExact] using qPreparedBranch_resolves
    exact HeadResolution.deterministic facts.resolution exactResolution
  have beforeFrontier :
      AlphaFreshFrontier before.carrier.index.alpha 1 1 := by
    have actual := ready.toNestedCallOperationalReady.alphaFresh
    simpa [beforeNextFresh, beforeCounter, OpenConf.toConf, Control.toConf] using
      actual
  have afterNextFresh :
      after.carrier.index.session.resolver.nextFresh = 2 := by
    rw [facts.sessionExact]
    change
      (prepareCall before.carrier.index.session.resolver
        (requestFor head.predicate head.referencePayload
          before.carrier.index.current)).2.nextFresh = 2
    rw [qPredicate, qPayload, beforeCurrent]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible referenceDatabase.generation
        [(.variable (.generated 0) : Term)] pSourceExtension 1
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).2 = 2
    rw [qVisibleClauses]
    rfl
  have afterFrontier :
      AlphaFreshFrontier after.carrier.index.alpha 2 2 := by
    have beforeCounterConf :
        before.carrier.index.openConf.toConf.counter = 1 := by
      change before.carrier.index.openConf.persistent.counter = 1
      exact beforeCounter
    simpa [branchExact, qPreparedBranch, beforeCounterConf] using
      facts.selectionFresh
  have afterExtension :
      AlphaExtendsAbove before.carrier.index.alpha
        after.carrier.index.alpha 1 1 := by
    have beforeCounterConf :
        before.carrier.index.openConf.toConf.counter = 1 := by
      change before.carrier.index.openConf.persistent.counter = 1
      exact beforeCounter
    simpa [branchExact, qPreparedBranch, beforeCounterConf] using
      facts.alphaExtension
  have qCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "q" [(.variable (.generated 0) : Term)] pSourceExtension)
        before.carrier after.carrier := by
    simpa [countZero, qPredicate, qPayload, beforeCurrent] using
      facts.certificate
  have sourceSteps := StepsN.trans rootSourceSteps qCertificate.sourceSteps
  have fineSteps :=
    DemandDrivenCallStep.StepsN.trans rootFineSteps qCertificate.fineSteps
  have singletonChain :
      NestedCallPushes prog gt
        [(0,
          requestFor "q" [(.variable (.generated 0) : Term)]
            pSourceExtension)]
        before after := by
    have raw := NestedCallPushes.snoc
      (NestedCallPushes.nil (prog := prog) (gt := gt) before) facts
    simpa [countZero, qPredicate, qPayload, beforeCurrent] using raw
  refine
    ⟨before, after, rootSourceSteps, rootFineSteps, beforeNextFresh,
      beforeFrontier, ?_, ?_, afterCurrent, afterNextFresh, afterFrontier,
      afterExtension, facts.representativeExtension, singletonChain⟩
  · simpa using sourceSteps
  · simpa using fineSteps

end PLeaTTa.PrologUnboundNestedCallRegression
