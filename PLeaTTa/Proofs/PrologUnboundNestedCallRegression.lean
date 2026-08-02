-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologUnboundNestedCallRegression
Purpose: Exercise the representative-preserving nested-call bridge on a
  reachable non-ground p(Z) :- q(Z) prefix.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge

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
open PrologHeterogeneousPrefixBridge
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

theorem qResolutionCandidates :
    executableWorld.resolutionCandidates "q" 0 = [qExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, qExecutableClause, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [Database.empty.allocate pReferenceClause] := by
  rfl

theorem qVisibleClauses :
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

theorem qCandidateBank :
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

private theorem pCopied_params : pCopied.params = [] := by
  rfl

private theorem pCopied_result :
    pCopied.result = .var ("x" ++ PLeaTTa.resolutionCompactSuffix 0) := by
  simp [pCopied, pExecutableClause, PLeaTTa.freshenResolutionClause,
    PLeaTTa.resolutionFreshSuffix, initialOpenConf, OpenConf.toConf,
    Control.toConf, PLeaTTa.renameAtomSuffix_var]

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
        RejectedPullsN 0
          (openedFor initialSession "p" [queryTerm] []).cursor finish ∧
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
      (by simpa [rejectsZero] using facts.pulls),
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
theorem qMaterializedReadyAfterP
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
        head.executableTail = [] ∧
        state.carrier.index.current = pSourceExtension ∧
        state.carrier.index.support = rootAlpha ∧
        AlphaTermAgrees state.carrier.index.alpha queryTerm queryAtom ∧
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote queryTerm) ∧
        state.carrier.index.qterm = queryAtom ∧
        state.carrier.index.openConf.control.qterm = queryAtom ∧
        state.carrier.index.callerReferences = [] ∧
        state.carrier.index.callerExecutables = [] ∧
        state.carrier.index.outer = [] ∧
        state.carrier.index.baseAlts = [] ∧
        state.carrier.index.openConf.frames = [] ∧
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
          (.ready initialOpenConf) state.carrier.fineState ∧
        PLeaTTa.subst state.carrier.index.runtime
            state.carrier.index.openConf.control.qterm = pCopied.result ∧
        PLeaTTa.subst state.carrier.index.runtime pCopied.result =
          pCopied.result := by
  obtain
    ⟨finish, branch, branchTail, altTail, copied, representative, nextAlpha,
      sourceCanonical, flattened, installed, branchExact, copiedExact,
      frontier, rootPulls, oldCumulative, materializedAtOpen, activation,
      rootSourceSteps, rootFineSteps, materialized, _rawUnsupported⟩ :=
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
  have finishPositioned :
      CallScopedCursorPosition
        (openedFor initialSession "p" [queryTerm] []).cursor finish 0 :=
    CallScopedCursorPosition.afterRejected rootPulls
      (CallScopedCursorPosition.refl
        (openedFor initialSession "p" [queryTerm] []).cursor)
  have retainedPositioned :
      CallScopedCursorPosition
        (openedFor initialSession "p" [queryTerm] []).cursor
        (finish.advance pPreparedBranch branchTail) 1 := by
    simpa using finishPositioned.advance frontier.finishRemaining
  obtain
      ⟨active, payloadContext, agreement, _outerExact,
        _snapshotRepresentative⟩ :=
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
      (prog := prog) (gt := gt) (alpha := rootAlpha) (support := rootAlpha)
      (canonical := []) (referenceBase := []) (referenceBindings := [])
      (argsv := []) (args := []) (res := queryAtom)
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (binding := []) (qterm := queryAtom)
      (callerBarrier := 0) (callerScope := rootScope)
      (outerScope := rootScope) (resources := []) (context := [])
      1 retainedPositioned frontier preHeadPayload oldCumulative
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
  have queryReading :
      AlphaTermAgrees state.carrier.index.alpha queryTerm queryAtom := by
    change AlphaTermAgrees nextAlpha queryTerm queryAtom
    exact
      AlphaTermAgrees.variable
        (activation.alphaIncluded (queryIdentity, "z")
          (by simp [rootAlpha, queryIdentity]))
  have querySupported :
      AlphaTreeSupported state.carrier.index.alpha
        state.carrier.index.support (Term.denote queryTerm) := by
    change AlphaTreeSupported nextAlpha rootAlpha (Term.denote queryTerm)
    change
      ∀ name, (queryIdentity, name) ∈ nextAlpha →
        (queryIdentity, name) ∈ rootAlpha
    intro name member
    rcases activation.alphaExtension with
      ⟨suffix, nextAlphaExact, generated, _referenceAbove,
        _executableAbove⟩
    rw [nextAlphaExact, List.mem_append] at member
    rcases member with old | fresh
    · exact old
    · obtain ⟨index, identityExact⟩ :=
        generated queryIdentity name fresh
      simp [queryIdentity] at identityExact
  have qtermExact : state.carrier.index.qterm = queryAtom := by
    rfl
  have openQtermExact :
      state.carrier.index.openConf.control.qterm = queryAtom := by
    change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
        pPending pCopied [] queryAtom installed).qterm = queryAtom
    calc
      _ = pPending.pulled.toConf.qterm := by
        exact
          PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor_qterm
            pPending pCopied [] queryAtom installed
      _ = pPending.installed.toConf.qterm := by
        rw [frontier.pulledExact]
      _ = pPending.outer.qterm := rfl
      _ = initialOpenConf.control.qterm := by
        rw [pEntry.entry.outer]
      _ = initialOpenConf.toConf.qterm := rfl
      _ = queryAtom := frontier.queryTerm.symm
  have runtimeQueryExact :
      PLeaTTa.subst state.carrier.index.runtime
          state.carrier.index.openConf.control.qterm = pCopied.result := by
    rw [openQtermExact]
    change
      PLeaTTa.subst (PLeaTTa.trimFor pCopied.body queryAtom installed)
        queryAtom = pCopied.result
    obtain ⟨base, args, result, pulledHead, headMgu⟩ := activation.headMgu
    rw [frontier.pulledExact] at pulledHead
    have pairExact := Option.some.inj pulledHead
    have baseExact : base = [] :=
      (congrArg Prod.snd pairExact).symm
    subst base
    have goalsExact := congrArg Prod.fst pairExact
    have headExact := (List.cons.inj goalsExact).1
    have operandsExact : args ++ [result] = [queryAtom] := by
      injection headExact with leftExact _rightExact
      injection leftExact with valuesExact
      exact valuesExact.symm
    obtain ⟨generated, generatedExact, generatedAgrees⟩ := headMgu
    have expectedGenerated :
        PLeaTTa.unifyTopExact (.expr [queryAtom])
            (.expr (pCopied.params ++ [pCopied.result])) =
          some [("z", pCopied.result)] := by
      rw [pCopied_params, pCopied_result]
      have nameNe :
          "z" ≠ "x" ++ PLeaTTa.resolutionCompactSuffix 0 := by
        decide
      unfold PLeaTTa.unifyTopExact
      simp [queryAtom, Metta.Unify.unifyTopWith, Atom.size,
        Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
        Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
        Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase, nameNe]
    rw [operandsExact] at generatedExact
    simp [PLeaTTa.subst_nil] at generatedExact
    rw [expectedGenerated] at generatedExact
    have generatedValue : generated = [("z", pCopied.result)] :=
      (Option.some.inj generatedExact).symm
    obtain ⟨generatedTopological⟩ := generatedAgrees.topological
    have installedTopological : PLeaTTa.SubstTopological installed := by
      rw [generatedAgrees.installedShape]
      exact
        PrologMguComposition.installGeneratedTopological
          emptyRuntimeTopological generatedTopological
          generatedAgrees.avoidsBase
    have queryRoot :
        ∀ name, name ∈ queryAtom.vars →
          PLeaTTa.isTrimRoot pCopied.body queryAtom name = true := by
      intro name member
      exact PLeaTTa.isTrimRoot_qterm_mem pCopied.body queryAtom name member
    rw [PLeaTTa.subst_trimFor_eq_of_topological pCopied.body queryAtom
      installed installedTopological queryAtom queryRoot]
    rw [generatedAgrees.installedShape]
    rw [PrologMguComposition.subst_installGenerated_eq_generated_after_base
      emptyRuntimeTopological generatedTopological generatedAgrees.avoidsBase
      queryAtom]
    rw [PLeaTTa.subst_nil, generatedValue]
    have expectedTopological :
        PLeaTTa.SubstTopological [("z", pCopied.result)] := by
      simpa [generatedValue] using generatedTopological
    have rootLookup :
        Metta.Subst.lookup [("z", pCopied.result)] "z" =
          some pCopied.result := by
      simp [Metta.Subst.lookup]
    change
      PLeaTTa.subst [("z", pCopied.result)] (.var "z") = pCopied.result
    calc
      _ = PLeaTTa.subst [("z", pCopied.result)] pCopied.result :=
        expectedTopological.subst_var_of_lookup
          [("z", pCopied.result)] "z" pCopied.result rootLookup
      _ = pCopied.result := by
        rw [pCopied_result]
        apply PLeaTTa.subst_var_of_lookup_none
        decide
  have runtimeResultFixed :
      PLeaTTa.subst state.carrier.index.runtime pCopied.result =
        pCopied.result := by
    obtain ⟨runtimeTopological⟩ := state.cumulative.runtimeTopological
    have resultLookupNone :
        Metta.Subst.lookup state.carrier.index.runtime
            ("x" ++ PLeaTTa.resolutionCompactSuffix 0) = none := by
      apply runtimeTopological.subst_resolvesDomain
        state.carrier.index.runtime
        state.carrier.index.openConf.control.qterm
      rw [runtimeQueryExact, pCopied_result]
      simp [Metta.Atom.vars]
    rw [pCopied_result]
    exact PLeaTTa.subst_var_of_lookup_none
      state.carrier.index.runtime
      ("x" ++ PLeaTTa.resolutionCompactSuffix 0) resultLookupNone
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
    ⟨state, head, ready, rfl, rfl, rfl, rfl, rfl, rfl, rfl, currentExact,
      supportExact, queryReading, querySupported, qtermExact, openQtermExact,
      rfl, rfl, rfl, rfl, rfl, databaseExact, worldExact, ?_, nextFreshOne,
      counterOne, ?_, ?_, runtimeQueryExact, runtimeResultFixed⟩
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
          before after ∧
        after.carrier.index.bodyReferences = [] ∧
        after.carrier.index.bodyExecutables = [] ∧
        after.carrier.index.callerReferences = [] ∧
        (∀ segment, segment ∈ after.carrier.index.outer →
          segment.references = []) ∧
        after.carrier.index.baseAlts = [] ∧
        after.carrier.index.openConf.frames = [] ∧
        after.carrier.index.qterm = queryAtom ∧
        after.carrier.index.openConf.control.qterm = queryAtom ∧
        AlphaTermAgrees after.carrier.index.alpha queryTerm queryAtom ∧
        AlphaTermsSupported after.carrier.index.alpha
          after.carrier.index.support [queryTerm] ∧
        after.carrier.index.current.applyTerm queryTerm =
          .variable (.generated 1) ∧
        after.carrier.index.current.applyTerm queryTerm ≠ queryTerm ∧
        PLeaTTa.subst after.carrier.index.runtime
            after.carrier.index.openConf.control.qterm =
          .var ("x" ++ PLeaTTa.resolutionCompactSuffix 1) ∧
        PLeaTTa.subst after.carrier.index.runtime
            after.carrier.index.openConf.control.qterm ≠
          after.carrier.index.openConf.control.qterm := by
  obtain
    ⟨before, head, ready, qPredicate, qPayload, qReferenceRest, qArguments,
      qResult, qExecutableRest, _qExecutableTail, beforeCurrent, beforeSupport,
      beforeQueryReading, _beforeQuerySupported, beforeQterm,
      beforeOpenQterm, beforeCallerReferences, _beforeCallerExecutables,
      beforeOuter, beforeBaseAlts, beforeFrames,
      beforeDatabase, beforeWorld, openedSingleton, beforeNextFresh,
      beforeCounter, rootSourceSteps, rootFineSteps, beforeRuntimeQueryExact,
      beforeRuntimeResultFixed⟩ :=
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
  have afterBodyReferences :
      after.carrier.index.bodyReferences = [] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have skippedClausesNil : skippedClauses = [] := by
    cases skippedClauses with
    | nil => rfl
    | cons skipped skippedTail =>
        have impossible := facts.executableSkipCount
        rw [countZero] at impossible
        simp at impossible
  have clauseExact : clause = qExecutableClause := by
    have bank := facts.executableBank
    rw [qPredicate, qArguments, beforeWorld, skippedClausesNil] at bank
    simp only [List.length_nil] at bank
    rw [qResolutionCandidates] at bank
    exact (List.cons.inj bank).1.symm
  have afterBodyExecutables :
      after.carrier.index.bodyExecutables = [] := by
    rw [facts.bodyExecutables, facts.frontier.copiedExact, clauseExact]
    rfl
  have afterCallerReferences :
      after.carrier.index.callerReferences = [] := by
    rw [facts.callerReferences, qReferenceRest]
  have afterOuterReferences :
      ∀ segment, segment ∈ after.carrier.index.outer →
        segment.references = [] := by
    intro segment member
    rw [facts.outerSegments, beforeCallerReferences, beforeOuter] at member
    simp only [List.mem_singleton] at member
    subst segment
    rfl
  have afterBaseAlts : after.carrier.index.baseAlts = [] := by
    rw [facts.baseAltsPreserved, beforeBaseAlts]
  have afterFrames : after.carrier.index.openConf.frames = [] := by
    rw [facts.openConfExact]
    simpa [NestedCallHead.pending] using beforeFrames
  have afterQterm : after.carrier.index.qterm = queryAtom := by
    rw [facts.qtermPreserved, beforeQterm]
  have afterOpenQterm :
      after.carrier.index.openConf.control.qterm = queryAtom := by
    rw [facts.openConfExact]
    change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
        head.pending copied head.executableTail before.carrier.index.qterm
        installed).qterm = queryAtom
    calc
      _ = head.pending.pulled.toConf.qterm := by
        exact
          PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor_qterm
            head.pending copied head.executableTail before.carrier.index.qterm
              installed
      _ = head.pending.installed.toConf.qterm := by
        rw [facts.frontier.pulledExact]
      _ = head.pending.outer.qterm := rfl
      _ = before.carrier.index.openConf.control.qterm := rfl
      _ = queryAtom := beforeOpenQterm
  have beforeCounterConf :
      before.carrier.index.openConf.toConf.counter = 1 := by
    change before.carrier.index.openConf.persistent.counter = 1
    exact beforeCounter
  have copiedParams : copied.params = [] := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have copiedResult :
      copied.result =
        .var ("x" ++ PLeaTTa.resolutionCompactSuffix 1) := by
    rw [facts.frontier.copiedExact, clauseExact,
      facts.frontier.startCounterExact, beforeCounterConf]
    simp [PLeaTTa.freshenResolutionClause, qExecutableClause,
      PLeaTTa.resolutionFreshSuffix, PLeaTTa.renameAtomSuffix_var]
  have copiedResultFixed :
      PLeaTTa.subst before.carrier.index.runtime copied.result =
        copied.result := by
    have freshLookup :=
      resolutionFreshSuffix_lookup_none
        _ _ _ _ _ _ facts.frontier.highWater "x"
    have exactLookup :
        Metta.Subst.lookup before.carrier.index.runtime
            ("x" ++ PLeaTTa.resolutionCompactSuffix 1) = none := by
      simpa [PLeaTTa.resolutionFreshSuffix,
        facts.frontier.startCounterExact, beforeCounterConf] using freshLookup
    rw [copiedResult]
    exact PLeaTTa.subst_var_of_lookup_none
      before.carrier.index.runtime
      ("x" ++ PLeaTTa.resolutionCompactSuffix 1) exactLookup
  have afterRuntimeQueryExact :
      PLeaTTa.subst after.carrier.index.runtime
          after.carrier.index.openConf.control.qterm = copied.result := by
    obtain ⟨_extension, _representativeExact, pendingMgu⟩ :=
      facts.generatedMguExtension
    obtain ⟨base, args, result, pulledHead, headMgu⟩ := pendingMgu
    rw [facts.frontier.pulledExact] at pulledHead
    have pairExact := Option.some.inj pulledHead
    have baseExact : base = before.carrier.index.runtime :=
      (congrArg Prod.snd pairExact).symm
    subst base
    have goalsExact := congrArg Prod.fst pairExact
    have headExact := (List.cons.inj goalsExact).1
    have operandsExact : args ++ [result] = [pCopied.result] := by
      injection headExact with leftExact _rightExact
      injection leftExact with valuesExact
      rw [qArguments, qResult] at valuesExact
      exact valuesExact.symm
    obtain ⟨generated, generatedExact, generatedAgrees⟩ := headMgu
    have expectedGenerated :
        PLeaTTa.unifyTopExact (.expr [pCopied.result])
            (.expr [copied.result]) =
          some [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)] := by
      rw [pCopied_result, copiedResult]
      have nameNe :
          "x" ++ PLeaTTa.resolutionCompactSuffix 0 ≠
            "x" ++ PLeaTTa.resolutionCompactSuffix 1 := by
        decide
      unfold PLeaTTa.unifyTopExact
      simp [Metta.Unify.unifyTopWith, Atom.size,
        Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
        Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
        Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase, nameNe]
    rw [operandsExact, copiedParams] at generatedExact
    simp only [List.map_singleton, List.nil_append,
      beforeRuntimeResultFixed, copiedResultFixed] at generatedExact
    rw [expectedGenerated] at generatedExact
    have generatedValue :
        generated =
          [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)] :=
      (Option.some.inj generatedExact).symm
    obtain ⟨beforeRuntimeTopological⟩ := before.cumulative.runtimeTopological
    obtain ⟨generatedTopological⟩ := generatedAgrees.topological
    have installedTopological : PLeaTTa.SubstTopological installed := by
      rw [generatedAgrees.installedShape]
      exact
        PrologMguComposition.installGeneratedTopological
          beforeRuntimeTopological generatedTopological
          generatedAgrees.avoidsBase
    have queryRoot :
        ∀ name, name ∈ queryAtom.vars →
          PLeaTTa.isTrimRoot
            (copied.body ++ head.executableTail)
            before.carrier.index.qterm name = true := by
      intro name member
      rw [beforeQterm]
      exact
        PLeaTTa.isTrimRoot_qterm_mem
          (copied.body ++ head.executableTail) queryAtom name member
    rw [afterOpenQterm, facts.runtimeExact]
    rw [PLeaTTa.subst_trimFor_eq_of_topological
      (copied.body ++ head.executableTail) before.carrier.index.qterm
      installed installedTopological queryAtom queryRoot]
    rw [generatedAgrees.installedShape]
    rw [PrologMguComposition.subst_installGenerated_eq_generated_after_base
      beforeRuntimeTopological generatedTopological
      generatedAgrees.avoidsBase queryAtom]
    have beforeRuntimeQueryAtomExact :
        PLeaTTa.subst before.carrier.index.runtime queryAtom =
          pCopied.result := by
      rw [← beforeOpenQterm]
      exact beforeRuntimeQueryExact
    rw [beforeRuntimeQueryAtomExact, generatedValue]
    have expectedTopological :
        PLeaTTa.SubstTopological
          [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)] := by
      simpa [generatedValue] using generatedTopological
    have rootLookup :
        Metta.Subst.lookup
            [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)]
            ("x" ++ PLeaTTa.resolutionCompactSuffix 0) =
          some copied.result := by
      simp [Metta.Subst.lookup]
    rw [pCopied_result]
    calc
      _ = PLeaTTa.subst
          [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)]
          copied.result :=
        expectedTopological.subst_var_of_lookup
          [("x" ++ PLeaTTa.resolutionCompactSuffix 0, copied.result)]
          ("x" ++ PLeaTTa.resolutionCompactSuffix 0) copied.result rootLookup
      _ = copied.result := by
        rw [copiedResult]
        apply PLeaTTa.subst_var_of_lookup_none
        decide
  have afterRuntimeValueExact :
      PLeaTTa.subst after.carrier.index.runtime
          after.carrier.index.openConf.control.qterm =
        .var ("x" ++ PLeaTTa.resolutionCompactSuffix 1) := by
    rw [afterRuntimeQueryExact, copiedResult]
  have afterRuntimeValueNontrivial :
      PLeaTTa.subst after.carrier.index.runtime
          after.carrier.index.openConf.control.qterm ≠
        after.carrier.index.openConf.control.qterm := by
    rw [afterRuntimeValueExact, afterOpenQterm]
    intro equality
    change
      Atom.var ("x" ++ PLeaTTa.resolutionCompactSuffix 1) =
        Atom.var "z" at equality
    injection equality with nameEquality
    have nameNe :
        "x" ++ PLeaTTa.resolutionCompactSuffix 1 ≠ "z" := by
      decide
    exact nameNe nameEquality
  have afterQueryReading :
      AlphaTermAgrees after.carrier.index.alpha queryTerm queryAtom :=
    AlphaTermAgrees.mono afterExtension.included beforeQueryReading
  have afterQuerySupported :
      AlphaTermsSupported after.carrier.index.alpha
        after.carrier.index.support [queryTerm] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    rw [facts.supportPreserved, beforeSupport]
    change
      ∀ name, (queryIdentity, name) ∈ after.carrier.index.alpha →
        (queryIdentity, name) ∈ rootAlpha
    intro name linked
    have beforeRootLinked :
        (queryIdentity, "z") ∈ before.carrier.index.alpha := by
      change
        AlphaTermAgrees before.carrier.index.alpha
          (.variable queryIdentity) (.var "z") at beforeQueryReading
      cases beforeQueryReading with
      | «variable» rootLinked => exact rootLinked
    have rootLinked :
        (queryIdentity, "z") ∈ after.carrier.index.alpha :=
      afterExtension.included _ beforeRootLinked
    have shared :=
      after.carrier.agreement.core.control.ready.2.2.2.headPayload.data.alphaShared
    have nameExact : name = "z" := shared.forward linked rootLinked
    subst name
    simp [rootAlpha, queryIdentity]
  have afterMaterialized :
      after.carrier.index.current.applyTerm queryTerm =
        .variable (.generated 1) := by
    rw [afterCurrent]
    rfl
  have afterMaterializedNontrivial :
      after.carrier.index.current.applyTerm queryTerm ≠ queryTerm := by
    rw [afterMaterialized]
    simp [queryTerm, queryIdentity]
  refine
    ⟨before, after, rootSourceSteps, rootFineSteps, beforeNextFresh,
      beforeFrontier, ?_, ?_, afterCurrent, afterNextFresh, afterFrontier,
      afterExtension, facts.representativeExtension, singletonChain,
      afterBodyReferences, afterBodyExecutables, afterCallerReferences,
      afterOuterReferences, afterBaseAlts, afterFrames, afterQterm,
      afterOpenQterm, afterQueryReading, afterQuerySupported,
      afterMaterialized, afterMaterializedNontrivial,
      afterRuntimeValueExact, afterRuntimeValueNontrivial⟩
  · simpa using sourceSteps
  · simpa using fineSteps

/-! ## Unbounded nondegenerate self recursion -/

namespace SelfRecursive

/-- A single locally owned clause which recursively calls a freshly copied
version of its own output variable.  Unlike `loop :- loop`, every activation
reserves a nonempty source interval and extends the ordered MGU chain. -/
def referenceClause : LocalClause :=
  { predicate := "p"
    arguments := [.variable clauseIdentity]
    body := [.call "p" [.variable clauseIdentity]] }

def executableClause : PLeaTTa.Clause :=
  { params := []
    result := .var "x"
    body := [.call "p" [] (.var "x")] }

def database : Database := Database.empty.assertz referenceClause

def world : PWorld :=
  (default : PWorld).reindexClauses.appendProgClause
    ("p", executableClause)

private theorem clauseAgrees :
    LocalClauseAgrees referenceClause ("p", executableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := variableDefinedCallGoalsAgrees "p"
      support := ?_ }
  · exact
      ⟨[], .variable clauseIdentity, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · intro name
    simp [referenceClause, executableClause, clauseIdentity,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables,
      OpenBindingAgreement.logicVarExecutableName]

theorem database_relates_world : DatabaseRelatesWorld database world := by
  have related := emptyDatabaseRelatesIndexedWorld.assertz clauseAgrees
  simpa [database, world] using related

private theorem worldCoherent : world.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have appended :=
    PWorld.appendProgClause_coherent _ ("p", executableClause) root
  simpa [world] using appended

theorem resolutionCandidates :
    world.resolutionCandidates "p" 0 = [executableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ worldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [world, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, executableClause, emptyClauses]

theorem visibleClauses :
    database.visibleClausesAt database.generation "p" 1 =
      [Database.empty.allocate referenceClause] := by
  rfl

theorem candidateBank :
    SupportedCandidateBank "p"
      (database.visibleClausesAt database.generation "p" 1)
      (world.resolutionCandidates "p" 0) := by
  rw [visibleClauses, resolutionCandidates]
  let head : CandidateClauseAgrees "p"
      (Database.empty.allocate referenceClause) executableClause := by
    change LocalClauseAgrees referenceClause ("p", executableClause)
    exact clauseAgrees
  have encoding :
      EncodingInjectiveOn
        (Database.empty.allocate referenceClause).clause.variables := by
    simp [EncodingInjectiveOn, Database.allocate, referenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, clauseIdentity]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate referenceClause).clause.variables
        (Database.empty.allocate referenceClause).clause.variables
        head.body := by
    change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        [clauseIdentity] [clauseIdentity] head.body
    have bodyEq : head.body = variableDefinedCallGoalsAgrees "p" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact variableDefinedCallGoalsSupported "p"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

def initialSession : Session :=
  { resolver :=
      { database := database
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := world
        counter := 0 }
    control :=
      { cur := some ([.call "p" [] queryAtom], [])
        alts := []
        qterm := queryAtom } }

private def scan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] queryAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf scan.1 scan.2

private theorem entry :
    RepresentativeSupportedCallEntryRelates rootAlpha
      (openedFor initialSession "p" [queryTerm] []) initialOpenConf pending
      [] [] queryAtom [] [] queryAtom
      (barrierDepth initialOpenConf.toConf + 1)
      initialOpenConf.toConf.counter := by
  have databaseAgreement :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using database_relates_world
  have ready : initialOpenConf.persistent.world.clauseIndexReady = true := by
    rfl
  have scanned :
      resolveAlts
          (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
          [] [] queryAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = scan := by
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
      databaseAgreement ready "p" [queryTerm] [] rootAlpha [] queryAtom [] []
      scan.1 scan.2 (by rfl) (by rfl)
      (by
        calc
          _ = scan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (scan.1, scan.2) := (Prod.eta scan).symm)
      query candidateBank
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
    terminalResolutionSeedRev, initialOpenConf, OpenConf.toConf,
    Control.toConf]

private def copied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] []
    initialOpenConf.control.qterm initialOpenConf.toConf.counter
    (barrierDepth initialOpenConf.toConf + 1) executableClause

private theorem copied_body :
    copied.body = [.call "p" [] copied.result] := by
  rfl

private def alt : PLeaTTa.Alt :=
  .br
    (.eq (.expr [queryAtom])
        (.expr (copied.params ++ [copied.result])) :: copied.body)
    []

private theorem scanExact :
    scan = ([alt], initialOpenConf.toConf.counter + 1) := by
  unfold scan
  change
    resolveAlts (world.resolutionCandidates "p" 0) [] [] queryAtom
        [] [] queryAtom 1 0 =
      ([alt], 1)
  rw [resolutionCandidates]
  simp [resolveAlts, executableClause, queryAtom, alt, copied,
    initialOpenConf, OpenConf.toConf, Control.toConf, barrierDepth,
    PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList]

private theorem scanNonempty : pending.branches ≠ [] := by
  rw [pending, scanExact]
  exact List.cons_ne_nil _ _

def preparedBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate referenceClause).id
    callGeneration := database.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated 0))]
    headEquations := [(queryTerm, .variable (.generated 0))]
    body := [.call "p" [.variable (.generated 0)]]
    bindings := []
    firstFresh := 0
    nextFresh := 1 }

private theorem openedRemaining :
    (openedFor initialSession "p" [queryTerm] []).cursor.remaining =
      [preparedBranch] := by
  rfl

private theorem preparedBranch_resolves :
    HeadResolution preparedBranch pSourceExtension := by
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
  · simpa [preparedBranch, ClauseBranch.normalizedHeadEquations,
      extension, queryTerm] using computed
  · simp [pSourceExtension, extension, preparedBranch]

/-! ## A depth-indexed recursive source frontier -/

/-- The exact cumulative source substitution after entering the root clause
and then `depth` recursive clause occurrences.  Every recursive MGU is
prepended in the resolver's deterministic left-variable orientation. -/
def sourceChain : Nat → Substitution
  | 0 => pSourceExtension
  | depth + 1 =>
      ((.generated depth : LogicVar),
          .variable (.generated (depth + 1))) :: sourceChain depth

/-- Raising a generated-domain boundary preserves the domain invariant. -/
private theorem domainsBelow_mono {smaller larger : Nat}
    {bindings : Substitution}
    (below : Substitution.DomainsBelow smaller bindings)
    (ordered : smaller ≤ larger) :
    Substitution.DomainsBelow larger bindings := by
  induction bindings with
  | nil => trivial
  | cons binding bindings inductionHypothesis =>
      rcases binding with ⟨source, replacement⟩
      rcases below with ⟨sourceBelow, tailBelow⟩
      constructor
      · cases source with
        | source name => trivial
        | anonymous index => trivial
        | generated index =>
            change index < larger
            change index < smaller at sourceBelow
            omega
      · exact inductionHypothesis tailBelow

/-- All generated substitution domains are strictly older than the current
recursive tip.  This is the domain-only fact needed to show that the tip is
still unbound. -/
theorem sourceChain_domainsBelow (depth : Nat) :
    Substitution.DomainsBelow depth (sourceChain depth) := by
  induction depth with
  | zero =>
      simp [sourceChain, pSourceExtension, TreeSubstitution.reify,
        Substitution.DomainsBelow, LogicVar.GeneratedBelowBoundary,
        queryIdentity]
  | succ depth inductionHypothesis =>
      constructor
      · simp [LogicVar.GeneratedBelowBoundary]
      · exact domainsBelow_mono inductionHypothesis (Nat.le_succ depth)

/-- Applying the cumulative state cannot rewrite any generated variable at
or above the current recursive tip. -/
theorem sourceChain_apply_generated_of_le (depth index : Nat)
    (atLeast : depth ≤ index) :
    (sourceChain depth).applyTerm (.variable (.generated index)) =
      .variable (.generated index) := by
  exact Substitution.applyTerm_eq_self_of_generatedAtLeast
    (sourceChain_domainsBelow depth)
    (by simpa [Term.GeneratedAtLeast] using atLeast)

/-- The variables carried by the cumulative substitution have exclusive
generated ceiling `depth + 1`: the newest variable occurs as a range value,
while its domain remains absent. -/
theorem sourceChain_generatedCeiling (depth : Nat) :
    variablesGeneratedCeiling (substitutionVariables (sourceChain depth)) =
      depth + 1 := by
  induction depth with
  | zero =>
      simp [sourceChain, pSourceExtension, TreeSubstitution.reify,
        substitutionVariables, variablesGeneratedCeiling,
        logicVarGeneratedCeiling, queryIdentity, Tree.reify, termVariables]
  | succ depth inductionHypothesis =>
      simp [sourceChain, substitutionVariables, termVariables,
        variablesGeneratedCeiling, logicVarGeneratedCeiling,
        inductionHypothesis]

/-- The live recursive request has the same exclusive ceiling as its
cumulative state, so an incoming high-water of `depth + 1` needs no repair. -/
theorem recursiveRequest_generatedCeiling (depth : Nat) :
    (requestFor "p" [(.variable (.generated depth) : Term)]
      (sourceChain depth)).generatedCeiling = depth + 1 := by
  change
    max (depth + 1)
      (variablesGeneratedCeiling
        (substitutionVariables (sourceChain depth))) = depth + 1
  rw [sourceChain_generatedCeiling]
  exact Nat.max_self _

/-- The unique stored recursive clause occurrence prepared at the current
call start.  Its one-variable interval is literally
`[depth + 1, depth + 2)`. -/
def preparedAt (depth : Nat) : ClauseBranch :=
  { sourceId := (Database.empty.allocate referenceClause).id
    callGeneration := database.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated (depth + 1)))]
    headEquations :=
      [(.variable (.generated depth),
        .variable (.generated (depth + 1)))]
    body := [.call "p" [.variable (.generated (depth + 1))]]
    bindings := sourceChain depth
    firstFresh := depth + 1
    nextFresh := depth + 2 }

/-- Opening the recursive request from the exact persistent state reserves
precisely the next depth-indexed occurrence. -/
theorem openedRemainingAt (session : Session) (depth : Nat)
    (databaseExact : session.resolver.database = database)
    (freshExact : session.resolver.nextFresh = depth + 1) :
    (openedFor session "p" [(.variable (.generated depth) : Term)]
      (sourceChain depth)).cursor.remaining = [preparedAt depth] := by
  change
    (prepareCall session.resolver
      (requestFor "p" [(.variable (.generated depth) : Term)]
        (sourceChain depth))).1.remaining = [preparedAt depth]
  simp only [prepareCall]
  rw [databaseExact, freshExact, recursiveRequest_generatedCeiling]
  simp only [Nat.max_self, requestFor, List.length_singleton]
  rw [visibleClauses]
  rfl

/-- The same open operation advances the persistent high-water by exactly
one, past the newly frozen clause copy. -/
theorem openedNextFreshAt (session : Session) (depth : Nat)
    (databaseExact : session.resolver.database = database)
    (freshExact : session.resolver.nextFresh = depth + 1) :
    (openedFor session "p" [(.variable (.generated depth) : Term)]
      (sourceChain depth)).session.resolver.nextFresh = depth + 2 := by
  change
    (prepareCall session.resolver
      (requestFor "p" [(.variable (.generated depth) : Term)]
        (sourceChain depth))).2.nextFresh = depth + 2
  simp only [prepareCall]
  rw [databaseExact, freshExact, recursiveRequest_generatedCeiling]
  simp only [Nat.max_self, requestFor, List.length_singleton]
  rw [visibleClauses]
  rfl

/-- Ordered head resolution links the current tip to the newly reserved tip
and prepends that MGU to the complete cumulative source state. -/
theorem preparedAt_resolves (depth : Nat) :
    HeadResolution (preparedAt depth) (sourceChain (depth + 1)) := by
  let extension : TreeSubstitution :=
    [((.generated depth : LogicVar),
      .variable (.generated (depth + 1)))]
  have computed :
      ComputesDenotationalMgu
        [(.variable (.generated depth),
          .variable (.generated (depth + 1)))]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_left_variable (.generated depth)
      (.variable (.generated (depth + 1))) (by
        intro equality
        injection equality with identityEquality
        injection identityEquality with indexEquality
        omega) (by
          have distinct :
              (.generated (depth + 1) : LogicVar) ≠ .generated depth := by
            intro equality
            injection equality with indexEquality
            omega
          change
            decide
              ((.generated (depth + 1) : LogicVar) = .generated depth) =
              false
          simp [distinct])
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · simpa [preparedAt, ClauseBranch.normalizedHeadEquations, extension,
      sourceChain_apply_generated_of_le] using computed
  · simp [sourceChain, extension, preparedAt, TreeSubstitution.reify,
      Tree.reify]

/-! ## Semantic readiness at every recursive depth -/

/-- The facts preserved from one literal recursive activation to the next.

No successor or transition occurs in this structure.  In particular,
`RecursiveReadyAt` cannot prove progress by projecting a hidden step; it must
first reconstruct `MaterializedNestedCallReady` and invoke the certified
resolver producer. -/
structure RecursiveReadyAt (state : RepresentativeActivePayloadState)
    (depth : Nat) (executableResult : Atom) : Prop where
  bodyReferences :
    state.carrier.index.bodyReferences =
      [.call "p" [(.variable (.generated depth) : Term)]]
  bodyExecutables :
    state.carrier.index.bodyExecutables =
      [.call "p" [] executableResult]
  executableContinuation :
    flattenExecutables
      ({ barrier := state.carrier.index.callerBarrier
         references := state.carrier.index.callerReferences
         executables := state.carrier.index.callerExecutables } ::
       state.carrier.index.outer) = []
  current : state.carrier.index.current = sourceChain depth
  support : state.carrier.index.support = rootAlpha
  qterm : state.carrier.index.qterm = queryAtom
  openQterm : state.carrier.index.openConf.control.qterm = queryAtom
  database : state.carrier.index.session.resolver.database = SelfRecursive.database
  world : state.carrier.index.openConf.persistent.world = SelfRecursive.world
  nextFresh : state.carrier.index.session.resolver.nextFresh = depth + 1
  exactFresh :
    state.carrier.index.freshFrontier =
      AlphaFreshFrontier state.carrier.index.alpha
  below : ConfBelowResolutionCounter state.carrier.index.openConf.toConf
  materialized :
    MaterializedCallAgreesWith state.carrier.index.alpha
      (sourceChain depth)
      [(.variable (.generated depth) : Term)] []
      (PLeaTTa.subst state.carrier.index.runtime executableResult)
      state.representative state.carrier.index.referenceBase

namespace RecursiveReadyAt

/-- The semantic invariant reconstructs the next literal local-call producer
premises without selecting a successor. -/
theorem materializedReady
    {state : RepresentativeActivePayloadState} {depth : Nat}
    {executableResult : Atom}
    (ready : RecursiveReadyAt state depth executableResult) :
    ∃ head : NestedCallHead state.carrier,
      MaterializedNestedCallReady state head ∧
        head.predicate = "p" ∧
        head.referencePayload =
          [(.variable (.generated depth) : Term)] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = executableResult ∧
        head.executableRest = [] ∧
        head.executableTail = [] := by
  let head : NestedCallHead state.carrier :=
    { predicate := "p"
      referencePayload := [(.variable (.generated depth) : Term)]
      referenceRest := []
      arguments := []
      result := executableResult
      executableRest := []
      referenceHead := ready.bodyReferences
      executableHead := ready.bodyExecutables }
  have executableTailNil : head.executableTail = [] := by
    simp [NestedCallHead.executableTail, head, ready.executableContinuation]
  have openedSingleton :
      (openedFor state.carrier.index.session "p"
        [(.variable (.generated depth) : Term)]
        (sourceChain depth)).cursor.remaining = [preparedAt depth] :=
    openedRemainingAt state.carrier.index.session depth ready.database
      ready.nextFresh
  have operational : NestedCallOperationalReady state.carrier head := by
    refine
      { exactFresh := ready.exactFresh
        indexReady := ?_
        below := ready.below
        candidateSupported := ?_
        sourceNonempty := ?_
        scanNonempty := ?_
        selected := ?_
        notThrow := ?_
        notDatabase := ?_ }
    · rw [ready.world]
      rfl
    · change
        SupportedCandidateBank "p"
          (state.carrier.index.session.resolver.database.visibleClausesAt
            state.carrier.index.session.resolver.database.generation "p" 1)
          (state.carrier.index.openConf.persistent.world.resolutionCandidates
            "p" 0)
      simpa [ready.database, ready.world] using candidateBank
    · change
        state.carrier.index.session.resolver.database.visibleClausesAt
          state.carrier.index.session.resolver.database.generation "p" 1 ≠ []
      rw [ready.database, visibleClauses]
      simp
    · unfold NestedCallHead.scan
      rw [executableTailNil]
      simp only [head, List.length_nil, List.map_nil]
      rw [ready.world, resolutionCandidates]
      have resultMatch :
          PLeaTTa.prologMatchCompat
              (PLeaTTa.subst state.carrier.index.runtime
                executableResult)
              (.var "x") = true := by
        generalize
          PLeaTTa.subst state.carrier.index.runtime
            executableResult = result
        cases result <;> rfl
      simp [resolveAlts, executableClause, resultMatch,
        PLeaTTa.prologMatchCompatList]
    · intro count finish branch clause branchTail clauseTail altTail
        copied pulls frontier
      have finishNonempty : finish.remaining ≠ [] := by
        rw [frontier.finishRemaining]
        simp
      have pullsExact :
          RejectedPullsN count
            (openedFor state.carrier.index.session "p"
              [(.variable (.generated depth) : Term)]
              (sourceChain depth)).cursor finish := by
        simpa [head, ready.current] using pulls
      have pathExact :=
        _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
          openedSingleton pullsExact finishNonempty
      have branchExact : branch = preparedAt depth := by
        have remaining := frontier.finishRemaining
        rw [pathExact.2, openedSingleton] at remaining
        exact (List.cons.inj remaining).1.symm
      refine ⟨sourceChain (depth + 1), ?_, ?_⟩
      · simpa [branchExact] using preparedAt_resolves depth
      · rw [ready.support, ready.qterm]
        rw [executableTailNil]
        simp only [List.append_nil]
        intro identity name member
        simp only [rootAlpha, List.mem_singleton] at member
        have nameExact : name = "z" := congrArg Prod.snd member
        subst name
        exact PLeaTTa.isTrimRoot_qterm_mem copied.body queryAtom "z"
          (by simp [queryAtom, Metta.Atom.vars])
    · simp [head, BuiltinThrowCall]
    · rfl
  have materialized : MaterializedNestedCallReady state head := by
    refine
      { toNestedCallOperationalReady := operational
        materialized := ?_ }
    simpa [head, ready.current, executableTailNil] using ready.materialized
  exact
    ⟨head, materialized, rfl, rfl, rfl, rfl, rfl, rfl,
      executableTailNil⟩

/-- Every recursive invariant state exposes the producer-ready constructor
used by the generic exact-prefix induction. -/
theorem activeStepReady
    {state : RepresentativeActivePayloadState} {depth : Nat}
    {executableResult : Atom}
    (ready : RecursiveReadyAt state depth executableResult) :
    Nonempty
      (PLeaTTa.PrologHeterogeneousPrefixBridge.ActiveStepReady
        (.active state)) := by
  obtain ⟨head, materialized, _predicate, _payload, _referenceRest,
      _arguments, _result, _executableRest, _tail⟩ := ready.materializedReady
  exact
    ⟨PLeaTTa.PrologHeterogeneousPrefixBridge.ActiveStepReady.localCall
      state head materialized⟩

end RecursiveReadyAt

/-! ## Literal root seed -/

/-- The literal root task reaches the first recursive body head with the
semantic invariant at depth zero.  The source and fine counts retain the
entry/activation cost rather than beginning from a hand-constructed active
midstate. -/
theorem rootReady
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : RepresentativeActivePayloadState, ∃ result : Atom,
      RecursiveReadyAt state 0 result ∧
        StepsN 2
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          state.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 3
          (.ready initialOpenConf) state.carrier.fineState := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier rootAlpha)
        ExactControlFrontiers initialSession initialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [initialSession, initialOpenConf] using database_relates_world
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
        {selectedCopy : PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor initialSession "p" [queryTerm] []).cursor finish →
          RepresentativeRetainedCallFrontier rootAlpha
            (openedFor initialSession "p" [queryTerm] []) initialOpenConf
            pending finish branch clause branchTail clauseTail altTail
            selectedCopy [] [] queryAtom [] [] queryAtom
            (barrierDepth initialOpenConf.toConf + 1)
            initialOpenConf.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive rootAlpha selectedCopy.body queryAtom := by
    intro count finish branch clause branchTail clauseTail altTail
      selectedCopy pulls frontier
    have finishNonempty : finish.remaining ≠ [] := by
      rw [frontier.finishRemaining]
      simp
    have pathExact :=
      _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
        openedRemaining pulls finishNonempty
    have branchExact : branch = preparedBranch := by
      have remaining := frontier.finishRemaining
      rw [pathExact.2, openedRemaining] at remaining
      exact (List.cons.inj remaining).1.symm
    refine ⟨pSourceExtension, ?_, ?_⟩
    · simpa [branchExact] using preparedBranch_resolves
    · intro identity name member
      simp only [rootAlpha, List.mem_singleton] at member
      have nameExact : name = "z" := congrArg Prod.snd member
      subst name
      exact PLeaTTa.isTrimRoot_qterm_mem selectedCopy.body queryAtom "z"
        (by simp [queryAtom, Metta.Atom.vars])
  have notThrow : ¬ BuiltinThrowCall "p" [queryTerm] := by
    simp [BuiltinThrowCall]
  have notDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [queryTerm] = none := by
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, selectedCopy, independentResult,
        representative, nextAlpha, sourceCanonical, flattened, installed,
        after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      entry preHeadPayload rootPayloadSupported beforeSession (by rfl)
      (by rfl) initialBelow scanNonempty selected notThrow notDatabase
  have sourceShape := facts.sourceBank
  rw [openedRemaining] at sourceShape
  have sourceLengths := congrArg List.length sourceShape
  simp only [List.length_cons, List.length_nil, List.length_append] at sourceLengths
  have skippedBranchesLength : skippedBranches.length = 0 := by omega
  have branchTailLength : branchTail.length = 0 := by omega
  have skippedBranchesNil : skippedBranches = [] :=
    List.eq_nil_of_length_eq_zero skippedBranchesLength
  have branchTailNil : branchTail = [] :=
    List.eq_nil_of_length_eq_zero branchTailLength
  have branchExact : branch = preparedBranch := by
    subst skippedBranches
    subst branchTail
    simpa using sourceShape.symm
  have rejectsZero : rejects = 0 := by
    rw [← facts.sourceSkipCount]
    exact skippedBranchesLength
  have executableShape := facts.executableBank
  change
    world.resolutionCandidates "p" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [resolutionCandidates] at executableShape
  have executableLengths := congrArg List.length executableShape
  simp only [List.length_cons, List.length_nil, List.length_append] at executableLengths
  have skippedClausesLength : skippedClauses.length = 0 := by omega
  have clauseTailLength : clauseTail.length = 0 := by omega
  have skippedClausesNil : skippedClauses = [] :=
    List.eq_nil_of_length_eq_zero skippedClausesLength
  have clauseTailNil : clauseTail = [] :=
    List.eq_nil_of_length_eq_zero clauseTailLength
  have clauseExact : clause = executableClause := by
    subst skippedClauses
    subst clauseTail
    simpa using executableShape.symm
  have selectedCopyExact : selectedCopy = copied := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have currentExact :
      after.carrier.index.current = sourceChain 0 := by
    have selectedResolution :
        HeadResolution branch after.carrier.index.current := facts.resolution
    have expected : HeadResolution branch pSourceExtension := by
      simpa [branchExact] using preparedBranch_resolves
    simpa [sourceChain] using
      HeadResolution.deterministic selectedResolution expected
  have bodyReferences :
      after.carrier.index.bodyReferences =
        [.call "p" [Term.variable (LogicVar.generated 0)]] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have bodyExecutables :
      after.carrier.index.bodyExecutables = [.call "p" [] copied.result] := by
    rw [facts.bodyExecutables, selectedCopyExact, copied_body]
  have supportExact : after.carrier.index.support = rootAlpha :=
    facts.supportPreserved
  have qtermExact : after.carrier.index.qterm = queryAtom := by
    rw [facts.qtermPreserved]
    rfl
  have openQtermExact :
      after.carrier.index.openConf.control.qterm = queryAtom := by
    calc
      _ = after.carrier.index.qterm :=
        after.carrier.agreement.core.control.ready.2.2.1
      _ = queryAtom := qtermExact
  have databaseExact :
      after.carrier.index.session.resolver.database = SelfRecursive.database := by
    rw [facts.sessionExact]
    rfl
  have worldExact :
      after.carrier.index.openConf.persistent.world = SelfRecursive.world := by
    rw [facts.worldPreserved]
    rfl
  have nextFreshExact :
      after.carrier.index.session.resolver.nextFresh = 1 := by
    rw [facts.sessionExact]
    rfl
  have continuationEmpty :
      flattenExecutables
        ({ barrier := after.carrier.index.callerBarrier
           references := after.carrier.index.callerReferences
           executables := after.carrier.index.callerExecutables } ::
         after.carrier.index.outer) = [] := by
    rw [facts.callerExecutablesEmpty, facts.outerEmpty]
    rfl
  have materialized :
      MaterializedCallAgreesWith after.carrier.index.alpha
        (sourceChain 0) [Term.variable (LogicVar.generated 0)] []
        (PLeaTTa.subst after.carrier.index.runtime copied.result)
        after.representative after.carrier.index.referenceBase := by
    have exactHead := facts.materializedBodyHeads bodyReferences bodyExecutables
    simpa [currentExact] using exactHead
  have recursiveReady : RecursiveReadyAt after 0 copied.result :=
    { bodyReferences := bodyReferences
      bodyExecutables := bodyExecutables
      executableContinuation := continuationEmpty
      current := currentExact
      support := supportExact
      qterm := qtermExact
      openQterm := openQtermExact
      database := databaseExact
      world := worldExact
      nextFresh := nextFreshExact
      exactFresh := facts.freshFrontierExact
      below := facts.below
      materialized := materialized }
  refine ⟨after, copied.result, recursiveReady, ?_, facts.fineSteps⟩
  simpa [rejectsZero] using facts.sourceSteps

/-! ## One invariant-preserving recursive activation -/

/-- Eliminate one recursive invariant through the real resolver producer.

The returned `RepresentativeNestedCallSuccessorFacts` is retained verbatim,
so later composition can construct `CertifiedTransition.localCall` from the
same literal successor that carries the next invariant.  Singleton-bank
inversion additionally pins the selected source interval and executable
clause. -/
theorem RecursiveReadyAt.pushDetailed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState} {depth : Nat}
    {executableResult : Atom}
    (ready : RecursiveReadyAt before depth executableResult) :
    ∃ head : NestedCallHead before.carrier,
      ∃ _materializedReady : MaterializedNestedCallReady before head,
      ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ selectedCopy : PLeaTTa.Clause, ∃ installed : Subst,
      ∃ after : RepresentativeActivePayloadState,
        RepresentativeNestedCallSuccessorFacts prog gt before head count
            skippedBranches skippedClauses finish branch clause branchTail
            clauseTail altTail selectedCopy installed after ∧
          RecursiveReadyAt after (depth + 1) selectedCopy.result ∧
          count = 0 ∧
          branch = preparedAt depth ∧
          clause = executableClause ∧
          head.predicate = "p" ∧
          head.referencePayload =
            [(.variable (.generated depth) : Term)] := by
  obtain ⟨head, materializedReady, predicateExact, payloadExact,
      _referenceRest, argumentsExact, _resultExact, _executableRest,
      executableTailNil⟩ := ready.materializedReady
  obtain
      ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, selectedCopy, installed, after,
        facts⟩ :=
    materializedReady.pushDetailed (prog := prog) (gt := gt)
  have openedSingleton :
      (openedFor before.carrier.index.session "p"
        [(.variable (.generated depth) : Term)]
        (sourceChain depth)).cursor.remaining = [preparedAt depth] :=
    openedRemainingAt before.carrier.index.session depth ready.database
      ready.nextFresh
  have finishNonempty : finish.remaining ≠ [] := by
    rw [facts.frontier.finishRemaining]
    simp
  have pullsExact :
      RejectedPullsN count
        (openedFor before.carrier.index.session "p"
          [(.variable (.generated depth) : Term)]
          (sourceChain depth)).cursor finish := by
    simpa [predicateExact, payloadExact, ready.current] using facts.pulls
  have pathExact :=
    _root_.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton pullsExact finishNonempty
  have countZero : count = 0 := pathExact.1
  have branchExact : branch = preparedAt depth := by
    have remaining := facts.frontier.finishRemaining
    rw [pathExact.2, openedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have executableShape := facts.executableBank
  rw [predicateExact, argumentsExact, ready.world] at executableShape
  simp only [List.length_nil] at executableShape
  rw [resolutionCandidates] at executableShape
  have executableLengths := congrArg List.length executableShape
  simp only [List.length_cons, List.length_nil, List.length_append] at executableLengths
  have skippedClausesLength : skippedClauses.length = 0 := by omega
  have clauseTailLength : clauseTail.length = 0 := by omega
  have skippedClausesNil : skippedClauses = [] :=
    List.eq_nil_of_length_eq_zero skippedClausesLength
  have clauseTailNil : clauseTail = [] :=
    List.eq_nil_of_length_eq_zero clauseTailLength
  have clauseExact : clause = executableClause := by
    subst skippedClauses
    subst clauseTail
    simpa using executableShape.symm
  have selectedCopyBody :
      selectedCopy.body = [.call "p" [] selectedCopy.result] := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have currentExact :
      after.carrier.index.current = sourceChain (depth + 1) := by
    have expected : HeadResolution branch (sourceChain (depth + 1)) := by
      simpa [branchExact] using preparedAt_resolves depth
    exact HeadResolution.deterministic facts.resolution expected
  have bodyReferences :
      after.carrier.index.bodyReferences =
        [.call "p" [Term.variable (LogicVar.generated (depth + 1))]] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have bodyExecutables :
      after.carrier.index.bodyExecutables =
        [.call "p" [] selectedCopy.result] := by
    rw [facts.bodyExecutables, selectedCopyBody]
  have continuationEmpty :
      flattenExecutables
        ({ barrier := after.carrier.index.callerBarrier
           references := after.carrier.index.callerReferences
           executables := after.carrier.index.callerExecutables } ::
         after.carrier.index.outer) = [] := by
    exact facts.executableContinuation.trans executableTailNil
  have supportExact : after.carrier.index.support = rootAlpha := by
    exact facts.supportPreserved.trans ready.support
  have qtermExact : after.carrier.index.qterm = queryAtom := by
    exact facts.qtermPreserved.trans ready.qterm
  have openQtermExact :
      after.carrier.index.openConf.control.qterm = queryAtom := by
    calc
      _ = after.carrier.index.qterm :=
        after.carrier.agreement.core.control.ready.2.2.1
      _ = queryAtom := qtermExact
  have databaseExact :
      after.carrier.index.session.resolver.database = SelfRecursive.database := by
    rw [facts.sessionExact]
    simp [openedFor, predicateExact, payloadExact, ready.current,
      ready.database]
  have worldExact :
      after.carrier.index.openConf.persistent.world = SelfRecursive.world := by
    exact facts.worldPreserved.trans ready.world
  have nextFreshExact :
      after.carrier.index.session.resolver.nextFresh = depth + 2 := by
    rw [facts.sessionExact]
    simpa [predicateExact, payloadExact, ready.current] using
      openedNextFreshAt before.carrier.index.session depth ready.database
        ready.nextFresh
  have materialized :
      MaterializedCallAgreesWith after.carrier.index.alpha
        (sourceChain (depth + 1))
        [Term.variable (LogicVar.generated (depth + 1))] []
        (PLeaTTa.subst after.carrier.index.runtime selectedCopy.result)
        after.representative after.carrier.index.referenceBase := by
    have exactHead := facts.materializedBodyHeads bodyReferences bodyExecutables
    simpa [currentExact] using exactHead
  have nextReady :
      RecursiveReadyAt after (depth + 1) selectedCopy.result :=
    { bodyReferences := bodyReferences
      bodyExecutables := bodyExecutables
      executableContinuation := continuationEmpty
      current := currentExact
      support := supportExact
      qterm := qtermExact
      openQterm := openQtermExact
      database := databaseExact
      world := worldExact
      nextFresh := by simpa [Nat.add_assoc] using nextFreshExact
      exactFresh := facts.freshFrontierExact
      below := facts.below
      materialized := materialized }
  exact
    ⟨head, materializedReady, count, skippedBranches, skippedClauses, finish,
      branch, clause,
      branchTail, clauseTail, altTail, selectedCopy, installed, after, facts,
      nextReady, countZero, branchExact, clauseExact, predicateExact,
      payloadExact⟩

/-- The exact public request issued at one recursive depth. -/
def recursiveRequestAt (depth : Nat) : CallRequest :=
  requestFor "p" [(.variable (.generated depth) : Term)] (sourceChain depth)

/-- Every recursive activation is a zero-rejection local-call transition. -/
def recursiveKindAt (depth : Nat) : TransitionKind :=
  .localCall 0 (recursiveRequestAt depth)

/-- Compact one-step form of `pushDetailed`, retaining the certified
transition and exact payload-cell growth while hiding only the already-pinned
singleton scan data. -/
theorem RecursiveReadyAt.pushCertified
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState} {depth : Nat}
    {executableResult : Atom}
    (ready : RecursiveReadyAt before depth executableResult) :
    ∃ after : RepresentativeActivePayloadState, ∃ nextResult : Atom,
      ∃ _step : CertifiedTransition prog gt (recursiveKindAt depth)
          (.active before) (.active after),
        RecursiveReadyAt after (depth + 1) nextResult ∧
          ∃ cell : PayloadCellIdentity,
            after.carrier.cellIdentities =
              cell :: before.carrier.cellIdentities := by
  obtain
      ⟨head, _materializedReady, count, skippedBranches, skippedClauses, finish, branch,
        clause, branchTail, clauseTail, altTail, selectedCopy, installed,
        after, facts, nextReady, countZero, _branchExact, _clauseExact,
        predicateExact, payloadExact⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  have step :
      CertifiedTransition prog gt (recursiveKindAt depth)
        (.active before) (.active after) := by
    simpa [recursiveKindAt, recursiveRequestAt, countZero, predicateExact,
      payloadExact, ready.current] using
      (CertifiedTransition.localCall facts)
  obtain ⟨cell, cells⟩ := facts.certificate.payloadCells
  exact ⟨after, selectedCopy.result, step, nextReady, cell, cells⟩

/-! ## Arbitrary exact recursive prefixes -/

/-- The fixture-specific invariant over the heterogeneous phase carrier.
Only active states can inhabit it, and each carries an explicit recursion
depth plus the executable result atom selected by the certified compiler
lane. -/
def RecursiveInvariant : ProductPhaseState → Prop
  | .active state =>
      ∃ depth : Nat, ∃ executableResult : Atom,
        RecursiveReadyAt state depth executableResult
  | .scheduled _ | .committed _ => False

/-- Coupled progress and invariant preservation for the self-recursive local
clause.  The transition and next readiness share the literal `after` returned
by one invocation of `pushDetailed`. -/
theorem recursiveProgress
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ProgressPreservesReady prog gt RecursiveInvariant := by
  intro phase invariant
  cases phase with
  | scheduled state => simp [RecursiveInvariant] at invariant
  | committed state => simp [RecursiveInvariant] at invariant
  | active before =>
      change
        ∃ depth : Nat, ∃ executableResult : Atom,
          RecursiveReadyAt before depth executableResult at invariant
      obtain ⟨depth, executableResult, ready⟩ := invariant
      obtain
        ⟨head, materializedReady, count, skippedBranches, skippedClauses,
          finish, branch, clause, branchTail, clauseTail, altTail,
          selectedCopy, installed, after, facts, nextReady, _countZero,
          _branchExact, _clauseExact, _predicateExact, _payloadExact⟩ :=
        ready.pushDetailed (prog := prog) (gt := gt)
      refine
        ⟨.localCall before head materializedReady, .active after, ?_, ?_⟩
      · exact .localCall before head materializedReady facts
      · exact ⟨depth + 1, selectedCopy.result, nextReady⟩

/-- From the literal root task, every requested finite number of recursive
local-call activations has one exact Type-valued prefix.  The endpoint remains
producer-ready; no totality, fuel, or choice principle selects an infinite
run. -/
theorem arbitrary_recursive_prefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ root : RepresentativeActivePayloadState, ∃ result : Atom,
      RecursiveReadyAt root 0 result ∧
        StepsN 2
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          root.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 3
          (.ready initialOpenConf) root.carrier.fineState ∧
        ∀ count : Nat,
          ∃ kinds : List TransitionKind, ∃ after : ProductPhaseState,
            kinds.length = count ∧
              ∃ _run : CertifiedPrefix prog gt kinds (.active root) after,
                RecursiveInvariant after ∧ Nonempty (ActiveStepReady after) := by
  obtain ⟨root, result, ready, sourceSteps, fineSteps⟩ :=
    rootReady (prog := prog) (gt := gt)
  have invariant : RecursiveInvariant (.active root) :=
    ⟨0, result, ready⟩
  refine ⟨root, result, ready, sourceSteps, fineSteps, ?_⟩
  exact
    ActiveStepReady.exists_prefix_of_ready
      (recursiveProgress (prog := prog) (gt := gt)) invariant

/-! ## Nondegenerate depth-four witness -/

/-- Four literal recursive activations witness that arbitrary readiness is
not coming from a stationary self-loop.

The source allocator advances through four disjoint one-variable intervals,
the ordered cumulative MGU moves from `sourceChain 0` through
`sourceChain 4`, and the proof-relevant payload zipper gains four concrete
cells.  Source observations and both execution costs are computed from the
same `CertifiedPrefix`. -/
theorem depth_four_recursive_prefix_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state0 state1 state2 state3 state4 : RepresentativeActivePayloadState,
      ∃ result0 result1 result2 result3 result4 : Atom,
      ∃ run : CertifiedPrefix prog gt
          [recursiveKindAt 0, recursiveKindAt 1,
            recursiveKindAt 2, recursiveKindAt 3]
          (.active state0) (.active state4),
      ∃ cell1 cell2 cell3 cell4 : PayloadCellIdentity,
        RecursiveReadyAt state0 0 result0 ∧
        RecursiveReadyAt state1 1 result1 ∧
        RecursiveReadyAt state2 2 result2 ∧
        RecursiveReadyAt state3 3 result3 ∧
        RecursiveReadyAt state4 4 result4 ∧
        run.states =
          [.active state0, .active state1, .active state2,
            .active state3, .active state4] ∧
        state0.carrier.index.current = sourceChain 0 ∧
        state1.carrier.index.current = sourceChain 1 ∧
        state2.carrier.index.current = sourceChain 2 ∧
        state3.carrier.index.current = sourceChain 3 ∧
        state4.carrier.index.current = sourceChain 4 ∧
        state0.carrier.index.session.resolver.nextFresh = 1 ∧
        state1.carrier.index.session.resolver.nextFresh = 2 ∧
        state2.carrier.index.session.resolver.nextFresh = 3 ∧
        state3.carrier.index.session.resolver.nextFresh = 4 ∧
        state4.carrier.index.session.resolver.nextFresh = 5 ∧
        (openedFor state0.carrier.index.session "p"
          [(.variable (.generated 0) : Term)] (sourceChain 0)).cursor.remaining =
            [preparedAt 0] ∧
        (openedFor state1.carrier.index.session "p"
          [(.variable (.generated 1) : Term)] (sourceChain 1)).cursor.remaining =
            [preparedAt 1] ∧
        (openedFor state2.carrier.index.session "p"
          [(.variable (.generated 2) : Term)] (sourceChain 2)).cursor.remaining =
            [preparedAt 2] ∧
        (openedFor state3.carrier.index.session "p"
          [(.variable (.generated 3) : Term)] (sourceChain 3)).cursor.remaining =
            [preparedAt 3] ∧
        [((preparedAt 0).firstFresh, (preparedAt 0).nextFresh),
          ((preparedAt 1).firstFresh, (preparedAt 1).nextFresh),
          ((preparedAt 2).firstFresh, (preparedAt 2).nextFresh),
          ((preparedAt 3).firstFresh, (preparedAt 3).nextFresh)] =
            [(1, 2), (2, 3), (3, 4), (4, 5)] ∧
        state1.carrier.cellIdentities =
          cell1 :: state0.carrier.cellIdentities ∧
        state2.carrier.cellIdentities =
          cell2 :: state1.carrier.cellIdentities ∧
        state3.carrier.cellIdentities =
          cell3 :: state2.carrier.cellIdentities ∧
        state4.carrier.cellIdentities =
          cell4 :: state3.carrier.cellIdentities ∧
        state4.carrier.cellIdentities =
          cell4 :: cell3 :: cell2 :: cell1 ::
            state0.carrier.cellIdentities ∧
        StepsN 10
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] []),
            .opened (recursiveRequestAt 0),
            .opened (recursiveRequestAt 1),
            .opened (recursiveRequestAt 2),
            .opened (recursiveRequestAt 3)]
          state4.carrier.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 15
          (.ready initialOpenConf) state4.carrier.fineState := by
  obtain ⟨state0, result0, ready0, rootSource, rootFine⟩ :=
    rootReady (prog := prog) (gt := gt)
  obtain ⟨state1, result1, step1, ready1, cell1, cells1⟩ :=
    ready0.pushCertified (prog := prog) (gt := gt)
  obtain ⟨state2, result2, step2, ready2, cell2, cells2⟩ :=
    ready1.pushCertified (prog := prog) (gt := gt)
  obtain ⟨state3, result3, step3, ready3, cell3, cells3⟩ :=
    ready2.pushCertified (prog := prog) (gt := gt)
  obtain ⟨state4, result4, step4, ready4, cell4, cells4⟩ :=
    ready3.pushCertified (prog := prog) (gt := gt)
  let run : CertifiedPrefix prog gt
      [recursiveKindAt 0, recursiveKindAt 1,
        recursiveKindAt 2, recursiveKindAt 3]
      (.active state0) (.active state4) :=
    .cons step1 (.cons step2 (.cons step3 (.cons step4 (.nil _))))
  have finalCells :
      state4.carrier.cellIdentities =
        cell4 :: cell3 :: cell2 :: cell1 ::
          state0.carrier.cellIdentities := by
    rw [cells4, cells3, cells2, cells1]
  have opened0 :=
    openedRemainingAt state0.carrier.index.session 0 ready0.database
      ready0.nextFresh
  have opened1 :=
    openedRemainingAt state1.carrier.index.session 1 ready1.database
      ready1.nextFresh
  have opened2 :=
    openedRemainingAt state2.carrier.index.session 2 ready2.database
      ready2.nextFresh
  have opened3 :=
    openedRemainingAt state3.carrier.index.session 3 ready3.database
      ready3.nextFresh
  have nestedSource := run.sourceSteps
  have allSource := rootSource.trans nestedSource
  have exactSource :
      StepsN 10
        (.running initialSession
          (.task rootScope [.call "p" [queryTerm]] []))
        [.opened (requestFor "p" [queryTerm] []),
          .opened (recursiveRequestAt 0),
          .opened (recursiveRequestAt 1),
          .opened (recursiveRequestAt 2),
          .opened (recursiveRequestAt 3)]
        state4.carrier.sourceState := by
    simpa [recursiveKindAt, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents, ProductPhaseState.sourceState] using
      allSource
  have nestedFine := run.fineSteps
  have allFine := rootFine.trans nestedFine
  have exactFine :
      DemandDrivenCallStep.StepsN prog gt 15
        (.ready initialOpenConf) state4.carrier.fineState := by
    simpa [recursiveKindAt, TransitionSchedule.fineCost,
      TransitionKind.fineCost, ProductPhaseState.fineState] using allFine
  refine
    ⟨state0, state1, state2, state3, state4,
      result0, result1, result2, result3, result4, run,
      cell1, cell2, cell3, cell4,
      ready0, ready1, ready2, ready3, ready4, rfl,
      ready0.current, ready1.current, ready2.current, ready3.current,
      ready4.current, ready0.nextFresh, ready1.nextFresh, ready2.nextFresh,
      ready3.nextFresh, ready4.nextFresh, opened0, opened1, opened2, opened3,
      rfl, cells1, cells2, cells3, cells4, finalCells, exactSource,
      exactFine⟩

end SelfRecursive

end PLeaTTa.PrologUnboundNestedCallRegression
