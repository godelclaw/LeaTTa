-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFailureRebaseRegression
Purpose: Inhabit the exact failure-rebase prefix with a reachable two-clause
  non-ground root call.
Trusted boundary: none
Main export: concrete_nonempty_failure_rebases_and_retries
-/
import PLeaTTa.Proofs.PrologFailureRebasePrefixBridge

namespace PLeaTTa.PrologFailureRebaseRegression

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
open PrologCallPayloadBridge
open PrologCallStepBridge
open PrologBooleanAliasSafety
open PrologCanonicalRuntimeReading
open PrologControlSegmentSpineBridge
open PrologFailureRebasePrefixBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRecursiveCallPayloadBridge
open PrologRootCallReadyBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-! ## A minimal reachable rollback program

The ground query `p(1)` first selects `p(X) :- 2 = 3`.  Standardizing the
clause apart and solving its head produces a real nonempty MGU even though the
root alpha/support and its representative are literally empty.  The body then
fails while a ground `p(1)` sibling remains in the immutable call snapshot.
Failure must therefore rebase to `[]`; retry then activates the retained
second clause from that literal snapshot.
-/

def clauseIdentity : LogicVar := .source "x"

def queryTerm : Term := .integer 1

def queryAtom : Atom := .gnd (.int 1)

def firstReference : LocalClause :=
  { predicate := "p"
    arguments := [.variable clauseIdentity]
    body := [.unify (.integer 2) (.integer 3)] }

def retainedReference : LocalClause :=
  { predicate := "p"
    arguments := [queryTerm]
    body := [] }

def firstExecutable : PLeaTTa.Clause :=
  { params := []
    result := .var "x"
    body := [.eq (.gnd (.int 2)) (.gnd (.int 3))] }

def retainedExecutable : PLeaTTa.Clause :=
  { params := []
    result := queryAtom
    body := [] }

def firstVersion : VersionedClause :=
  Database.empty.allocate firstReference

def retainedVersion : VersionedClause :=
  (Database.empty.assertz firstReference).allocate retainedReference

def referenceDatabase : Database :=
  (Database.empty.assertz firstReference).assertz retainedReference

def executableWorld : PWorld :=
  (((default : PWorld).reindexClauses).appendProgClause
      ("p", firstExecutable)).appendProgClause
      ("p", retainedExecutable)

def rootAlpha : List (LogicVar × String) := []

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
    simp [rootAlpha] at member

private theorem rootTaskData :
    TaskDataAgrees rootAlpha rootAlpha [] [] [] [] :=
  ⟨rootShared, TreeSubstitution.wellFormed_nil, rfl, rootValuation⟩

private theorem rootControl (barrier : Nat) :
    NormalizedAlphaGoalsAgree rootAlpha barrier
      [.call "p" [queryTerm]] [.call "p" [] queryAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.integer 1))
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
  simp [AlphaTreeSupported, queryTerm, Term.denote,
    PrologMguOpenAgreement.TreeVariablesSatisfy,
    PrologMguOpenAgreement.TreesVariablesSatisfy]

private def clashGoalAgrees :
    CompilerAdequacy.GoalAgrees
      (.unify (.integer 2) (.integer 3))
      (.eq (.gnd (.int 2)) (.gnd (.int 3))) :=
  .unify (CompilerAdequacy.TermAgrees.integer 2)
    (CompilerAdequacy.TermAgrees.integer 3)

private def clashGoalsAgrees :
    CompilerAdequacy.GoalsAgree firstReference.body firstExecutable.body :=
  .cons clashGoalAgrees .nil

private theorem clashGoalsSupported (vars : List LogicVar) :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported vars vars
      clashGoalsAgrees := by
  have headExact :
      clashGoalAgrees =
        CompilerAdequacy.GoalAgrees.unify
          (CompilerAdequacy.TermAgrees.integer 2)
          (CompilerAdequacy.TermAgrees.integer 3) :=
    Subsingleton.elim _ _
  have headSupported :
      CompilerGoalSubstitutionAdequacy.GoalAgreesSupported vars vars
        clashGoalAgrees := by
    rw [headExact]
    exact
      @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.unify
        vars vars (.integer 2) (.integer 3)
        (.gnd (.int 2)) (.gnd (.int 3))
        (CompilerAdequacy.TermAgrees.integer 2)
        (CompilerAdequacy.TermAgrees.integer 3)
        (by simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
          CompilerSubstitutionAdequacy.termVariablesIn])
        (by simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
          CompilerSubstitutionAdequacy.termVariablesIn])
  exact .cons headSupported .nil

private theorem firstClauseAgrees :
    LocalClauseAgrees firstReference ("p", firstExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := clashGoalsAgrees
      support := ?_ }
  · exact
      ⟨[], .variable clauseIdentity, rfl,
        CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.sourceVariable "x"⟩
  · intro name
    simp [firstReference, firstExecutable, LocalClause.variables,
      resolutionClauseVars, Metta.Atom.vars, specializationGoalsVars,
      specializationGoalVars, termsVariables, termVariables, goalsVariables,
      goalVariables, clauseIdentity,
      OpenBindingAgreement.logicVarExecutableName]

private theorem retainedClauseAgrees :
    LocalClauseAgrees retainedReference ("p", retainedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], queryTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 1⟩
  · intro name
    simp [retainedReference, retainedExecutable, LocalClause.variables,
      resolutionClauseVars, Metta.Atom.vars, specializationGoalsVars,
      termsVariables, termVariables, goalsVariables, queryTerm, queryAtom]

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
  have retained := first.assertz retainedClauseAgrees
  simpa [referenceDatabase, executableWorld] using retained

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have first :=
    PWorld.appendProgClause_coherent _ ("p", firstExecutable) root
  have retained :=
    PWorld.appendProgClause_coherent _ ("p", retainedExecutable) first
  simpa [executableWorld] using retained

private theorem pResolutionCandidates :
    executableWorld.resolutionCandidates "p" 0 =
      [firstExecutable, retainedExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, firstExecutable, retainedExecutable, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [firstVersion, retainedVersion] := by
  rfl

private theorem pCandidateBank :
    SupportedCandidateBank "p"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1)
      (executableWorld.resolutionCandidates "p" 0) := by
  rw [pVisibleClauses, pResolutionCandidates]
  let firstHead : CandidateClauseAgrees "p" firstVersion firstExecutable := by
    change LocalClauseAgrees firstReference ("p", firstExecutable)
    exact firstClauseAgrees
  let retainedHead :
      CandidateClauseAgrees "p" retainedVersion retainedExecutable := by
    change LocalClauseAgrees retainedReference ("p", retainedExecutable)
    exact retainedClauseAgrees
  have firstEncoding : EncodingInjectiveOn firstVersion.clause.variables := by
    simp [EncodingInjectiveOn, firstVersion, Database.allocate,
      firstReference, LocalClause.variables, termsVariables, termVariables,
      goalsVariables, goalVariables, clauseIdentity]
  have retainedEncoding :
      EncodingInjectiveOn retainedVersion.clause.variables := by
    simp [EncodingInjectiveOn, retainedVersion, Database.allocate,
      retainedReference, LocalClause.variables, termsVariables,
      termVariables, goalsVariables, queryTerm]
  have firstBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        firstVersion.clause.variables firstVersion.clause.variables
        firstHead.body := by
    change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        [clauseIdentity] [clauseIdentity] firstHead.body
    have bodyEq : firstHead.body = clashGoalsAgrees := Subsingleton.elim _ _
    rw [bodyEq]
    exact clashGoalsSupported [clauseIdentity]
  have retainedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        retainedVersion.clause.variables retainedVersion.clause.variables
        retainedHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      retainedHead.body
    have bodyEq : retainedHead.body =
        (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  let tailAgreement := List.Forall₂.cons retainedHead List.Forall₂.nil
  let agreement := List.Forall₂.cons firstHead tailAgreement
  refine ⟨agreement, ?_⟩
  exact
    @CandidateBankSupported.cons "p" firstVersion firstExecutable
      [retainedVersion] [retainedExecutable] firstHead tailAgreement
      firstEncoding firstBody
      (@CandidateBankSupported.cons "p" retainedVersion retainedExecutable
        [] [] retainedHead List.Forall₂.nil retainedEncoding retainedBody
        CandidateBankSupported.nil)

/-! ## Exact root entry -/

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

/-! ## Literal two-clause scan and selected head -/

private def firstCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] []
    initialOpenConf.control.qterm initialOpenConf.toConf.counter
    (barrierDepth initialOpenConf.toConf + 1) firstExecutable

private def retainedCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause [] [] queryAtom [] []
    initialOpenConf.control.qterm (initialOpenConf.toConf.counter + 1)
    (barrierDepth initialOpenConf.toConf + 1) retainedExecutable

private def firstAlt : PLeaTTa.Alt :=
  .br
    (.eq (.expr [queryAtom])
        (.expr (firstCopied.params ++ [firstCopied.result])) ::
      firstCopied.body)
    []

private def retainedAlt : PLeaTTa.Alt :=
  .br
    (.eq (.expr [queryAtom])
        (.expr (retainedCopied.params ++ [retainedCopied.result])) ::
      retainedCopied.body)
    []

private theorem pScanExact :
    pScan = ([firstAlt, retainedAlt], initialOpenConf.toConf.counter + 2) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 0) [] [] queryAtom
        [] [] queryAtom 1 0 =
      ([firstAlt, retainedAlt], 2)
  rw [pResolutionCandidates]
  rw [resolveAlts_eq_scanResolution]
  have scan :
      ResolutionScan [] [] queryAtom [] [] queryAtom 1
        [firstExecutable, retainedExecutable] 0
        [firstAlt, retainedAlt] 2 :=
    .retained firstExecutable [retainedExecutable] 0 2 [retainedAlt]
      (by
        simp [resolutionClauseRetained, queryAtom, firstExecutable,
          PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList])
      (.retained retainedExecutable [] 1 2 []
        (by
          simp [resolutionClauseRetained, queryAtom, retainedExecutable,
            PLeaTTa.prologGroundIdentical, PLeaTTa.prologMatchCompat,
            PLeaTTa.prologMatchCompatList])
        (.nil 2))
  simpa [firstAlt, retainedAlt, firstCopied, retainedCopied,
    initialOpenConf, OpenConf.toConf, Control.toConf, barrierDepth,
    resolutionAlt] using scan.result_eq

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

private def firstPrepared : ClauseBranch :=
  { sourceId := firstVersion.id
    callGeneration := referenceDatabase.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated 0))]
    headEquations := [(queryTerm, .variable (.generated 0))]
    body := [.unify (.integer 2) (.integer 3)]
    bindings := []
    firstFresh := 0
    nextFresh := 1 }

private def retainedPrepared : ClauseBranch :=
  { sourceId := retainedVersion.id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(queryTerm, queryTerm)]
    body := []
    bindings := []
    firstFresh := 1
    nextFresh := 1 }

private theorem pOpenedRemaining :
    (openedFor initialSession "p" [queryTerm] []).cursor.remaining =
      [firstPrepared, retainedPrepared] := by
  rfl

def firstCanonical : TreeSubstitution :=
  [((.generated 0 : LogicVar), Term.denote (.integer 1))]

def firstResult : Substitution := TreeSubstitution.reify firstCanonical

def retainedResult : Substitution := []

private theorem firstCanonical_ordered :
    OrderedTreeMgu
      (denoteEquations firstPrepared.normalizedHeadEquations)
      firstCanonical := by
  change
    OrderedTreeMgu
      [(Term.denote (.integer 1),
        Term.denote (.variable (.generated 0)))] firstCanonical
  exact .cons (Term.denote (.integer 1)) (.variable (.generated 0)) []
    firstCanonical []
    (.bindRight (Term.denote (.integer 1)) (.generated 0)
      (by intro identity equality; cases equality) (by rfl))
    .nil

private theorem firstPrepared_resolves :
    HeadResolution firstPrepared firstResult := by
  refine ⟨TreeSubstitution.reify firstCanonical, ?_, ?_⟩
  · exact firstCanonical_ordered.computesReified
  · simp [firstResult, firstPrepared]

private theorem retainedPrepared_resolves :
    HeadResolution retainedPrepared retainedResult := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    change
      OrderedTreeMgu
        [(Term.denote queryTerm, Term.denote queryTerm)] []
    exact OrderedTreeMgu.cons
      (Term.denote queryTerm) (Term.denote queryTerm) [] [] []
      (.reflexive (Term.denote queryTerm)) OrderedTreeMgu.nil
  · simp [retainedResult, retainedPrepared]

private theorem firstHeadEquations_booleanAliasSafe :
    TermEquationsBooleanAliasSafe firstPrepared.headEquations := by
  intro equation member
  simp only [firstPrepared, List.mem_singleton] at member
  subst equation
  constructor <;>
    simp [TermBooleanAliasSafe, Term.denote, NoRuntimeBooleanAliases,
      NoRuntimeBooleanAliasesList, queryTerm]

private theorem firstResult_booleanAliasSafe :
    Substitution.BooleanAliasSafe firstResult :=
  PrologBooleanAliasSafety.HeadResolution.preserves_booleanAliasSafe
    firstPrepared_resolves
    Substitution.BooleanAliasSafe.nil firstHeadEquations_booleanAliasSafe

private theorem ground_two_three_do_not_unify (bindings : Substitution) :
    ¬ ∃ result,
      UnifyResolution bindings (.integer 2) (.integer 3) result := by
  rintro ⟨_result, extension, computed, _resultExact⟩
  have unifies := computed.isMostGeneral.1
  have impossible :=
    unifies ((.integer 2), (.integer 3)) (by simp)
  have twoGround :
      PrologMguVariant.TreeGround (Term.denote (.integer 2)) := by
    change True
    trivial
  have threeGround :
      PrologMguVariant.TreeGround (Term.denote (.integer 3)) := by
    change True
    trivial
  simp only at impossible
  unfold DenotationalUnifier at impossible
  rw [twoGround.apply_eq_self, threeGround.apply_eq_self] at impossible
  simp [Term.denote] at impossible

private def rootScope : CutScopeId := 0

/-- The literal root query activates the first clause without rejection and
retains the second occurrence in both exact lanes. -/
theorem first_selected_retained_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ nextAlpha sourceCanonical flattened installed after,
      RepresentativeRootCallSuccessorFacts prog gt rootAlpha rootAlpha [] []
        initialSession initialOpenConf rootScope "p" [queryTerm] []
        [] queryAtom [] pScan.1 pScan.2 0
        0 [] []
        (openedFor initialSession "p" [queryTerm] []).cursor
        firstPrepared firstExecutable [retainedPrepared]
        [retainedExecutable] [retainedAlt] firstCopied firstResult
        [] nextAlpha sourceCanonical flattened installed after := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier rootAlpha)
        ExactControlFrontiers initialSession initialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [initialSession, initialOpenConf] using
        referenceDatabase_relates_executableWorld
    · simp [AlphaFreshFrontier, GeneratedBelow, rootAlpha,
        resolutionSeedHighWaterNames, initialSession, initialOpenConf]
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
    cases pulls with
    | zero cursor =>
        have shape := frontier.finishRemaining
        rw [pOpenedRemaining] at shape
        have branchExact : branch = firstPrepared :=
          (List.cons.inj shape).1.symm
        refine ⟨firstResult, ?_, ?_⟩
        · simpa [branchExact] using firstPrepared_resolves
        · intro identity name member
          simp [rootAlpha] at member
    | succ count cursor branch branches finish remaining clash tail =>
        rw [pOpenedRemaining] at remaining
        have branchExact : branch = firstPrepared :=
          (List.cons.inj remaining).1.symm
        subst branch
        exact False.elim (clash ⟨firstResult, firstPrepared_resolves⟩)
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
      (by rfl) initialBelow pScanNonempty selected notThrow notDatabase
  cases facts.pulls with
  | zero cursor =>
      have sourceShape := facts.sourceBank
      rw [pOpenedRemaining] at sourceShape
      have skippedBranchesNil : skippedBranches = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using facts.sourceSkipCount
      subst skippedBranches
      have sourceExact :
          [firstPrepared, retainedPrepared] = branch :: branchTail := by
        simpa using sourceShape
      have branchExact : branch = firstPrepared :=
        (List.cons.inj sourceExact).1.symm
      have branchTailExact : branchTail = [retainedPrepared] :=
        (List.cons.inj sourceExact).2.symm
      subst branch
      subst branchTail
      have executableShape := facts.executableBank
      change
        executableWorld.resolutionCandidates "p" 0 =
          skippedClauses ++ clause :: clauseTail at executableShape
      rw [pResolutionCandidates] at executableShape
      have skippedClausesNil : skippedClauses = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using facts.executableSkipCount
      subst skippedClauses
      have clauseExact : clause = firstExecutable :=
        (List.cons.inj executableShape).1.symm
      have clauseTailExact : clauseTail = [retainedExecutable] :=
        (List.cons.inj executableShape).2.symm
      subst clause
      subst clauseTail
      have copiedExact : copied = firstCopied := by
        rw [facts.frontier.copiedExact]
        rfl
      subst copied
      have tailScan :
          ResolutionScan [] [] queryAtom [] [] queryAtom 1
            [retainedExecutable] 1 altTail 2 := by
        simpa [pPending, pScanExact, initialOpenConf, OpenConf.toConf,
          Control.toConf, barrierDepth] using facts.frontier.tailScan
      have expectedTail :
          ResolutionScan [] [] queryAtom [] [] queryAtom 1
            [retainedExecutable] 1 [retainedAlt] 2 :=
        .retained retainedExecutable [] 1 2 []
          (by
            simp [resolutionClauseRetained, queryAtom, retainedExecutable,
              PLeaTTa.prologMatchCompat,
              PLeaTTa.prologMatchCompatList])
          (.nil 2)
      have altTailExact : altTail = [retainedAlt] :=
        (tailScan.deterministic expectedTail).1
      subst altTail
      have selectedResolution :
          HeadResolution firstPrepared independentResult := by
        rw [← facts.carrierCurrent]
        exact facts.resolution
      have independentExact : independentResult = firstResult :=
        HeadResolution.deterministic selectedResolution firstPrepared_resolves
      subst independentResult
      have representativeNil : representative = [] := by
        cases representative with
        | nil => rfl
        | cons entry tail =>
            have covered :=
              facts.oldCumulative.representativeCovered entry (by simp)
            simp [PrologMguOpenAgreement.AlphaCovers, rootAlpha] at covered
      subst representative
      refine
        ⟨nextAlpha, sourceCanonical, flattened, installed, after, ?_⟩
      simpa [pPending, DemandDrivenCallStep.pendingCallOf] using facts
  | succ count cursor branch branches finish remaining clash tail =>
      rw [pOpenedRemaining] at remaining
      have branchExact : branch = firstPrepared :=
        (List.cons.inj remaining).1.symm
      subst branch
      exact False.elim (clash ⟨firstResult, firstPrepared_resolves⟩)

private theorem first_selected_representative_nonempty
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst} {before : RepresentativeActivePayloadState}
    (facts :
      RepresentativeRootCallSuccessorFacts prog gt rootAlpha rootAlpha [] []
        initialSession initialOpenConf rootScope "p" [queryTerm] []
        [] queryAtom [] pScan.1 pScan.2 0
        0 [] []
        (openedFor initialSession "p" [queryTerm] []).cursor
        firstPrepared firstExecutable [retainedPrepared]
        [retainedExecutable] [retainedAlt] firstCopied firstResult
        [] nextAlpha sourceCanonical flattened installed before) :
    before.representative ≠ [] := by
  have sourceCanonicalExact : sourceCanonical = firstCanonical :=
    facts.activation.sourceOrdered.deterministic firstCanonical_ordered
  have variants :
      TreeSubstitutionVariants firstCanonical flattened := by
    simpa [sourceCanonicalExact, Substitution.denote] using
      facts.activation.cumulative.variants
  have sourceGround :
      TreeSubstitution.apply firstCanonical
          (Term.denote (.variable (.generated 0))) =
        Term.denote (.integer 1) := by
    rfl
  have sourceGrounded :
      PrologMguVariant.TreeGround
        (TreeSubstitution.apply firstCanonical
          (Term.denote (.variable (.generated 0)))) := by
    rw [sourceGround]
    change True
    trivial
  have beforeRepresentative : before.representative = flattened := by
    simpa using facts.carrierRepresentative
  intro beforeEmpty
  have flattenedEmpty : flattened = [] := by
    rw [beforeRepresentative] at beforeEmpty
    exact beforeEmpty
  have same := variants.apply_eq_of_first_ground
    (Term.denote (.variable (.generated 0))) sourceGrounded
  rw [sourceGround, flattenedEmpty] at same
  simp [Term.denote, TreeSubstitution.apply] at same

private theorem reachable_nonempty_failure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativeActivePayloadState,
      ∃ failure : RetainedFailureSuccessor prog gt before,
        StepsN 2
            (.running initialSession
              (.task rootScope [.call "p" [queryTerm]] []))
            [.opened (requestFor "p" [queryTerm] [])]
            before.carrier.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 3 (.ready initialOpenConf)
            before.carrier.fineState ∧
          before.representative ≠ [] ∧
          failure.after.representative = [] ∧
          ¬ ∃ extension : TreeSubstitution,
              failure.after.representative =
                extension ++ before.representative := by
  obtain
      ⟨nextAlpha, sourceCanonical, flattened, installed, before, facts⟩ :=
    first_selected_retained_exact (prog := prog) (gt := gt)
  have beforeNonempty : before.representative ≠ [] :=
    first_selected_representative_nonempty facts
  have referenceHead :
      before.carrier.index.bodyReferences =
        [.unify (.integer 2) (.integer 3)] := by
    simpa [firstPrepared] using facts.bodyReferences
  have leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote (.integer 2)) := by
    change True
    trivial
  have rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote (.integer 3)) := by
    change True
    trivial
  have currentSafe :
      Substitution.BooleanAliasSafe before.carrier.index.current := by
    rw [facts.carrierCurrent]
    exact firstResult_booleanAliasSafe
  have leftAliasSafe : TermBooleanAliasSafe (.integer 2) := by
    simp [TermBooleanAliasSafe, Term.denote, NoRuntimeBooleanAliases,
      NoRuntimeBooleanAliasesList]
  have rightAliasSafe : TermBooleanAliasSafe (.integer 3) := by
    simp [TermBooleanAliasSafe, Term.denote, NoRuntimeBooleanAliases,
      NoRuntimeBooleanAliasesList]
  have activeAlts :
      before.carrier.index.active.alts = [retainedAlt] := by
    exact facts.activeAltsExact
  have activeNonempty : before.carrier.index.active.alts ≠ [] := by
    rw [activeAlts]
    simp
  obtain ⟨failure⟩ :=
    PrologFailureRebasePrefixBridge.RepresentativeActivePayloadState.retainedFailureSuccessor
      (prog := prog) (gt := gt) before
      referenceHead leftSupported rightSupported currentSafe
      leftAliasSafe rightAliasSafe
      (ground_two_three_do_not_unify before.carrier.index.current)
      facts.freshFrontierExact activeNonempty
  have snapshotEmpty : failure.after.representative = [] := by
    have exactSnapshot :=
      failure.after_representative_eq_before_snapshot
    rw [facts.snapshotRepresentative] at exactSnapshot
    exact exactSnapshot
  have notExtension :=
    ResolverCertifiedPrefix.retainedFailure_not_representativeExtension_of_empty_snapshot
      failure beforeNonempty snapshotEmpty
  exact
    ⟨before, failure, by simpa using facts.sourceSteps,
      by simpa using facts.fineSteps, beforeNonempty, snapshotEmpty,
      notExtension⟩

/-- A failure whose retained cursor is the singleton second clause cannot
reject that clause: its known head resolution makes the only nonempty
post-failure frontier select it immediately. -/
private theorem singleton_failure_selects_retained
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (singleton :
      (before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail).remaining = [retainedPrepared])
    (failure : RetainedFailureSuccessor prog gt before) :
    failure.count = 0 ∧
      failure.next =
        before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail ∧
      failure.nextBranch = retainedPrepared ∧
      failure.nextBranchTail = [] := by
  have finishNonempty : failure.next.remaining ≠ [] := by
    rw [failure.offset.cursorRemaining]
    simp
  have zeroAndSame :=
    PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      singleton failure.pulls finishNonempty
  have remaining := failure.offset.cursorRemaining
  rw [zeroAndSame.2, singleton] at remaining
  have headAndTail := List.cons.inj remaining
  exact
    ⟨zeroAndSame.1, zeroAndSame.2, headAndTail.1.symm,
      headAndTail.2.symm⟩

/-- A fully reachable failure/retry prefix from the literal root query.

The first selected clause contributes a genuine nonempty head MGU, its body
then fails on the rigid equation `2 = 3`, and the retained singleton clause
is selected without rejection.  Failure restores the retained empty
representative rather than extending the failed one; activation then prepends
exactly its newly certified residual.  The source and fine lanes are counted
from the same root state through the same dependent midpoint.
[SPEC metta.pl:251-256; translator.pl:117; ISO:unification] -/
theorem concrete_nonempty_failure_rebases_and_retries
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativeActivePayloadState,
      ∃ failure : RetainedFailureSuccessor prog gt before,
        ∃ activation :
            RetainedActivationSuccessor prog gt failure.after,
          StepsN 4
              (.running initialSession
                (.task rootScope [.call "p" [queryTerm]] []))
              [.opened (requestFor "p" [queryTerm] [])]
              activation.after.carrier.sourceState ∧
            DemandDrivenCallStep.StepsN prog gt 5 (.ready initialOpenConf)
              activation.after.carrier.fineState ∧
            before.representative ≠ [] ∧
            failure.count = 0 ∧
            failure.after.representative = [] ∧
            failure.after.index.branch.sourceId = retainedVersion.id ∧
            failure.after.index.branch.body = [] ∧
            activation.after.representative = activation.flattened ∧
            (ResolverCertifiedPrefix.failureThenActivation failure activation).states =
              [.ordinary (.active before), .postFailure failure.after,
                .ordinary (.active activation.after)] ∧
            ¬ ∃ extension : TreeSubstitution,
                failure.after.representative =
                  extension ++ before.representative := by
  obtain
      ⟨nextAlpha, sourceCanonical, flattened, installed, before, facts⟩ :=
    first_selected_retained_exact (prog := prog) (gt := gt)
  have beforeNonempty : before.representative ≠ [] :=
    first_selected_representative_nonempty facts
  have referenceHead :
      before.carrier.index.bodyReferences =
        [.unify (.integer 2) (.integer 3)] := by
    simpa [firstPrepared] using facts.bodyReferences
  have leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote (.integer 2)) := by
    change True
    trivial
  have rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote (.integer 3)) := by
    change True
    trivial
  have currentSafe :
      Substitution.BooleanAliasSafe before.carrier.index.current := by
    rw [facts.carrierCurrent]
    exact firstResult_booleanAliasSafe
  have leftAliasSafe : TermBooleanAliasSafe (.integer 2) := by
    simp [TermBooleanAliasSafe, Term.denote, NoRuntimeBooleanAliases,
      NoRuntimeBooleanAliasesList]
  have rightAliasSafe : TermBooleanAliasSafe (.integer 3) := by
    simp [TermBooleanAliasSafe, Term.denote, NoRuntimeBooleanAliases,
      NoRuntimeBooleanAliasesList]
  have activeNonempty : before.carrier.index.active.alts ≠ [] := by
    rw [facts.activeAltsExact]
    simp
  obtain ⟨failure⟩ :=
    PrologFailureRebasePrefixBridge.RepresentativeActivePayloadState.retainedFailureSuccessor
      (prog := prog) (gt := gt) before referenceHead leftSupported
      rightSupported currentSafe leftAliasSafe rightAliasSafe
      (ground_two_three_do_not_unify before.carrier.index.current)
      facts.freshFrontierExact activeNonempty
  have retainedSingleton :
      (before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail).remaining = [retainedPrepared] := by
    rw [facts.retainedCursorExact]
    rfl
  have selected :=
    singleton_failure_selects_retained retainedSingleton failure
  have snapshotEmpty : failure.after.representative = [] := by
    have exactSnapshot :=
      failure.after_representative_eq_before_snapshot
    rw [facts.snapshotRepresentative] at exactSnapshot
    exact exactSnapshot
  have currentShared :
      SharedRuntimeAlpha failure.after.index.alpha := by
    change SharedRuntimeAlpha before.carrier.index.alpha
    rw [facts.carrierAlpha]
    exact facts.activation.nextShared
  have below :
      ConfBelowResolutionCounter failure.after.index.openConf.toConf := by
    change
      ConfBelowResolutionCounter
        (unifyFailureSuccessor before.carrier.index.openConf).toConf
    exact
      PrologOrdinaryStepBridge.ConfBelowResolutionCounter.unifyFailureSuccessor
        before.carrier.index.openConf facts.below
  have live :
      AlphaRuntimeNamesLive failure.after.index.support
        (failure.after.index.copied.body ++
          failure.after.index.resource.rest)
        failure.after.index.resource.qterm := by
    intro identity name member
    have supportEmpty : failure.after.index.support = [] := by
      change before.carrier.index.support = []
      exact facts.carrierSupport
    rw [supportEmpty] at member
    simp at member
  have resolved :
      HeadResolution failure.after.index.branch retainedResult := by
    change HeadResolution failure.nextBranch retainedResult
    rw [selected.2.2.1]
    exact retainedPrepared_resolves
  obtain ⟨activation⟩ :=
    PrologFailureRebasePrefixBridge.PostFailurePayloadState.retainedActivationSuccessor
      (prog := prog) (gt := gt) failure.after currentShared below live resolved
  let retry :=
    ResolverCertifiedPrefix.failureThenActivation failure activation
  have sourceRun :
      StepsN 4
          (.running initialSession
            (.task rootScope [.call "p" [queryTerm]] []))
          [.opened (requestFor "p" [queryTerm] [])]
          activation.after.carrier.sourceState := by
    have composed := StepsN.trans facts.sourceSteps retry.sourceSteps
    simpa [retry, ResolverTransitionSchedule.sourceCost,
      ResolverTransitionKind.sourceCost,
      ResolverTransitionSchedule.sourceEvents,
      ResolverTransitionKind.sourceEvents, selected.1,
      ResolverPhaseState.sourceState, ProductPhaseState.sourceState] using
      composed
  have fineRun :
      DemandDrivenCallStep.StepsN prog gt 5 (.ready initialOpenConf)
        activation.after.carrier.fineState := by
    have composed :=
      DemandDrivenCallStep.StepsN.trans facts.fineSteps retry.fineSteps
    simpa [retry, ResolverTransitionSchedule.fineCost,
      ResolverTransitionKind.fineCost, selected.1,
      ResolverPhaseState.fineState, ProductPhaseState.fineState] using
      composed
  have retainedSource :
      failure.after.index.branch.sourceId = retainedVersion.id := by
    change failure.nextBranch.sourceId = retainedVersion.id
    rw [selected.2.2.1]
    rfl
  have retainedBody : failure.after.index.branch.body = [] := by
    change failure.nextBranch.body = []
    rw [selected.2.2.1]
    rfl
  have retryRepresentative :
      activation.after.representative = activation.flattened := by
    simpa [snapshotEmpty] using
      (ResolverCertifiedPrefix.failureThenActivation_representative_exact
        failure activation)
  have notExtension :=
    ResolverCertifiedPrefix.retainedFailure_not_representativeExtension_of_empty_snapshot
      failure beforeNonempty snapshotEmpty
  exact
    ⟨before, failure, activation, sourceRun, fineRun, beforeNonempty,
      selected.1, snapshotEmpty, retainedSource, retainedBody,
      retryRepresentative, by rfl, notExtension⟩

end PLeaTTa.PrologFailureRebaseRegression
