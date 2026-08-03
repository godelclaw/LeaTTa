-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledRejectionReachabilityRegression
Purpose: Inhabit the complete scheduled retained-head rejection and its
  positive internal live continuation from one literal root program.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionCatchupBridge
import PLeaTTa.Proofs.PrologRepresentativeCallPrefilterBridge

namespace PLeaTTa.PrologScheduledRejectionReachabilityRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open OpenBindingAgreement
open PrologActivationMacro
open PrologActivationFailureBridge
open PrologAlphaFreshFrontierBridge
open PrologAnswerSourceCatchupBridge
open PrologBodyFailureOuterResourceActivationBridge
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologPersistentFreeScheduledRejectionCatchupBridge
open PrologPersistentFreeScheduledRejectionPullBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeCallPrefilterBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRootCallReadyBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadResumeBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
# Four ordered occurrences

`selected` produces the first answer.  The next fine alternative is
`jointlyRejected`: its repeated source variable is a conservative prefilter
match but the complete head equations fail.  After that failure, `hidden`
is visible only to the source cursor and `live` is the next fine alternative.
Consequently the post-failure live continuation must consume exactly one
internal source rejection before selecting `live`.
-/

def leftTerm : Term := .atom "left"
def rightTerm : Term := .atom "right"
def blockedTerm : Term := .atom "blocked"
def okTerm : Term := .atom "ok"
def sharedIdentity : LogicVar := .source "shared"

def leftAtom : Atom := .sym "left"
def rightAtom : Atom := .sym "right"
def blockedAtom : Atom := .sym "blocked"
def okAtom : Atom := .sym "ok"

def queryTerms : List Term := [leftTerm, rightTerm, okTerm]
def queryArgs : List Atom := [leftAtom, rightAtom]

def selectedReference : LocalClause :=
  { predicate := "p"
    arguments := queryTerms
    body := [.conjunction []] }

def jointlyRejectedReference : LocalClause :=
  { predicate := "p"
    arguments :=
      [.variable sharedIdentity, .variable sharedIdentity, okTerm]
    body := [] }

def hiddenReference : LocalClause :=
  { predicate := "p"
    arguments := [leftTerm, blockedTerm, okTerm]
    body := [] }

def liveReference : LocalClause :=
  { predicate := "p"
    arguments := queryTerms
    body := [] }

def selectedExecutable : PLeaTTa.Clause :=
  { params := [leftAtom, rightAtom]
    result := okAtom
    body := [] }

def jointlyRejectedExecutable : PLeaTTa.Clause :=
  { params := [.var "shared", .var "shared"]
    result := okAtom
    body := [] }

def hiddenExecutable : PLeaTTa.Clause :=
  { params := [leftAtom, blockedAtom]
    result := okAtom
    body := [] }

def liveExecutable : PLeaTTa.Clause :=
  { params := [leftAtom, rightAtom]
    result := okAtom
    body := [] }

def selectedVersion : VersionedClause :=
  Database.empty.allocate selectedReference

def jointlyRejectedVersion : VersionedClause :=
  (Database.empty.assertz selectedReference).allocate
    jointlyRejectedReference

def hiddenVersion : VersionedClause :=
  ((Database.empty.assertz selectedReference).assertz
    jointlyRejectedReference).allocate hiddenReference

def liveVersion : VersionedClause :=
  (((Database.empty.assertz selectedReference).assertz
    jointlyRejectedReference).assertz hiddenReference).allocate liveReference

def referenceDatabase : Database :=
  (((Database.empty.assertz selectedReference).assertz
    jointlyRejectedReference).assertz hiddenReference).assertz liveReference

def executableWorld : PWorld :=
  ((((default : PWorld).reindexClauses.appendProgClause
    ("p", selectedExecutable)).appendProgClause
    ("p", jointlyRejectedExecutable)).appendProgClause
    ("p", hiddenExecutable)).appendProgClause ("p", liveExecutable)

/-! ## Empty cumulative valuation and ground root control -/

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
      [.call "p" queryTerms] [.call "p" queryArgs okAtom] := by
  exact
    .cons
      (.definedCall
        (.cons (AlphaTermAgrees.atom (by decide) (by decide))
          (.cons (AlphaTermAgrees.atom (by decide) (by decide)) .nil))
        (AlphaTermAgrees.atom (by decide) (by decide)))
      .nil

private theorem rootPayload (barrier : Nat) :
    TaskPayloadAgrees [] [] barrier [] [] [] []
      [.call "p" queryTerms] [.call "p" queryArgs okAtom] :=
  emptyTaskData.withControl (rootControl barrier)

private theorem querySupported :
    AlphaTermsSupported [] [] queryTerms := by
  intro term member
  simp [queryTerms, leftTerm, rightTerm, okTerm] at member
  rcases member with rfl | rfl | rfl
  all_goals
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]

/-! ## Database/world and compiler correspondence -/

private def groundParamsAgrees :
    CompilerAdequacy.TermsAgree [leftTerm, rightTerm]
      [leftAtom, rightAtom] :=
  .cons (CompilerAdequacy.TermAgrees.atom (by decide) (by decide))
    (.cons (CompilerAdequacy.TermAgrees.atom (by decide) (by decide)) .nil)

private def repeatedParamsAgrees :
    CompilerAdequacy.TermsAgree
      [.variable sharedIdentity, .variable sharedIdentity]
      [.var "shared", .var "shared"] :=
  .cons (CompilerAdequacy.TermAgrees.sourceVariable "shared")
    (.cons (CompilerAdequacy.TermAgrees.sourceVariable "shared") .nil)

private def hiddenParamsAgrees :
    CompilerAdequacy.TermsAgree [leftTerm, blockedTerm]
      [leftAtom, blockedAtom] :=
  .cons (CompilerAdequacy.TermAgrees.atom (by decide) (by decide))
    (.cons (CompilerAdequacy.TermAgrees.atom (by decide) (by decide)) .nil)

private theorem selectedClauseAgrees :
    LocalClauseAgrees selectedReference ("p", selectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .conjunction .nil .nil
      support := ?_ }
  · exact
      ⟨[leftTerm, rightTerm], okTerm, rfl, groundParamsAgrees,
        CompilerAdequacy.TermAgrees.atom (by decide) (by decide)⟩
  · intro name
    simp [selectedReference, selectedExecutable, queryTerms, leftTerm,
      rightTerm, okTerm, leftAtom, rightAtom, okAtom,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem jointlyRejectedClauseAgrees :
    LocalClauseAgrees jointlyRejectedReference
      ("p", jointlyRejectedExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[.variable sharedIdentity, .variable sharedIdentity], okTerm, rfl,
        repeatedParamsAgrees,
        CompilerAdequacy.TermAgrees.atom (by decide) (by decide)⟩
  · intro name
    simp [jointlyRejectedReference, jointlyRejectedExecutable,
      sharedIdentity, okTerm, okAtom, OpenBindingAgreement.logicVarExecutableName,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars,
      termsVariables, termVariables, goalsVariables]

private theorem hiddenClauseAgrees :
    LocalClauseAgrees hiddenReference ("p", hiddenExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[leftTerm, blockedTerm], okTerm, rfl, hiddenParamsAgrees,
        CompilerAdequacy.TermAgrees.atom (by decide) (by decide)⟩
  · intro name
    simp [hiddenReference, hiddenExecutable, leftTerm, blockedTerm, okTerm,
      leftAtom, blockedAtom, okAtom, LocalClause.variables,
      resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables,
      goalsVariables]

private theorem liveClauseAgrees :
    LocalClauseAgrees liveReference ("p", liveExecutable) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[leftTerm, rightTerm], okTerm, rfl, groundParamsAgrees,
        CompilerAdequacy.TermAgrees.atom (by decide) (by decide)⟩
  · intro name
    simp [liveReference, liveExecutable, queryTerms, leftTerm, rightTerm,
      okTerm, leftAtom, rightAtom, okAtom, LocalClause.variables,
      resolutionClauseVars, Metta.Atom.vars,
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
  have selected := emptyDatabaseRelatesIndexedWorld.assertz selectedClauseAgrees
  have rejected := selected.assertz jointlyRejectedClauseAgrees
  have hidden := rejected.assertz hiddenClauseAgrees
  have live := hidden.assertz liveClauseAgrees
  simpa [referenceDatabase, executableWorld] using live

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "p" queryArgs okAtom], [])
        alts := []
        qterm := okAtom } }

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have selected :=
    PWorld.appendProgClause_coherent _ ("p", selectedExecutable) root
  have rejected :=
    PWorld.appendProgClause_coherent _ ("p", jointlyRejectedExecutable)
      selected
  have hidden :=
    PWorld.appendProgClause_coherent _ ("p", hiddenExecutable) rejected
  have live := PWorld.appendProgClause_coherent _ ("p", liveExecutable) hidden
  simpa [executableWorld] using live

private theorem pResolutionCandidates :
    executableWorld.resolutionCandidates "p" 2 =
      [selectedExecutable, jointlyRejectedExecutable, hiddenExecutable,
        liveExecutable] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, selectedExecutable, jointlyRejectedExecutable,
    hiddenExecutable, liveExecutable, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 3 =
      [selectedVersion, jointlyRejectedVersion, hiddenVersion, liveVersion] := by
  rfl

private theorem pCandidateBank :
    SupportedCandidateBank "p"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 3)
      (executableWorld.resolutionCandidates "p" 2) := by
  rw [pVisibleClauses, pResolutionCandidates]
  let selectedHead : CandidateClauseAgrees "p" selectedVersion
      selectedExecutable := by
    change LocalClauseAgrees selectedReference ("p", selectedExecutable)
    exact selectedClauseAgrees
  let rejectedHead : CandidateClauseAgrees "p" jointlyRejectedVersion
      jointlyRejectedExecutable := by
    change LocalClauseAgrees jointlyRejectedReference
      ("p", jointlyRejectedExecutable)
    exact jointlyRejectedClauseAgrees
  let hiddenHead : CandidateClauseAgrees "p" hiddenVersion hiddenExecutable := by
    change LocalClauseAgrees hiddenReference ("p", hiddenExecutable)
    exact hiddenClauseAgrees
  let liveHead : CandidateClauseAgrees "p" liveVersion liveExecutable := by
    change LocalClauseAgrees liveReference ("p", liveExecutable)
    exact liveClauseAgrees
  have selectedEncoding : EncodingInjectiveOn selectedVersion.clause.variables := by
    simp [EncodingInjectiveOn, selectedVersion, Database.allocate,
      selectedReference, queryTerms, leftTerm, rightTerm, okTerm,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables]
  have rejectedEncoding :
      EncodingInjectiveOn jointlyRejectedVersion.clause.variables := by
    simp [EncodingInjectiveOn, jointlyRejectedVersion, Database.allocate,
      jointlyRejectedReference, sharedIdentity, okTerm, LocalClause.variables,
      termsVariables, termVariables, goalsVariables]
  have hiddenEncoding : EncodingInjectiveOn hiddenVersion.clause.variables := by
    simp [EncodingInjectiveOn, hiddenVersion, Database.allocate,
      hiddenReference, leftTerm, blockedTerm, okTerm, LocalClause.variables,
      termsVariables, termVariables, goalsVariables]
  have liveEncoding : EncodingInjectiveOn liveVersion.clause.variables := by
    simp [EncodingInjectiveOn, liveVersion, Database.allocate, liveReference,
      queryTerms, leftTerm, rightTerm, okTerm, LocalClause.variables,
      termsVariables, termVariables, goalsVariables]
  have selectedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        selectedVersion.clause.variables selectedVersion.clause.variables
        selectedHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      selectedHead.body
    have bodyEq : selectedHead.body =
        (CompilerAdequacy.GoalsAgree.conjunction
          CompilerAdequacy.GoalsAgree.nil CompilerAdequacy.GoalsAgree.nil) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .conjunction .nil .nil
  have rejectedBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        jointlyRejectedVersion.clause.variables
        jointlyRejectedVersion.clause.variables rejectedHead.body := by
    have bodyEq : rejectedHead.body =
        (CompilerAdequacy.GoalsAgree.nil : CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  have hiddenBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        hiddenVersion.clause.variables hiddenVersion.clause.variables
        hiddenHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      hiddenHead.body
    have bodyEq : hiddenHead.body =
        (CompilerAdequacy.GoalsAgree.nil : CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  have liveBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        liveVersion.clause.variables liveVersion.clause.variables
        liveHead.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      liveHead.body
    have bodyEq : liveHead.body =
        (CompilerAdequacy.GoalsAgree.nil : CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  refine
    ⟨List.Forall₂.cons selectedHead
      (List.Forall₂.cons rejectedHead
        (List.Forall₂.cons hiddenHead
          (List.Forall₂.cons liveHead .nil))), ?_⟩
  exact
    .cons (head := selectedHead) selectedEncoding selectedBody
      (.cons (head := rejectedHead) rejectedEncoding rejectedBody
        (.cons (head := hiddenHead) hiddenEncoding hiddenBody
          (.cons (head := liveHead) liveEncoding liveBody .nil)))

/-! ## Exact executable scan and source cursor -/

private def pScan : List PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 2)
    queryArgs queryArgs okAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf pScan.1 pScan.2

private theorem pEntry :
    RepresentativeSupportedCallEntryRelates []
      (openedFor initialSession "p" queryTerms []) initialOpenConf pPending
      queryArgs queryArgs okAtom [] [] okAtom
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
          (initialOpenConf.persistent.world.resolutionCandidates "p" 2)
          queryArgs queryArgs okAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = pScan := by
    rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (rootPayload (barrierDepth initialOpenConf.toConf + 1))
      querySupported
      (openedFor initialSession "p" queryTerms []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "p" queryTerms [] [] queryArgs okAtom [] []
      pScan.1 pScan.2 (by rfl) (by rfl)
      (by
        calc
          _ = pScan := by
            simpa [queryArgs, leftAtom, rightAtom, Metta.Subst.apply,
              Metta.Subst.lookup] using scanned
          _ = (pScan.1, pScan.2) := (Prod.eta pScan).symm)
      query pCandidateBank
  simpa [pPending, initialOpenConf] using constructed

private theorem initialBelow :
    ConfBelowResolutionCounter initialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, initialOpenConf, OpenConf.toConf, Control.toConf,
    specializationGoalsVars, specializationGoalVars, resolutionSubstVars,
    queryArgs, leftAtom, rightAtom, okAtom, Metta.Atom.vars] at member

private def selectedCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause queryArgs queryArgs okAtom [] [] okAtom 0 1
    selectedExecutable

private def rejectedCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause queryArgs queryArgs okAtom [] [] okAtom 1 1
    jointlyRejectedExecutable

private def liveCopied : PLeaTTa.Clause :=
  PLeaTTa.freshenResolutionClause queryArgs queryArgs okAtom [] [] okAtom 2 1
    liveExecutable

private def selectedAlt : PLeaTTa.Alt :=
  resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 0 selectedExecutable

private def rejectedAlt : PLeaTTa.Alt :=
  resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 1
    jointlyRejectedExecutable

private def liveAlt : PLeaTTa.Alt :=
  resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 2 liveExecutable

theorem selectedCopied_body_empty : selectedCopied.body = [] := by
  rfl

theorem rejectedAlt_is_branch :
    ∃ goals binding, rejectedAlt = .br goals binding := by
  exact ⟨_, _, rfl⟩

theorem liveAlt_is_branch :
    ∃ goals binding, liveAlt = .br goals binding := by
  exact ⟨_, _, rfl⟩

private theorem pScanExact :
    pScan = ([selectedAlt, rejectedAlt, liveAlt], 3) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 2)
        queryArgs queryArgs okAtom [] [] okAtom 1 0 =
      ([selectedAlt, rejectedAlt, liveAlt], 3)
  rw [pResolutionCandidates, resolveAlts_eq_scanResolution]
  have scan :
      ResolutionScan queryArgs queryArgs okAtom [] [] okAtom 1
        [selectedExecutable, jointlyRejectedExecutable, hiddenExecutable,
          liveExecutable]
        0 [selectedAlt, rejectedAlt, liveAlt] 3 :=
    .retained selectedExecutable
      [jointlyRejectedExecutable, hiddenExecutable, liveExecutable]
      0 3 [rejectedAlt, liveAlt]
      (by
        simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
          okAtom, selectedExecutable,
          PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList])
      (.retained jointlyRejectedExecutable
        [hiddenExecutable, liveExecutable] 1 3 [liveAlt]
        (by
          simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
            okAtom, jointlyRejectedExecutable,
            PLeaTTa.prologMatchCompat,
            PLeaTTa.prologMatchCompatList])
        (.skipped hiddenExecutable [liveExecutable] 2 3 [liveAlt]
          (by
            simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
              blockedAtom, okAtom, hiddenExecutable,
              PLeaTTa.prologMatchCompat,
              PLeaTTa.prologMatchCompatList])
          (.retained liveExecutable [] 2 3 []
            (by
              simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
                okAtom, liveExecutable, PLeaTTa.prologMatchCompat,
                PLeaTTa.prologMatchCompatList])
            (.nil 3))))
  simpa [selectedAlt, rejectedAlt, liveAlt] using scan.result_eq

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

private def selectedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation queryTerms [] 0
    selectedVersion

private def rejectedPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation queryTerms [] 0
    jointlyRejectedVersion

private def hiddenPrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation queryTerms [] 1 hiddenVersion

private def livePrepared : ClauseBranch :=
  preparedBranchOf referenceDatabase.generation queryTerms [] 1 liveVersion

private theorem pOpenedRemaining :
    (openedFor initialSession "p" queryTerms []).cursor.remaining =
      [selectedPrepared, rejectedPrepared, hiddenPrepared, livePrepared] := by
  rfl

private theorem selectedNormalized :
    selectedPrepared.normalizedHeadEquations =
      [(leftTerm, leftTerm), (rightTerm, rightTerm), (okTerm, okTerm)] := by
  rfl

private theorem selectedResolves : HeadResolution selectedPrepared [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [selectedNormalized]
    change
      OrderedTreeMgu
        [(Term.denote leftTerm, Term.denote leftTerm),
          (Term.denote rightTerm, Term.denote rightTerm),
          (Term.denote okTerm, Term.denote okTerm)] []
    have okMgu :
        OrderedTreeMgu
          [(Term.denote okTerm, Term.denote okTerm)] [] :=
      OrderedTreeMgu.cons _ _ [] [] []
        (.reflexive (Term.denote okTerm)) OrderedTreeMgu.nil
    have rightOkMgu :
        OrderedTreeMgu
          [(Term.denote rightTerm, Term.denote rightTerm),
            (Term.denote okTerm, Term.denote okTerm)] [] := by
      apply OrderedTreeMgu.cons _ _
        [(Term.denote okTerm, Term.denote okTerm)] [] []
      · exact .reflexive (Term.denote rightTerm)
      · simpa [TreeSubstitution.applyEquations, TreeSubstitution.apply] using
          okMgu
    apply OrderedTreeMgu.cons _ _
      [(Term.denote rightTerm, Term.denote rightTerm),
        (Term.denote okTerm, Term.denote okTerm)] [] []
    · exact .reflexive (Term.denote leftTerm)
    · simpa [TreeSubstitution.applyEquations, TreeSubstitution.apply] using
        rightOkMgu
  · simp [selectedPrepared, preparedBranchOf]

private theorem rejectedPrepared_has_no_resolution :
    ¬ ∃ result, HeadResolution rejectedPrepared result := by
  rintro ⟨result, resolution⟩
  have unifies := resolution.unifies
  have headExact :
      rejectedPrepared.headEquations =
        [(leftTerm, .variable (.generated 0)),
          (rightTerm, .variable (.generated 0)), (okTerm, okTerm)] := by
    rfl
  rw [headExact] at unifies
  have left :
      DenotationalUnifier result leftTerm
        (.variable (.generated 0)) :=
    unifies (leftTerm, .variable (.generated 0)) (by simp)
  have right :
      DenotationalUnifier result rightTerm
        (.variable (.generated 0)) :=
    unifies (rightTerm, .variable (.generated 0)) (by simp)
  have impossible : DenotationalUnifier result leftTerm rightTerm := by
    unfold DenotationalUnifier at left right ⊢
    exact left.trans right.symm
  exact
    distinct_atoms_have_no_denotational_unifier "left" "right" (by decide)
      ⟨result, impossible⟩

private theorem rejectedNormalized :
    rejectedPrepared.normalizedHeadEquations =
      [(leftTerm, .variable (.generated 0)),
      (rightTerm, .variable (.generated 0)), (okTerm, okTerm)] := by
  rfl

private theorem hiddenNormalized :
    hiddenPrepared.normalizedHeadEquations =
      [(leftTerm, leftTerm), (rightTerm, blockedTerm), (okTerm, okTerm)] := by
  rfl

private theorem livePrepared_resolves :
    HeadResolution livePrepared [] := by
  have normalizedExact :
      livePrepared.normalizedHeadEquations =
        selectedPrepared.normalizedHeadEquations := by
    rfl
  have selected := selectedResolves
  unfold HeadResolution at selected ⊢
  rw [normalizedExact]
  simpa [livePrepared, selectedPrepared, preparedBranchOf] using
    selected

/-- Each repeated-variable head equation is independently unifiable even
though the complete three-equation head is not.  This is the precise reason
the conservative executable prefilter must retain the occurrence. -/
private theorem rejectedHead_pointwise_unifiable :
    ∀ equation, equation ∈ rejectedPrepared.normalizedHeadEquations →
      ∃ candidate : Substitution,
        DenotationalUnifier candidate equation.1 equation.2 := by
  intro equation member
  rw [rejectedNormalized] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · let mostGeneral :=
      singleton_variable_is_denotational_mgu (.generated 0) leftTerm (by rfl)
    refine ⟨[(.generated 0, leftTerm)], ?_⟩
    exact
      (mostGeneral.1 (.variable (.generated 0), leftTerm) (by simp)).symm
  · let mostGeneral :=
      singleton_variable_is_denotational_mgu (.generated 0) rightTerm (by rfl)
    refine ⟨[(.generated 0, rightTerm)], ?_⟩
    exact
      (mostGeneral.1 (.variable (.generated 0), rightTerm) (by simp)).symm
  · exact ⟨[], by rfl⟩

/-- A selected ready frontier over the concrete retained tail cannot consume
the repeated-variable occurrence as part of its prefilter-rejected prefix.
Although full unification rejects that occurrence, every individual head
equation is unifiable, so the conservative prefilter necessarily retained
it.  This distinguishes prefilter rejection from later full-head rejection.
-/
private theorem falsePositiveFrontier_rejectedCount_zero
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (resourceExact :
      resource =
        retainedTailResource original queryArgs queryArgs okAtom [] [] okAtom
          1 0 [rejectedAlt, liveAlt] 3)
    (remainingExact :
      original.remaining =
        [rejectedPrepared, hiddenPrepared, livePrepared])
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    frontier.rejectedCount = 0 := by
  by_contra nonzero
  have skippedNonempty : frontier.skippedCandidates ≠ [] := by
    intro empty
    have count := frontier.skippedCandidates_count
    rw [empty] at count
    simp at count
    exact nonzero count.symm
  cases skippedShape : frontier.skippedCandidates with
  | nil => exact skippedNonempty skippedShape
  | cons candidate skippedTail =>
      have supportedSpine :
          List.Forall₂
            (SupportedPreparedCandidateAgrees original.callGeneration
              original.predicate original.arguments original.bindings)
            [rejectedPrepared, hiddenPrepared, livePrepared]
            (candidate :: (skippedTail ++ candidates)) := by
        simpa [remainingExact, frontier.originalCandidatesExact,
          skippedShape] using frontier.originalSupported
      cases supportedSpine with
      | cons supportedHead supportedTail =>
          rcases frontier.ownership.scan with
            ⟨_ownedCandidates, wellFormed, query, _substitutedArgs,
              _supported, _arities, _scan⟩
          have candidateMember : candidate ∈ frontier.originalCandidates := by
            rw [frontier.originalCandidatesExact, skippedShape]
            simp
          have retained :
              resolutionClauseRetained queryArgs okAtom candidate = true := by
            have exact :=
              PLeaTTa.PrologRepresentativeCallPrefilterBridge.RepresentativeNormalizedCallAgrees.retained_of_pointwise_unifiable
                query wellFormed (by rw [remainingExact]; simp) supportedHead
                (frontier.originalArities candidate candidateMember)
                rejectedHead_pointwise_unifiable
            simpa [resourceExact, retainedTailResource, okAtom, PLeaTTa.subst,
              PLeaTTa.substN, Metta.Subst.lookup] using exact
          have rejected :
              resolutionClauseRetained queryArgs okAtom candidate = false := by
            have exact := frontier.skippedCandidate_rejected (clause := candidate)
              (by rw [skippedShape]; simp)
            simpa [resourceExact, retainedTailResource, okAtom, PLeaTTa.subst,
              PLeaTTa.substN, Metta.Subst.lookup] using exact
          rw [retained] at rejected
          contradiction

/-- After the retained false positive has been consumed, the literal hidden
occurrence is the unique source-only prefilter rejection before `live`.

The proof is occurrence-sensitive and does not identify either executable
candidate by value.  If the rejection count were zero, the ready scan would
retain the hidden head while the supported second occurrence `live` must also
be retained because it has a complete head resolution.  That would force two
counter increments, contradicting the exact one-alternative retained bank.
Nonemptiness of that bank simultaneously rules out consuming both remaining
source occurrences. -/
private theorem postRejectedFrontier_rejectedCount_one
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {resourceOrigin callStart original finish : PreparedCursor}
    {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (resourceExact :
      resource =
        PrologBodyFailureResourceTransitionBridge.afterPulledHead
          (retainedTailResource resourceOrigin queryArgs queryArgs okAtom
            [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3)
          [liveAlt])
    (remainingExact :
      original.remaining = [hiddenPrepared, livePrepared])
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    frontier.rejectedCount = 1 := by
  have altsNonempty : resource.alts ≠ [] := by
    rw [resourceExact]
    simp [PrologBodyFailureResourceTransitionBridge.afterPulledHead,
      retainedTailResource]
  have finishNonempty : finish.remaining ≠ [] :=
    frontier.ready.branches_nonempty_of_alts_nonempty altsNonempty
  have finishRemaining := frontier.rejectedPulls.remaining_eq_drop
  have countBound := frontier.rejectedPulls.count_le_remaining_length
  have countLtTwo : frontier.rejectedCount < 2 := by
    rw [remainingExact] at finishRemaining countBound
    simp only [List.length_cons, List.length_nil] at countBound
    by_contra notLt
    have countExact : frontier.rejectedCount = 2 := by omega
    rw [countExact] at finishRemaining
    simp at finishRemaining
    exact finishNonempty finishRemaining
  by_contra notOne
  have countZero : frontier.rejectedCount = 0 := by omega
  have finishExact : finish = original := by
    have pulls : RejectedPullsN 0 original finish := by
      simpa [countZero] using frontier.rejectedPulls
    exact pulls.eq_of_count_zero
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail, headRemaining,
      candidatesExact, altsExact, _selectedExact, headSupported, _headArity,
      _headKept, tailSupported, tailScan⟩ := frontier.head_exact
  have remainingHead :
      branch :: branchTail = [hiddenPrepared, livePrepared] := by
    calc
      _ = finish.remaining := headRemaining.symm
      _ = original.remaining := congrArg PreparedCursor.remaining finishExact
      _ = _ := remainingExact
  have branchExact : branch = hiddenPrepared :=
    (List.cons.inj remainingHead).1
  have branchTailExact : branchTail = [livePrepared] :=
    (List.cons.inj remainingHead).2
  subst branch
  subst branchTail
  have clauseTailLength : clauseTail.length = 1 := by
    simpa using tailSupported.length_eq.symm
  obtain ⟨liveCandidate, clauseTailExact⟩ :=
    List.length_eq_one_iff.mp clauseTailLength
  subst clauseTail
  cases tailSupported with
  | cons liveSupported supportedDone =>
      cases supportedDone
      rcases frontier.ownership.scan with
        ⟨_ownedCandidates, wellFormed, query, _substitutedArgs,
          _supported, _arities, _scan⟩
      have liveMember : livePrepared ∈ original.remaining := by
        rw [remainingExact]
        simp
      have liveArity : liveCandidate.params.length = resource.argsv.length :=
        frontier.readyArities liveCandidate (by rw [candidatesExact]; simp)
      have liveKept :
          resolutionClauseRetained resource.argsv
              (PLeaTTa.subst resource.binding resource.res) liveCandidate =
            true :=
        PLeaTTa.PrologRepresentativeCallPrefilterBridge.RepresentativeNormalizedCallAgrees.retained_of_headResolution
          query wellFormed liveMember liveSupported liveArity
          ⟨[], livePrepared_resolves⟩
      have liveKeptExact :
          resolutionClauseRetained queryArgs okAtom liveCandidate = true := by
        simpa [resourceExact,
          PrologBodyFailureResourceTransitionBridge.afterPulledHead,
          retainedTailResource, okAtom, PLeaTTa.subst, PLeaTTa.substN,
          Metta.Subst.lookup] using liveKept
      have tailCounter := tailScan.counter_exact
      simp [resourceExact,
        PrologBodyFailureResourceTransitionBridge.afterPulledHead,
        retainedTailResource, retainedClauseCount] at tailCounter
      rw [liveKeptExact] at tailCounter
      contradiction

private theorem rejectedFailureExact :
    RetainedHeadFailureAgrees rejectedPrepared queryArgs okAtom [] [] okAtom
      1 1 jointlyRejectedExecutable := by
  constructor
  · constructor
    · rfl
    · have equations :
          AlphaEquationsAgree
            [(leftTerm, .variable (.generated 0)),
              (rightTerm, .variable (.generated 0)),
              (okTerm, okTerm)]
            [leftAtom, rightAtom, okAtom]
            [.var "shared", .var "shared", okAtom] := by
        exact .cons
          (AlphaTermAgrees.atom (alpha := []) (name := "left")
            (by decide) (by decide))
          (AlphaTermAgrees.variable
            (alpha := [(.generated 0, "shared")])
            (identity := .generated 0) (name := "shared") (by simp))
          (.cons
            (AlphaTermAgrees.atom (alpha := []) (name := "right")
              (by decide) (by decide))
            (AlphaTermAgrees.variable
              (alpha := [(.generated 0, "shared")])
              (identity := .generated 0) (name := "shared") (by simp))
            (.cons
              (AlphaTermAgrees.atom (alpha := []) (name := "ok")
                (by decide) (by decide))
              (AlphaTermAgrees.atom (alpha := []) (name := "ok")
                (by decide) (by decide))
              .nil))
      rw [rejectedNormalized]
      simpa [jointlyRejectedExecutable, queryArgs, leftAtom, rightAtom,
        okAtom] using equations
  · simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom, okAtom,
      jointlyRejectedExecutable, PLeaTTa.prologMatchCompat,
      PLeaTTa.prologMatchCompatList]
  · exact rejectedPrepared_has_no_resolution
  · simp [queryArgs, leftAtom, rightAtom, okAtom,
      jointlyRejectedExecutable, PLeaTTa.freshenResolutionClause,
      PLeaTTa.resolutionFreshSuffix, PLeaTTa.resolutionCompactSuffix,
      PLeaTTa.renameAtomSuffix, PLeaTTa.unifyB, PLeaTTa.unifyTopExact,
      Metta.Unify.unifyTopWith, Atom.size, Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith, Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup]

/-- Equality with the literal retained alternative pins the complete
freshened runtime head strongly enough to transport the concrete unification
failure.  No injectivity claim about clauses is needed: only the equality
goal actually executed by the machine is observed. -/
private theorem resolutionAlt_eq_rejected_implies_failure
    {clause : PLeaTTa.Clause}
    (same :
      resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 1 clause =
        rejectedAlt) :
    PLeaTTa.unifyB [] (.expr (queryArgs ++ [okAtom]))
        (.expr
          ((PLeaTTa.freshenResolutionClause queryArgs queryArgs okAtom [] []
              okAtom 1 1 clause).params ++
            [(PLeaTTa.freshenResolutionClause queryArgs queryArgs okAtom [] []
              okAtom 1 1 clause).result])) = none := by
  have sameShape := same
  unfold rejectedAlt resolutionAlt at sameShape
  dsimp at sameShape
  have goalsExact := (PLeaTTa.Alt.br.inj sameShape).1
  have headExact := (List.cons.inj goalsExact).1
  have atomsExact := PLeaTTa.Goal.eq.inj headExact
  rw [atomsExact.2]
  exact rejectedFailureExact.executableRejected

private theorem selectedFrontierResolves :
    ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause},
      RejectedPullsN count
          (openedFor initialSession "p" queryTerms []).cursor finish →
        RepresentativeRetainedCallFrontier []
          (openedFor initialSession "p" queryTerms []) initialOpenConf
          pPending finish branch clause branchTail clauseTail altTail copied
          queryArgs queryArgs okAtom [] [] okAtom
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter →
        ∃ independentResult : Substitution,
          HeadResolution branch independentResult ∧
            AlphaRuntimeNamesLive [] copied.body okAtom := by
  intro count finish branch clause branchTail clauseTail altTail copied
    pulls frontier
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [pOpenedRemaining] at shape
      have branchExact : branch = selectedPrepared :=
        (List.cons.inj shape).1.symm
      subst branch
      exact ⟨[], selectedResolves, by intro identity name member; simp at member⟩
  | succ count cursor entered branches finish remaining clash tail =>
      rw [pOpenedRemaining] at remaining
      have enteredExact : entered = selectedPrepared :=
        (List.cons.inj remaining).1.symm
      subst entered
      exact False.elim (clash ⟨[], selectedResolves⟩)

private theorem selectedFrontierShape
    {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (pulls :
      RejectedPullsN count
        (openedFor initialSession "p" queryTerms []).cursor finish)
    (frontier :
      RepresentativeRetainedCallFrontier []
        (openedFor initialSession "p" queryTerms []) initialOpenConf
        pPending finish branch clause branchTail clauseTail altTail copied
        queryArgs queryArgs okAtom [] [] okAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter) :
    count = 0 ∧
      finish = (openedFor initialSession "p" queryTerms []).cursor ∧
      branch = selectedPrepared ∧
      branchTail = [rejectedPrepared, hiddenPrepared, livePrepared] := by
  cases pulls with
  | zero cursor =>
      have shape := frontier.finishRemaining
      rw [pOpenedRemaining] at shape
      exact
        ⟨rfl, rfl, (List.cons.inj shape).1.symm,
          (List.cons.inj shape).2.symm⟩
  | succ count cursor entered branches finish remaining clash tail =>
      rw [pOpenedRemaining] at remaining
      have enteredExact : entered = selectedPrepared :=
        (List.cons.inj remaining).1.symm
      subst entered
      exact False.elim (clash ⟨[], selectedResolves⟩)

private def rootScope : CutScopeId := 0

/-- The literal four-occurrence program enters and activates `selected` with
the source-only `hidden` occurrence still present between the retained
false-positive and the final live occurrence.  This is the reachability base
for the later positive post-rejection catch-up witness. -/
theorem selected_root_activation_retains_asymmetric_tail
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish representative nextAlpha sourceCanonical flattened installed
        after,
      RepresentativeRootCallSuccessorFacts prog gt [] [] [] []
        initialSession initialOpenConf rootScope "p" queryTerms []
        queryArgs okAtom [] pScan.1 pScan.2 0
        0 [] [] finish selectedPrepared selectedExecutable
        [rejectedPrepared, hiddenPrepared, livePrepared]
        [jointlyRejectedExecutable, hiddenExecutable, liveExecutable]
        [rejectedAlt, liveAlt] selectedCopied [] representative nextAlpha
        sourceCanonical flattened installed after ∧
      finish = (openedFor initialSession "p" queryTerms []).cursor ∧
      finish.remaining =
        [selectedPrepared, rejectedPrepared, hiddenPrepared, livePrepared] ∧
      after.carrier.index.bodyReferences = selectedReference.body ∧
      after.carrier.index.bodyExecutables = selectedCopied.body ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" queryTerms] []))
        [.opened (requestFor "p" queryTerms [])]
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
           references := [.call "p" queryTerms]
           executables := [.call "p" queryArgs okAtom] }] :=
    TaskSpinePayloadAgrees.singleton (rootPayload 0)
  have notThrow : ¬ BuiltinThrowCall "p" queryTerms := by
    simp [BuiltinThrowCall]
  have notDatabase :
      DatabaseActions.recognizeDatabaseAction "p" queryTerms = none := by
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, independentResult,
        representative, nextAlpha, sourceCanonical, flattened, installed,
        after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      (branches := pScan.1) (finalCounter := pScan.2)
      (by
        simpa [pPending, initialOpenConf, queryArgs, leftAtom, rightAtom,
          PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup] using pEntry)
      preHeadPayload querySupported beforeSession (by rfl) (by rfl)
      initialBelow pScanNonempty
      (by
        intro count finish branch clause branchTail clauseTail altTail copied
          pulls frontier
        apply selectedFrontierResolves pulls
        simpa [pPending, initialOpenConf, queryArgs, leftAtom, rightAtom,
          PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup] using frontier)
      notThrow notDatabase
  have frontierNormalized :
      RepresentativeRetainedCallFrontier []
        (openedFor initialSession "p" queryTerms []) initialOpenConf pPending
        finish branch clause branchTail clauseTail altTail copied queryArgs
        queryArgs okAtom [] [] okAtom
        (barrierDepth initialOpenConf.toConf + 1)
        initialOpenConf.toConf.counter := by
    simpa [pPending, initialOpenConf, queryArgs, leftAtom, rightAtom,
      PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup] using facts.frontier
  obtain ⟨rejectsExact, finishExact, branchExact, branchTailExact⟩ :=
    selectedFrontierShape facts.pulls frontierNormalized
  subst rejects
  subst finish
  subst branch
  subst branchTail
  have skippedBranchesExact : skippedBranches = [] :=
    List.length_eq_zero_iff.mp (by simpa using facts.sourceSkipCount)
  subst skippedBranches
  have skippedClausesExact : skippedClauses = [] :=
    List.length_eq_zero_iff.mp (by simpa using facts.executableSkipCount)
  subst skippedClauses
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "p" 2 =
      clause :: clauseTail at executableShape
  rw [pResolutionCandidates] at executableShape
  have clauseExact : clause = selectedExecutable :=
    (List.cons.inj executableShape).1.symm
  have clauseTailExact :
      clauseTail =
        [jointlyRejectedExecutable, hiddenExecutable, liveExecutable] :=
    (List.cons.inj executableShape).2.symm
  subst clause
  subst clauseTail
  have copiedExact : copied = selectedCopied := by
    rw [facts.frontier.copiedExact]
    rfl
  subst copied
  have tailScan :
      ResolutionScan queryArgs queryArgs okAtom [] [] okAtom 1
        [jointlyRejectedExecutable, hiddenExecutable, liveExecutable]
        1 altTail 3 := by
    simpa [pPending, pScanExact, initialOpenConf, OpenConf.toConf,
      Control.toConf, barrierDepth, queryArgs, leftAtom, rightAtom,
      Metta.Subst.apply, Metta.Subst.lookup] using facts.frontier.tailScan
  have expectedTailScan :
      ResolutionScan queryArgs queryArgs okAtom [] [] okAtom 1
        [jointlyRejectedExecutable, hiddenExecutable, liveExecutable]
        1 [rejectedAlt, liveAlt] 3 :=
    .retained jointlyRejectedExecutable [hiddenExecutable, liveExecutable]
      1 3 [liveAlt]
      (by
        simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
          okAtom, jointlyRejectedExecutable, PLeaTTa.prologMatchCompat,
          PLeaTTa.prologMatchCompatList])
      (.skipped hiddenExecutable [liveExecutable] 2 3 [liveAlt]
        (by
          simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
            blockedAtom, okAtom, hiddenExecutable,
            PLeaTTa.prologMatchCompat, PLeaTTa.prologMatchCompatList])
        (.retained liveExecutable [] 2 3 []
          (by
            simp [resolutionClauseRetained, queryArgs, leftAtom, rightAtom,
              okAtom, liveExecutable, PLeaTTa.prologMatchCompat,
              PLeaTTa.prologMatchCompatList])
          (.nil 3)))
  have altTailExact : altTail = [rejectedAlt, liveAlt] :=
    (tailScan.deterministic expectedTailScan).1
  subst altTail
  have selectedResolution :
      HeadResolution selectedPrepared independentResult := by
    rw [← facts.carrierCurrent]
    exact facts.resolution
  have independentResultExact : independentResult = [] :=
    HeadResolution.deterministic selectedResolution selectedResolves
  subst independentResult
  refine
    ⟨(openedFor initialSession "p" queryTerms []).cursor, representative,
      nextAlpha, sourceCanonical, flattened, installed,
      after, ?_, rfl, ?_, facts.bodyReferences, facts.bodyExecutables, ?_,
      facts.fineSteps⟩
  · exact facts
  · exact pOpenedRemaining
  · simpa using facts.sourceSteps

private def postSelectedCursor : PreparedCursor :=
  (openedFor initialSession "p" queryTerms []).cursor.advance
    selectedPrepared [rejectedPrepared, hiddenPrepared, livePrepared]

private theorem postSelectedCursor_remaining :
    postSelectedCursor.remaining =
      [rejectedPrepared, hiddenPrepared, livePrepared] := by
  rfl

/-! ## The retained false positive is the literal next scheduled head -/

/-- The first answer of the literal four-occurrence program reaches the real
scheduled pull whose selected source occurrence is `jointlyRejected`.

The executable prefilter has retained that occurrence, so its source-only
prefix is exactly zero.  The statement exposes the post-consumption source
tail as `[hidden, live]`; no equality or injectivity principle over candidate
values is used to recover the occurrence. -/
private theorem reachable_false_positive_selected
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (before : RepresentativeScheduledPayloadState)
        (ready : RootClosedAnswerReady before)
        (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
        (scope : CutScopeId)
        (transition :
          ScheduledSelectedHeadTransition ready.payloadAlignment selection
            scope before.carrier.index.session),
      transition.frontier.rejectedCount = 0 ∧
      transition.branch = rejectedPrepared ∧
      transition.branchTail = [hiddenPrepared, livePrepared] ∧
      selection.selected.resource =
        retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
          [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3 ∧
      selection.selected.cursor = postSelectedCursor ∧
      selection.localTail = [liveAlt] ∧
      selection.suffix = [] ∧
      (transition.finish.advance transition.branch
          transition.branchTail).remaining =
        [hiddenPrepared, livePrepared] := by
  obtain
    ⟨finish, _representative, _nextAlpha, _sourceCanonical, _flattened,
      _installed, active, facts, finishExact, _finishRemaining, bodyReferences,
      bodyExecutables, _sourceSteps, _fineSteps⟩ :=
    selected_root_activation_retains_asymmetric_tail
      (prog := prog) (gt := gt)
  subst finish
  have referenceConjunction :
      active.carrier.index.bodyReferences = [.conjunction []] := by
    simpa [selectedReference] using bodyReferences
  have executableEmpty : active.carrier.index.bodyExecutables = [] := by
    exact bodyExecutables.trans selectedCopied_body_empty
  have administration :
      AdministrativeStepsN 1 active.carrier.index.bodyReferences [] := by
    rw [referenceConjunction]
    exact .succ 0 _ _ _ (.conjunction [] []) (.zero [])
  let normalized :=
    RepresentativeActivePayloadState.afterAdministrative prog gt active
      administration
  have normalizedReferencesEmpty :
      normalized.carrier.index.bodyReferences = [] := by
    rfl
  have normalizedExecutablesEmpty :
      normalized.carrier.index.bodyExecutables = [] := by
    change active.carrier.index.bodyExecutables = []
    exact executableEmpty
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt normalized
      normalizedReferencesEmpty normalizedExecutablesEmpty
  have callerEmpty : before.carrier.index.callerReferences = [] := by
    simpa [before, normalized] using facts.callerReferencesEmpty
  have outerEmpty : before.carrier.index.outer = [] := by
    simpa [before, normalized] using facts.outerEmpty
  have baseEmpty : before.carrier.index.baseAlts = [] := by
    simpa [before, normalized] using facts.baseAltsEmpty
  have resourcesEmpty : before.carrier.index.resources = [] := by
    simpa [before, normalized] using facts.resourcesEmpty
  have allOuterEmpty :
      ∀ segment, segment ∈ before.carrier.index.outer →
        segment.references = [] := by
    rw [outerEmpty]
    simp
  let ready :=
    RepresentativeScheduledPayloadState.rootClosedAnswerReady before
      callerEmpty allOuterEmpty baseEmpty
  have activeAltsShape :
      before.carrier.index.active.alts = [rejectedAlt, liveAlt] := by
    simpa [before, normalized] using facts.activeAltsExact
  have historyResources :
      ready.result.history.resources = [before.carrier.index.active] := by
    rw [ready.result.resourcesExact, currentAnswerHistory_resources,
      resourcesEmpty]
    rfl
  have bankShape :
      before.carrier.index.openConf.control.alts =
        [rejectedAlt, liveAlt, .barrier] := by
    rw [ready.bankExact, historyResources]
    simp only [PrologProductResourceContextBridge.flattenOwnedAlts_cons,
      PrologProductResourceContextBridge.flattenOwnedAlts_nil]
    rw [activeAltsShape]
    rfl
  have cellsLength : ready.result.historyBuild.cells.length = 1 := by
    have mapped := congrArg List.length
      ready.result.historyBuild.cells_map_resource
    rw [historyResources] at mapped
    simpa using mapped
  obtain ⟨only, cellsExact⟩ := List.length_eq_one_iff.mp cellsLength
  have onlyResource : only.resource = before.carrier.index.active := by
    have mapped := ready.result.historyBuild.cells_map_resource
    rw [cellsExact, historyResources] at mapped
    exact (List.cons.inj mapped).1
  have tailCellsEmpty :
      payloadCells
          (ActiveProductPayloadContext.outerPayload
            before.carrier.payloadContext) = [] := by
    have mapped := payloadCells_map_resource
      (ActiveProductPayloadContext.outerPayload before.carrier.payloadContext)
    have mappedEmpty := mapped.trans resourcesEmpty
    apply List.eq_nil_of_length_eq_zero
    have lengths := congrArg List.length mappedEmpty
    simpa using lengths
  have initialCellsExact :
      ready.result.historyBuild.cells =
        (currentAnswerHistoryBuild before).cells := by
    rw [ready.result.historyCellsExact, tailCellsEmpty]
    simp
  have onlyCursor :
      only.cursor =
        before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail := by
    have mapped := congrArg
      (List.map ScheduledHistoryCell.cursor) initialCellsExact
    rw [cellsExact] at mapped
    simpa [currentAnswerHistoryBuild, ScheduledHistoryBuild.cells] using
      (List.cons.inj mapped).1
  have beforeCursorExact :
      before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail = postSelectedCursor := by
    calc
      _ = active.carrier.index.finish.advance active.carrier.index.branch
            active.carrier.index.branchTail := rfl
      _ = postSelectedCursor := facts.retainedCursorExact
  have beforeActiveExact :
      before.carrier.index.active =
        retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
          [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3 := by
    calc
      _ = active.carrier.index.active := by
        simp [before, normalized]
      _ = retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
            [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3 := by
        simpa [postSelectedCursor, initialOpenConf, OpenConf.toConf,
          Control.toConf, barrierDepth, pScanExact,
      queryArgs, leftAtom, rightAtom, okAtom, PLeaTTa.subst,
          PLeaTTa.substN, Metta.Subst.lookup] using facts.activeResourceExact
  cases classified :
      PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.classifyPull
        ready.payloadAlignment with
  | terminal falls =>
      have impossible := falls.pullAux_eq
      change
        PLeaTTa.pullAux
            (PrologProductResourceContextBridge.flattenOwnedAlts
              ready.result.history.resources []) =
          PLeaTTa.pullAux [] at impossible
      rw [historyResources] at impossible
      simp only [PrologProductResourceContextBridge.flattenOwnedAlts_cons,
        PrologProductResourceContextBridge.flattenOwnedAlts_nil] at impossible
      rw [activeAltsShape] at impossible
      obtain ⟨rejectedGoals, rejectedBinding, rejectedShape⟩ :=
        rejectedAlt_is_branch
      rw [rejectedShape] at impossible
      simp [PLeaTTa.pullAux] at impossible
  | localLive selection landing =>
      have decomposition :
          [only] = selection.earlier ++ selection.selected :: selection.suffix :=
        cellsExact.symm.trans selection.cellsExact
      have lengths := congrArg List.length decomposition
      simp only [List.length_cons, List.length_nil, List.length_append] at lengths
      have earlierLength : selection.earlier.length = 0 := by omega
      have suffixLength : selection.suffix.length = 0 := by omega
      have earlierExact : selection.earlier = [] :=
        List.length_eq_zero_iff.mp earlierLength
      have suffixExact : selection.suffix = [] :=
        List.length_eq_zero_iff.mp suffixLength
      have selectedExact : selection.selected = only := by
        rw [earlierExact, suffixExact] at decomposition
        simpa using (List.cons.inj decomposition).1.symm
      have selectedResourceExact :
          selection.selected.resource =
            retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
              [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3 := by
        rw [selectedExact, onlyResource, beforeActiveExact]
      have selectedCursorExact :
          selection.selected.cursor = postSelectedCursor := by
        rw [selectedExact, onlyCursor, beforeCursorExact]
      have localTailExact : selection.localTail = [liveAlt] := by
        have selectedHead := selection.selectedHead
        rw [selectedResourceExact] at selectedHead
        exact (List.cons.inj selectedHead).2.symm
      obtain ⟨transition⟩ :=
        PLeaTTa.PrologScheduledPayloadPostHeadBridge.ScheduledPayloadAlignment.selectAndAdvanceHead
          ready.payloadAlignment selection before.carrier.index.session
      have countZero : transition.frontier.rejectedCount = 0 := by
        apply falsePositiveFrontier_rejectedCount_zero
        · simpa [selectedCursorExact] using selectedResourceExact
        · rw [selectedCursorExact]
          exact postSelectedCursor_remaining
      have finishRemaining := transition.frontier.rejectedPulls.remaining_eq_drop
      rw [countZero, List.drop_zero, selectedCursorExact,
        postSelectedCursor_remaining] at finishRemaining
      have selectedHeadRemaining := transition.offset.cursorRemaining
      rw [finishRemaining] at selectedHeadRemaining
      have branchExact : transition.branch = rejectedPrepared :=
        (List.cons.inj selectedHeadRemaining).1.symm
      have branchTailExact :
          transition.branchTail = [hiddenPrepared, livePrepared] :=
        (List.cons.inj selectedHeadRemaining).2.symm
      refine
        ⟨before, ready, selection,
          (ready.payloadAlignment.payloadPath selection.path).cell.currentScope,
          transition, countZero, branchExact, branchTailExact,
          selectedResourceExact, selectedCursorExact, localTailExact,
          suffixExact, ?_⟩
      simp [PreparedCursor.advance, branchTailExact]

/-- The literal selected occurrence is rejected by both complete resolvers,
and the paired scheduled transition consumes that occurrence exactly once.
This is constructed from the selected runtime equality rather than from a
global candidate-injectivity assumption. -/
private theorem reachable_false_positive_rejected
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (before : RepresentativeScheduledPayloadState)
        (ready : RootClosedAnswerReady before)
        (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
        (scope : CutScopeId)
        (transition :
          ScheduledSelectedHeadTransition ready.payloadAlignment selection
            scope before.carrier.index.session)
        (partition : RootPayloadPartition before),
      ScheduledRejectedHeadRelates prog gt before ready selection scope
          transition partition ∧
      transition.frontier.rejectedCount = 0 ∧
      transition.branch = rejectedPrepared ∧
      transition.branchTail = [hiddenPrepared, livePrepared] ∧
      selection.selected.resource =
        retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
          [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3 ∧
      selection.selected.cursor = postSelectedCursor ∧
      selection.localTail = [liveAlt] ∧
      selection.suffix = [] ∧
      (transition.finish.advance transition.branch
          transition.branchTail).remaining =
        [hiddenPrepared, livePrepared] := by
  obtain
    ⟨before, ready, selection, scope, transition, countZero, branchExact,
      branchTailExact, resourceExact, cursorExact, localTailExact,
      suffixExact, advancedRemaining⟩ :=
    reachable_false_positive_selected (prog := prog) (gt := gt)
  have pullsZero :
      RejectedPullsN 0 selection.selected.cursor transition.finish := by
    simpa [countZero] using transition.frontier.rejectedPulls
  have finishExact : transition.finish = selection.selected.cursor := by
    exact pullsZero.eq_of_count_zero
  have normalizedCall :
      NormalizedCallAgrees [] transition.finish queryArgs okAtom := by
    rw [finishExact, cursorExact]
    constructor
    change
      AlphaTermsAgree [] [leftTerm, rightTerm, okTerm]
        [leftAtom, rightAtom, okAtom]
    exact
      .cons (AlphaTermAgrees.atom (by decide) (by decide))
        (.cons (AlphaTermAgrees.atom (by decide) (by decide))
          (.cons (AlphaTermAgrees.atom (by decide) (by decide)) .nil))
  have normalizedHead :
      NormalizedHeadAgrees transition.branch queryArgs okAtom
        transition.clause :=
    supportedPreparedCandidate_normalizedHeadAgrees normalizedCall
      transition.offset.cursorWellFormed
      (by rw [transition.offset.cursorRemaining]; simp)
      transition.offset.supported
      (by simpa [resourceExact] using transition.offset.arity)
  have priorAlts := transition.offset.priorAlts
  rw [resourceExact] at priorAlts
  change
    [rejectedAlt, liveAlt] =
      resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 1
          transition.clause :: selection.localTail at priorAlts
  have actualAltExact :
      resolutionAlt queryArgs queryArgs okAtom [] [] okAtom 1 1
          transition.clause = rejectedAlt :=
    (List.cons.inj priorAlts).1.symm
  have failure :
      RetainedHeadFailureAgrees transition.branch
        selection.selected.resource.args selection.selected.resource.res
        selection.selected.resource.rest selection.selected.resource.binding
        selection.selected.resource.qterm selection.selected.resource.counter
        selection.selected.resource.barrier transition.clause := by
    constructor
    · simpa [resourceExact, okAtom, PLeaTTa.subst, PLeaTTa.substN,
        Metta.Subst.lookup] using normalizedHead
    · simpa [resourceExact, PLeaTTa.subst, PLeaTTa.substN,
        Metta.Subst.lookup] using transition.offset.retained
    · simpa [branchExact] using rejectedPrepared_has_no_resolution
    · simpa [resourceExact, retainedTailResource] using
        (resolutionAlt_eq_rejected_implies_failure actualAltExact)
  obtain ⟨partition, agreement⟩ :=
    PLeaTTa.PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.rejectHead
      transition failure
  exact
    ⟨before, ready, selection, scope, transition, partition, agreement,
      countZero, branchExact, branchTailExact, resourceExact, cursorExact,
      localTailExact, suffixExact, advancedRemaining⟩

/-! ## Exact real rejection followed by one hidden source skip -/

/-- The literal four-occurrence root program reaches the actual scheduled
fine/source rejection seam and then catches up exactly once:

* the fine lane consumes the conservatively retained false positive;
* its real failure successor selects the sole remaining executable branch;
* the independent lane silently rejects exactly the hidden occurrence; and
* both lanes land on the literal `livePrepared` source occurrence.

The statement exposes the positional cursor and branch equations, not merely
an answer-set coincidence.  No clause-value injectivity or candidate lookup is
assumed, so duplicate-valued occurrences remain distinguished by the frozen
cursor and payload coordinates. -/
theorem four_occurrence_rejection_then_one_source_skip_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (before : RepresentativeScheduledPayloadState)
        (ready : RootClosedAnswerReady before)
        (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
        (scope : CutScopeId)
        (transition :
          ScheduledSelectedHeadTransition ready.payloadAlignment selection
            scope before.carrier.index.session)
        (oldPartition : RootPayloadPartition before)
        (next : PayloadLocalSelection transition.postPayload)
        (partition :
          PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledSelectedHeadTransition.PostRejectedPayloadPartition
            transition)
        (callStart : PreparedCursor) (startPosition : Nat)
        (finish : PreparedCursor) (readyClauses : List PLeaTTa.Clause)
        (frontier :
          SelectedReadyFrontier before.carrier.index.alpha partition.first
            partition.goals partition.binding partition.tail callStart
            partition.firstCursor finish startPosition readyClauses),
      ScheduledRejectedHeadRelates prog gt before ready selection scope
          transition oldPartition ∧
      next.path.position.val = 0 ∧
      next.path.cell.resource =
        PrologBodyFailureResourceTransitionBridge.afterPulledHead
          (retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
            [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3)
          [liveAlt] ∧
      next.path.cell.cursor =
        transition.finish.advance transition.branch transition.branchTail ∧
      .br next.erased.goals next.erased.binding = liveAlt ∧
      next.erased.localTail = [] ∧
      PayloadLocalPartitionAgrees next partition ∧
      frontier.rejectedCount = 1 ∧
      finish.remaining = [livePrepared] ∧
      StepsN 1
        (.running before.carrier.index.session
          (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
            transition
            (transition.finish.advance transition.branch
              transition.branchTail)))
        []
        (.running before.carrier.index.session
          (firstLiveReadySourceFrontier partition finish)) ∧
      StepsN
        (postAnswerRejectedHeadCount ready transition oldPartition + 1)
        (.running before.carrier.index.session ready.result.targetNext)
        []
        (.running before.carrier.index.session
          (firstLiveReadySourceFrontier partition finish)) := by
  obtain
    ⟨before, ready, selection, scope, transition, oldPartition, agreement,
      _countZero, _branchExact, _branchTailExact, selectedResourceExact,
      _selectedCursorExact, localTailExact, suffixExact,
      advancedRemaining⟩ :=
    reachable_false_positive_rejected (prog := prog) (gt := gt)
  let postResource : RetainedAlternativeSegment :=
    PrologBodyFailureResourceTransitionBridge.afterPulledHead
      (retainedTailResource postSelectedCursor queryArgs queryArgs okAtom
        [] [] okAtom 1 0 [rejectedAlt, liveAlt] 3)
      [liveAlt]
  have postResources :
      (payloadCells transition.postPayload).map PayloadCell.resource =
        [postResource] := by
    rw [transition.postResourcesExact]
    simp [ScheduledLocalSelection.postResources, localTailExact, suffixExact,
      selectedResourceExact, postResource]
  have cellsLength : (payloadCells transition.postPayload).length = 1 := by
    have lengths := congrArg List.length postResources
    simpa using lengths
  obtain ⟨only, cellsExact⟩ := List.length_eq_one_iff.mp cellsLength
  have onlyResource : only.resource = postResource := by
    rw [cellsExact] at postResources
    simpa using (List.cons.inj postResources).1
  have onlyExact :
      only =
        PayloadCell.afterSelectedHead transition.selectedPayloadCell
          (PrologBodyFailureResourceTransitionBridge.afterPulledHead
            selection.selected.resource selection.localTail)
          (transition.finish.advance transition.branch transition.branchTail)
          ⟨transition.callStart,
            (transition.startPosition + transition.frontier.rejectedCount) + 1,
            transition.tailOwnershipExact⟩
          transition.consumedSnapshot := by
    have spine := transition.postCellSpineExact
    rw [cellsExact] at spine
    exact (List.cons.inj spine).1
  cases outcome :
      PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledRejectedHeadRelates.classifyFineAndCatchup
        agreement with
  | exhausted allEmpty _fineCurrent _fineAlts _terminal =>
      have impossible := allEmpty only (by rw [cellsExact]; simp)
      rw [onlyResource] at impossible
      have live : postResource.alts = [liveAlt] := by rfl
      rw [live] at impossible
      contradiction
  | localLive next _fineCurrent _fineAlts _fineBarriers _certificate =>
      have erasedCells :
          (payloadCells transition.postPayload).map PayloadCell.historyCell =
            [only.historyCell] := by
        rw [cellsExact]
        rfl
      have decomposition :
          [only.historyCell] =
            next.erased.earlier ++
              next.erased.selected :: next.erased.suffix := by
        exact erasedCells.symm.trans next.erased.cellsExact
      have lengths := congrArg List.length decomposition
      simp only [List.length_cons, List.length_nil, List.length_append] at lengths
      have earlierLength : next.erased.earlier.length = 0 := by omega
      have suffixLength : next.erased.suffix.length = 0 := by omega
      have earlierExact : next.erased.earlier = [] :=
        List.length_eq_zero_iff.mp earlierLength
      have suffixNextExact : next.erased.suffix = [] :=
        List.length_eq_zero_iff.mp suffixLength
      have selectedExact : next.erased.selected = only.historyCell := by
        rw [earlierExact, suffixNextExact] at decomposition
        simpa using (List.cons.inj decomposition).1.symm
      have positionZero : next.path.position.val = 0 := by
        change next.erased.earlier.length = 0
        rw [earlierExact]
        rfl
      have nextResourceOnly : next.path.cell.resource = only.resource := by
        have exact := congrArg ScheduledHistoryCell.resource
          next.selected_historyCell_exact
        rw [selectedExact] at exact
        simpa [PayloadCell.historyCell] using exact
      have nextCursorOnly : next.path.cell.cursor = only.cursor := by
        have exact := congrArg ScheduledHistoryCell.cursor
          next.selected_historyCell_exact
        rw [selectedExact] at exact
        simpa [PayloadCell.historyCell] using exact
      have nextResourceExact : next.path.cell.resource = postResource :=
        nextResourceOnly.trans onlyResource
      have onlyCursorExact :
          only.cursor =
            transition.finish.advance transition.branch
              transition.branchTail := by
        rw [onlyExact]
        rfl
      have nextCursorExact :
          next.path.cell.cursor =
            transition.finish.advance transition.branch
              transition.branchTail :=
        nextCursorOnly.trans onlyCursorExact
      have selectedHead := next.selected_head
      rw [nextResourceExact] at selectedHead
      have postAlts : postResource.alts = [liveAlt] := by rfl
      rw [postAlts] at selectedHead
      have fineBranchExact :
          .br next.erased.goals next.erased.binding = liveAlt :=
        (List.cons.inj selectedHead).1.symm
      have fineTailExact : next.erased.localTail = [] :=
        (List.cons.inj selectedHead).2.symm
      obtain
        ⟨partition, callStart, startPosition, finish, readyClauses, frontier,
          partitionExact, sourceRun⟩ :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToSelectedFrontier
          next before.carrier.index.session
      have firstResourceExact : partition.first = postResource :=
        partitionExact.firstResourceExact.trans nextResourceExact
      have firstCursorRemaining :
          partition.firstCursor.remaining =
            [hiddenPrepared, livePrepared] := by
        calc
          partition.firstCursor.remaining =
              next.path.cell.cursor.remaining :=
            congrArg PreparedCursor.remaining
              partitionExact.firstCursorExact
          _ =
              (transition.finish.advance transition.branch
                transition.branchTail).remaining :=
            congrArg PreparedCursor.remaining nextCursorExact
          _ = [hiddenPrepared, livePrepared] := advancedRemaining
      have countOne : frontier.rejectedCount = 1 :=
        postRejectedFrontier_rejectedCount_one firstResourceExact
          firstCursorRemaining frontier
      have finishRemaining := frontier.rejectedPulls.remaining_eq_drop
      rw [countOne, firstCursorRemaining] at finishRemaining
      have finishLive : finish.remaining = [livePrepared] := by
        simpa using finishRemaining
      have crossedLengthZero : partition.crossedFrames.length = 0 :=
        partitionExact.crossedDepthExact.trans positionZero
      have crossedFramesEmpty : partition.crossedFrames = [] :=
        List.length_eq_zero_iff.mp crossedLengthZero
      have crossedWork :
          PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge.CrossedEmptyResourceFramesAgrees
            before.carrier.index.alpha
            partition.crossedResources [] partition.rejectionSteps := by
        simpa [crossedFramesEmpty] using partition.crossedWork
      obtain ⟨_crossedResourcesEmpty, rejectionStepsZero⟩ :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.indicesOfFramesNil
          crossedWork
      have sourceOneEntered :
          StepsN 1
            (.running before.carrier.index.session
              (PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
                next))
            []
            (.running before.carrier.index.session
              (firstLiveReadySourceFrontier partition finish)) := by
        simpa [countOne, crossedFramesEmpty, rejectionStepsZero] using
          sourceRun
      have sourceStart :=
        PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledSelectedHeadTransition.rejectedSourceFrontier_eq_entered
          transition next
      have sourceOne :
          StepsN 1
            (.running before.carrier.index.session
              (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
                transition
                (transition.finish.advance transition.branch
                  transition.branchTail)))
            []
            (.running before.carrier.index.session
              (firstLiveReadySourceFrontier partition finish)) := by
        rw [sourceStart]
        exact sourceOneEntered
      have combined := agreement.postAnswerSourceRun.trans sourceOne
      exact
        ⟨before, ready, selection, scope, transition, oldPartition, next,
          partition, callStart, startPosition, finish, readyClauses, frontier,
          agreement, positionZero, by simpa [postResource] using nextResourceExact,
          nextCursorExact, fineBranchExact, fineTailExact, partitionExact,
          countOne, finishLive, sourceOne, by simpa using combined⟩

end PLeaTTa.PrologScheduledRejectionReachabilityRegression
