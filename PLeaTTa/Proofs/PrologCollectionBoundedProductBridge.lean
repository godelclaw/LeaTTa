-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCollectionBoundedProductBridge
Purpose: Compose the existing active-product resource zipper with the nearest
  positional findall occurrence, stopping executable alternative ownership at
  that collection boundary.
Trusted boundary: none
Main exports:
  collectionOccurrence_head_of_cells,
  spinedActiveProduct_activeCollectionCells_empty,
  spinedActiveProduct_currentBank_closed,
  spinedActiveProduct_underNearestCollection,
  SpinedRepresentativeProductActivation.underNearestCollection
-/
import PLeaTTa.Proofs.PrologProductActiveControlEmbeddingBridge
import PLeaTTa.Proofs.PrologProductResourceTransitionBridge

namespace PLeaTTa.PrologCollectionBoundedProductBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologActivatedProductStepBridge
open PrologActiveControlContextBridge
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologFindallEntryBridge
open PrologFindallFrameZipperBridge
open PrologProductActiveControlEmbeddingBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open DemandDrivenStep

/-!
`findall/3` is an executable alternative-bank discontinuity: the active
generator owns only `control.alts`, while every older bank is suspended in a
typed `FindallFrame`.  The mature product/resource relation already accepts a
literal `baseAlts` suffix.  This module specializes that suffix to `[]` at the
nearest collection boundary under an explicit closed-older-bank premise and
composes that preservation result with the source-derived, positional
collection occurrence zipper.

No new operational relation is introduced.  In particular, the exact closed
bank below is projected from `ActiveProductResourceStackAgrees.actualAlts`;
it is not a second independently asserted account of the same resources.
-/

/-- Head inversion for the source-derived positional occurrence zipper.

The returned frame is the literal head of the executable frame stack.  This
is stronger than finding any extensionally agreeing frame and remains
discriminating when two source cells have equal payloads. -/
theorem collectionOccurrence_head_of_cells
    {search : Search} {frames : List Frame}
    {cell : SourceCollectionCell} {cells : List SourceCollectionCell}
    (cellsExact : activeCollectionCells search = some (cell :: cells))
    (agreement : CollectionOccurrenceAgrees search frames) :
    ∃ frame : FindallFrame, ∃ remaining : List Frame,
      frames = .findall frame :: remaining ∧
        cell.AgreesFrame (.findall frame) ∧
        List.Forall₂ SourceCollectionCell.AgreesFrame cells remaining := by
  rw [CollectionOccurrenceAgrees, cellsExact] at agreement
  cases agreement with
  | cons headAgreement tailAgreement =>
      rename_i headFrame remaining
      cases headFrame with
      | findall frame =>
          exact ⟨frame, remaining, rfl, headAgreement, tailAgreement⟩

/-! ## Collection-free active product projection -/

/-- An active product and every older predicate-product frame are
collection-free.  This follows through the exact heterogeneous embedding;
it is not assumed as a reachability side condition. -/
theorem spinedActiveProduct_activeCollectionCells_empty
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state) :
    activeCollectionCells source = some [] := by
  rw [agreement.sourceShape]
  rw [← plug_toActiveControlContext context
    (activeSourceProduct callerScope opened finish branch branchTail current
      bodyReferences callerReferences)]
  rw [ActiveControlContext.plug_activeCollectionCells]
  simp [activeSourceProduct, activeCollectionCells,
    collectionCells_toActiveControlContext]

/-- At a collection boundary the exact active-product resource bank has the
empty older suffix.  The equation is derived from the pre-existing resource
stack's `actualAlts` field; this module adds no second bank account. -/
theorem spinedActiveProduct_currentBank_closed
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {source : Search} {state : OpenConf}
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context [] source
        state) :
    state.control.alts = flattenOwnedAlts (active :: resources) [] := by
  exact agreement.resourceStack.actualAlts

/-! ## Exact nearest-collection composition -/

/-- An active product whose older bank is already closed preserves that
closure under its nearest collection and has one exact heterogeneous source
path and one exact positional executable frame.

The local product stack is expanded through the proved representation
embedding.  The collection frame then terminates current-bank ownership; all
outer alternatives remain in the positional `FindallFrame` suffix described
by `CollectionOccurrenceAgrees`.  No outer bank appears in the current-bank
equation.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem spinedActiveProduct_underNearestCollection
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {productContext : ActiveProductContext}
    {generatorSource fullSource : Search} {state : OpenConf}
    (activeAgreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope productContext []
        generatorSource state)
    (collectionScope : CollectionScopeId)
    (collectionCallerScope generatorScope : CutScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (outerContext : ActiveControlContext)
    (fullSourceExact :
      fullSource =
        ActiveControlContext.plug
          (.collection collectionScope collectionCallerScope generatorScope
              template output entryBindings tail reversed :: outerContext)
          generatorSource)
    (occurrences : CollectionOccurrenceAgrees fullSource state.frames) :
    state.control.alts = flattenOwnedAlts (active :: resources) [] ∧
      fullSource =
        ActiveControlContext.plug
          (toActiveControlContext productContext ++
            .collection collectionScope collectionCallerScope generatorScope
                template output entryBindings tail reversed :: outerContext)
          (activeSourceProduct callerScope opened finish branch branchTail
            current bodyReferences callerReferences) ∧
      ∃ frame : FindallFrame, ∃ remaining : List Frame,
        state.frames = .findall frame :: remaining ∧
          (sourceCollectionCell generatorScope collectionScope
            collectionCallerScope template output entryBindings tail reversed
          ).AgreesFrame (.findall frame) ∧
          List.Forall₂ SourceCollectionCell.AgreesFrame
            outerContext.collectionCells remaining := by
  have currentBank := spinedActiveProduct_currentBank_closed activeAgreement
  have embeddedSource :
      generatorSource =
        ActiveControlContext.plug (toActiveControlContext productContext)
          (activeSourceProduct callerScope opened finish branch branchTail
            current bodyReferences callerReferences) := by
    rw [activeAgreement.sourceShape]
    exact
      (plug_toActiveControlContext productContext
        (activeSourceProduct callerScope opened finish branch branchTail
          current bodyReferences callerReferences)).symm
  have wholeSource :
      fullSource =
        ActiveControlContext.plug
          (toActiveControlContext productContext ++
            .collection collectionScope collectionCallerScope generatorScope
                template output entryBindings tail reversed :: outerContext)
          (activeSourceProduct callerScope opened finish branch branchTail
            current bodyReferences callerReferences) := by
    rw [fullSourceExact, embeddedSource, activeControl_plug_append]
  have generatorCells :=
    spinedActiveProduct_activeCollectionCells_empty activeAgreement
  have fullCells :
      activeCollectionCells fullSource =
        some
          (sourceCollectionCell generatorScope collectionScope
              collectionCallerScope template output entryBindings tail
              reversed :: outerContext.collectionCells) := by
    rw [fullSourceExact, ActiveControlContext.plug_activeCollectionCells,
      generatorCells]
    simp [ActiveControlContext.collectionCells,
      ActiveControlFrame.collectionCells]
  obtain ⟨frame, remaining, framesExact, headAgreement, tailAgreement⟩ :=
    collectionOccurrence_head_of_cells fullCells occurrences
  exact
    ⟨currentBank, wholeSource, frame, remaining, framesExact, headAgreement,
      tailAgreement⟩

/-- A real retained-clause activation under its nearest collection preserves
an already-closed older bank and constructs the positional collection-frame
witness in one package.

Unlike `spinedActiveProduct_underNearestCollection`, this theorem does not
accept an already-composed active-product relation.  It obtains that relation
from the actual representative activation and the existing outer-resource
zipper, using the explicit empty-base premise to specialize the arbitrary base
bank.  Thus this conditional preservation result is available directly at the
actual call-push frontier rather than only for an abstractly supplied active
state.  It does not by itself prove that every reachable generator bank is
closed.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem SpinedRepresentativeProductActivation.underNearestCollection
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {productContext : ActiveProductContext}
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        callerReferences callerExecutables outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope productContext outerScope)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources [])
    (collectionScope : CollectionScopeId)
    (collectionCallerScope generatorScope : CutScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (outerContext : ActiveControlContext)
    (occurrences :
      CollectionOccurrenceAgrees
        (ActiveControlContext.plug
          (.collection collectionScope collectionCallerScope generatorScope
              template output entryBindings tail reversed :: outerContext)
          (ActiveProductContext.plug productContext
            (activatedSourceProduct callerScope opened finish branch branchTail
              independentResult callerReferences)))
        (activatedOpenSuccessor pending copied
          (callerExecutables ++ flattenExecutables outer) qterm
          installed).frames) :
    ∃ active : RetainedAlternativeSegment,
      SpinedActiveProductResourceRelates
          (AlphaFreshFrontier nextAlpha) nextAlpha support
          (sourceCanonical ++ canonical) referenceBase opened pending finish
          branch branchTail altTail bodyBarrier callerBarrier branch.body
          copied.body callerReferences callerExecutables outer
          independentResult
          (PLeaTTa.trimFor
            (copied.body ++
              (callerExecutables ++ flattenExecutables outer))
            qterm installed)
          qterm active resources callerScope outerScope productContext []
          (ActiveProductContext.plug productContext
            (activatedSourceProduct callerScope opened finish branch branchTail
              independentResult callerReferences))
          (activatedOpenSuccessor pending copied
            (callerExecutables ++ flattenExecutables outer) qterm installed) ∧
        (activatedOpenSuccessor pending copied
            (callerExecutables ++ flattenExecutables outer) qterm
            installed).control.alts =
          flattenOwnedAlts (active :: resources) [] ∧
        ActiveControlContext.plug
            (.collection collectionScope collectionCallerScope generatorScope
                template output entryBindings tail reversed :: outerContext)
            (ActiveProductContext.plug productContext
              (activatedSourceProduct callerScope opened finish branch
                branchTail independentResult callerReferences)) =
          ActiveControlContext.plug
            (toActiveControlContext productContext ++
              .collection collectionScope collectionCallerScope generatorScope
                  template output entryBindings tail reversed :: outerContext)
            (activeSourceProduct callerScope opened finish branch branchTail
              independentResult branch.body callerReferences) ∧
        ∃ frame : FindallFrame, ∃ remaining : List Frame,
          (activatedOpenSuccessor pending copied
              (callerExecutables ++ flattenExecutables outer) qterm
              installed).frames = .findall frame :: remaining ∧
            (sourceCollectionCell generatorScope collectionScope
              collectionCallerScope template output entryBindings tail
              reversed).AgreesFrame (.findall frame) ∧
            List.Forall₂ SourceCollectionCell.AgreesFrame
              outerContext.collectionCells remaining := by
  obtain ⟨active, activeAgreement⟩ :=
    _root_.PLeaTTa.PrologProductResourceTransitionBridge.SpinedRepresentativeProductActivation.spinedProductResourceRelates
      activation alignment [] outerAlts
  have composed :=
    spinedActiveProduct_underNearestCollection
      (activeAgreement := activeAgreement) collectionScope
      collectionCallerScope generatorScope template output entryBindings tail
      reversed outerContext rfl occurrences
  exact ⟨active, activeAgreement, composed⟩

/-! ## Anti-vacuity witnesses -/

/-- Two real fine `findallEnter` steps isolate a live outer-generator
alternative in the inner frame while the nested generator starts with an
empty runnable bank.

The intermediate state deliberately represents ordinary generator progress:
its current goal is a nested findall and its local alternative bank is
nonempty.  Entering that nested collector transfers the bank into the new
head frame.  Thus equating the inner current bank with the whole active frame
stack is observably false even though total ownership is conserved. -/
theorem nested_findall_entry_isolates_live_outer_bank
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : OpenConf)
    (outerTemplate : Atom) (outerSub : List PLeaTTa.Goal)
    (outerResult : Atom) (outerRest : List PLeaTTa.Goal)
    (outerBinding : Subst)
    (outerHead :
      before.toConf.cur =
        some
          (PLeaTTa.Goal.findall outerTemplate outerSub outerResult ::
            outerRest, outerBinding))
    (innerTemplate : Atom) (innerSub : List PLeaTTa.Goal)
    (innerResult : Atom) (innerRest : List PLeaTTa.Goal)
    (innerBinding : Subst) :
    let outerEntered :=
      enterFindall before outerTemplate outerSub outerResult outerRest
        outerBinding
    let live : PLeaTTa.Alt := .br [] []
    let outerRunning : OpenConf :=
      { outerEntered with
        control :=
          { outerEntered.control with
            cur :=
              some
                ([PLeaTTa.Goal.findall innerTemplate innerSub innerResult] ++
                  innerRest, innerBinding)
            alts := [live] } }
    let innerEntered :=
      enterFindall outerRunning innerTemplate innerSub innerResult innerRest
        innerBinding
    DemandDrivenStep.Step prog gt before outerEntered ∧
      DemandDrivenStep.Step prog gt outerRunning innerEntered ∧
      innerEntered.control.alts = [] ∧
      ∃ innerFrame outerFrame remaining,
        innerEntered.frames =
          .findall innerFrame :: .findall outerFrame :: remaining ∧
        innerFrame.outer.alts = [live] ∧
        outerFrame.outer.alts = before.control.alts ∧
        innerEntered.control.alts ≠ innerFrame.outer.alts := by
  dsimp only
  refine
    ⟨.findallEnter before outerTemplate outerSub outerResult outerRest
        outerBinding outerHead,
      .findallEnter _ innerTemplate innerSub innerResult innerRest
        innerBinding ?_,
      rfl, ?_⟩
  · rfl
  · refine
      ⟨executableFindallFrame
          { enterFindall before outerTemplate outerSub outerResult outerRest
              outerBinding with
            control :=
              { (enterFindall before outerTemplate outerSub outerResult
                    outerRest outerBinding).control with
                cur :=
                  some
                    ([PLeaTTa.Goal.findall innerTemplate innerSub innerResult] ++
                      innerRest, innerBinding)
                alts := [.br [] []] } }
          innerTemplate innerResult innerRest innerBinding,
        executableFindallFrame before outerTemplate outerResult outerRest
          outerBinding,
        before.frames, ?_⟩
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro same
    have lengths := congrArg List.length same
    simp [enterFindall, executableFindallFrame, OpenConf.stepOpen,
      OpenConf.ofConfWith, subConfOf, controlOf] at lengths

/-- A source state containing two extensionally equal collection cells.
Their equality is deliberate: only the executable frame-stack position may
identify which suspended bank belongs to the nearest collector. -/
def twoEqualCollectionSearch
    (scope : CutScopeId) (collectionScope : CollectionScopeId) : Search :=
  .collectionBoundary collectionScope scope
    (.cutBoundary scope
      (.collectionBoundary collectionScope scope
        (.cutBoundary scope .done)
        (.atom "template") (.atom "output") [] [] []))
    (.atom "template") (.atom "output") [] [] []

/-- Equal source cells cannot authorize selecting the outer executable frame
as the nearest one.  Both frames agree extensionally with the same cell, but
their suspended banks differ and the literal list head fixes the inner frame.
This is the positional anti-crossing witness required for nested collectors. -/
theorem equal_cells_wrong_outer_frame_rejected
    (state : OpenConf) (template result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) :
    let scope : CutScopeId := state.scopes.nextCutScope
    let collectionScope : CollectionScopeId :=
      { index := state.scopes.nextCollectionScope }
    let outerFrame :=
      executableFindallFrame state template result rest binding
    let innerFrame : FindallFrame :=
      { outerFrame with
        outer :=
          { outerFrame.outer with
            alts := .barrier :: outerFrame.outer.alts } }
    let cell :=
      sourceCollectionCell scope collectionScope scope
        (.atom "template") (.atom "output") [] [] []
    innerFrame ≠ outerFrame ∧
      activeCollectionCells
          (twoEqualCollectionSearch scope collectionScope) =
        some [cell, cell] ∧
      CollectionOccurrenceAgrees
        (twoEqualCollectionSearch scope collectionScope)
        [.findall innerFrame, .findall outerFrame] ∧
      ¬ ∃ remaining,
        ([.findall innerFrame, .findall outerFrame] : List Frame) =
          .findall outerFrame :: remaining := by
  dsimp only
  have different :
      ({ executableFindallFrame state template result rest binding with
          outer :=
            { (executableFindallFrame state template result rest
                binding).outer with
              alts :=
                .barrier ::
                  (executableFindallFrame state template result rest
                    binding).outer.alts } } : FindallFrame) ≠
        executableFindallFrame state template result rest binding := by
    intro same
    have altsSame := congrArg (fun frame : FindallFrame => frame.outer.alts)
      same
    have lengths := congrArg List.length altsSame
    simp [executableFindallFrame] at lengths
  refine ⟨different, rfl, ?_, ?_⟩
  · simp [twoEqualCollectionSearch, CollectionOccurrenceAgrees,
      activeCollectionCells, SourceCollectionCell.AgreesFrame,
      sourceCollectionCell, executableFindallFrame]
  · intro wrong
    obtain ⟨remaining, wrong⟩ := wrong
    have heads := congrArg List.head? wrong
    simp at heads
    exact different heads

end PLeaTTa.PrologCollectionBoundedProductBridge
