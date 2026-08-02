-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallVariantExitPayloadBridge
Purpose: Preserve one findall caller's entry-time residual-MGU semantics
  through private collection and expose an alpha-aware exit payload.
Trusted boundary: none
Main exports: FindallFrameVariantPayloadAgrees,
  FindallVariantExitPayloadAgrees,
  ContextualFindallVariantExitPayloadRelates
-/
import PLeaTTa.Proofs.PrologFindallExitPayloadBridge
import PLeaTTa.Proofs.PrologFindallResidualVariantBridge

namespace PLeaTTa.PrologFindallVariantExitPayloadBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open CompilerAdequacy
open PrologAnswerValueBridge
open PrologFindallCopyBridge
open PrologFindallEntryBridge
open PrologFindallExitBridge
open PrologFindallExitPayloadBridge
open PrologFindallFrameZipperBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge
open DemandDrivenStep

/-!
The older `FindallFramePayloadAgrees` asks the independently chosen and
executable cumulative substitutions to produce literally the same residual
variable spelling at entry.  Principal unifiers need not choose the same
orientation, so that premise excludes valid local states.

This module freezes the actual pre-entry `TaskPayloadAgrees` instead.  The
caller alpha, observable support, and barrier are type indices; the hidden
canonical residual state remains existential inside the packet.  Thus every
derived field uses one entry valuation, while generator-answer and
per-solution copy alphas remain separate.  Materialized tail transport is not
claimed here; the raw normalized continuation and its future liveness remain
explicit until a goal-level residual-variant transport theorem is proved.
-/

/-- A normalized source findall head exposes the exact fine findall head and
the same normalized tail.  Compiler truth erasure and conjunction flattening
remain confined to the tail relation; no alternative constructor can mimic
the non-administrative head.

[SPEC translator.pl:112-116] -/
theorem NormalizedAlphaGoalsAgree.findallHead
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceTemplate referenceOutput : Term}
    {referenceGenerator referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.findall referenceTemplate (.conjunction referenceGenerator)
            referenceOutput :: referenceTail)
        executables) :
    ∃ executableTemplate executableOutput : Atom,
      ∃ executableGenerator executableTail : List PLeaTTa.Goal,
        executables =
            .findall executableTemplate executableGenerator
                executableOutput :: executableTail ∧
          AlphaTermAgrees alpha referenceTemplate executableTemplate ∧
          AlphaGoalsAgree alpha barrier referenceGenerator
            executableGenerator ∧
          AlphaTermAgrees alpha referenceOutput executableOutput ∧
          NormalizedAlphaGoalsAgree alpha barrier referenceTail
            executableTail := by
  cases agreement with
  | cons head tail =>
      cases head with
      | findall template body output =>
          exact ⟨_, _, _, _, rfl, template, body, output, tail⟩

/-- Entry-time liveness for the exact control installed by a future exit.

The copied bag is universally quantified because it does not exist at entry.
This is stronger and more precise than requiring only `frame.rest` to stay
live: the exit first installs `eq frame.result bag :: frame.rest`, and a
result variable may be used only by that equality. -/
def FindallExitContinuationLive
    (support : List (LogicVar × String)) (frame : FindallFrame) : Prop :=
  ∀ copiedValues : List Atom,
    AlphaRuntimeNamesLive support
      (.eq frame.result (chainOf copiedValues) :: frame.rest)
      frame.outer.qterm

/-- Alpha-aware payload frozen from one actual pre-entry task.

The historical task certificate is the only source of the template, output,
tail, and cumulative valuation.  Keeping `alpha`, `support`, and `barrier` as
indices prevents later consumers from combining facts from different caller
lanes.  `canonical` and `referenceBase` remain hidden implementation witnesses
of the entry valuation. -/
def FindallFrameVariantPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (cell : SourceCollectionCell) (frame : FindallFrame) : Prop :=
  ∃ referenceGenerator : List PeTTaSpec.PrologCore.Goal,
    ∃ executableGenerator : List PLeaTTa.Goal,
      ∃ canonical : TreeSubstitution,
        ∃ referenceBase : Substitution,
          TaskPayloadAgrees alpha support barrier canonical referenceBase
              cell.entryBindings frame.binding
              (.findall cell.template (.conjunction referenceGenerator)
                  cell.output :: cell.tail)
              (.findall frame.template executableGenerator frame.result ::
                frame.rest) ∧
            AlphaTermsSupported alpha support [cell.output] ∧
            FindallExitContinuationLive support frame

namespace FindallFrameVariantPayloadAgrees

/-- All reusable caller fields are derived from one historical task
certificate and therefore share one hidden cumulative representative. -/
theorem components
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    ∃ canonical : TreeSubstitution, ∃ referenceBase : Substitution,
      TaskDataAgrees alpha support canonical referenceBase
          cell.entryBindings frame.binding ∧
        AlphaTermAgrees alpha cell.template frame.template ∧
        AlphaTermAgrees alpha cell.output frame.result ∧
        NormalizedAlphaGoalsAgree alpha barrier cell.tail frame.rest ∧
        AlphaTermsSupported alpha support [cell.output] ∧
        FindallExitContinuationLive support frame := by
  rcases agreement with
    ⟨referenceGenerator, executableGenerator, canonical, referenceBase,
      entryTask, outputSupported, continuationLive⟩
  obtain ⟨executableTemplate, executableOutput, executableGenerator',
      executableTail, executableExact, template, _generator, output,
      tail⟩ :=
    PLeaTTa.PrologFindallVariantExitPayloadBridge.NormalizedAlphaGoalsAgree.findallHead
      entryTask.control
  simp only [List.cons.injEq, PLeaTTa.Goal.findall.injEq] at executableExact
  rcases executableExact with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  exact
    ⟨canonical, referenceBase, entryTask.data, template, output, tail,
      outputSupported, continuationLive⟩

/-- The historical task fixes the exact raw template relation. -/
theorem template
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    AlphaTermAgrees alpha cell.template frame.template := by
  rcases agreement.components with
    ⟨_canonical, _referenceBase, _data, template, _output, _tail,
      _outputSupported, _continuationLive⟩
  exact template

/-- The historical task fixes the exact raw output relation. -/
theorem output
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    AlphaTermAgrees alpha cell.output frame.result := by
  rcases agreement.components with
    ⟨_canonical, _referenceBase, _data, _template, output, _tail,
      _outputSupported, _continuationLive⟩
  exact output

/-- The historical task fixes the raw normalized caller continuation. -/
theorem tail
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    NormalizedAlphaGoalsAgree alpha barrier cell.tail frame.rest := by
  rcases agreement.components with
    ⟨_canonical, _referenceBase, _data, _template, _output, tail,
      _outputSupported, _continuationLive⟩
  exact tail

/-- Forgetting control from the one frozen entry task yields its cumulative
caller valuation. -/
theorem data
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    ∃ canonical : TreeSubstitution, ∃ referenceBase : Substitution,
      TaskDataAgrees alpha support canonical referenceBase
        cell.entryBindings frame.binding := by
  rcases agreement.components with
    ⟨canonical, referenceBase, data, _template, _output, _tail,
      _outputSupported, _continuationLive⟩
  exact ⟨canonical, referenceBase, data⟩

/-- The alpha-aware output packet is derived from the historical entry; no
post-substitution value is supplied independently. -/
theorem outputProducer
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    AnswerValueProducerAgrees alpha support cell.entryBindings frame.binding
      cell.output frame.result :=
  by
    rcases agreement.components with
      ⟨canonical, referenceBase, data, _template, output, _tail,
        outputSupported, _continuationLive⟩
    exact
      ⟨canonical, referenceBase, data, output, outputSupported⟩

/-- Opposite residual-MGU orientations still give the same observable caller
output up to a finite, sharing-preserving runtime alpha. -/
theorem materializedOutput
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame) :
    RuntimeTermAgrees
      (cell.entryBindings.applyTerm cell.output)
      (PLeaTTa.subst frame.binding frame.result) :=
  agreement.outputProducer.runtimeTermAgrees

/-- The entry certificate already names every caller alpha root needed by
the literal control installed after payment, for any certified copied bag. -/
theorem postExitLive
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame)
    (copiedValues : List Atom) :
    AlphaRuntimeNamesLive support
      (.eq frame.result (chainOf copiedValues) :: frame.rest)
      frame.outer.qterm :=
  by
    rcases agreement.components with
      ⟨_canonical, _referenceBase, _data, _template, _output, _tail,
        _outputSupported, continuationLive⟩
    exact continuationLive copiedValues

end FindallFrameVariantPayloadAgrees

/-- One real contextual `findall` entry paired with the alpha-aware payload
that its newly installed frame must retain until exit.

The control half proves the actual source and fine transitions.  The payload
half is indexed by that transition's literal `entered.cell` and
`executableFindallFrame`; it cannot be reconstructed from a later frame that
happens to have equal delimiter counts. -/
structure ContextualFindallVariantEntryPayloadRelates
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (freshFrontier : FreshFrontierRelation)
    (prog : Prog) (gt : GroundingTable)
    (session : Session) (search : Search) (before : OpenConf)
    (entered : ActiveFindallEntryResult session search)
    (template : Atom) (sub : List PLeaTTa.Goal) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (after : OpenConf) : Prop where
  control :
    ContextualFindallEntryRelates freshFrontier prog gt session search before
      entered template sub result rest binding after
  payload :
    FindallFrameVariantPayloadAgrees alpha support barrier entered.cell
      (executableFindallFrame before template result rest binding)

namespace ContextualFindallVariantEntryPayloadRelates

/-- Freeze the payload carried by the actual pre-entry task together with the
real contextual frame push.

The source generator and executable subprogram are kept in the historical
task certificate.  Later consumers may invert that certificate, but may not
reselect its hidden cumulative representative.

[SPEC translator.pl:112-116] -/
theorem ofTask
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {freshFrontier : FreshFrontierRelation}
    {prog : Prog} {gt : GroundingTable}
    {session : Session} {search : Search} {before : OpenConf}
    {entered : ActiveFindallEntryResult session search}
    {template result : Atom} {sub rest : List PLeaTTa.Goal}
    {binding : Subst} {after : OpenConf}
    {referenceGenerator : List PeTTaSpec.PrologCore.Goal}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    (control :
      ContextualFindallEntryRelates freshFrontier prog gt session search before
        entered template sub result rest binding after)
    (entryTask :
      TaskPayloadAgrees alpha support barrier canonical referenceBase
        entered.cell.entryBindings binding
        (.findall entered.cell.template (.conjunction referenceGenerator)
            entered.cell.output :: entered.cell.tail)
        (.findall template sub result :: rest))
    (outputSupported :
      AlphaTermsSupported alpha support [entered.cell.output])
    (continuationLive :
      FindallExitContinuationLive support
        (executableFindallFrame before template result rest binding)) :
    ContextualFindallVariantEntryPayloadRelates alpha support barrier
      freshFrontier prog gt session search before entered template sub result
      rest binding after := by
  exact
    { control := control
      payload :=
        ⟨referenceGenerator, sub, canonical, referenceBase, entryTask,
          outputSupported, continuationLive⟩ }

end ContextualFindallVariantEntryPayloadRelates

private def supportQuery (support : List (LogicVar × String)) : Atom :=
  .expr (support.map fun pair => .var pair.2)

private theorem supportQuery_name_mem
    {support : List (LogicVar × String)} {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ support) :
    name ∈ (supportQuery support).vars := by
  simp only [supportQuery, Atom.vars, List.mem_flatten]
  refine ⟨[ name ], ?_, by simp⟩
  have child :
      Atom.var name ∈ support.map (fun pair => Atom.var pair.2) :=
    List.mem_map_of_mem linked
  have childVars :
      (Atom.var name).vars ∈
        (support.map (fun pair => Atom.var pair.2)).map Atom.vars :=
    List.mem_map_of_mem child
  simpa only [Atom.vars] using childVars

/-- The exit equality, rather than the saved query or caller tail, can be the
only reason the result name remains live.

This discriminator rejects the former rest-only premise on the literal same
frame: removing `eq frame.result bag` makes the support name dead.  Therefore
the strengthened `FindallExitContinuationLive` is load-bearing rather than a
cosmetic quantification over copied bags. -/
theorem exit_result_equality_is_load_bearing :
    let resultIdentity : LogicVar := .source "dead"
    let resultName := "x#r10"
    let support := [(resultIdentity, resultName)]
    let outer : Control :=
      { cur := none
        alts := []
        qterm := .var "answer" }
    let frame : FindallFrame :=
      { preCut := 2
        preCollection := 1
        outer := outer
        template := .sym "template"
        result := .var resultName
        rest := []
        binding := [] }
    FindallExitContinuationLive support frame ∧
      ¬ AlphaRuntimeNamesLive support frame.rest frame.outer.qterm := by
  let resultIdentity : LogicVar := .source "dead"
  let resultName := "x#r10"
  let support := [(resultIdentity, resultName)]
  let outer : Control :=
    { cur := none
      alts := []
      qterm := .var "answer" }
  let frame : FindallFrame :=
    { preCut := 2
      preCollection := 1
      outer := outer
      template := .sym "template"
      result := .var resultName
      rest := []
      binding := [] }
  constructor
  · intro copiedValues identity name linked
    simp only [List.mem_singleton, Prod.mk.injEq] at linked
    rcases linked with ⟨rfl, rfl⟩
    simpa [frame] using
      (PLeaTTa.isTrimRoot_eq_left_var resultName (chainOf copiedValues)
        outer.qterm [])
  · intro oldLive
    rcases PrologMguBridge.dead_alpha_name_is_not_trim_preserved with
      ⟨_topological, _before, notLive, _after⟩
    apply notLive
    intro identity name linked
    change
      (identity, name) ∈ [(LogicVar.source "dead", "x#r10")] at linked
    simp only [List.mem_singleton, Prod.mk.injEq] at linked
    rcases linked with ⟨rfl, rfl⟩
    exact oldLive
      (identity := LogicVar.source "dead") (name := "x#r10") (by simp)

/-- The alpha-aware entry packet is strictly more expressive than the former
exact post-materialization packet.

This closed witness uses opposite but equivalent residual-MGU orientations.
Its historical task and future exit continuation are valid, and the
materialized outputs have a finite runtime alpha, while the former exact
`TermAgrees` entry-output field is impossible.  The saved query contains every
support name so this witness isolates residual-MGU strictness;
`exit_result_equality_is_load_bearing` separately proves that the strengthened
continuation premise itself cannot be reverted to rest-only liveness. -/
theorem residual_alias_variant_exit_payload_is_strictly_more_general :
    let fixture :=
      PrologFindallResidualVariantBridge.residualAliasMaterializationWitness
    let cell :=
      sourceCollectionCell 2 ⟨1⟩ 0 fixture.sourceTemplate
        fixture.sourceTemplate fixture.sourceBindings [] []
    ∃ alpha support : List (LogicVar × String), ∃ frame : FindallFrame,
      FindallFrameVariantPayloadAgrees alpha support 0 cell frame ∧
        RuntimeTermAgrees
          (cell.entryBindings.applyTerm cell.output)
          (PLeaTTa.subst frame.binding frame.result) ∧
        ¬ FindallFramePayloadAgrees cell frame := by
  let fixture :=
    PrologFindallResidualVariantBridge.residualAliasMaterializationWitness
  let cell :=
    sourceCollectionCell 2 ⟨1⟩ 0 fixture.sourceTemplate
      fixture.sourceTemplate fixture.sourceBindings [] []
  rcases fixture.producer with
    ⟨alpha, support, canonical, referenceBase, data, template,
      templateSupported⟩
  let outer : Control :=
    { cur := none
      alts := []
      qterm := supportQuery support }
  let frame : FindallFrame :=
    { preCut := 2
      preCollection := 1
      outer := outer
      template := fixture.runtimeTemplate
      result := fixture.runtimeTemplate
      rest := []
      binding := fixture.runtimeBindings }
  have entryControl :
      NormalizedAlphaGoalsAgree alpha 0
        [.findall fixture.sourceTemplate (.conjunction [])
          fixture.sourceTemplate]
        [.findall fixture.runtimeTemplate [] fixture.runtimeTemplate] :=
    .cons (.findall template .nil template) .nil
  have entryTask :
      TaskPayloadAgrees alpha support 0 canonical referenceBase
        fixture.sourceBindings fixture.runtimeBindings
        [.findall fixture.sourceTemplate (.conjunction [])
          fixture.sourceTemplate]
        [.findall fixture.runtimeTemplate [] fixture.runtimeTemplate] :=
    data.withControl entryControl
  have continuationLive : FindallExitContinuationLive support frame := by
    intro copiedValues identity name linked
    exact
      PLeaTTa.isTrimRoot_qterm_mem
        (.eq frame.result (chainOf copiedValues) :: frame.rest)
        frame.outer.qterm name (by
          simpa [frame, outer] using supportQuery_name_mem linked)
  have packet :
      FindallFrameVariantPayloadAgrees alpha support 0 cell frame := by
    refine ⟨[], [], canonical, referenceBase, ?_, ?_, continuationLive⟩
    · simpa [cell, frame, sourceCollectionCell] using entryTask
    · simpa [cell, sourceCollectionCell] using templateSupported
  refine ⟨alpha, support, frame, packet, packet.materializedOutput, ?_⟩
  intro strict
  apply fixture.exactMaterializationFails
  simpa [cell, frame, sourceCollectionCell] using strict.entryOutput

/-- Variant-aware payload immediately before one fine exit.  Copy debt and
caller-entry semantics remain separate fields: per-solution copy alphas must
not be merged with the historical caller alpha. -/
structure FindallVariantExitPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (sourceSession : Session) (cell : SourceCollectionCell)
    (before : OpenConf) (frame : FindallFrame) : Prop where
  framePayload :
    FindallFrameVariantPayloadAgrees alpha support barrier cell frame
  session :
    CollectionSessionRelates cell.reversed before.control.answers
      sourceSession before.persistent

namespace FindallVariantExitPayloadAgrees

/-- Variant-aware exit uses the same exact ordered copy debt as the strict
packet; only caller residual spelling has been generalized. -/
theorem copyFrontier
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallVariantExitPayloadAgrees alpha support barrier sourceSession
        cell before frame) :
    CollectionCopyFrontier sourceSession.resolver.nextFresh
      before.persistent.counter cell.reversed before.control.answers :=
  agreement.session.fresh

/-- Debt payment remains a bounded, exact local algorithm under the variant
caller packet. -/
theorem boundedPayment
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallVariantExitPayloadAgrees alpha support barrier sourceSession
        cell before frame) :
    FindallCopy.BagCopyStepsN cell.reversed.length
        (FindallCopy.BagCopyState.initial before.persistent.counter
          before.control.answerValues)
        (paidCollectionCopyState before.persistent.counter
          before.control.answers) ∧
      CopyPaymentAgrees sourceSession.resolver.nextFresh [] cell.reversed
        (paidCollectionCopyState before.persistent.counter
          before.control.answers) := by
  have exact :=
    agreement.copyFrontier.payment_exact_target before.persistent.counter
  have lengths :
      cell.reversed.length = before.control.answers.length :=
    List.Forall₂.length_eq agreement.copyFrontier.debt
  simpa only [rawAnswerAccumulator_sourceOrder, lengths] using exact

/-- The paid bag, caller output, and future trim roots are all derived from
one variant-aware exit packet while retaining separate per-solution alphas. -/
theorem paidPayload
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallVariantExitPayloadAgrees alpha support barrier sourceSession
        cell before frame) :
    List.Forall₂ RuntimeTermAgrees cell.reversed.reverse
        (copyFindallBag before.persistent.counter
          before.control.answerValues).values ∧
      RuntimeTermAgrees
        (cell.entryBindings.applyTerm cell.output)
        (PLeaTTa.subst frame.binding frame.result) ∧
      AlphaRuntimeNamesLive support
        (.eq frame.result
            (chainOf
              (copyFindallBag before.persistent.counter
                before.control.answerValues).values) ::
          frame.rest)
        frame.outer.qterm := by
  refine ⟨?_, agreement.framePayload.materializedOutput,
    agreement.framePayload.postExitLive _⟩
  simpa only [rawAnswerAccumulator_sourceOrder] using
    agreement.copyFrontier.pay before.persistent.counter

end FindallVariantExitPayloadAgrees

/-- One real control exit paired with the alpha-aware caller packet and exact
copy debt.  The materialized-tail analogue remains an explicit downstream
obligation rather than a hidden exact-name premise. -/
structure ContextualFindallVariantExitPayloadRelates
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (prog : Prog) (gt : GroundingTable)
    (beforeSession : Session) (beforeSearch : Search)
    (afterSession : Session) (afterSearch : Search)
    (cell : SourceCollectionCell)
    (before after : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) : Prop where
  control :
    ContextualFindallExitRelates prog gt beforeSession beforeSearch
      afterSession afterSearch cell before after frame remaining
  payload :
    FindallVariantExitPayloadAgrees alpha support barrier afterSession cell
      before frame

namespace ContextualFindallVariantExitPayloadRelates

/-- The variant packet composes with the real exit target without changing
world, counter, bag order, multiplicity, or the literal rejoined control. -/
theorem bounded_copy_rejoin_variant
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallVariantExitPayloadRelates alpha support barrier prog gt
        beforeSession beforeSearch afterSession afterSearch cell before after
        frame remaining) :
    ∃ final : FindallCopy.BagCopyState,
      FindallCopy.BagCopyStepsN cell.reversed.length
        (FindallCopy.BagCopyState.initial before.persistent.counter
          before.control.answerValues)
        final ∧
      final =
        paidCollectionCopyState before.persistent.counter
          before.control.answers ∧
      List.Forall₂ RuntimeTermAgrees cell.reversed.reverse
        final.copiedRev.reverse ∧
      RuntimeTermAgrees
        (cell.entryBindings.applyTerm cell.output)
        (PLeaTTa.subst frame.binding frame.result) ∧
      AlphaRuntimeNamesLive support
        (.eq frame.result (chainOf final.copiedRev.reverse) :: frame.rest)
        frame.outer.qterm ∧
      after.persistent.counter = final.counter ∧
      after.persistent.world = before.persistent.world ∧
      after.control.cur =
        some
          (.eq frame.result (chainOf final.copiedRev.reverse) :: frame.rest,
            frame.binding) := by
  let final :=
    paidCollectionCopyState before.persistent.counter before.control.answers
  have payment := related.payload.boundedPayment
  have paid := related.payload.paidPayload
  refine ⟨final, payment.1, rfl, ?_, paid.2.1, ?_, ?_, ?_, ?_⟩
  · simpa [final] using List.rel_reverse payment.2.paid
  · intro identity name linked
    simpa [final, paidCollectionCopyState,
      rawAnswerAccumulator_sourceOrder] using
      (paid.2.2 (identity := identity) (name := name) linked)
  · simpa [final, paidCollectionCopyState,
      rawAnswerAccumulator_sourceOrder] using
      related.control.counter_after_copy
  · exact related.control.world_preserved
  · rw [related.control.fineTarget]
    simp [resumeFindall, final, paidCollectionCopyState,
      rawAnswerAccumulator_sourceOrder]

end ContextualFindallVariantExitPayloadRelates

end PLeaTTa.PrologFindallVariantExitPayloadBridge
