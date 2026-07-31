-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallExitPayloadBridge
Purpose: Pay one active local findall copy debt and relate the exact source
  and fine rejoin payloads without merging per-solution alpha maps.
Trusted boundary: none
Main exports: FindallFramePayloadAgrees, FindallExitPayloadAgrees,
  ContextualFindallExitPayloadRelates,
  ContextualFindallExitPayloadRelates.bounded_copy_rejoin_exact
-/
import PLeaTTa.Proofs.PrologFindallCopyBridge
import PLeaTTa.Proofs.PrologFindallExitBridge

namespace PLeaTTa.PrologFindallExitPayloadBridge

open Metta (Atom GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open PrologFindallCopyBridge
open PrologFindallFrameZipperBridge
open PrologFindallExitBridge
open DemandDrivenStep

/-!
The source collector stores one already-copied `Term` per generator solution
in reverse discovery order.  The fine machine stores the corresponding raw
`Atom`s in the same reverse order and pays the copy debt only after the
generator terminates.

The relation below is deliberately separate from the control-only exit/pop
theorem.  It retains one independent `RuntimeTermAgrees` witness per
solution: different solutions were copied at different allocator generations,
so replacing the ordered `Forall₂` with one bag-wide alpha graph would conflate
their fresh-name scopes.
-/

/-- The fine collector's private accumulator is reverse discovery order;
reversing it is definitionally the exact source order consumed by
`copyFindallBag`.  Naming this equation is load-bearing because the final
counter alone cannot detect an accidental bag reversal. -/
@[simp] theorem rawAnswerAccumulator_sourceOrder (control : Control) :
    control.answers.reverse = control.answerValues := rfl

/-- Static and entry-materialized payload agreement for the source collection
cell and the fine frame that suspended its caller.

The raw fields are needed to reconnect this theorem to compiler adequacy.
The materialized fields pin what the two entry substitutions mean when the
caller resumes; they are not inferred from association-list equality.
`collectionAnswer` changes neither the caller tail nor its entry binding:
generator answer bindings are used only to materialize the copied template. -/
structure FindallFramePayloadAgrees
    (cell : SourceCollectionCell) (frame : FindallFrame) : Prop where
  template : TermAgrees cell.template frame.template
  output : TermAgrees cell.output frame.result
  tail : GoalsAgree cell.tail frame.rest
  entryOutput :
    TermAgrees
      (cell.entryBindings.applyTerm cell.output)
      (PLeaTTa.subst frame.binding frame.result)
  entryTail :
    GoalsAgree
      (cell.entryBindings.applyGoals cell.tail)
      (substCompiledGoals frame.binding frame.rest)

/-- Existing finite-domain substitution transport constructs the materialized
half of `FindallFramePayloadAgrees`; no equality of source and executable
substitution representations is required. -/
theorem FindallFramePayloadAgrees.of_variableState
    {cell : SourceCollectionCell} {frame : FindallFrame}
    {domain : List LogicVar}
    (template : TermAgrees cell.template frame.template)
    (output : TermAgrees cell.output frame.result)
    (tail : GoalsAgree cell.tail frame.rest)
    (variableState :
      VariableStateAgreesOn cell.entryBindings frame.binding domain)
    (outputSupported : termVariablesIn domain cell.output)
    (tailSupported : goalsVariablesIn domain cell.tail)
    (goalTransport :
      GoalsSubstitutionAgrees cell.entryBindings frame.binding domain) :
    FindallFramePayloadAgrees cell frame := by
  exact
    { template := template
      output := output
      tail := tail
      entryOutput :=
        PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableState output outputSupported
      entryTail := goalTransport tail tailSupported }

/-- Payload and persistent-state relation immediately before one fine exit.

`sourceSession` is the independent session *after* the generator's final child
transition.  It therefore aligns with the already-terminal fine generator
state, not with the session before that child transition. -/
structure FindallExitPayloadAgrees
    (sourceSession : Session) (cell : SourceCollectionCell)
    (before : OpenConf) (frame : FindallFrame) : Prop where
  framePayload : FindallFramePayloadAgrees cell frame
  session :
    CollectionSessionRelates cell.reversed before.control.answers
      sourceSession before.persistent

namespace FindallExitPayloadAgrees

/-- The private persistent relation exposes the exact reverse-discovery debt
used by the bounded payment phase. -/
theorem copyFrontier
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallExitPayloadAgrees sourceSession cell before frame) :
    CollectionCopyFrontier sourceSession.resolver.nextFresh
      before.persistent.counter cell.reversed before.control.answers :=
  agreement.session.fresh

/-- Paying the debt at the actual pre-exit fine counter yields exact
source-discovery order and duplicate multiplicity.  Every list position keeps
its own runtime-alpha witness. -/
theorem paidBag
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallExitPayloadAgrees sourceSession cell before frame) :
    List.Forall₂ RuntimeTermAgrees cell.reversed.reverse
      (copyFindallBag before.persistent.counter
        before.control.answerValues).values := by
  simpa only [rawAnswerAccumulator_sourceOrder] using
    agreement.copyFrontier.pay before.persistent.counter

/-- Debt payment is exactly one certified local microstep per collected
solution and reaches the one named macro-copy endpoint. -/
theorem boundedPayment
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallExitPayloadAgrees sourceSession cell before frame) :
    FindallCopy.BagCopyStepsN cell.reversed.length
        (FindallCopy.BagCopyState.initial before.persistent.counter
          before.control.answerValues)
        (paidCollectionCopyState before.persistent.counter
          before.control.answers) ∧
      CopyPaymentAgrees sourceSession.resolver.nextFresh []
        cell.reversed
        (paidCollectionCopyState before.persistent.counter
          before.control.answers) := by
  have exact :=
    agreement.copyFrontier.payment_exact_target before.persistent.counter
  have lengths :
      cell.reversed.length = before.control.answers.length :=
    List.Forall₂.length_eq agreement.copyFrontier.debt
  simpa only [rawAnswerAccumulator_sourceOrder, lengths] using exact

end FindallExitPayloadAgrees

/-- Exact post-copy rejoin payload.  The source and executable bags are in
discovery order; their pointwise relation does not identify the distinct
alpha maps allocated for different solutions. -/
structure FindallRejoinPayloadAgrees
    (cell : SourceCollectionCell) (frame : FindallFrame)
    (copiedValues : List Atom) : Prop where
  framePayload : FindallFramePayloadAgrees cell frame
  bag :
    List.Forall₂ RuntimeTermAgrees cell.reversed.reverse copiedValues

/-- Paying one related debt produces the exact macro-copy rejoin payload. -/
theorem FindallExitPayloadAgrees.rejoinPayload
    {sourceSession : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    (agreement :
      FindallExitPayloadAgrees sourceSession cell before frame) :
    FindallRejoinPayloadAgrees cell frame
      (copyFindallBag before.persistent.counter
        before.control.answerValues).values :=
  ⟨agreement.framePayload, agreement.paidBag⟩

/-- Control pop and payload payment are composed side by side.  The source
session index is forced to the post-child session carried by the control exit;
using the pre-child session would not typecheck this relation. -/
structure ContextualFindallExitPayloadRelates
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
    FindallExitPayloadAgrees afterSession cell before frame

namespace ContextualFindallExitPayloadRelates

/-- The same certified fold simultaneously witnesses the bounded local copy
run, the per-solution source-order payload relation, the exact fine counter
successor, retained generator world, and the literal rejoined executable
control head.

This remains a local rejoin theorem.  It does not identify the independent
child-completion derivation with the supplied fine terminal premise, nor does
it claim that the surrounding source wrapper tree already agrees with
`frame.outer`. -/
theorem bounded_copy_rejoin_exact
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitPayloadRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining) :
    ∃ final : FindallCopy.BagCopyState,
      FindallCopy.BagCopyStepsN cell.reversed.length
        (FindallCopy.BagCopyState.initial before.persistent.counter
          before.control.answerValues)
        final ∧
      final =
        paidCollectionCopyState before.persistent.counter
          before.control.answers ∧
      FindallRejoinPayloadAgrees cell frame final.copiedRev.reverse ∧
      after.persistent.counter = final.counter ∧
      after.persistent.world = before.persistent.world ∧
      after.control.cur =
        some
          (PLeaTTa.Goal.eq frame.result (chainOf final.copiedRev.reverse) ::
              frame.rest,
            frame.binding) := by
  let final :=
    paidCollectionCopyState before.persistent.counter before.control.answers
  have payment := related.payload.boundedPayment
  refine ⟨final, payment.1, rfl, ?_, ?_, ?_, ?_⟩
  · exact
      { framePayload := related.payload.framePayload
        bag := by
          simpa [final] using List.rel_reverse payment.2.paid }
  · simpa [final, paidCollectionCopyState,
      rawAnswerAccumulator_sourceOrder] using
      related.control.counter_after_copy
  · exact related.control.world_preserved
  · rw [related.control.fineTarget]
    simp [resumeFindall, final, paidCollectionCopyState,
      rawAnswerAccumulator_sourceOrder]

/-- Pointwise payload agreement fixes both bag length and multiplicity. -/
theorem bag_length_exact
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitPayloadRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining) :
    cell.reversed.length = before.control.answers.length :=
  List.Forall₂.length_eq related.payload.copyFrontier.debt

end ContextualFindallExitPayloadRelates

/-- Runtime agreement on integer leaves is value-reflecting. -/
theorem runtimeIntegerAgrees_exact
    {reference executable : Int}
    (agreement :
      RuntimeTermAgrees (.integer reference) (.gnd (.int executable))) :
    reference = executable := by
  rcases agreement with ⟨_, _, _, term⟩
  cases term
  rfl

/-- The ordered bag relation rejects a concrete two-element permutation; it
is not a multiset or set quotient. -/
theorem swapped_integer_bag_rejected :
    ¬ List.Forall₂ RuntimeTermAgrees
      [.integer 1, .integer 2]
      [.gnd (.int 2), .gnd (.int 1)] := by
  intro agreement
  cases agreement with
  | cons head tail =>
      have impossible := runtimeIntegerAgrees_exact head
      omega

/-- Restoring the raw accumulator to discovery order before paying the bag
copy debt is accepted pointwise.  Together with
`wrong_raw_accumulator_orientation_rejected`, this distinguishes the intended
orientation from its concrete reversal instead of merely rejecting one
arbitrary bag. -/
theorem correct_raw_accumulator_orientation_accepted :
    List.Forall₂ RuntimeTermAgrees
      [.integer 1, .integer 2]
      (copyFindallBag 0 [.gnd (.int 1), .gnd (.int 2)]).values := by
  have encoding (value : Int) :
      OpenBindingAgreement.EncodingInjectiveOn
        (PeTTaSpec.PrologCore.Copy.copyVariables (.integer value)) := by
    intro left right leftMember
    simp [PeTTaSpec.PrologCore.Copy.copyVariables,
      PeTTaSpec.PrologCore.Resolver.termVariables] at leftMember
  have first :=
    copyTerm_copyFindallAtom_runtime_agrees
      (TermAgrees.integer 1) (encoding 1) 0 0
  have second :=
    copyTerm_copyFindallAtom_runtime_agrees
      (TermAgrees.integer 2) (encoding 2) 0 0
  simpa [copyFindallBag, copyFindallAtom, resolutionAtomClosed,
    PersistentSubst.atomClosed, PeTTaSpec.PrologCore.Copy.copyTerm,
    Term.renameVariables] using
      (List.Forall₂.cons first (List.Forall₂.cons second List.Forall₂.nil))

/-- Copying the reverse accumulator without first restoring source order
produces a concrete bag rejected by the payload relation.  Both the wrong and
right folds return the same counter on these closed values, so this witness
specifically guards the otherwise-invisible orientation seam. -/
theorem wrong_raw_accumulator_orientation_rejected :
    ¬ List.Forall₂ RuntimeTermAgrees
      [.integer 1, .integer 2]
      (copyFindallBag 0 [.gnd (.int 2), .gnd (.int 1)]).values := by
  simpa [copyFindallBag, copyFindallAtom, resolutionAtomClosed,
    PersistentSubst.atomClosed] using swapped_integer_bag_rejected

/-- A fully closed, ground, empty collector inhabits the payload bridge.
This rules out a vacuous interface whose database/world or copy-frontier
premises cannot be jointly satisfied. -/
theorem ground_empty_exit_payload_inhabited :
    let cell :=
      sourceCollectionCell 0 ⟨0⟩ 0
        (.integer 7) (.integer 9) [] [] []
    let control : Control :=
      { cur := none
        alts := []
        qterm := .gnd (.int 0)
        answers := [] }
    let before : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control := control }
    let frame : FindallFrame :=
      { preCut := 0
        preCollection := 0
        outer := control
        template := .gnd (.int 7)
        result := .gnd (.int 9)
        rest := []
        binding := [] }
    FindallExitPayloadAgrees ({} : Session) cell before frame := by
  dsimp
  constructor
  · exact
      { template := TermAgrees.integer 7
        output := TermAgrees.integer 9
        tail := GoalsAgree.nil
        entryOutput := by
          simpa [sourceCollectionCell] using (TermAgrees.integer 9)
        entryTail := by
          simpa [sourceCollectionCell, substCompiledGoals] using
            (GoalsAgree.nil : GoalsAgree [] []) }
  · exact
      PrologStateBridge.empty_session_relates
        (CopyDebtFrontier [] [])
        (CollectionCopyFrontier.empty 0 0)

/-- A fully closed two-answer collector inhabits the nonempty payload path.
The same variable template is materialized first as `1` and then as `2`;
both the independent and fine accumulators are reverse discovery order, and
the certified payment phase takes exactly two steps. -/
theorem ground_two_answer_exit_payload_inhabited :
    let template : Term := .variable (.source "x")
    let firstBindings : Substitution :=
      [(.source "x", .integer 1)]
    let secondBindings : Substitution :=
      [(.source "x", .integer 2)]
    let initialSession : Session := {}
    let first :=
      collectTemplate initialSession template firstBindings
    let second :=
      collectTemplate first.session template secondBindings
    let cell :=
      sourceCollectionCell 0 ⟨0⟩ 0 template (.integer 9) [] []
        [second.prepared.copied, first.prepared.copied]
    let control : Control :=
      { cur := none
        alts := []
        qterm := .gnd (.int 0)
        answers := [.gnd (.int 2), .gnd (.int 1)] }
    let before : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control := control }
    let frame : FindallFrame :=
      { preCut := 0
        preCollection := 0
        outer := control
        template := .var "x"
        result := .gnd (.int 9)
        rest := []
        binding := [] }
    FindallExitPayloadAgrees second.session cell before frame ∧
      FindallCopy.BagCopyStepsN 2
        (FindallCopy.BagCopyState.initial
          before.persistent.counter before.control.answerValues)
        (paidCollectionCopyState
          before.persistent.counter before.control.answers) := by
  dsimp
  have initial :
      CollectionSessionRelates [] [] ({} : Session)
        ({ world := {}, counter := 0 } : Persistent) :=
    PrologStateBridge.empty_session_relates
      (CopyDebtFrontier [] [])
      (CollectionCopyFrontier.empty 0 0)
  have first :
      CollectionSessionRelates
        [(collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).prepared.copied]
        [.gnd (.int 1)]
        (collectTemplate ({} : Session) (.variable (.source "x"))
          [(.source "x", .integer 1)]).session
        ({ world := {}, counter := 0 } : Persistent) := by
    apply initial.collect (.variable (.source "x"))
      [(.source "x", .integer 1)] (.gnd (.int 1))
    · simpa [Substitution.applyTerm, Term.instantiateOne] using
        (TermAgrees.integer 1)
    · intro left right leftMember
      simp [PeTTaSpec.PrologCore.Copy.copyVariables,
        PeTTaSpec.PrologCore.Resolver.termVariables,
        Substitution.applyTerm, Term.instantiateOne] at leftMember
    · rfl
    · exact Nat.le_refl 0
    · simp [Atom.vars, resolutionSeedHighWaterNames]
  have second :
      CollectionSessionRelates
        [(collectTemplate
            (collectTemplate ({} : Session) (.variable (.source "x"))
              [(.source "x", .integer 1)]).session
            (.variable (.source "x"))
            [(.source "x", .integer 2)]).prepared.copied,
          (collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).prepared.copied]
        [.gnd (.int 2), .gnd (.int 1)]
        (collectTemplate
          (collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).session
          (.variable (.source "x"))
          [(.source "x", .integer 2)]).session
        ({ world := {}, counter := 0 } : Persistent) := by
    apply first.collect (.variable (.source "x"))
      [(.source "x", .integer 2)] (.gnd (.int 2))
    · simpa [Substitution.applyTerm, Term.instantiateOne] using
        (TermAgrees.integer 2)
    · intro left right leftMember
      simp [PeTTaSpec.PrologCore.Copy.copyVariables,
        PeTTaSpec.PrologCore.Resolver.termVariables,
        Substitution.applyTerm, Term.instantiateOne] at leftMember
    · rfl
    · exact Nat.le_refl 0
    · simp [Atom.vars, resolutionSeedHighWaterNames]
  have payload :
      FindallExitPayloadAgrees
        (collectTemplate
          (collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).session
          (.variable (.source "x"))
          [(.source "x", .integer 2)]).session
        (sourceCollectionCell 0 ⟨0⟩ 0
          (.variable (.source "x")) (.integer 9) [] []
          [(collectTemplate
              (collectTemplate ({} : Session) (.variable (.source "x"))
                [(.source "x", .integer 1)]).session
              (.variable (.source "x"))
              [(.source "x", .integer 2)]).prepared.copied,
            (collectTemplate ({} : Session) (.variable (.source "x"))
              [(.source "x", .integer 1)]).prepared.copied])
        { persistent := { world := {}, counter := 0 }
          control :=
            { cur := none
              alts := []
              qterm := .gnd (.int 0)
              answers := [.gnd (.int 2), .gnd (.int 1)] } }
        { preCut := 0
          preCollection := 0
          outer :=
            { cur := none
              alts := []
              qterm := .gnd (.int 0)
              answers := [.gnd (.int 2), .gnd (.int 1)] }
          template := .var "x"
          result := .gnd (.int 9)
          rest := []
          binding := [] } := by
    constructor
    · exact
        { template := TermAgrees.sourceVariable "x"
          output := TermAgrees.integer 9
          tail := GoalsAgree.nil
          entryOutput := by
            simpa [sourceCollectionCell] using (TermAgrees.integer 9)
          entryTail := by
            simpa [sourceCollectionCell, substCompiledGoals] using
              (GoalsAgree.nil : GoalsAgree [] []) }
    · exact second
  refine ⟨payload, ?_⟩
  simpa only [sourceCollectionCell, List.length_cons, List.length_nil,
    Nat.reduceAdd, Control.answerValues, List.reverse_cons,
    List.reverse_nil] using payload.boundedPayment.1

end PLeaTTa.PrologFindallExitPayloadBridge
