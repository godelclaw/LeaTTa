-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallTailForestBridge
Purpose: Freeze complete supported caller-tail forests across local findall
  collection and materialize them under one shared residual alpha
Trusted boundary: none
Main exports: FindallFrameForestPayloadAgrees,
  FindallFrameForestPayloadAgrees.materializedTailForest
-/
import PLeaTTa.Proofs.PrologFindallVariantExitPayloadBridge
import PLeaTTa.Proofs.PrologFindallAnswerBridge
import PLeaTTa.Proofs.PrologGoalControlCarryBridge

namespace PLeaTTa.PrologFindallTailForestBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologFindallBagAlphaBridge
open PrologFindallFrameZipperBridge
open PrologFindallVariantExitPayloadBridge
open PrologGoalControlCarryBridge
open PrologGoalTermForestBridge
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge
open DemandDrivenStep

/-!
`FindallFrameVariantPayloadAgrees` freezes the historical task and raw caller
tail but intentionally predates goal-level residual materialization.  This
additive packet strengthens it with one proof-indexed complete tail forest
and the historical support needed to transport that forest through the
single cumulative residual representative.

The forest is stored once at entry.  It cannot be reselected leaf by leaf at
exit, and a deterministic traversal stores every executable soft-cut packet;
private collection steps neither inspect nor modify either object.
-/

/-- Alpha-aware findall frame packet enriched with one complete supported
forest for the exact frozen caller-tail agreement.  The certificate remains
in `Prop`; clients consume its existential forest only inside proofs. -/
def FindallFrameForestPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (cell : SourceCollectionCell) (frame : FindallFrame) : Prop :=
  ∃ variant :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame,
    ∃ (forest : AlphaTermForest alpha)
        (controls : List MaterializedSoftCutControl),
      NormalizedAlphaGoalsTermForest alpha barrier variant.tail forest ∧
        AlphaTermsSupported alpha support forest.references ∧
        controls = materializedSoftCutControlsGoals frame.binding frame.rest

namespace FindallFrameForestPayloadAgrees

/-- The explicit agreement-indexed support premise constructs the stronger
frozen packet without choosing a second tail agreement. -/
theorem ofVariant
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (variant :
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame)
    (supported :
      PLeaTTa.PrologGoalTermForestBridge.NormalizedAlphaGoalsAgree.ForestSupported
        support variant.tail) :
    FindallFrameForestPayloadAgrees alpha support barrier cell frame := by
  obtain ⟨forest, tailRelation, tailSupported⟩ := supported
  exact ⟨variant, forest,
    materializedSoftCutControlsGoals frame.binding frame.rest,
    tailRelation, tailSupported, rfl⟩

/-- The stored forest really covers every variable in the frozen independent
caller tail.  Hidden executable fields may contribute additional leaves. -/
theorem coversTail
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
    FindallFrameForestPayloadAgrees alpha support barrier cell frame) :
    ∃ forest : AlphaTermForest alpha,
      List.Subset (goalsVariables cell.tail) forest.referenceVariables ∧
        List.Subset (PLeaTTa.specializationGoalsVars frame.rest)
          forest.executableVariables := by
  obtain ⟨_variant, forest, _controls, tailRelation, _tailSupported,
      _controlRelation⟩ := agreement
  exact ⟨forest, tailRelation.covers, tailRelation.coversExecutable⟩

/-- One historical cumulative representative materializes the entire frozen
tail forest under one shared runtime alpha.  Cross-goal aliases therefore
cannot be split or merged by independent leaf witnesses. -/
theorem materializedTailForest
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameForestPayloadAgrees alpha support barrier cell frame) :
    ∃ (variant :
        FindallFrameVariantPayloadAgrees alpha support barrier cell frame)
      (forest : AlphaTermForest alpha)
      (controls : List MaterializedSoftCutControl)
      (referenceSupport : List LogicVar) (executableSupport : List String),
      FindallFrameVariantPayloadAgrees alpha support barrier cell frame ∧
        NormalizedAlphaGoalsTermForest alpha barrier variant.tail forest ∧
        controls = materializedSoftCutControlsGoals frame.binding frame.rest ∧
        List.Subset (goalsVariables cell.tail) forest.referenceVariables ∧
        List.Subset (PLeaTTa.specializationGoalsVars frame.rest)
          forest.executableVariables ∧
        RuntimeTermsAgreesWith referenceSupport executableSupport
          (cell.entryBindings.applyTerms forest.references)
          (forest.executables.map (PLeaTTa.subst frame.binding)) := by
  obtain ⟨variant, forest, controls, tailRelation, tailSupported,
      controlsExact⟩ := agreement
  obtain ⟨canonical, referenceBase, data⟩ := variant.data
  obtain ⟨referenceSupport, executableSupport, materialized⟩ :=
    PLeaTTa.PrologResidualForestBridge.TaskDataAgrees.runtimeTermsAgreesWith
      data forest.agreement tailSupported
  exact ⟨variant, forest, controls, referenceSupport, executableSupport,
    variant, tailRelation, controlsExact, tailRelation.covers,
    tailRelation.coversExecutable, materialized⟩

/-- The frozen caller packet yields one exact semantic continuation relation:
the materialized source goals, the actual substituted executable goals, all
ordinary term leaves under one residual alpha, and every hidden soft-cut
control occurrence come from the same entry witness. -/
theorem materializedTailControl
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameForestPayloadAgrees alpha support barrier cell frame) :
    ∃ variant :
        FindallFrameVariantPayloadAgrees alpha support barrier cell frame,
      MaterializedControlAgrees barrier cell.entryBindings frame.binding
        cell.tail frame.rest variant.tail
        (cell.entryBindings.applyGoals cell.tail)
        (PLeaTTa.substCompiledGoals frame.binding frame.rest) := by
  obtain ⟨variant, forest, controls, tailRelation, tailSupported,
      controlsExact⟩ := agreement
  obtain ⟨canonical, referenceBase, data⟩ := variant.data
  let payload := data.withControl variant.tail
  have supported :
      PLeaTTa.PrologGoalControlCarryBridge.NormalizedAlphaGoalsAgree.ControlSupported
        support frame.binding payload.control := by
    exact ⟨forest, controls, tailRelation, tailSupported, controlsExact⟩
  exact ⟨variant,
    PLeaTTa.PrologGoalControlCarryBridge.TaskPayloadAgrees.materializeControl
      payload supported⟩

/-- A private generator answer changes only the collector accumulator and
persistent copy frontier.  The caller tail, entry binding, executable frame,
and its one frozen forest packet remain literally unchanged. -/
theorem afterAnswer
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    (agreement :
      FindallFrameForestPayloadAgrees alpha support barrier cell frame)
    (childAfter : Session) (answerBindings : Substitution) :
    FindallFrameForestPayloadAgrees alpha support barrier
      (PrologFindallAnswerBridge.afterAnswer cell childAfter answerBindings)
      frame := by
  obtain ⟨variant, forest, controls, tailRelation, tailSupported,
      controlsExact⟩ := agreement
  have variantAfter :
      FindallFrameVariantPayloadAgrees alpha support barrier
        (PrologFindallAnswerBridge.afterAnswer cell childAfter answerBindings)
        frame := by
    simpa [FindallFrameVariantPayloadAgrees,
      PrologFindallAnswerBridge.afterAnswer] using variant
  have tailProofEq : variantAfter.tail = variant.tail :=
    Subsingleton.elim _ _
  refine ⟨variantAfter, forest, controls, ?_, tailSupported, ?_⟩
  · rw [tailProofEq]
    exact tailRelation
  · exact controlsExact

end FindallFrameForestPayloadAgrees

end PLeaTTa.PrologFindallTailForestBridge
