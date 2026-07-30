-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologOrdinaryStepBridge
Purpose: Relate compiler-erased local task administration to exact zero-step
  executable prefixes while retaining cumulative substitution and persistent
  state agreement.
Trusted boundary: none
Main exports:
  NormalizedAlphaGoalsAgree,
  ReadyTaskRelates,
  administrative_prefix_correspondence
-/
import PLeaTTa.Proofs.PrologActivationUnifierBridge
import PLeaTTa.Proofs.PrologCanonicalMguSimulation
import PLeaTTa.Proofs.PrologSequentialMgu
import PLeaTTa.Proofs.PrologStateBridge
import PLeaTTa.Proofs.DemandDrivenCallStep

namespace PLeaTTa.PrologOrdinaryStepBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologStateBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologMguDirectSimulation
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologPrefilterBridge
open PrologSequentialMgu
open PrologActivationUnifierBridge
open PrologCanonicalMguSimulation
open DemandDrivenStep

/-!
The independent goal language retains two administrative forms which the
compiler removes before executable control starts:

* `truth` contributes no executable goal;
* a top-level `conjunction` wrapper is flattened into the surrounding goal
  list.

They are genuine independent `RawStep`s, so an exact state bridge cannot
pretend that they are executable steps.  Conversely, inserting a dummy
executable transition would invent behavior absent from the sealed machine.
This file represents the mismatch as a finite, strictly ranked source-only
prefix paired with an exact zero-step executable prefix.

The relation below is not a new compiler semantics.  It is the existing
`AlphaGoalsAgree`, closed only under those two source administrative forms.
Its task-state layer retains the cumulative residual-MGU valuation produced
by clause activation and the already-proved `SessionRelatesPersistent`
database/world and fresh-frontier relation.
-/

/-- Runtime-alpha goal agreement after erasing source `truth` nodes and
flattening source conjunction wrappers.  Every non-administrative goal still
requires the existing constructor-specific `AlphaGoalAgrees` evidence. -/
inductive NormalizedAlphaGoalsAgree
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | nil : NormalizedAlphaGoalsAgree alpha barrier [] []
  | truth {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables) :
      NormalizedAlphaGoalsAgree alpha barrier
        (.truth :: references) executables
  | cons {reference : PeTTaSpec.PrologCore.Goal}
      {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (head : AlphaGoalAgrees alpha barrier reference executable)
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables) :
      NormalizedAlphaGoalsAgree alpha barrier
        (reference :: references) (executable :: executables)
  | conjunction {referenceBlock referenceTail :
        List PeTTaSpec.PrologCore.Goal}
      {executableBlock executableTail : List PLeaTTa.Goal}
      (block :
        NormalizedAlphaGoalsAgree alpha barrier
          referenceBlock executableBlock)
      (tail :
        NormalizedAlphaGoalsAgree alpha barrier
          referenceTail executableTail) :
      NormalizedAlphaGoalsAgree alpha barrier
        (.conjunction referenceBlock :: referenceTail)
        (executableBlock ++ executableTail)

namespace NormalizedAlphaGoalsAgree

/-- The sealed machine retains two spellings of primitive equality.
`compileAlias` is defensive compiler metadata, but both constructors execute
the same `unifyB` operation.  Keeping the spelling explicit lets the bridge
invert the executable head without identifying the constructors. -/
inductive ExecutableUnifySpelling where
  | equality
  | compilerAlias
deriving DecidableEq

/-- Reconstruct the exact executable goal selected by one equality spelling. -/
def ExecutableUnifySpelling.goal :
    ExecutableUnifySpelling → Metta.Atom → Metta.Atom → PLeaTTa.Goal
  | .equality, left, right => .eq left right
  | .compilerAlias, left, right => .compileAlias left right

/-- Concatenation preserves the exact flattened executable spine. -/
theorem append
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {leftReference rightReference : List PeTTaSpec.PrologCore.Goal}
    {leftExecutable rightExecutable : List PLeaTTa.Goal}
    (left :
      NormalizedAlphaGoalsAgree alpha barrier
        leftReference leftExecutable)
    (right :
      NormalizedAlphaGoalsAgree alpha barrier
        rightReference rightExecutable) :
    NormalizedAlphaGoalsAgree alpha barrier
      (leftReference ++ rightReference)
      (leftExecutable ++ rightExecutable) := by
  induction left with
  | nil =>
      simpa using right
  | truth tail inductionHypothesis =>
      exact .truth inductionHypothesis
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis
  | conjunction block tail blockIH tailIH =>
      simpa [List.append_assoc] using
        NormalizedAlphaGoalsAgree.conjunction block tailIH

/-- Exact compiler/runtime alpha agreement embeds without weakening any
non-administrative constructor. -/
theorem ofAlphaGoalsAgree
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : AlphaGoalsAgree alpha barrier references executables) :
    NormalizedAlphaGoalsAgree alpha barrier references executables := by
  cases agreement with
  | nil =>
      exact .nil
  | cons head tail =>
      exact .cons head (ofAlphaGoalsAgree tail)
  | conjunction block tail =>
      exact .conjunction
        (ofAlphaGoalsAgree block)
        (ofAlphaGoalsAgree tail)

/-- Consuming one source truth node leaves the executable spine unchanged. -/
theorem afterTruth
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.truth :: references) executables) :
    NormalizedAlphaGoalsAgree alpha barrier references executables := by
  cases agreement with
  | truth tail =>
      exact tail
  | cons head tail =>
      cases head

/-- Flattening one source conjunction wrapper leaves the executable spine
unchanged. -/
theorem afterConjunction
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {nested rest : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.conjunction nested :: rest) executables) :
    NormalizedAlphaGoalsAgree alpha barrier
      (nested ++ rest) executables := by
  cases agreement with
  | conjunction block tail =>
      exact block.append tail
  | cons head tail =>
      cases head

/-- A non-administrative source cut exposes exactly the executable cut at the
barrier carried by the alpha-goal relation.  No other executable constructor
can be selected by administrative normalization. -/
theorem cutHead
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.cut :: references) executables) :
    ∃ executableTail,
      executables = .cutAt barrier :: executableTail ∧
        NormalizedAlphaGoalsAgree alpha barrier
          references executableTail := by
  cases agreement with
  | cons head tail =>
      cases head with
      | cut =>
          exact ⟨_, rfl, tail⟩

/-- A non-administrative source equality exposes exactly one of the two
sealed equality spellings, together with the same operand agreements and
normalized continuation.  No other executable constructor can be selected
by administrative normalization. -/
theorem unifyHead
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.unify left right :: references) executables) :
    ∃ (spelling : ExecutableUnifySpelling)
        (executableLeft executableRight : Metta.Atom)
        (executableTail : List PLeaTTa.Goal),
      executables =
          spelling.goal executableLeft executableRight :: executableTail ∧
        AlphaTermAgrees alpha left executableLeft ∧
        AlphaTermAgrees alpha right executableRight ∧
        NormalizedAlphaGoalsAgree alpha barrier
          references executableTail := by
  cases agreement with
  | cons head tail =>
      cases head with
      | unify left right =>
          exact ⟨.equality, _, _, _, rfl, left, right, tail⟩
      | compileAlias left right =>
          exact ⟨.compilerAlias, _, _, _, rfl, left, right, tail⟩

end NormalizedAlphaGoalsAgree

/-- One source-only administrative transition at the active leftmost goal. -/
inductive AdministrativeStep :
    List PeTTaSpec.PrologCore.Goal →
      List PeTTaSpec.PrologCore.Goal → Prop where
  | truth (rest : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStep (.truth :: rest) rest
  | conjunction (nested rest : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStep (.conjunction nested :: rest) (nested ++ rest)

/-- Exact transition-counted closure of the source-only administrative
fragment. -/
inductive AdministrativeStepsN :
    Nat → List PeTTaSpec.PrologCore.Goal →
      List PeTTaSpec.PrologCore.Goal → Prop where
  | zero (goals : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStepsN 0 goals goals
  | succ (count : Nat) (before middle after :
        List PeTTaSpec.PrologCore.Goal)
      (head : AdministrativeStep before middle)
      (tail : AdministrativeStepsN count middle after) :
      AdministrativeStepsN (count + 1) before after

mutual

/-- Number of source administrative nodes exposed by recursively flattening
only conjunction wrappers.  Administrative nodes hidden beneath other
control constructors are not active task steps and are deliberately not
counted until that constructor opens them. -/
def administrativeGoalRank : PeTTaSpec.PrologCore.Goal → Nat
  | .truth => 1
  | .conjunction goals => administrativeRank goals + 1
  | _ => 0

/-- Finite rank for compiler-erased administration in one active task. -/
def administrativeRank : List PeTTaSpec.PrologCore.Goal → Nat
  | [] => 0
  | goal :: goals =>
      administrativeGoalRank goal + administrativeRank goals

end

@[simp] theorem administrativeRank_append
    (left right : List PeTTaSpec.PrologCore.Goal) :
    administrativeRank (left ++ right) =
      administrativeRank left + administrativeRank right := by
  induction left with
  | nil =>
      simp [administrativeRank]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, administrativeRank, inductionHypothesis,
        Nat.add_assoc]

/-- Every administrative transition spends exactly one unit of the finite
source rank. -/
theorem AdministrativeStep.rank_exact
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after) :
    administrativeRank before = administrativeRank after + 1 := by
  cases step with
  | truth rest =>
      simp [administrativeRank, administrativeGoalRank]
      omega
  | conjunction nested rest =>
      simp [administrativeRank, administrativeGoalRank,
        administrativeRank_append]
      omega

/-- An exact administrative prefix spends exactly its transition count. -/
theorem AdministrativeStepsN.rank_exact
    {count : Nat} {before after : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count before after) :
    administrativeRank before =
      count + administrativeRank after := by
  induction steps with
  | zero goals =>
      simp
  | succ count before middle after head tail inductionHypothesis =>
      have first := head.rank_exact
      omega

/-- One administrative goal-list step is the corresponding actual local
`RawStep`, with no observations, cut signal, session change, or binding
change. -/
theorem AdministrativeStep.rawStep
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    RawStep session (.task scope before bindings) [] .none session
      (.running (.task scope after bindings)) := by
  cases step with
  | truth _ =>
      exact RawStep.taskTruth scope _ bindings session
  | conjunction _ _ =>
      exact RawStep.taskConjunction scope _ _ bindings session

/-- One administrative goal-list step is also one actual public local-search
transition. -/
theorem AdministrativeStep.transition
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    Transition
      (.running session (.task scope before bindings)) []
      (.running session (.task scope after bindings)) := by
  exact .ordinary _ _ _ _ _ (step.rawStep scope bindings session)

/-- The abstract administrative prefix is inhabited by an exact public
source execution with the same count and an empty observation trace. -/
theorem AdministrativeStepsN.sourceSteps
    {count : Nat} {before after : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
      (.running session (.task scope before bindings)) []
      (.running session (.task scope after bindings)) := by
  induction steps with
  | zero goals =>
      exact .zero _
  | succ count before middle after head tail inductionHypothesis =>
      simpa using
        PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ count
          (.running session (.task scope before bindings))
          (.running session (.task scope middle bindings))
          (.running session (.task scope after bindings))
          [] [] (head.transition scope bindings session)
          inductionHypothesis

/-- Actual task payload agreement after compiler-erased administration.  The
independent cumulative binding remains explicit rather than being folded into
the goal syntax. -/
structure TaskPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (runtime : Metta.Subst)
    (references : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal) : Prop where
  alphaShared : SharedRuntimeAlpha alpha
  canonicalWellFormed : canonical.WellFormed
  bindingShape :
    current = TreeSubstitution.reify canonical ++ referenceBase
  control :
    NormalizedAlphaGoalsAgree alpha barrier references executables
  valuation :
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase runtime

/-- The exact post-clause-activation payload already proved by the MGU bridge
embeds into administrative-normalized task agreement. -/
theorem TaskPayloadAgrees.ofActivated
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst}
    {entered : PeTTaSpec.PrologCore.Resolver.EnteredClause}
    {executables : List PLeaTTa.Goal}
    (agreement :
      ActivatedTaskAgrees alpha support barrier canonical referenceBase
        runtime entered executables) :
    TaskPayloadAgrees alpha support barrier canonical referenceBase
      entered.bindings runtime entered.rawBody executables := by
  exact
    ⟨agreement.1, agreement.2.1, agreement.2.2.1,
      NormalizedAlphaGoalsAgree.ofAlphaGoalsAgree agreement.2.2.2.1,
      agreement.2.2.2.2⟩

/-- The source task's concrete carried substitution denotes exactly the
canonical residual MGU followed by the older source state.  The retained
well-formedness certificate is load-bearing for the reification round trip. -/
theorem TaskPayloadAgrees.denoteCurrent
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables) :
    Substitution.denote current =
      canonical ++ Substitution.denote referenceBase := by
  rw [agreement.bindingShape, Substitution.denote_append,
    TreeSubstitution.denote_reify agreement.canonicalWellFormed]

/-- The source canonical binding and the hidden canonical representative
which interprets the executable state remain variants after both are
composed with the same older source binding. -/
theorem TaskPayloadAgrees.cumulativeVariants
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionTopological canonical ∧
      Nonempty (PLeaTTa.SubstTopological runtime) ∧
      AlphaValuationAgreesOn alpha support
        (representative ++ Substitution.denote referenceBase) runtime := by
  rcases agreement.valuation with
    ⟨representative, variants, canonicalTopological,
      runtimeTopological, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      runtimeTopological, valuation⟩

/-- One primitive source equality, presented directly in the canonical
equation space after applying the carried binding. -/
def carriedUnifyEquation
    (base : TreeSubstitution) (left right : Term) :
    List TreeEquation :=
  [(TreeSubstitution.apply base (Term.denote left),
    TreeSubstitution.apply base (Term.denote right))]

/-- A real source `UnifyResolution` exposes the well-formed ordered canonical
extension which it prepends to the carried task binding.  The post-binding
denotation is exact, not merely a factorization statement. -/
theorem TaskPayloadAgrees.sourceUnifyExtension
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables)
    {left right : Term} {result : Substitution}
    (resolved : UnifyResolution current left right result) :
    ∃ extension : TreeSubstitution,
      OrderedTreeMgu
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase) left right)
        extension ∧
      extension.WellFormed ∧
      result = TreeSubstitution.reify extension ++ current ∧
      Substitution.denote result =
        extension ++
          (canonical ++ Substitution.denote referenceBase) := by
  rcases resolved with
    ⟨sourceExtension, computed, concreteResultShape⟩
  rcases computed with
    ⟨extension, ordered, sourceExtensionShape⟩
  have extensionWellFormed :
      extension.WellFormed :=
    ordered.binding_wellFormed
      (denoteEquations_wellFormed
        [(current.applyTerm left, current.applyTerm right)])
  have extensionOrdered :
      OrderedTreeMgu
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase) left right)
        extension := by
    simpa [carriedUnifyEquation, denoteEquations,
      Substitution.denote_applyTerm, agreement.denoteCurrent] using
      ordered
  refine
    ⟨extension, extensionOrdered, extensionWellFormed, ?_, ?_⟩
  · rw [concreteResultShape, sourceExtensionShape]
  · rw [concreteResultShape, Substitution.denote_append,
      sourceExtensionShape,
    TreeSubstitution.denote_reify extensionWellFormed,
    agreement.denoteCurrent]

/-- The source successor of primitive unification is a principal solution
relative to the exact carried canonical state.  This is the source half of
the later `taskUnifySuccess`/`eq_ok` correspondence. -/
theorem TaskPayloadAgrees.sourceUnifyRelative
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables)
    {left right : Term} {result : Substitution}
    (resolved : UnifyResolution current left right result) :
    TreeIsRelativeMgu
      (Substitution.denote result)
      (canonical ++ Substitution.denote referenceBase)
      [(Term.denote left, Term.denote right)] := by
  rcases agreement.sourceUnifyExtension resolved with
    ⟨extension, extensionOrdered, _extensionWellFormed,
      _concreteResultShape, resultShape⟩
  have extensionMgu := extensionOrdered.isMostGeneral
  have extensionMguApplied :
      TreeIsMgu extension
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) := by
    simpa [carriedUnifyEquation,
      TreeSubstitution.applyEquations] using extensionMgu
  have relative := TreeIsMgu.relativeCompose extensionMguApplied
  rw [resultShape]
  exact relative

/-- Every alpha link for a variable which actually occurs in `tree` belongs
to the observable support.  This is deliberately weaker than requiring the
whole alpha graph to remain live: dead clause-local links need not be
retained merely because a different term is being evaluated. -/
def AlphaTreeSupported
    (alpha support : List (LogicVar × String)) (tree : Tree) : Prop :=
  TreeVariablesSatisfy
    (fun identity =>
      ∀ name, (identity, name) ∈ alpha →
        (identity, name) ∈ support)
    tree

/-- Support-indexed counterpart of `canonicalRuntimeAgrees_apply`.

Only alpha links traversed by the represented tree must be observable.  The
proof follows the canonical/runtime relation structurally, so a caller
cannot satisfy the premise with an unrelated live variable. -/
theorem canonicalRuntimeAgrees_apply_on
    {alpha support : List (LogicVar × String)}
    {tree : Tree} {atom : Metta.Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Metta.Subst}
    (valuation :
      AlphaValuationAgreesOn alpha support canonical runtime)
    (supported : AlphaTreeSupported alpha support tree) :
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  induction agreement with
  | «variable» linked =>
      simp only [AlphaTreeSupported, TreeVariablesSatisfy] at supported
      exact valuation (supported _ linked)
  | atom notTrue notFalse =>
      simpa using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa using (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa using (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa using (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa using (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa using (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | partialValue arguments inductionHypothesis =>
      simp only [AlphaTreeSupported, TreeVariablesSatisfy,
        TreesVariablesSatisfy] at supported
      simpa [partialC, partialTagA, TreeSubstitution.apply_node,
        PLeaTTa.subst_chainOf] using
        (CanonicalRuntimeAgrees.partialValue
          (inductionHypothesis supported.2.1))
  | nil =>
      simpa [nilA] using (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simp only [AlphaTreeSupported, TreeVariablesSatisfy,
        TreesVariablesSatisfy] at supported
      simpa [TreeSubstitution.apply_node, consC,
        PLeaTTa.subst_expr] using
        (CanonicalRuntimeAgrees.cons
          (headInduction supported.1)
          (tailInduction supported.2.1))

/-- A source-successful primitive equality forces the actual executable
top-level unifier to succeed on the corresponding runtime-substituted atoms.

`supportCovers` is the explicit live-continuation obligation: every alpha
link needed by these two terms must remain in the support-indexed valuation.
The theorem does not manufacture that compiler/caller invariant.  Under it,
the old source and hidden-runtime canonical states are variant bases; the
source and executable residual MGUs therefore produce variant cumulative
successors even when both residual orientations differ. -/
theorem TaskPayloadAgrees.executableUnifyTopExact
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables)
    {left right : Term} {executableLeft executableRight : Metta.Atom}
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    {result : Substitution}
    (resolved : UnifyResolution current left right result) :
    ∃ representative sourceExtension executableCanonical generated,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionTopological canonical ∧
      AlphaValuationAgreesOn alpha support
        (representative ++ Substitution.denote referenceBase) runtime ∧
      OrderedTreeMgu
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase) left right)
        sourceExtension ∧
      TreeIsMgu sourceExtension
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) ∧
      sourceExtension.WellFormed ∧
      result = TreeSubstitution.reify sourceExtension ++ current ∧
      TreeIsMgu executableCanonical
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) ∧
      Substitution.denote result =
        sourceExtension ++
          (canonical ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionVariants
        (Substitution.denote result)
        (executableCanonical ++
          (representative ++ Substitution.denote referenceBase)) ∧
      PLeaTTa.unifyTopExact
          (PLeaTTa.subst runtime executableLeft)
          (PLeaTTa.subst runtime executableRight) =
        some generated ∧
      AlphaValuationAgrees alpha executableCanonical generated ∧
      TreeSubstitutionTopological executableCanonical ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      Nonempty (PLeaTTa.SubstTopological runtime) := by
  rcases agreement.sourceUnifyExtension resolved with
    ⟨sourceExtension, sourceExtensionOrdered, sourceExtensionWellFormed,
      sourceConcreteResultShape, sourceResultShape⟩
  have sourceExtensionMgu := sourceExtensionOrdered.isMostGeneral
  have sourceExtensionApplied :
      TreeIsMgu sourceExtension
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) := by
    simpa [carriedUnifyEquation,
      TreeSubstitution.applyEquations] using sourceExtensionMgu
  rcases agreement.cumulativeVariants with
    ⟨representative, bases, canonicalTopological,
      runtimeTopological, valuationOn⟩
  have leftAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote left))
        (PLeaTTa.subst runtime executableLeft) :=
    canonicalRuntimeAgrees_apply_on
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        leftAgreement)
      valuationOn leftSupported
  have rightAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote right))
        (PLeaTTa.subst runtime executableRight) :=
    canonicalRuntimeAgrees_apply_on
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        rightAgreement)
      valuationOn rightSupported
  have sourceRelative :
      TreeIsRelativeMgu
        (sourceExtension ++
          (canonical ++ Substitution.denote referenceBase))
        (canonical ++ Substitution.denote referenceBase)
        [(Term.denote left, Term.denote right)] :=
    TreeIsMgu.relativeCompose sourceExtensionApplied
  have sourceFactorsRepresentative :
      TreeFactorsThrough
        (sourceExtension ++
          (canonical ++ Substitution.denote referenceBase))
        (representative ++ Substitution.denote referenceBase) :=
    TreeFactorsThrough.trans sourceRelative.1 bases.1
  rcases sourceFactorsRepresentative with
    ⟨candidate, candidateFactors⟩
  have candidateUnifies :
      TreeUnifiesEquations candidate
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) := by
    intro normalized normalizedMember
    simp only [TreeSubstitution.applyEquations, List.mem_map]
      at normalizedMember
    obtain ⟨equation, member, rfl⟩ := normalizedMember
    rw [← candidateFactors equation.1, ← candidateFactors equation.2]
    exact sourceRelative.2.1 equation member
  obtain ⟨runtimeOrdered, runtimeDerivation⟩ :=
    OrderedTreeMgu.complete candidate candidateUnifies
  obtain
    ⟨executableCanonical, generated, generatedExact,
      _generatedAgreement, executableTopological, generatedTopological,
      generatedValuation, executableMgu,
      _executableFactorsOrdered, _orderedFactorsExecutable⟩ :=
    PLeaTTa.PrologCanonicalMguSimulation.OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
      agreement.alphaShared leftAfter rightAfter runtimeDerivation
  have executableMguApplied :
      TreeIsMgu executableCanonical
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote left, Term.denote right)]) := by
    simpa [TreeSubstitution.applyEquations] using executableMgu
  have successors :=
    sequential_mgu_composites_are_variants
      bases sourceExtensionApplied executableMguApplied
  refine
    ⟨representative, sourceExtension, executableCanonical, generated,
      bases, canonicalTopological, valuationOn,
      sourceExtensionOrdered, sourceExtensionApplied,
      sourceExtensionWellFormed, sourceConcreteResultShape,
      executableMguApplied, sourceResultShape, ?_,
      generatedExact, generatedValuation,
      executableTopological, generatedTopological, runtimeTopological⟩
  rw [sourceResultShape]
  exact successors

/-- One successful primitive equality installs the actual executable MGU,
trims it on the exact continuation, and preserves the task payload relation.

The support premises remain caller-visible.  `leftSupported` and
`rightSupported` say that evaluating this equality does not need a dead
alpha link; `supportIncluded` permits restricting the newly generated full
valuation; `runtimeAvoids` is the carried-state separation needed by eager
composition; and `live` is exactly the machine trim obligation. -/
theorem TaskPayloadAgrees.afterUnifySuccess
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term} {executableLeft executableRight : Metta.Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {wholeExecutables executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references)
        wholeExecutables)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (tailControl :
      NormalizedAlphaGoalsAgree alpha barrier references executables)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    (qterm : Metta.Atom)
    (live : AlphaRuntimeNamesLive support executables qterm)
    {result : Substitution}
    (resolved : UnifyResolution current left right result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed ∧
      TaskPayloadAgrees alpha support barrier
        (sourceExtension ++ canonical) referenceBase result
        (PLeaTTa.trimFor executables qterm installed)
        references executables := by
  obtain
    ⟨representative, sourceExtension, executableCanonical, generated,
      bases, oldCanonicalTopological, oldValuation,
      sourceExtensionOrdered, _sourceExtensionMgu,
      sourceExtensionWellFormed, sourceConcreteResultShape,
      _executableMgu, sourceResultShape, successorVariants,
      generatedExact, generatedValuation, executableTopological,
      ⟨generatedTopological⟩, ⟨runtimeTopological⟩⟩ :=
    agreement.executableUnifyTopExact leftAgreement rightAgreement
      leftSupported rightSupported resolved
  let installed :=
    PrologMguComposition.installGenerated generated runtime
  have installedExact :
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed := by
    cases generated with
    | nil =>
        simp [PLeaTTa.unifyB, installed,
          PrologMguComposition.installGenerated, generatedExact]
    | cons head tail =>
        simp [PLeaTTa.unifyB, installed,
          PrologMguComposition.installGenerated, generatedExact]
  have leftAvoids :
      PLeaTTa.AtomAvoids runtime
        (PLeaTTa.subst runtime executableLeft) := by
    intro name member
    exact runtimeTopological.subst_resolvesDomain
      runtime executableLeft name member
  have rightAvoids :
      PLeaTTa.AtomAvoids runtime
        (PLeaTTa.subst runtime executableRight) := by
    intro name member
    exact runtimeTopological.subst_resolvesDomain
      runtime executableRight name member
  have generatedAvoidsRuntime :
      PLeaTTa.SubstEntriesAvoid runtime generated :=
    PLeaTTa.unifyTopExact_avoidsExternal runtime
      (PLeaTTa.subst runtime executableLeft)
      (PLeaTTa.subst runtime executableRight)
      generated leftAvoids rightAvoids generatedExact
  have installedTopological :
      PLeaTTa.SubstTopological installed := by
    cases generated with
    | nil =>
        simpa [installed, PrologMguComposition.installGenerated] using
          runtimeTopological
    | cons head tail =>
        simpa [installed, PrologMguComposition.installGenerated] using
          PLeaTTa.SubstTopological.compose_of_avoids
            runtime (head :: tail) runtimeTopological generatedTopological
            generatedAvoidsRuntime
  have sourceEquationsAvoidCanonical :
      TreeEquationsVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys canonical)
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase)
          left right) := by
    intro equation member
    simp only [carriedUnifyEquation, List.mem_singleton] at member
    rcases member with rfl
    have leftOutside :
        TreeVariablesSatisfy
          (fun identity =>
            identity ∉ TreeSubstitution.keys canonical)
          (TreeSubstitution.apply
            (canonical ++ Substitution.denote referenceBase)
            (Term.denote left)) := by
      rw [TreeSubstitution.apply_append]
      exact oldCanonicalTopological.apply_avoids
        (TreeSubstitution.apply
          (Substitution.denote referenceBase) (Term.denote left))
    have rightOutside :
        TreeVariablesSatisfy
          (fun identity =>
            identity ∉ TreeSubstitution.keys canonical)
          (TreeSubstitution.apply
            (canonical ++ Substitution.denote referenceBase)
            (Term.denote right)) := by
      rw [TreeSubstitution.apply_append]
      exact oldCanonicalTopological.apply_avoids
        (TreeSubstitution.apply
          (Substitution.denote referenceBase) (Term.denote right))
    exact ⟨leftOutside, rightOutside⟩
  have sourceCompositeTopological :
      TreeSubstitutionTopological (sourceExtension ++ canonical) :=
    PrologSequentialMgu.OrderedTreeMgu.prepend_topological_of_equations_avoid
      oldCanonicalTopological sourceExtensionOrdered
      sourceEquationsAvoidCanonical
  have cumulativeVariants :
      TreeSubstitutionVariants
        ((sourceExtension ++ canonical) ++
          Substitution.denote referenceBase)
        ((executableCanonical ++ representative) ++
          Substitution.denote referenceBase) := by
    simpa [sourceResultShape, List.append_assoc] using successorVariants
  have installedValuation :
      AlphaValuationAgreesOn alpha support
        ((executableCanonical ++ representative) ++
          Substitution.denote referenceBase)
        installed := by
    intro identity name linked
    have linkedAlpha : (identity, name) ∈ alpha :=
      supportIncluded (identity, name) linked
    have runtimeFixed :
        PLeaTTa.subst runtime (.var name) = .var name :=
      PLeaTTa.subst_var_of_lookup_none runtime name (runtimeAvoids linked)
    have oldAgreement :
        CanonicalRuntimeAgrees alpha
          (TreeSubstitution.apply
            (representative ++ Substitution.denote referenceBase)
            (.variable identity))
          (.var name) := by
      simpa [runtimeFixed] using oldValuation linked
    obtain ⟨oldIdentity, oldShape, oldLinked⟩ :=
      CanonicalRuntimeAgrees.of_runtime_variable oldAgreement
    have oldIdentityEq : oldIdentity = identity :=
      agreement.alphaShared.backward oldLinked linkedAlpha
    have oldFixed :
        TreeSubstitution.apply
            (representative ++ Substitution.denote referenceBase)
            (.variable identity) =
          .variable identity := by
      rw [oldShape, oldIdentityEq]
    have runtimeAtomAvoids :
        PLeaTTa.AtomAvoids runtime (.var name) := by
      intro candidate member
      simp only [Metta.Atom.vars, List.mem_singleton] at member
      subst candidate
      exact runtimeAvoids linked
    have installedEqGenerated :
        PLeaTTa.subst installed (.var name) =
          PLeaTTa.subst generated (.var name) := by
      cases generated with
      | nil =>
          simp only [installed, PrologMguComposition.installGenerated]
          rw [PLeaTTa.subst_eq_self_of_domain_free
            runtime (.var name) runtimeAtomAvoids]
          simp
      | cons head tail =>
          simpa [installed, PrologMguComposition.installGenerated] using
            PLeaTTa.PersistentSubst.subst_compose_eq_generated_of_avoids
              runtime (head :: tail) runtimeTopological
              generatedTopological generatedAvoidsRuntime runtimeAtomAvoids
    have canonicalEq :
        TreeSubstitution.apply
            ((executableCanonical ++ representative) ++
              Substitution.denote referenceBase)
            (.variable identity) =
          TreeSubstitution.apply executableCanonical
            (.variable identity) := by
      simp only [TreeSubstitution.apply_append]
      have oldFixedExpanded :
          TreeSubstitution.apply representative
              (TreeSubstitution.apply
                (Substitution.denote referenceBase)
                (.variable identity)) =
            .variable identity := by
        simpa only [TreeSubstitution.apply_append] using oldFixed
      exact congrArg
        (TreeSubstitution.apply executableCanonical) oldFixedExpanded
    rw [canonicalEq, installedEqGenerated]
    exact generatedValuation linkedAlpha
  have installedCumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support (sourceExtension ++ canonical)
        referenceBase installed :=
    ⟨executableCanonical ++ representative, cumulativeVariants,
      sourceCompositeTopological, ⟨installedTopological⟩,
      installedValuation⟩
  have trimmedCumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support (sourceExtension ++ canonical)
        referenceBase (PLeaTTa.trimFor executables qterm installed) :=
    installedCumulative.trimFor live
  refine
    ⟨sourceExtension, installed, installedExact, ?_⟩
  refine
    ⟨agreement.alphaShared,
      sourceExtensionWellFormed.append agreement.canonicalWellFormed,
      ?_, tailControl, trimmedCumulative⟩
  calc
    result =
        TreeSubstitution.reify sourceExtension ++ current :=
      sourceConcreteResultShape
    _ =
        TreeSubstitution.reify sourceExtension ++
          (TreeSubstitution.reify canonical ++ referenceBase) := by
      rw [agreement.bindingShape]
    _ =
        TreeSubstitution.reify (sourceExtension ++ canonical) ++
          referenceBase := by
      rw [TreeSubstitution.reify_append]
      simp only [List.append_assoc]

/-- Leaf-level state relation for one active independent task and one ready
fine executable state.  The broader Search/OpenConf bridge will add relations
for choices and typed delimiter frames; this leaf pins the actual current
goal/substitution payload and persistent state without constraining those
future frame relations prematurely. -/
def ReadyTaskRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (references : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop :=
  ∃ executableGoals : List PLeaTTa.Goal, ∃ runtime : Metta.Subst,
    SessionRelatesPersistent freshFrontier session state.persistent ∧
      state.control.cur = some (executableGoals, runtime) ∧
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executableGoals

/-- The carried runtime binding is separated from every observable alpha
name, and those names remain trim-roots in the exact continuation after the
active executable head.  This is the explicit state-side obligation needed
by eager MGU composition and `trimFor`; it is not implied by mere goal-shape
agreement. -/
def ReadyUnifyContinuationSafe
    (support : List (LogicVar × String)) (state : OpenConf) : Prop :=
  ∀ {head : PLeaTTa.Goal} {rest : List PLeaTTa.Goal}
      {runtime : Metta.Subst},
    state.control.cur = some (head :: rest, runtime) →
      AlphaRuntimeNamesAvoid support runtime ∧
      AlphaRuntimeNamesLive support rest state.control.qterm

/-- Clause activation plus the persistent state bridge constructs the actual
ready-task relation consumed by ordinary-step simulation. -/
theorem ReadyTaskRelates.ofActivated
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {state : OpenConf}
    {runtime : Metta.Subst}
    {entered : PeTTaSpec.PrologCore.Resolver.EnteredClause}
    {executables : List PLeaTTa.Goal}
    (persistent :
      SessionRelatesPersistent freshFrontier session state.persistent)
    (current : state.control.cur = some (executables, runtime))
    (activated :
      ActivatedTaskAgrees alpha support barrier canonical referenceBase
        runtime entered executables) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session entered.bindings entered.rawBody state := by
  exact
    ⟨executables, runtime, persistent, current,
      TaskPayloadAgrees.ofActivated activated⟩

/-- One source administrative step preserves the exact ready executable
state, cumulative valuation, and persistent bridge. -/
theorem ReadyTaskRelates.afterAdministrativeStep
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {current : Substitution}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (step : AdministrativeStep before after) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session current after state := by
  rcases agreement with
    ⟨executables, runtime, persistent, currentControl, payload⟩
  refine
    ⟨executables, runtime, persistent, currentControl,
      ⟨payload.alphaShared, payload.canonicalWellFormed,
        payload.bindingShape,
        ?_, payload.valuation⟩⟩
  cases step with
  | truth rest =>
      exact payload.control.afterTruth
  | conjunction nested rest =>
      exact payload.control.afterConjunction

/-- A finite source administrative prefix preserves the ready-task relation
without moving the executable state. -/
theorem ReadyTaskRelates.afterAdministrativeSteps
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {current : Substitution}
    {count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (steps : AdministrativeStepsN count before after) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session current after state := by
  induction steps with
  | zero goals =>
      exact agreement
  | succ count before middle after head tail inductionHypothesis =>
      exact inductionHypothesis
        (agreement.afterAdministrativeStep head)

/-- Exact bounded-stutter correspondence for compiler-erased task
administration.

The independent side performs exactly `count` real transitions and emits no
observations.  The executable side performs exactly zero transitions, so it
cannot invent an effect, answer, failure, or scheduling decision.  The rank
equation proves that a fixed source task admits no infinite administrative
stutter. -/
theorem administrative_prefix_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (steps : AdministrativeStepsN count before after) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running session (.task scope before current)) []
        (.running session (.task scope after current)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current after state ∧
      administrativeRank before =
        count + administrativeRank after := by
  exact
    ⟨steps.sourceSteps scope current session,
      .zero (.ready state),
      agreement.afterAdministrativeSteps steps,
      steps.rank_exact⟩

/-! ## Local cut: one real step on each side -/

/-- Exact executable successor of one tagged cut.  The current goal advances
and the alternative/barrier stacks are pruned by the sealed machine's shared
`cutToTracked`; persistent world and fresh allocation are untouched. -/
def cutSuccessor (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) : OpenConf :=
  OpenConf.ofConf
    { state.toConf with
      cur := some (rest, runtime)
      alts := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).1
      barriers := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).2 }
    state.frames

@[simp] theorem cutSuccessor_persistent
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (cutSuccessor state barrier rest runtime).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames =>
      cases persistent
      cases control
      rfl

@[simp] theorem cutSuccessor_current
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (cutSuccessor state barrier rest runtime).control.cur =
      some (rest, runtime) := by
  rfl

/-- An executable cut head takes exactly one real transition in the
findall/call-fine lane.  It cannot be mistaken for either a nested collector
or a local-call installation head. -/
theorem executable_cut_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst)
    (head :
      state.control.cur = some (.cutAt barrier :: rest, runtime)) :
    DemandDrivenCallStep.Step prog gt (.ready state)
      (.ready (cutSuccessor state barrier rest runtime)) := by
  have sealedHead :
      state.toConf.cur = some (.cutAt barrier :: rest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
  have notFindall : ¬ findallRunHead state.toConf := by
    simp [findallRunHead, sealedHead]
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead state := by
    simp [DemandDrivenCallStep.LocalResolveHead, sealedHead]
  apply DemandDrivenCallStep.Step.ordinary state
    (cutSuccessor state barrier rest runtime) notLocalCall
  apply DemandDrivenStep.Step.ordinary state
    (cutSuccessor state barrier rest runtime).toConf notFindall
  simpa [cutSuccessor] using
    (PLeaTTa.Step.cut_at state.toConf barrier rest runtime sealedHead)

/-- Paired local-cut transition on the actual task states.

The independent transition emits no observation and exposes a typed commit
signal; the executable transition performs the exact `cutToTracked` update at
the barrier selected by `AlphaGoalAgrees.cut`.  The task payload, cumulative
MGU valuation, database/world relation, and fresh frontier survive.  This
leaf theorem intentionally does not yet identify the source choice resources
pruned by commit propagation with executable `Alt`s; that is the separate
wrapper/resource-linearity obligation. -/
theorem cut_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {references : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current (.cut :: references) state) :
    ∃ executableTail runtime,
      state.control.cur =
          some (.cutAt barrier :: executableTail, runtime) ∧
        RawStep session (.task scope (.cut :: references) current)
          [] (.commit scope) session
          (.running (.task scope references current)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (cutSuccessor state barrier executableTail runtime)) ∧
        (cutSuccessor state barrier executableTail runtime).persistent =
          state.persistent ∧
        ReadyTaskRelates freshFrontier alpha support barrier canonical
          referenceBase session current references
          (cutSuccessor state barrier executableTail runtime) := by
  rcases agreement with
    ⟨executables, runtime, persistent, currentControl, payload⟩
  rcases payload.control.cutHead with
    ⟨executableTail, executableShape, tailControl⟩
  subst executables
  refine
    ⟨executableTail, runtime, currentControl,
      RawStep.taskCut scope references current session,
      executable_cut_step state barrier executableTail runtime currentControl,
      cutSuccessor_persistent state barrier executableTail runtime, ?_⟩
  refine
    ⟨executableTail, runtime, ?_,
      cutSuccessor_current state barrier executableTail runtime,
      ⟨payload.alphaShared, payload.canonicalWellFormed,
        payload.bindingShape,
        tailControl, payload.valuation⟩⟩
  simpa using persistent

/-! ## Primitive equality: one real step on each side -/

/-- Exact executable successor of one successful primitive equality.  The
sealed machine installs the returned MGU, trims it on the exact continuation,
and leaves persistent world/allocation and suspended frames untouched. -/
def unifySuccessor (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) : OpenConf :=
  OpenConf.ofConf
    { state.toConf with
      cur := some
        (rest, PLeaTTa.trimFor rest state.toConf.qterm installed) }
    state.frames

@[simp] theorem unifySuccessor_persistent
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames =>
      cases persistent
      cases control
      rfl

@[simp] theorem unifySuccessor_current
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.cur =
      some
        (rest, PLeaTTa.trimFor rest state.control.qterm installed) := by
  rfl

/-- Either sealed equality spelling takes exactly one transition in the
findall/call-fine lane.  The spelling is retained through head inversion, but
both cases execute the same proved `unifyB` result and exact successor. -/
theorem executable_unify_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf)
    (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
    (left right : Metta.Atom) (rest : List PLeaTTa.Goal)
    (runtime installed : Metta.Subst)
    (head :
      state.control.cur =
        some (spelling.goal left right :: rest, runtime))
    (unified : PLeaTTa.unifyB runtime left right = some installed) :
    DemandDrivenCallStep.Step prog gt (.ready state)
      (.ready (unifySuccessor state rest installed)) := by
  have sealedHead :
      state.toConf.cur =
        some (spelling.goal left right :: rest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
  have notFindall : ¬ findallRunHead state.toConf := by
    cases spelling <;> simp
      [findallRunHead,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal,
        sealedHead]
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead state := by
    cases spelling <;> simp
      [DemandDrivenCallStep.LocalResolveHead,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal,
        sealedHead]
  apply DemandDrivenCallStep.Step.ordinary state
    (unifySuccessor state rest installed) notLocalCall
  apply DemandDrivenStep.Step.ordinary state
    (unifySuccessor state rest installed).toConf notFindall
  cases spelling with
  | equality =>
      simpa [unifySuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.eq_ok state.toConf left right rest runtime installed
          sealedHead unified)
  | compilerAlias =>
      simpa [unifySuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.compileAlias_ok state.toConf left right rest runtime
          installed sealedHead unified)

/-- Paired successful primitive-unification transition on the actual task
states.

The independent side takes its relational `taskUnifySuccess` step.  Head
inversion selects the actual sealed `eq_ok` or `compileAlias_ok` constructor;
the canonical/runtime MGU simulation proves that the executable call
succeeds, installs a variant of the same composite MGU, and remains related
after exact continuation trimming.  Both persistent states are unchanged. -/
theorem unify_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current result : Substitution}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current
        (.unify left right :: references) state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (safe : ReadyUnifyContinuationSafe support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Metta.Atom)
        (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst),
      ∃ sourceExtension installed,
        state.control.cur =
            some (spelling.goal executableLeft executableRight ::
              executableTail, runtime) ∧
        RawStep session
          (.task scope (.unify left right :: references) current)
          [] .none session (.running (.task scope references result)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (unifySuccessor state executableTail installed)) ∧
        (unifySuccessor state executableTail installed).persistent =
          state.persistent ∧
        ReadyTaskRelates freshFrontier alpha support barrier
          (sourceExtension ++ canonical) referenceBase session result
          references (unifySuccessor state executableTail installed) := by
  rcases agreement with
    ⟨executables, runtime, persistent, currentControl, payload⟩
  rcases payload.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, executableTail,
      executableShape, leftAgreement, rightAgreement, tailControl⟩
  subst executables
  obtain ⟨runtimeAvoids, live⟩ := safe currentControl
  obtain ⟨sourceExtension, installed, installedExact, nextPayload⟩ :=
    payload.afterUnifySuccess leftAgreement rightAgreement tailControl
      leftSupported rightSupported supportIncluded runtimeAvoids
      state.control.qterm live resolved
  refine
    ⟨spelling, executableLeft, executableRight, executableTail, runtime,
      sourceExtension, installed, currentControl,
      RawStep.taskUnifySuccess scope left right references current result
        session resolved,
      executable_unify_step state spelling executableLeft executableRight
        executableTail runtime installed currentControl installedExact,
      unifySuccessor_persistent state executableTail installed, ?_⟩
  refine
    ⟨executableTail,
      PLeaTTa.trimFor executableTail state.control.qterm installed,
      ?_, unifySuccessor_current state executableTail installed,
      nextPayload⟩
  simpa using persistent

/-! ## Anti-vacuity: exact count and strictness -/

/-- The shared successful-step proof does not identify the two executable
spellings.  A consumer that silently rewrites compiler metadata to ordinary
equality therefore cannot justify that rewrite from this bridge. -/
theorem executable_unify_spellings_are_distinct
    (left right : Metta.Atom) :
    NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal
        .equality left right ≠
      NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal
        .compilerAlias left right := by
  simp [NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal]

private def threeAdministrativeGoals :
    List PeTTaSpec.PrologCore.Goal :=
  [.truth, .conjunction [.truth]]

/-- The administrative relation really contains a three-transition prefix;
the count is not reflexive closure dressed as a bounded simulation. -/
theorem three_administrative_steps_are_exact :
    AdministrativeStepsN 3 threeAdministrativeGoals [] := by
  apply AdministrativeStepsN.succ 2 threeAdministrativeGoals
    [.conjunction [.truth]] []
  · exact .truth _
  · apply AdministrativeStepsN.succ 1 [.conjunction [.truth]] [.truth] []
    · exact .conjunction [.truth] []
    · apply AdministrativeStepsN.succ 0 [.truth] [] []
      · exact .truth []
      · exact .zero []

/-- A wrong two-step collapse of the same source prefix is refuted by the
strict administrative rank. -/
theorem three_administrative_steps_are_not_two :
    ¬ AdministrativeStepsN 2 threeAdministrativeGoals [] := by
  intro wrong
  have rank := wrong.rank_exact
  norm_num [threeAdministrativeGoals, administrativeRank,
    administrativeGoalRank] at rank

end PLeaTTa.PrologOrdinaryStepBridge
