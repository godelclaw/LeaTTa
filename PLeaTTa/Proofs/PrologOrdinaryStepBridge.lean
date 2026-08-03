-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologOrdinaryStepBridge
Purpose: Relate compiler-erased local task administration to exact zero-step
  executable prefixes while retaining cumulative substitution and persistent
  state agreement.
Trusted boundary: none
Main exports:
  NormalizedAlphaGoalsAgree,
  TaskDataAgrees,
  ReadyTaskRelates,
  TaskPayloadAgrees.afterUnifySuccessData,
  administrative_prefix_correspondence
-/
import PLeaTTa.Proofs.PrologActivationUnifierBridge
import PLeaTTa.Proofs.PrologBooleanAliasSafety
import PLeaTTa.Proofs.PrologCanonicalMguSimulation
import PLeaTTa.Proofs.PrologGoalMguVariant
import PLeaTTa.Proofs.PrologRuntimeDecode
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
open PrologCanonicalRuntimeReading
open PrologMguBridge
open PrologMguComposition
open PrologMguDirectSimulation
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologPrefilterBridge
open PrologRuntimeDecode
open PrologSequentialMgu
open PrologActivationUnifierBridge
open PrologBooleanAliasSafety
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

/-- An administratively normalized source region with no source goals cannot
hide executable work.  Truth erasure and conjunction flattening may remove
source constructors, but none of the constructors can manufacture an
executable goal from the literal empty source list. -/
theorem executables_eq_nil_of_references_eq_nil
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables)
    (referencesEmpty : references = []) :
    executables = [] := by
  subst references
  cases agreement
  rfl

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

/-- Substitution and valuation agreement independent of executable control
spelling.

This is the reusable data half of `TaskPayloadAgrees`.  Keeping it separate
is load-bearing for segmented continuations: a clause body and its caller may
carry distinct cut barriers while sharing one cumulative source/runtime
valuation. -/
structure TaskDataAgrees
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (runtime : Metta.Subst) : Prop where
  alphaShared : SharedRuntimeAlpha alpha
  canonicalWellFormed : canonical.WellFormed
  bindingShape :
    current = TreeSubstitution.reify canonical ++ referenceBase
  valuation :
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase runtime

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

/-- Forget only the control spelling and barrier from a task payload. -/
theorem TaskPayloadAgrees.data
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables) :
    TaskDataAgrees alpha support canonical referenceBase current runtime :=
  ⟨agreement.alphaShared, agreement.canonicalWellFormed,
    agreement.bindingShape, agreement.valuation⟩

/-- Add an independently proved control spelling to shared task data. -/
theorem TaskDataAgrees.withControl
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (control :
      NormalizedAlphaGoalsAgree alpha barrier references executables) :
    TaskPayloadAgrees alpha support barrier canonical referenceBase current
      runtime references executables :=
  ⟨agreement.alphaShared, agreement.canonicalWellFormed,
    agreement.bindingShape, control, agreement.valuation⟩

/-- Liveness trimming changes only the executable representative carried by
the data relation.  Source binding shape and canonical MGU structure remain
unchanged. -/
theorem TaskDataAgrees.trimFor
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    {goals : List PLeaTTa.Goal} {qterm : Metta.Atom}
    (live : AlphaRuntimeNamesLive support goals qterm) :
    TaskDataAgrees alpha support canonical referenceBase current
      (PLeaTTa.trimFor goals qterm runtime) :=
  ⟨agreement.alphaShared, agreement.canonicalWellFormed,
    agreement.bindingShape, agreement.valuation.trimFor live⟩

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
canonical residual MGU followed by the older source state.  This fact depends
only on the cumulative valuation, not on either side's control spelling. -/
theorem TaskDataAgrees.denoteCurrent
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime) :
    Substitution.denote current =
      canonical ++ Substitution.denote referenceBase := by
  rw [agreement.bindingShape, Substitution.denote_append,
    TreeSubstitution.denote_reify agreement.canonicalWellFormed]

/-- Control-bearing specialization retained for ordinary task consumers. -/
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
      canonical ++ Substitution.denote referenceBase :=
  agreement.data.denoteCurrent

/-- The source canonical binding and the hidden canonical representative
which interprets the executable state remain variants after both are
composed with the same older source binding.  Control is irrelevant. -/
theorem TaskDataAgrees.cumulativeVariants
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionTopological canonical ∧
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
      Nonempty (PLeaTTa.SubstTopological runtime) ∧
      AlphaValuationAgreesOn alpha support
        (representative ++ Substitution.denote referenceBase) runtime := by
  rcases agreement.valuation with
    ⟨representative, variants, canonicalTopological,
      representativeCovered, runtimeTopological, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      representativeCovered, runtimeTopological, valuation⟩

/-- Control-bearing specialization retained for ordinary task consumers. -/
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
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
      Nonempty (PLeaTTa.SubstTopological runtime) ∧
      AlphaValuationAgreesOn alpha support
        (representative ++ Substitution.denote referenceBase) runtime :=
  agreement.data.cumulativeVariants

/-- Exact source-guided readings of the two executable equality operands
against one hidden cumulative representative.

The ordinary payload relation intentionally exposes only the broader
forward runtime agreement, which admits PeTTa aliases such as source
`true` and source `True` at the same executable atom.  Failure reflection
needs the strictly invertible reading instead.  This certificate names no
preferred residual-MGU orientation: it merely records that one
representative variant of the carried source binding gives the exact two
runtime operands. -/
def StrictUnifyOperands
    (alpha : List (LogicVar × String))
    (sourceBase : TreeSubstitution)
    (runtime : Metta.Subst)
    (left right : Term)
    (executableLeft executableRight : Metta.Atom) : Prop :=
  ∃ representative : TreeSubstitution,
    TreeSubstitutionVariants sourceBase representative ∧
      CanonicalRuntimeReading alpha
        (TreeSubstitution.apply representative (Term.denote left))
        (PLeaTTa.subst runtime executableLeft) ∧
      CanonicalRuntimeReading alpha
        (TreeSubstitution.apply representative (Term.denote right))
        (PLeaTTa.subst runtime executableRight)

/-- One primitive source equality, presented directly in the canonical
equation space after applying the carried binding. -/
def carriedUnifyEquation
    (base : TreeSubstitution) (left right : Term) :
    List TreeEquation :=
  [(TreeSubstitution.apply base (Term.denote left),
    TreeSubstitution.apply base (Term.denote right))]

/-- The two source equality operands contain no unnormalized use of the
runtime-private Boolean spellings after applying the carried source binding.

This is the source-side producer condition for failure reflection.  It is
strictly weaker and more stable than asking a caller to supply readings of
the actual runtime atoms: residual MGU orientation remains hidden, while the
only intentional PeTTa alias (`True`/`true`, `False`/`false`) is excluded at
the source boundary where the reader normalization is known. -/
def SourceUnifyOperandsAliasSafe
    (base : TreeSubstitution) (left right : Term) : Prop :=
  NoRuntimeBooleanAliases
      (TreeSubstitution.apply base (Term.denote left)) ∧
    NoRuntimeBooleanAliases
      (TreeSubstitution.apply base (Term.denote right))

/-- Source-syntax form of Boolean-alias safety at the actual carried
independent substitution.  This is the interface consumed by the ready-state
step theorem; callers need not name the hidden canonical residual MGU. -/
def CurrentUnifyOperandsAliasSafe
    (current : Substitution) (left right : Term) : Prop :=
  NoRuntimeBooleanAliases
      (Term.denote (current.applyTerm left)) ∧
    NoRuntimeBooleanAliases
      (Term.denote (current.applyTerm right))

/-- A stable safe-substitution invariant plus safe raw operands produces the
exact current-operand premise used by failure reflection. -/
theorem CurrentUnifyOperandsAliasSafe.of_booleanAliasSafe
    {current : Substitution} {left right : Term}
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftSafe : TermBooleanAliasSafe left)
    (rightSafe : TermBooleanAliasSafe right) :
    CurrentUnifyOperandsAliasSafe current left right :=
  ⟨PrologBooleanAliasSafety.Substitution.BooleanAliasSafe.applyTerm
      currentSafe left leftSafe,
    PrologBooleanAliasSafety.Substitution.BooleanAliasSafe.applyTerm
      currentSafe right rightSafe⟩

/-- Exact task data transports source-syntax alias-safety into the canonical
binding currency used by MGU variation.  Control spelling is irrelevant:
this is the reusable premise for both ordinary and operand-reversed equality
lowerings. -/
theorem TaskDataAgrees.sourceUnifyOperandsAliasSafe_of_current
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (safe : CurrentUnifyOperandsAliasSafe current left right) :
    SourceUnifyOperandsAliasSafe
      (canonical ++ Substitution.denote referenceBase) left right := by
  constructor
  · rw [← agreement.denoteCurrent,
      ← Substitution.denote_applyTerm]
    exact safe.1
  · rw [← agreement.denoteCurrent,
      ← Substitution.denote_applyTerm]
    exact safe.2

/-- Control-bearing specialization retained for ordinary task consumers. -/
theorem TaskPayloadAgrees.sourceUnifyOperandsAliasSafe_of_current
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables)
    (safe : CurrentUnifyOperandsAliasSafe current left right) :
    SourceUnifyOperandsAliasSafe
      (canonical ++ Substitution.denote referenceBase) left right :=
  agreement.data.sourceUnifyOperandsAliasSafe_of_current safe

/-- Executable primitive-unification success reflects through a semantically
equivalent source equation to an actual source `UnifyResolution`.

The generated runtime MGU first supplies a concrete canonical unifier over
the representative-applied runtime operands.  Worklist equivalence transports
that unifier to the source equation before semantic variation of the
cumulative bases transports it to the source-applied operands.  Completeness
of the independent ordered algorithm then constructs the typed source
substitution.  Control spelling and residual association-list orientation are
both absent from the statement. -/
theorem TaskDataAgrees.unifyResolution_of_runtime_success_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (strict :
      StrictUnifyOperands alpha
        (canonical ++ Substitution.denote referenceBase)
        runtime runtimeLeft runtimeRight executableLeft executableRight)
    {installed : Metta.Subst}
    (returned :
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed) :
    ∃ result, UnifyResolution current sourceLeft sourceRight result := by
  rcases strict with
    ⟨representative, baseVariants, leftReading, rightReading⟩
  obtain
    ⟨generated, _generatedExact, runtimeMgu, _installedShape⟩ :=
    PLeaTTa.unifyB_result_has_generated_mgu
      runtime executableLeft executableRight installed returned
  obtain ⟨representativeExtension, representativeOrdered⟩ :=
    orderedTreeMgu_exists_of_runtime_mgu
      agreement.alphaShared leftReading rightReading runtimeMgu
  have representativeHas :
      ∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations representative
            [(Term.denote runtimeLeft, Term.denote runtimeRight)]) := by
    refine ⟨representativeExtension, ?_⟩
    simpa [TreeSubstitution.applyEquations] using
      representativeOrdered.isMostGeneral.1
  have representativeSourceHas :
      ∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations representative
            [(Term.denote sourceLeft, Term.denote sourceRight)]) := by
    rcases representativeHas with ⟨candidate, candidateUnifies⟩
    refine ⟨candidate, ?_⟩
    apply
      (PrologMguDirectSimulation.treeUnifiesEquations_applyEquations_iff
        candidate representative
        [(Term.denote sourceLeft, Term.denote sourceRight)]).2
    have cumulativeRuntime :
        TreeUnifiesEquations (candidate ++ representative)
          [(Term.denote runtimeLeft, Term.denote runtimeRight)] :=
      (PrologMguDirectSimulation.treeUnifiesEquations_applyEquations_iff
        candidate representative
        [(Term.denote runtimeLeft, Term.denote runtimeRight)]).1
          candidateUnifies
    exact (equivalent (candidate ++ representative)).2 cumulativeRuntime
  have sourceHas :
      ∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations
            (canonical ++ Substitution.denote referenceBase)
            [(Term.denote sourceLeft, Term.denote sourceRight)]) :=
    (PrologSequentialMgu.TreeSubstitutionVariants.applied_has_unifier_iff
      baseVariants [(Term.denote sourceLeft, Term.denote sourceRight)]).2
        representativeSourceHas
  obtain ⟨sourceCandidate, sourceUnifies⟩ := sourceHas
  obtain ⟨sourceExtension, sourceOrdered⟩ :=
    OrderedTreeMgu.complete sourceCandidate sourceUnifies
  let extension := TreeSubstitution.reify sourceExtension
  have computed :
      ComputesDenotationalMgu
        [(current.applyTerm sourceLeft, current.applyTerm sourceRight)]
        extension := by
    refine ⟨sourceExtension, ?_, rfl⟩
    simpa only [denoteEquations, List.map_singleton,
      TreeSubstitution.applyEquations,
      Substitution.denote_applyTerm, agreement.denoteCurrent] using
      sourceOrdered
  exact
    ⟨extension ++ current,
      ⟨extension, computed, rfl⟩⟩

/-- Ordinary-control specialization of semantic runtime-success reflection. -/
theorem TaskPayloadAgrees.unifyResolution_of_runtime_success
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references) executables)
    (strict :
      StrictUnifyOperands alpha
        (canonical ++ Substitution.denote referenceBase)
        runtime left right executableLeft executableRight)
    {installed : Metta.Subst}
    (returned :
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed) :
    ∃ result, UnifyResolution current left right result :=
  agreement.data.unifyResolution_of_runtime_success_of_equivalent
    (by intro binding; rfl) strict returned

/-- A source primitive-equality clash forces an executable call for any
semantically equivalent equation to fail.  This is the contrapositive use of
data-level runtime-success reflection; it does not inspect or duplicate the
executable unification algorithm. -/
theorem TaskDataAgrees.unifyB_eq_none_of_no_resolution_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (strict :
      StrictUnifyOperands alpha
        (canonical ++ Substitution.denote referenceBase)
        runtime runtimeLeft runtimeRight executableLeft executableRight)
    (clash :
      ¬ ∃ result,
        UnifyResolution current sourceLeft sourceRight result) :
    PLeaTTa.unifyB runtime executableLeft executableRight = none := by
  cases returned :
      PLeaTTa.unifyB runtime executableLeft executableRight with
  | none =>
      rfl
  | some installed =>
      exact False.elim
        (clash
          (agreement.unifyResolution_of_runtime_success_of_equivalent
            equivalent strict returned))

/-- Ordinary-control specialization of semantic failure reflection. -/
theorem TaskPayloadAgrees.unifyB_eq_none_of_no_resolution
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references) executables)
    (strict :
      StrictUnifyOperands alpha
        (canonical ++ Substitution.denote referenceBase)
        runtime left right executableLeft executableRight)
    (clash : ¬ ∃ result, UnifyResolution current left right result) :
    PLeaTTa.unifyB runtime executableLeft executableRight = none :=
  agreement.data.unifyB_eq_none_of_no_resolution_of_equivalent
    (by intro binding; rfl) strict clash

/-- A real source `UnifyResolution` exposes the well-formed ordered canonical
extension which it prepends to the carried task binding.  The post-binding
denotation is exact and independent of control spelling. -/
theorem TaskDataAgrees.sourceUnifyExtension
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
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

/-- Control-bearing specialization retained for ordinary task consumers. -/
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
          (canonical ++ Substitution.denote referenceBase) :=
  agreement.data.sourceUnifyExtension resolved

/-- The source successor of primitive unification is a principal solution
relative to the exact carried canonical state.  This is the source half of
the later `taskUnifySuccess`/`eq_ok` correspondence. -/
theorem TaskDataAgrees.sourceUnifyRelative
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
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

/-- Control-bearing specialization retained for ordinary task consumers. -/
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
      [(Term.denote left, Term.denote right)] :=
  agreement.data.sourceUnifyRelative resolved

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

/-- Source alias-safety and the support-indexed task-data relation
construct the strict readings needed for runtime-success reflection.

The cumulative source binding and its hidden runtime representative are
mutual instances.  If applying the source binding contains no reserved
Boolean spelling, then applying the representative cannot contain one
either: the residual factor from source to representative could substitute
variables but could not erase a rigid `True`/`False` node.  The existing
broad runtime agreement can therefore be narrowed to the functional reading
without exposing or choosing the representative's MGU orientation. -/
theorem TaskDataAgrees.strictUnifyOperands_of_aliasSafe
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (aliasSafe :
      SourceUnifyOperandsAliasSafe
        (canonical ++ Substitution.denote referenceBase) left right) :
    StrictUnifyOperands alpha
      (canonical ++ Substitution.denote referenceBase)
      runtime left right executableLeft executableRight := by
  rcases agreement.cumulativeVariants with
    ⟨representative, variants, _canonicalTopological,
      _representativeCovered, _runtimeTopological, valuation⟩
  let runtimeBase :=
    representative ++ Substitution.denote referenceBase
  have leftBroad :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply runtimeBase (Term.denote left))
        (PLeaTTa.subst runtime executableLeft) :=
    canonicalRuntimeAgrees_apply_on
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        leftAgreement)
      valuation leftSupported
  have rightBroad :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply runtimeBase (Term.denote right))
        (PLeaTTa.subst runtime executableRight) :=
    canonicalRuntimeAgrees_apply_on
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        rightAgreement)
      valuation rightSupported
  rcases variants.1 with ⟨residual, factors⟩
  have leftRepresentativeSafe :
      NoRuntimeBooleanAliases
        (TreeSubstitution.apply runtimeBase (Term.denote left)) := by
    apply noRuntimeBooleanAliases_of_apply residual
    rw [← factors (Term.denote left)]
    exact aliasSafe.1
  have rightRepresentativeSafe :
      NoRuntimeBooleanAliases
        (TreeSubstitution.apply runtimeBase (Term.denote right)) := by
    apply noRuntimeBooleanAliases_of_apply residual
    rw [← factors (Term.denote right)]
    exact aliasSafe.2
  exact
    ⟨runtimeBase, variants,
      PLeaTTa.PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
        leftBroad leftRepresentativeSafe,
      PLeaTTa.PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
        rightBroad rightRepresentativeSafe⟩

/-- Alias-safety stated at the actual carried source substitution constructs
strict task-data operand readings without exposing the canonical residual
MGU. -/
theorem TaskDataAgrees.strictUnifyOperands_of_currentAliasSafe
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (aliasSafe : CurrentUnifyOperandsAliasSafe current left right) :
    StrictUnifyOperands alpha
      (canonical ++ Substitution.denote referenceBase)
      runtime left right executableLeft executableRight :=
  agreement.strictUnifyOperands_of_aliasSafe
    leftAgreement rightAgreement leftSupported rightSupported
    (agreement.sourceUnifyOperandsAliasSafe_of_current aliasSafe)

/-- Control-bearing specialization retained for ordinary task consumers. -/
theorem TaskPayloadAgrees.strictUnifyOperands_of_aliasSafe
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references) executables)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (aliasSafe :
      SourceUnifyOperandsAliasSafe
        (canonical ++ Substitution.denote referenceBase) left right) :
    StrictUnifyOperands alpha
      (canonical ++ Substitution.denote referenceBase)
      runtime left right executableLeft executableRight :=
  agreement.data.strictUnifyOperands_of_aliasSafe
    leftAgreement rightAgreement leftSupported rightSupported aliasSafe

/-- Carried-substitution specialization for ordinary task control. -/
theorem TaskPayloadAgrees.strictUnifyOperands_of_currentAliasSafe
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references) executables)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (aliasSafe : CurrentUnifyOperandsAliasSafe current left right) :
    StrictUnifyOperands alpha
      (canonical ++ Substitution.denote referenceBase)
      runtime left right executableLeft executableRight :=
  agreement.data.strictUnifyOperands_of_currentAliasSafe
    leftAgreement rightAgreement leftSupported rightSupported aliasSafe

/-- A source-successful primitive equality forces the actual executable
top-level unifier to succeed on a semantically equivalent equation.

`supportCovers` is the explicit live-continuation obligation: every alpha
link needed by these two terms must remain in the support-indexed valuation.
The theorem does not manufacture that compiler/caller invariant.  Under it,
the old source and hidden-runtime canonical states are variant bases; the
source and executable residual MGUs therefore produce variant cumulative
successors even when the compiler reverses the equation operands and both
residual orientations differ. -/
structure SelectedUnifyTopExact
    (alpha support : List (LogicVar × String))
    (canonical representative : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst)
    (sourceLeft sourceRight runtimeLeft runtimeRight : Term)
    (executableLeft executableRight : Metta.Atom)
    (result : Substitution)
    (sourceExtension executableExtension : TreeSubstitution)
    (generated : Metta.Subst) : Prop where
  bases :
    TreeSubstitutionVariants
      (canonical ++ Substitution.denote referenceBase)
      (representative ++ Substitution.denote referenceBase)
  canonicalTopological : TreeSubstitutionTopological canonical
  representativeCovered :
    TreeSubstitutionVariablesSatisfy
      (AlphaCovers alpha) representative
  oldValuation :
    AlphaValuationAgreesOn alpha support
      (representative ++ Substitution.denote referenceBase) runtime
  sourceExtensionOrdered :
    OrderedTreeMgu
      (carriedUnifyEquation
        (canonical ++ Substitution.denote referenceBase)
        sourceLeft sourceRight)
      sourceExtension
  sourceExtensionMgu :
    TreeIsMgu sourceExtension
      (TreeSubstitution.applyEquations
        (canonical ++ Substitution.denote referenceBase)
        [(Term.denote sourceLeft, Term.denote sourceRight)])
  sourceExtensionWellFormed : sourceExtension.WellFormed
  sourceConcreteResultShape :
    result = TreeSubstitution.reify sourceExtension ++ current
  executableMgu :
    TreeIsMgu executableExtension
      (TreeSubstitution.applyEquations
        (representative ++ Substitution.denote referenceBase)
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
  sourceResultShape :
    Substitution.denote result =
      sourceExtension ++
        (canonical ++ Substitution.denote referenceBase)
  successorVariants :
    TreeSubstitutionVariants
      (Substitution.denote result)
      (executableExtension ++
        (representative ++ Substitution.denote referenceBase))
  generatedExact :
    PLeaTTa.unifyTopExact
        (PLeaTTa.subst runtime executableLeft)
        (PLeaTTa.subst runtime executableRight) =
      some generated
  generatedValuation :
    AlphaValuationAgrees alpha executableExtension generated
  executableExtensionCovered :
    TreeSubstitutionVariablesSatisfy
      (AlphaCovers alpha) executableExtension
  executableTopological :
    TreeSubstitutionTopological executableExtension
  generatedTopological : Nonempty (PLeaTTa.SubstTopological generated)
  runtimeTopological : Nonempty (PLeaTTa.SubstTopological runtime)

/-- Exact post-substitution readings of one ordered operand list under a
selected residual representative.

Unlike `AlphaTreeSupported`, this relation does not claim that the raw source
operands belong to the caller's immutable observation support.  It records
the semantic objects actually presented to the next executable operation.
Fresh clause-body variables can therefore be materialized locally without
widening the retained payload support, while the single shared `alpha` still
preserves aliases between operand positions. -/
structure MaterializedOperandsAgreeWith
    (alpha : List (LogicVar × String))
    (representative : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Metta.Subst) (references : List Term)
    (executables : List Metta.Atom) : Prop where
  operands :
    List.Forall₂
      (fun term atom =>
        CanonicalRuntimeAgrees alpha
          (TreeSubstitution.apply
            (representative ++ Substitution.denote referenceBase)
            (Term.denote term))
          (PLeaTTa.subst runtime atom))
      references executables

/-- Exact current equality head after its operands have been materialized.

The executable shape and normalized tail tie the certificate to the current
control occurrence; `operands` then supplies the post-substitution semantic
readings without requiring the raw clause-local variables to belong to the
caller's immutable support. -/
def MaterializedUnifyHeadReady
    (alpha : List (LogicVar × String))
    (representative : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Metta.Subst) (barrier : Nat)
    (left right : Term) (referenceTail : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal) : Prop :=
  ∃ (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
      (executableLeft executableRight : Metta.Atom)
      (executableTail : List PLeaTTa.Goal),
    executables =
        spelling.goal executableLeft executableRight :: executableTail ∧
      AlphaTermAgrees alpha left executableLeft ∧
      AlphaTermAgrees alpha right executableRight ∧
      NormalizedAlphaGoalsAgree alpha barrier referenceTail executableTail ∧
      MaterializedOperandsAgreeWith alpha representative referenceBase runtime
        [left, right] [executableLeft, executableRight]

/-- One aligned source/executable goal pair carries materialized operands when
it is primitive equality.  The condition is deliberately generic over the
other goal constructors: their equality premise is impossible, while the
recursive spine below keeps their exact alpha-control evidence. -/
def MaterializedUnifyGoalAgreesWith
    (alpha : List (LogicVar × String))
    (representative : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Metta.Subst)
    (reference : PeTTaSpec.PrologCore.Goal)
    (executable : PLeaTTa.Goal) : Prop :=
  ∀ {left right : Term}
      {spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling}
      {executableLeft executableRight : Metta.Atom},
    reference = .unify left right →
    executable = spelling.goal executableLeft executableRight →
    MaterializedOperandsAgreeWith alpha representative referenceBase runtime
      [left, right] [executableLeft, executableRight]

/-- Exact normalized source/executable spine with every primitive-equality
occurrence materialized under one post-trim runtime valuation.

Unlike a head-only predicate, this relation cannot become vacuous when a cut,
truth node, or conjunction wrapper precedes equality.  `cons` consumes one
aligned source/executable goal, `truth` consumes only the compiler-erased
source node, and `conjunction` records the same ordered flattening as
`NormalizedAlphaGoalsAgree`.  Consequently cut and administrative transitions
project a structurally smaller certificate rather than carrying an unrelated
head fact. -/
inductive MaterializedUnifyGoalsAgreeWith
    (alpha : List (LogicVar × String))
    (representative : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Metta.Subst) (barrier : Nat) :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | nil :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier [] []
  | truth {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (tail :
        MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
          runtime barrier references executables) :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.truth :: references) executables
  | cons {reference : PeTTaSpec.PrologCore.Goal}
      {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (control : AlphaGoalAgrees alpha barrier reference executable)
      (materialized :
        MaterializedUnifyGoalAgreesWith alpha representative referenceBase
          runtime reference executable)
      (tail :
        MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
          runtime barrier references executables) :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (reference :: references) (executable :: executables)
  | conjunction {referenceBlock referenceTail :
        List PeTTaSpec.PrologCore.Goal}
      {executableBlock executableTail : List PLeaTTa.Goal}
      (block :
        MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
          runtime barrier referenceBlock executableBlock)
      (tail :
        MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
          runtime barrier referenceTail executableTail) :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.conjunction referenceBlock :: referenceTail)
        (executableBlock ++ executableTail)

namespace MaterializedUnifyGoalsAgreeWith

/-- Forget only the materialized values; the exact normalized alpha control
spine remains. -/
theorem toNormalized
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier references executables) :
    NormalizedAlphaGoalsAgree alpha barrier references executables := by
  induction agreement with
  | nil => exact .nil
  | truth tail inductionHypothesis => exact .truth inductionHypothesis
  | cons control materialized tail inductionHypothesis =>
      exact .cons control inductionHypothesis
  | conjunction block tail blockIH tailIH =>
      exact .conjunction blockIH tailIH

/-- Concatenation preserves both alignment and every occurrence certificate. -/
theorem append
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {leftReferences rightReferences : List PeTTaSpec.PrologCore.Goal}
    {leftExecutables rightExecutables : List PLeaTTa.Goal}
    (left :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier leftReferences leftExecutables)
    (right :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier rightReferences rightExecutables) :
    MaterializedUnifyGoalsAgreeWith alpha representative referenceBase runtime
      barrier (leftReferences ++ rightReferences)
      (leftExecutables ++ rightExecutables) := by
  induction left with
  | nil => simpa using right
  | truth tail inductionHypothesis => exact .truth inductionHypothesis
  | cons control materialized tail inductionHypothesis =>
      exact .cons control materialized inductionHypothesis
  | conjunction block tail blockIH tailIH =>
      simpa [List.append_assoc] using
        MaterializedUnifyGoalsAgreeWith.conjunction block tailIH

/-- Consume one compiler-erased truth node. -/
theorem afterTruth
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.truth :: references) executables) :
    MaterializedUnifyGoalsAgreeWith alpha representative referenceBase runtime
      barrier references executables := by
  cases agreement with
  | truth tail => exact tail
  | cons control materialized tail => cases control

/-- Consume one compiler-erased conjunction wrapper while retaining all
materialized occurrences in the flattened block and tail. -/
theorem afterConjunction
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {nested rest : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.conjunction nested :: rest) executables) :
    MaterializedUnifyGoalsAgreeWith alpha representative referenceBase runtime
      barrier (nested ++ rest) executables := by
  cases agreement with
  | conjunction block tail => exact block.append tail
  | cons control materialized tail => cases control

/-- Every exactly counted administrative prefix consumes only source
constructors and leaves the post-trim valuation unchanged. -/
theorem afterAdministrativeSteps
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier before executables)
    (steps : AdministrativeStepsN count before after) :
    MaterializedUnifyGoalsAgreeWith alpha representative referenceBase runtime
      barrier after executables := by
  induction steps with
  | zero goals => exact agreement
  | succ count before middle after head tail inductionHypothesis =>
      apply inductionHypothesis
      cases head with
      | truth rest => exact agreement.afterTruth
      | conjunction nested rest => exact agreement.afterConjunction

/-- A cut consumes one aligned source/executable node and exposes the exact
tail certificate; alternative pruning is orthogonal to the valuation. -/
theorem cutHead
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.cut :: references) executables) :
    ∃ executableTail,
      executables = .cutAt barrier :: executableTail ∧
        MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
          runtime barrier references executableTail := by
  cases agreement with
  | cons control materialized tail =>
      cases control with
      | cut => exact ⟨_, rfl, tail⟩

/-- Project the current equality occurrence after any earlier aligned or
administrative constructors have been consumed. -/
theorem unifyHeadReady
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {left right : Term}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.unify left right :: referenceTail) executables) :
    MaterializedUnifyHeadReady alpha representative referenceBase runtime
      barrier left right referenceTail executables := by
  cases agreement with
  | cons control materialized tail =>
      cases control with
      | unify leftAgreement rightAgreement =>
          exact
            ⟨.equality, _, _, _, rfl, leftAgreement, rightAgreement,
              tail.toNormalized,
              materialized (spelling := .equality) rfl rfl⟩
      | compileAlias leftAgreement rightAgreement =>
          exact
            ⟨.compilerAlias, _, _, _, rfl, leftAgreement, rightAgreement,
              tail.toNormalized,
              materialized (spelling := .compilerAlias) rfl rfl⟩

/-- Enrich two structurally identical alpha-goal derivations with one
materialized equality certificate at every aligned occurrence.

The local derivation supplies clause-copy freshness, the ambient derivation
supplies the shared runtime alpha, and `materialize` is the only semantic
callback.  Occurrence membership in `allExecutables` is derived recursively,
so a caller cannot certify an equality from a different body. -/
theorem ofAlphaGoalsAgree
    {localAlpha alpha : List (LogicVar × String)}
    {representative : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables allExecutables : List PLeaTTa.Goal}
    (localAgreement :
      NormalizedAlphaGoalsAgree localAlpha barrier references executables)
    (alphaIncluded : ∀ pair, pair ∈ localAlpha → pair ∈ alpha)
    (materialize :
      ∀ {left right : Term}
          {spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling}
          {executableLeft executableRight : Metta.Atom},
        AlphaGoalAgrees localAlpha barrier (.unify left right)
          (spelling.goal executableLeft executableRight) →
        AlphaGoalAgrees alpha barrier (.unify left right)
          (spelling.goal executableLeft executableRight) →
        spelling.goal executableLeft executableRight ∈ allExecutables →
        MaterializedOperandsAgreeWith alpha representative referenceBase
          runtime [left, right] [executableLeft, executableRight])
    (included : ∀ goal, goal ∈ executables → goal ∈ allExecutables) :
    MaterializedUnifyGoalsAgreeWith alpha representative referenceBase runtime
      barrier references executables := by
  induction localAgreement with
  | nil =>
      exact .nil
  | truth localTail inductionHypothesis =>
      exact .truth (inductionHypothesis included)
  | @cons reference executable references executables localHead localTail
      inductionHypothesis =>
      let ambientHead : AlphaGoalAgrees alpha barrier reference executable :=
        PLeaTTa.PrologGoalMguVariant.AlphaGoalAgrees.mono alphaIncluded
          localHead
      refine MaterializedUnifyGoalsAgreeWith.cons ambientHead ?_ ?_
      · intro left right spelling executableLeft executableRight
          referenceShape executableShape
        subst reference
        subst executable
        exact materialize localHead ambientHead
          (included _ (by simp))
      · exact inductionHypothesis
          (fun goal member => included goal (by simp [member]))
  | @conjunction referenceBlock referenceTail executableBlock executableTail
      localBlock localTail blockIH tailIH =>
      exact MaterializedUnifyGoalsAgreeWith.conjunction
        (blockIH
          (fun goal member => included goal
            (List.mem_append_left executableTail member)))
        (tailIH
          (fun goal member => included goal
            (List.mem_append_right executableBlock member)))

end MaterializedUnifyGoalsAgreeWith

/-- Combine the normalized payload shape with an activation-time materialized
operand certificate. -/
theorem TaskPayloadAgrees.materializedUnifyHeadReady_of_materializedHeads
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {left right : Term}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (_payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: referenceTail) executables)
    (materialized :
      MaterializedUnifyGoalsAgreeWith alpha representative referenceBase
        runtime barrier (.unify left right :: referenceTail) executables) :
    MaterializedUnifyHeadReady alpha representative referenceBase runtime
      barrier left right referenceTail executables := by
  exact materialized.unifyHeadReady

/-- Existing support-based task payloads materialize their current equality
head into the smaller execution-ready interface. -/
theorem TaskPayloadAgrees.materializedUnifyHeadReady_of_supported
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {left right : Term}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: referenceTail) executables)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right)) :
    MaterializedUnifyHeadReady alpha representative referenceBase runtime
      barrier left right referenceTail executables := by
  obtain
    ⟨spelling, executableLeft, executableRight, executableTail,
      executableShape, leftAgreement, rightAgreement, tailControl⟩ :=
    payload.control.unifyHead
  have leftAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote left))
        (PLeaTTa.subst runtime executableLeft) :=
    canonicalRuntimeAgrees_apply_on
      (AlphaTermAgrees.canonicalRuntimeAgrees leftAgreement)
      selected.valuation leftSupported
  have rightAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote right))
        (PLeaTTa.subst runtime executableRight) :=
    canonicalRuntimeAgrees_apply_on
      (AlphaTermAgrees.canonicalRuntimeAgrees rightAgreement)
      selected.valuation rightSupported
  exact
    ⟨spelling, executableLeft, executableRight, executableTail,
      executableShape, leftAgreement, rightAgreement, tailControl,
      ⟨.cons leftAfter (.cons rightAfter .nil)⟩⟩

/-- The freshly generated executable MGU cannot capture any carried runtime
domain entry.  This is derived from the exact selected operands, not added as
an independent installation assumption. -/
theorem SelectedUnifyTopExact.generatedAvoidsRuntime
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated : Metta.Subst}
    (exact :
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated) :
    PLeaTTa.SubstEntriesAvoid runtime generated := by
  obtain ⟨runtimeTopological⟩ := exact.runtimeTopological
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
  exact
    PLeaTTa.unifyTopExact_avoidsExternal runtime
      (PLeaTTa.subst runtime executableLeft)
      (PLeaTTa.subst runtime executableRight) generated leftAvoids rightAvoids
      exact.generatedExact

/-- The empty executable residual substitution preserves every alpha-linked
variable literally.  This is the identity element used by reflexive
primitive unification; it is not a vacuous valuation because every link in
`alpha` is still checked. -/
theorem alphaValuationAgrees_nil
    (alpha : List (LogicVar × String)) :
    AlphaValuationAgrees alpha [] [] := by
  intro identity name linked
  simpa [TreeSubstitution.apply, PLeaTTa.subst_nil] using
    (PLeaTTa.PrologPrefilterBridge.CanonicalRuntimeAgrees.variable linked)

/-- Reflexive primitive equality has the literal identity MGU on both source
and executable sides for any already-selected cumulative representative.

All three residual outputs are indexed as `[]`; no existential orientation
can be reselected between this theorem and a successor transition. -/
theorem TaskDataAgrees.selectedUnifyTopExact_reflexive
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (term : Term) (atom : Metta.Atom) :
    SelectedUnifyTopExact alpha support canonical representative
      referenceBase current runtime term term term term atom atom current
      [] [] [] := by
  let sourceTree :=
    TreeSubstitution.apply
      (canonical ++ Substitution.denote referenceBase) (Term.denote term)
  let executableTree :=
    TreeSubstitution.apply
      (representative ++ Substitution.denote referenceBase) (Term.denote term)
  have sourceOrdered :
      OrderedTreeMgu
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase) term term) [] := by
    simpa [carriedUnifyEquation, sourceTree] using
      (OrderedTreeMgu.cons sourceTree sourceTree [] [] []
        (.reflexive sourceTree) OrderedTreeMgu.nil)
  have sourceMgu :
      TreeIsMgu []
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote term, Term.denote term)]) := by
    simpa [TreeSubstitution.applyEquations, sourceTree] using
      (tree_reflexive_is_mgu sourceTree)
  have executableMgu :
      TreeIsMgu []
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote term, Term.denote term)]) := by
    simpa [TreeSubstitution.applyEquations, executableTree] using
      (tree_reflexive_is_mgu executableTree)
  have currentDenote :
      Substitution.denote current =
        canonical ++ Substitution.denote referenceBase := by
    rw [agreement.bindingShape, Substitution.denote_append,
      TreeSubstitution.denote_reify agreement.canonicalWellFormed]
  exact
    { bases := selected.variants
      canonicalTopological := selected.canonicalTopological
      representativeCovered := selected.representativeCovered
      oldValuation := selected.valuation
      sourceExtensionOrdered := sourceOrdered
      sourceExtensionMgu := sourceMgu
      sourceExtensionWellFormed := TreeSubstitution.wellFormed_nil
      sourceConcreteResultShape := by rfl
      executableMgu := executableMgu
      sourceResultShape := by simpa using currentDenote
      successorVariants := by simpa [currentDenote] using selected.variants
      generatedExact := by
        simpa using
          (PLeaTTa.unifyTopExact_self (PLeaTTa.subst runtime atom))
      generatedValuation := alphaValuationAgrees_nil alpha
      executableExtensionCovered := by intro entry member; simp at member
      executableTopological := TreeSubstitutionTopological.nil
      generatedTopological := ⟨PLeaTTa.emptySubstTopological⟩
      runtimeTopological := selected.runtimeTopological }

/-- Strong form of executable-unification adequacy relative to one selected
cumulative representative.

The representative is an input index, not an existential eliminated inside
the proof.  The returned source and executable extensions are therefore tied
to that literal orientation.  This is the producer used by the heterogeneous
prefix zipper; the older existential theorem below is only its weak wrapper.
-/
theorem TaskDataAgrees.selectedUnifyTopExact_of_equivalent_materialized
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (materialized :
      MaterializedOperandsAgreeWith alpha representative referenceBase
        runtime [runtimeLeft, runtimeRight]
        [executableLeft, executableRight])
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated := by
  rcases agreement.sourceUnifyExtension resolved with
    ⟨sourceExtension, sourceExtensionOrdered, sourceExtensionWellFormed,
      sourceConcreteResultShape, sourceResultShape⟩
  have sourceExtensionMgu := sourceExtensionOrdered.isMostGeneral
  have sourceExtensionApplied :
      TreeIsMgu sourceExtension
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote sourceLeft, Term.denote sourceRight)]) := by
    simpa [carriedUnifyEquation,
      TreeSubstitution.applyEquations] using sourceExtensionMgu
  have leftAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote runtimeLeft))
        (PLeaTTa.subst runtime executableLeft) := by
    cases materialized.operands with
    | cons left tail => exact left
  have rightAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote runtimeRight))
        (PLeaTTa.subst runtime executableRight) := by
    cases materialized.operands with
    | cons _ tail =>
        cases tail with
        | cons right _ => exact right
  have sourceRelativeOriginal :
      TreeIsRelativeMgu
        (sourceExtension ++
          (canonical ++ Substitution.denote referenceBase))
        (canonical ++ Substitution.denote referenceBase)
        [(Term.denote sourceLeft, Term.denote sourceRight)] :=
    TreeIsMgu.relativeCompose sourceExtensionApplied
  have sourceRelative :
      TreeIsRelativeMgu
        (sourceExtension ++
          (canonical ++ Substitution.denote referenceBase))
        (canonical ++ Substitution.denote referenceBase)
        [(Term.denote runtimeLeft, Term.denote runtimeRight)] :=
    sourceRelativeOriginal.of_equivalent equivalent
  have sourceFactorsRepresentative :
      TreeFactorsThrough
        (sourceExtension ++
          (canonical ++ Substitution.denote referenceBase))
        (representative ++ Substitution.denote referenceBase) :=
    TreeFactorsThrough.trans sourceRelative.1 selected.variants.1
  rcases sourceFactorsRepresentative with
    ⟨candidate, candidateFactors⟩
  have candidateUnifies :
      TreeUnifiesEquations candidate
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote runtimeLeft, Term.denote runtimeRight)]) := by
    intro normalized normalizedMember
    simp only [TreeSubstitution.applyEquations, List.mem_map]
      at normalizedMember
    obtain ⟨equation, member, rfl⟩ := normalizedMember
    rw [← candidateFactors equation.1, ← candidateFactors equation.2]
    exact sourceRelative.2.1 equation member
  obtain ⟨runtimeOrdered, runtimeDerivation⟩ :=
    OrderedTreeMgu.complete candidate candidateUnifies
  obtain
    ⟨executableExtension, generated, generatedExact,
      generatedAgreement, executableTopological, generatedTopological,
      generatedValuation, executableMgu,
      _executableFactorsOrdered, _orderedFactorsExecutable⟩ :=
    PLeaTTa.PrologCanonicalMguSimulation.OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
      agreement.alphaShared leftAfter rightAfter runtimeDerivation
  have executableMguApplied :
      TreeIsMgu executableExtension
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote runtimeLeft, Term.denote runtimeRight)]) := by
    simpa [TreeSubstitution.applyEquations] using executableMgu
  have successors :=
    sequential_mgu_composites_are_variants_of_equivalent
      selected.variants equivalent sourceExtensionApplied
        executableMguApplied
  exact
    ⟨sourceExtension, executableExtension, generated,
      { bases := selected.variants
        canonicalTopological := selected.canonicalTopological
        representativeCovered := selected.representativeCovered
        oldValuation := selected.valuation
        sourceExtensionOrdered := sourceExtensionOrdered
        sourceExtensionMgu := sourceExtensionApplied
        sourceExtensionWellFormed := sourceExtensionWellFormed
        sourceConcreteResultShape := sourceConcreteResultShape
        executableMgu := executableMguApplied
        sourceResultShape := sourceResultShape
        successorVariants := by
          rw [sourceResultShape]
          exact successors
        generatedExact := generatedExact
        generatedValuation := generatedValuation
        executableExtensionCovered := generatedAgreement.variablesSatisfy
        executableTopological := executableTopological
        generatedTopological := generatedTopological
        runtimeTopological := selected.runtimeTopological }⟩

/-- Support-based compatibility interface for existing task producers.

The immutable payload support is used only to materialize the two current
operands.  The lower theorem consumes those readings directly, allowing a
clause-activation producer to supply the same evidence from its fresh local
valuation without changing the payload's observation domain. -/
theorem TaskDataAgrees.selectedUnifyTopExact_of_equivalent_canonicalAgreement
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      CanonicalRuntimeAgrees alpha
        (Term.denote runtimeLeft) executableLeft)
    (rightAgreement :
      CanonicalRuntimeAgrees alpha
        (Term.denote runtimeRight) executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated := by
  have leftAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote runtimeLeft))
        (PLeaTTa.subst runtime executableLeft) :=
    canonicalRuntimeAgrees_apply_on
      leftAgreement selected.valuation leftSupported
  have rightAfter :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote runtimeRight))
        (PLeaTTa.subst runtime executableRight) :=
    canonicalRuntimeAgrees_apply_on
      rightAgreement selected.valuation rightSupported
  apply agreement.selectedUnifyTopExact_of_equivalent_materialized selected
    equivalent
  · exact ⟨.cons leftAfter (.cons rightAfter .nil)⟩
  · exact resolved

/-- Compatibility wrapper for raw-alpha callers.  The proof above only needs
canonical readings, so raw term agreement is converted exactly once at this
boundary and is not retained as an artificial requirement of the MGU
producer. -/
theorem TaskDataAgrees.selectedUnifyTopExact_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      AlphaTermAgrees alpha runtimeLeft executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha runtimeRight executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated := by
  exact agreement.selectedUnifyTopExact_of_equivalent_canonicalAgreement selected
    equivalent
    (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
      leftAgreement)
    (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
      rightAgreement)
    leftSupported rightSupported resolved

theorem TaskDataAgrees.executableUnifyTopExact_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      AlphaTermAgrees alpha runtimeLeft executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha runtimeRight executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ representative sourceExtension executableCanonical generated,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionTopological canonical ∧
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
      AlphaValuationAgreesOn alpha support
        (representative ++ Substitution.denote referenceBase) runtime ∧
      OrderedTreeMgu
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase)
          sourceLeft sourceRight)
        sourceExtension ∧
      TreeIsMgu sourceExtension
        (TreeSubstitution.applyEquations
          (canonical ++ Substitution.denote referenceBase)
          [(Term.denote sourceLeft, Term.denote sourceRight)]) ∧
      sourceExtension.WellFormed ∧
      result = TreeSubstitution.reify sourceExtension ++ current ∧
      TreeIsMgu executableCanonical
        (TreeSubstitution.applyEquations
          (representative ++ Substitution.denote referenceBase)
          [(Term.denote runtimeLeft, Term.denote runtimeRight)]) ∧
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
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) executableCanonical ∧
      TreeSubstitutionTopological executableCanonical ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      Nonempty (PLeaTTa.SubstTopological runtime) := by
  obtain ⟨representative, selected⟩ := agreement.valuation.existsWith
  obtain ⟨sourceExtension, executableCanonical, generated, exact⟩ :=
    agreement.selectedUnifyTopExact_of_equivalent selected equivalent
      leftAgreement rightAgreement leftSupported rightSupported resolved
  exact
    ⟨representative, sourceExtension, executableCanonical, generated,
      exact.bases, exact.canonicalTopological,
      exact.representativeCovered, exact.oldValuation,
      exact.sourceExtensionOrdered, exact.sourceExtensionMgu,
      exact.sourceExtensionWellFormed, exact.sourceConcreteResultShape,
      exact.executableMgu, exact.sourceResultShape,
      exact.successorVariants, exact.generatedExact,
      exact.generatedValuation, exact.executableExtensionCovered,
      exact.executableTopological, exact.generatedTopological,
      exact.runtimeTopological⟩

/-- Strict ordinary-task specialization: both sides read the same oriented
source equation.  Existing consumers keep this API while the amb bridge uses
the equivalence-aware data theorem above. -/
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
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
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
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) executableCanonical ∧
      TreeSubstitutionTopological executableCanonical ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      Nonempty (PLeaTTa.SubstTopological runtime) := by
  apply agreement.data.executableUnifyTopExact_of_equivalent
    (sourceLeft := left) (sourceRight := right)
    (runtimeLeft := left) (runtimeRight := right)
    (by intro binding; rfl)
    leftAgreement rightAgreement leftSupported rightSupported resolved

/-- Installation certificate for one explicitly selected primitive-unifier
orientation.

Unlike `TaskDataAgrees`, the successor valuation names its literal residual
representative.  The generated executable extension is prepended to the
predecessor representative; no existential can replace it with a merely
variant orientation between two prefix transitions. -/
structure SelectedUnifySuccessData
    (alpha support : List (LogicVar × String))
    (canonical representative : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst)
    (sourceLeft sourceRight runtimeLeft runtimeRight : Term)
    (executableLeft executableRight : Metta.Atom)
    (result : Substitution)
    (sourceExtension executableExtension : TreeSubstitution)
    (generated installed : Metta.Subst) : Prop where
  topExact :
    SelectedUnifyTopExact alpha support canonical representative
      referenceBase current runtime sourceLeft sourceRight runtimeLeft
      runtimeRight executableLeft executableRight result sourceExtension
      executableExtension generated
  installedExact :
    PLeaTTa.unifyB runtime executableLeft executableRight = some installed
  nextCanonicalWellFormed : (sourceExtension ++ canonical).WellFormed
  nextBindingShape :
    result =
      TreeSubstitution.reify (sourceExtension ++ canonical) ++ referenceBase
  nextCumulative :
    AlphaCumulativeResidualVariantAgreesOnWith alpha support
      (sourceExtension ++ canonical) referenceBase installed
      (executableExtension ++ representative)

namespace SelectedUnifySuccessData

/-- Forget only the selected successor representative.  The weak payload is
derived from the strong certificate rather than proved independently. -/
theorem taskData
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Metta.Subst}
    (success :
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated installed)
    (shared : SharedRuntimeAlpha alpha) :
    TaskDataAgrees alpha support (sourceExtension ++ canonical)
      referenceBase result installed :=
  ⟨shared, success.nextCanonicalWellFormed, success.nextBindingShape,
    success.nextCumulative.weak⟩

/-- The selected successor stores exactly the executable installation policy,
even though its public structure records the result through `unifyB`. -/
theorem installed_eq_installGenerated
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Metta.Subst}
    (success :
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated installed) :
    installed = PrologMguComposition.installGenerated generated runtime := by
  cases generated with
  | nil =>
      have same : some installed = some runtime := by
        calc
          some installed =
              PLeaTTa.unifyB runtime executableLeft executableRight :=
            success.installedExact.symm
          _ = some runtime := by
            simp [PLeaTTa.unifyB, success.topExact.generatedExact]
      exact Option.some.inj same
  | cons head tail =>
      have same :
          some installed =
            some (Metta.Subst.compose (head :: tail) runtime) := by
        calc
          some installed =
              PLeaTTa.unifyB runtime executableLeft executableRight :=
            success.installedExact.symm
          _ = some (Metta.Subst.compose (head :: tail) runtime) := by
            simp [PLeaTTa.unifyB, success.topExact.generatedExact]
      simpa [PrologMguComposition.installGenerated] using
        Option.some.inj same

/-- Applying the selected installed runtime is exactly sequential semantic
application of the carried runtime followed by the generated residual. -/
theorem subst_installed_eq_generated_after_runtime
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Metta.Subst}
    (success :
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated installed)
    (atom : Metta.Atom) :
    PLeaTTa.subst installed atom =
      PLeaTTa.subst generated (PLeaTTa.subst runtime atom) := by
  rw [success.installed_eq_installGenerated]
  obtain ⟨runtimeTopological⟩ := success.topExact.runtimeTopological
  obtain ⟨generatedTopological⟩ := success.topExact.generatedTopological
  exact
    PrologMguComposition.subst_installGenerated_eq_generated_after_base
      runtimeTopological generatedTopological
      success.topExact.generatedAvoidsRuntime atom

/-- The literal selected installation remains topological. -/
theorem installedTopological
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Metta.Subst}
    (success :
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated installed) :
    Nonempty (PLeaTTa.SubstTopological installed) := by
  rw [success.installed_eq_installGenerated]
  obtain ⟨runtimeTopological⟩ := success.topExact.runtimeTopological
  obtain ⟨generatedTopological⟩ := success.topExact.generatedTopological
  exact ⟨
    PrologMguComposition.installGeneratedTopological runtimeTopological
      generatedTopological success.topExact.generatedAvoidsRuntime⟩

end SelectedUnifySuccessData

/-- Install one already selected executable MGU while retaining its literal
canonical orientation in the successor valuation.

Previously supported runtime names may already be bound.  Their old
valuation is composed with the generated MGU semantically; no domain-
avoidance premise is needed. -/
theorem SelectedUnifyTopExact.afterUnifySuccessDataGeneral
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (exact :
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated) :
    SelectedUnifySuccessData alpha support canonical representative
      referenceBase current runtime sourceLeft sourceRight runtimeLeft
      runtimeRight executableLeft executableRight result sourceExtension
      executableExtension generated
      (PrologMguComposition.installGenerated generated runtime) := by
  have installedExact :
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some (PrologMguComposition.installGenerated generated runtime) := by
    cases generated with
    | nil =>
        simp [PLeaTTa.unifyB,
          PrologMguComposition.installGenerated, exact.generatedExact]
    | cons head tail =>
        simp [PLeaTTa.unifyB,
          PrologMguComposition.installGenerated, exact.generatedExact]
  obtain ⟨runtimeTopological⟩ := exact.runtimeTopological
  obtain ⟨generatedTopological⟩ := exact.generatedTopological
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
      generated leftAvoids rightAvoids exact.generatedExact
  have installedTopological :
      PLeaTTa.SubstTopological
        (PrologMguComposition.installGenerated generated runtime) :=
    PrologMguComposition.installGeneratedTopological
      runtimeTopological generatedTopological generatedAvoidsRuntime
  have sourceEquationsAvoidCanonical :
      TreeEquationsVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys canonical)
        (carriedUnifyEquation
          (canonical ++ Substitution.denote referenceBase)
          sourceLeft sourceRight) := by
    intro equation member
    simp only [carriedUnifyEquation, List.mem_singleton] at member
    rcases member with rfl
    have leftOutside :
        TreeVariablesSatisfy
          (fun identity =>
            identity ∉ TreeSubstitution.keys canonical)
          (TreeSubstitution.apply
            (canonical ++ Substitution.denote referenceBase)
            (Term.denote sourceLeft)) := by
      rw [TreeSubstitution.apply_append]
      exact exact.canonicalTopological.apply_avoids
        (TreeSubstitution.apply
          (Substitution.denote referenceBase) (Term.denote sourceLeft))
    have rightOutside :
        TreeVariablesSatisfy
          (fun identity =>
            identity ∉ TreeSubstitution.keys canonical)
          (TreeSubstitution.apply
            (canonical ++ Substitution.denote referenceBase)
            (Term.denote sourceRight)) := by
      rw [TreeSubstitution.apply_append]
      exact exact.canonicalTopological.apply_avoids
        (TreeSubstitution.apply
          (Substitution.denote referenceBase) (Term.denote sourceRight))
    exact ⟨leftOutside, rightOutside⟩
  have sourceCompositeTopological :
      TreeSubstitutionTopological (sourceExtension ++ canonical) :=
    PrologSequentialMgu.OrderedTreeMgu.prepend_topological_of_equations_avoid
      exact.canonicalTopological exact.sourceExtensionOrdered
      sourceEquationsAvoidCanonical
  have cumulativeVariants :
      TreeSubstitutionVariants
        ((sourceExtension ++ canonical) ++
          Substitution.denote referenceBase)
        ((executableExtension ++ representative) ++
          Substitution.denote referenceBase) := by
    simpa [exact.sourceResultShape, List.append_assoc] using
      exact.successorVariants
  have installedValuation :
      AlphaValuationAgreesOn alpha support
        ((executableExtension ++ representative) ++
          Substitution.denote referenceBase)
        (PrologMguComposition.installGenerated generated runtime) := by
    have lifted :
        AlphaValuationAgreesOn alpha support
          (executableExtension ++
            (representative ++ Substitution.denote referenceBase))
          (PrologMguComposition.installGenerated generated runtime) :=
      PLeaTTa.PrologMguComposition.AlphaValuationAgreesOn.installGenerated_compose
        exact.oldValuation runtimeTopological generatedTopological
        generatedAvoidsRuntime exact.generatedValuation
    intro identity name linked
    simpa [List.append_assoc] using lifted linked
  have successorRepresentativeCovered :
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha)
        (executableExtension ++ representative) :=
    treeSubstitutionVariablesSatisfy_append
      exact.executableExtensionCovered exact.representativeCovered
  have nextCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support
        (sourceExtension ++ canonical) referenceBase
        (PrologMguComposition.installGenerated generated runtime)
        (executableExtension ++ representative) :=
    ⟨cumulativeVariants, sourceCompositeTopological,
      successorRepresentativeCovered, ⟨installedTopological⟩,
      installedValuation⟩
  refine
    { topExact := exact
      installedExact := installedExact
      nextCanonicalWellFormed :=
        exact.sourceExtensionWellFormed.append agreement.canonicalWellFormed
      nextBindingShape := ?_
      nextCumulative := nextCumulative }
  calc
    result =
        TreeSubstitution.reify sourceExtension ++ current :=
      exact.sourceConcreteResultShape
    _ =
        TreeSubstitution.reify sourceExtension ++
          (TreeSubstitution.reify canonical ++ referenceBase) := by
      rw [agreement.bindingShape]
    _ =
        TreeSubstitution.reify (sourceExtension ++ canonical) ++
          referenceBase := by
      rw [TreeSubstitution.reify_append]
      simp only [List.append_assoc]

/-- Compatibility wrapper for older callers which already establish the
conservative unbound-support premises.  The stronger composition theorem
above shows that neither premise is needed for semantic installation. -/
theorem SelectedUnifyTopExact.afterUnifySuccessData
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    {result : Substitution}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated : Metta.Subst}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (exact :
      SelectedUnifyTopExact alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated)
    (_supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (_runtimeAvoids : AlphaRuntimeNamesAvoid support runtime) :
    SelectedUnifySuccessData alpha support canonical representative
      referenceBase current runtime sourceLeft sourceRight runtimeLeft
      runtimeRight executableLeft executableRight result sourceExtension
      executableExtension generated
      (PrologMguComposition.installGenerated generated runtime) :=
  exact.afterUnifySuccessDataGeneral agreement

/-- Strong selected-representative producer for one successful primitive
equality over an arbitrary carried runtime.  All chosen extensions remain
explicit indices of the returned certificate. -/
theorem TaskDataAgrees.afterUnifySuccessDataWith_of_equivalentGeneral_canonicalAgreement
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      CanonicalRuntimeAgrees alpha
        (Term.denote runtimeLeft) executableLeft)
    (rightAgreement :
      CanonicalRuntimeAgrees alpha
        (Term.denote runtimeRight) executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated
        (PrologMguComposition.installGenerated generated runtime) := by
  obtain ⟨sourceExtension, executableExtension, generated, exact⟩ :=
    agreement.selectedUnifyTopExact_of_equivalent_canonicalAgreement selected equivalent
      leftAgreement rightAgreement leftSupported rightSupported resolved
  exact
    ⟨sourceExtension, executableExtension, generated,
      exact.afterUnifySuccessDataGeneral agreement⟩

/-- Materialized-operand form of the selected success producer.

This is the fresh clause-body entry point: the task's immutable support still
governs its public cumulative valuation, while the exact current operands are
interpreted by an activation-local certificate. -/
theorem TaskDataAgrees.afterUnifySuccessDataWith_of_equivalentGeneral_materialized
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (materialized :
      MaterializedOperandsAgreeWith alpha representative referenceBase
        runtime [runtimeLeft, runtimeRight]
        [executableLeft, executableRight])
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated
        (PrologMguComposition.installGenerated generated runtime) := by
  obtain ⟨sourceExtension, executableExtension, generated, exact⟩ :=
    agreement.selectedUnifyTopExact_of_equivalent_materialized selected
      equivalent materialized resolved
  exact
    ⟨sourceExtension, executableExtension, generated,
      exact.afterUnifySuccessDataGeneral agreement⟩

/-- Raw-alpha compatibility wrapper for the canonical success-data producer.
No proof below the boundary needs the stronger raw presentation. -/
theorem TaskDataAgrees.afterUnifySuccessDataWith_of_equivalentGeneral
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      AlphaTermAgrees alpha runtimeLeft executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha runtimeRight executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated
        (PrologMguComposition.installGenerated generated runtime) := by
  exact
    agreement.afterUnifySuccessDataWith_of_equivalentGeneral_canonicalAgreement
      selected equivalent
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        leftAgreement)
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        rightAgreement)
      leftSupported rightSupported resolved

/-- Compatibility form retaining the older conservative support premises. -/
theorem TaskDataAgrees.afterUnifySuccessDataWith_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase runtime representative)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      AlphaTermAgrees alpha runtimeLeft executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha runtimeRight executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    (_supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (_runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension executableExtension generated,
      SelectedUnifySuccessData alpha support canonical representative
        referenceBase current runtime sourceLeft sourceRight runtimeLeft
        runtimeRight executableLeft executableRight result sourceExtension
        executableExtension generated
        (PrologMguComposition.installGenerated generated runtime) :=
  agreement.afterUnifySuccessDataWith_of_equivalentGeneral selected equivalent
    leftAgreement rightAgreement leftSupported rightSupported resolved

/-- One successful primitive equality installs the actual executable MGU and
preserves the continuation-independent task data relation.

The support premises remain caller-visible.  `leftSupported` and
`rightSupported` say that evaluating this equality does not need a dead
alpha link; `supportIncluded` permits restricting the newly generated full
valuation; `runtimeAvoids` is the carried-state separation needed by eager
composition.  Trimming and control reconstruction are deliberately left to
`TaskDataAgrees.trimFor` and `TaskDataAgrees.withControl`, so segmented
body/caller continuations can reuse this MGU proof without retagging either
control region. -/
theorem TaskDataAgrees.afterUnifySuccessData_of_equivalent
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {sourceLeft sourceRight runtimeLeft runtimeRight : Term}
    {executableLeft executableRight : Metta.Atom}
    (agreement :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (equivalent :
      TreeUnificationEquivalent
        [(Term.denote sourceLeft, Term.denote sourceRight)]
        [(Term.denote runtimeLeft, Term.denote runtimeRight)])
    (leftAgreement :
      AlphaTermAgrees alpha runtimeLeft executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha runtimeRight executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeLeft))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote runtimeRight))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    {result : Substitution}
    (resolved : UnifyResolution current sourceLeft sourceRight result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed ∧
      TaskDataAgrees alpha support (sourceExtension ++ canonical)
        referenceBase result installed := by
  obtain ⟨representative, selected⟩ := agreement.valuation.existsWith
  obtain ⟨sourceExtension, executableExtension, generated, success⟩ :=
    agreement.afterUnifySuccessDataWith_of_equivalent selected equivalent
      leftAgreement rightAgreement leftSupported rightSupported
      supportIncluded runtimeAvoids resolved
  exact
    ⟨sourceExtension,
      PrologMguComposition.installGenerated generated runtime,
      success.installedExact,
      success.taskData agreement.alphaShared⟩

/-- Strict ordinary-task specialization retained for existing callers. -/
theorem TaskPayloadAgrees.afterUnifySuccessData
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {left right : Term} {executableLeft executableRight : Metta.Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {wholeExecutables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime (.unify left right :: references)
        wholeExecutables)
    (leftAgreement :
      AlphaTermAgrees alpha left executableLeft)
    (rightAgreement :
      AlphaTermAgrees alpha right executableRight)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    {result : Substitution}
    (resolved : UnifyResolution current left right result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed ∧
      TaskDataAgrees alpha support (sourceExtension ++ canonical)
        referenceBase result installed :=
  agreement.data.afterUnifySuccessData_of_equivalent
    (sourceLeft := left) (sourceRight := right)
    (runtimeLeft := left) (runtimeRight := right)
    (by intro binding; rfl)
    leftAgreement rightAgreement leftSupported rightSupported
    supportIncluded runtimeAvoids resolved

/-- One successful primitive equality installs the actual executable MGU,
trims it on the exact continuation, and preserves the full task payload
relation.

This is the uniform-control specialization of
`TaskPayloadAgrees.afterUnifySuccessData`. -/
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
  obtain ⟨sourceExtension, installed, installedExact, data⟩ :=
    agreement.afterUnifySuccessData leftAgreement rightAgreement
      leftSupported rightSupported supportIncluded runtimeAvoids resolved
  exact
    ⟨sourceExtension, installed, installedExact,
      (data.trimFor live).withControl tailControl⟩

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

/-- Exact continuation-liveness obligation for primitive unification over an
arbitrary carried runtime.

Unlike `ReadyUnifyContinuationSafe`, this does not require observable runtime
names to be absent from the carried substitution.  Arbitrary-base MGU
composition interprets such bindings semantically; only their survival in the
post-equality continuation is needed for `trimFor`. -/
def ReadyUnifyContinuationLive
    (support : List (LogicVar × String)) (state : OpenConf) : Prop :=
  ∀ {head : PLeaTTa.Goal} {rest : List PLeaTTa.Goal}
      {runtime : Metta.Subst},
    state.control.cur = some (head :: rest, runtime) →
      AlphaRuntimeNamesLive support rest state.control.qterm

/-- The conservative predecessor predicate projects to the exact liveness
condition used by the arbitrary-base producer. -/
theorem ReadyUnifyContinuationSafe.live
    {support : List (LogicVar × String)} {state : OpenConf}
    (safe : ReadyUnifyContinuationSafe support state) :
    ReadyUnifyContinuationLive support state := by
  intro head rest runtime current
  exact (safe current).2

/-- Strict, invertible readings for whichever executable equality spelling
is actually at the ready state's head.  Quantifying over head decomposition
ties the certificate to `state.control.cur`; it cannot certify unrelated
atoms beside the real transition. -/
def ReadyUnifyOperandsStrict
    (alpha : List (LogicVar × String))
    (sourceBase : TreeSubstitution)
    (left right : Term) (state : OpenConf) : Prop :=
  ∀ (spelling :
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
      (executableLeft executableRight : Metta.Atom)
      (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst),
    state.control.cur =
        some (spelling.goal executableLeft executableRight ::
          executableTail, runtime) →
      StrictUnifyOperands alpha sourceBase runtime left right
        executableLeft executableRight

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
  state.stepOpen
    { state.toConf with
      cur := some (rest, runtime)
      alts := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).1
      barriers := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).2 }

@[simp] theorem cutSuccessor_persistent
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (cutSuccessor state barrier rest runtime).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames scopes =>
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
  state.stepOpen
    { state.toConf with
      cur := some
        (rest, PLeaTTa.trimFor rest state.toConf.qterm installed) }

@[simp] theorem unifySuccessor_persistent
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames scopes =>
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

@[simp] theorem unifySuccessor_alts
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.alts =
      state.control.alts := by
  rfl

@[simp] theorem unifySuccessor_qterm
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.qterm =
      state.control.qterm := by
  rfl

@[simp] theorem unifySuccessor_answers
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.answers =
      state.control.answers := by
  rfl

@[simp] theorem unifySuccessor_answerKeys
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.answerKeys =
      state.control.answerKeys := by
  rfl

@[simp] theorem unifySuccessor_barriers
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).control.barriers =
      state.control.barriers := by
  rfl

@[simp] theorem unifySuccessor_frames
    (state : OpenConf) (rest : List PLeaTTa.Goal)
    (installed : Metta.Subst) :
    (unifySuccessor state rest installed).frames = state.frames := by
  rfl

/-- Either sealed equality spelling takes exactly one transition in the
sealed machine and reaches the shared trimmed successor. -/
theorem executable_unify_sealed_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf)
    (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
    (left right : Metta.Atom) (rest : List PLeaTTa.Goal)
    (runtime installed : Metta.Subst)
    (head :
      state.control.cur =
        some (spelling.goal left right :: rest, runtime))
    (unified : PLeaTTa.unifyB runtime left right = some installed) :
    PLeaTTa.Step prog gt state.toConf
      (unifySuccessor state rest installed).toConf := by
  have sealedHead :
      state.toConf.cur =
        some (spelling.goal left right :: rest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
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
  exact executable_unify_sealed_step state spelling left right rest runtime
    installed head unified

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

/-! ## Primitive equality failure: semantic reflection and control mismatch -/

/-- Exact executable successor of one failed primitive equality.  The sealed
machine immediately pulls the next retained alternative; this is deliberately
not identified with the independent leaf's branch-completion terminal. -/
def unifyFailureSuccessor (state : OpenConf) : OpenConf :=
  state.stepOpen (PLeaTTa.pull { state.toConf with cur := none })

/-- The eager pull after a failed primitive equality preserves the global
resolution-name bound.  Clearing the failed current goal only removes live
names; the existing pull theorem then accounts for the selected alternative. -/
theorem ConfBelowResolutionCounter.unifyFailureSuccessor
    (state : OpenConf)
    (below : ConfBelowResolutionCounter state.toConf) :
    ConfBelowResolutionCounter (unifyFailureSuccessor state).toConf := by
  let cleared : Conf := { state.toConf with cur := none }
  have clearedBelow : ConfBelowResolutionCounter cleared := by
    apply ConfBelowResolutionCounter.of_subset (target := cleared) below
      (Nat.le_refl _)
    intro name member
    simp only [cleared, resolutionLiveVars, List.nil_append,
      List.mem_append] at member ⊢
    aesop
  have pulledBelow := clearedBelow.pull
  unfold _root_.PLeaTTa.PrologOrdinaryStepBridge.unifyFailureSuccessor
  rw [OpenConf.stepOpen_toConf]
  simpa [cleared] using pulledBelow

/-- Pulling after primitive-unification failure changes only backtrackable
control.  The dynamic world and global high-water remain current. -/
@[simp] theorem unifyFailureSuccessor_persistent (state : OpenConf) :
    (unifyFailureSuccessor state).persistent = state.persistent := by
  have world :
      (PLeaTTa.pull { state.toConf with cur := none }).world =
        state.toConf.world := by
    unfold PLeaTTa.pull
    generalize outcomeEq :
      PLeaTTa.pullAuxTracked state.toConf.barriers state.toConf.alts =
        outcome
    rcases outcome with ⟨outcome, barriers⟩
    cases outcome with
    | none => rfl
    | some pulled =>
        rcases pulled with ⟨target, rest⟩
        cases target with
        | softcutExhausted frame seenSuccess =>
            cases seenSuccess <;> rfl
        | _ => rfl
  have counter :
      (PLeaTTa.pull { state.toConf with cur := none }).counter =
        state.toConf.counter := by
    unfold PLeaTTa.pull
    generalize outcomeEq :
      PLeaTTa.pullAuxTracked state.toConf.barriers state.toConf.alts =
        outcome
    rcases outcome with ⟨outcome, barriers⟩
    cases outcome with
    | none => rfl
    | some pulled =>
        rcases pulled with ⟨target, rest⟩
        cases target with
        | softcutExhausted frame seenSuccess =>
            cases seenSuccess <;> rfl
        | _ => rfl
  change
    persistentOf (PLeaTTa.pull { state.toConf with cur := none }) =
      state.persistent
  unfold persistentOf
  rw [world, counter]
  cases state with
  | mk persistent control frames scopes =>
      cases persistent
      rfl

/-- An enabled exact barrier cache remains enabled and exact across the eager
pull performed after primitive-unification failure.

This is stronger than coherence: the reference `none` cache lane cannot
inhabit the conclusion.  It is useful when a surrounding correspondence must
rule out silently inheriting the pre-pull depth. -/
theorem unifyFailureSuccessor_barrierCacheExact
    (state : OpenConf)
    (cache : state.control.barriers =
      some (PLeaTTa.barrierCount state.control.alts)) :
    (unifyFailureSuccessor state).control.barriers =
      some
        (PLeaTTa.barrierCount
          (unifyFailureSuccessor state).control.alts) := by
  have sealedCache : state.toConf.barriers =
      some (PLeaTTa.barrierCount state.toConf.alts) := by
    simpa [OpenConf.toConf, Control.toConf] using cache
  change
    (PLeaTTa.pull { state.toConf with cur := none }).barriers =
      some
        (PLeaTTa.barrierCount
          (PLeaTTa.pull { state.toConf with cur := none }).alts)
  unfold PLeaTTa.pull
  simp only [sealedCache, PLeaTTa.pullAuxTracked]
  rw [PLeaTTa.pullAuxCached_exact]
  cases pulled : PLeaTTa.pullAux state.toConf.alts with
  | none => simp [PLeaTTa.barrierCount]
  | some result =>
      rcases result with ⟨target, rest⟩
      cases target with
      | branch goals binding => simp
      | catchResume frame protectedAlts =>
          simp [Nat.add_comm]
      | softcutExhausted frame seenSuccess =>
          cases seenSuccess <;> simp
      | softcutResume frame protectedAlts =>
          simp [Nat.add_comm]

/-- Failed primitive unification may pull another alternative, but it never
manufactures a nested-run answer. -/
@[simp] theorem unifyFailureSuccessor_answers (state : OpenConf) :
    (unifyFailureSuccessor state).control.answers = state.control.answers := by
  change
    (PLeaTTa.pull { state.toConf with cur := none }).answers =
      state.control.answers
  unfold PLeaTTa.pull
  generalize outcomeEq :
    PLeaTTa.pullAuxTracked state.toConf.barriers state.toConf.alts = outcome
  rcases outcome with ⟨outcome, barriers⟩
  cases outcome with
  | none => rfl
  | some pulled =>
      rcases pulled with ⟨target, rest⟩
      cases target with
      | softcutExhausted frame seenSuccess =>
          cases seenSuccess <;> rfl
      | _ => rfl

@[simp] theorem unifyFailureSuccessor_frames (state : OpenConf) :
    (unifyFailureSuccessor state).frames = state.frames := by
  rfl

@[simp] theorem unifyFailureSuccessor_scopes (state : OpenConf) :
    (unifyFailureSuccessor state).scopes = state.scopes := by
  rfl

/-- With no retained alternative, the sealed failed-unification pull reaches
an actual terminal generator.  The barrier cache may normalize on exhaustion;
terminality depends only on current work and alternatives. -/
theorem unifyFailureSuccessor_terminal_of_alts_empty
    (state : OpenConf) (empty : state.control.alts = []) :
    PLeaTTa.Terminal (unifyFailureSuccessor state).toConf := by
  have sealedEmpty : state.toConf.alts = [] := by
    simpa [OpenConf.toConf, Control.toConf] using empty
  constructor <;>
    cases cache : state.toConf.barriers <;>
      simp [unifyFailureSuccessor, PLeaTTa.pull, PLeaTTa.pullAux,
        PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached, sealedEmpty, cache]

/-- Either sealed equality spelling takes exactly one failure transition in
the findall/call-fine lane.  The target includes the sealed machine's eager
DFS pull rather than fabricating a branch-completion state. -/
theorem executable_unify_failure_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf)
    (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
    (left right : Metta.Atom) (rest : List PLeaTTa.Goal)
    (runtime : Metta.Subst)
    (head :
      state.control.cur =
        some (spelling.goal left right :: rest, runtime))
    (failed : PLeaTTa.unifyB runtime left right = none) :
    DemandDrivenCallStep.Step prog gt (.ready state)
      (.ready (unifyFailureSuccessor state)) := by
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
    (unifyFailureSuccessor state) notLocalCall
  apply DemandDrivenStep.Step.ordinary state
    (unifyFailureSuccessor state).toConf notFindall
  cases spelling with
  | equality =>
      simpa [unifyFailureSuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.eq_fail state.toConf left right rest runtime
          sealedHead failed)
  | compilerAlias =>
      simpa [unifyFailureSuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.compileAlias_fail state.toConf left right rest runtime
          sealedHead failed)

/-- Paired failed primitive-unification transitions on the actual task
states.

Source-side Boolean-alias safety, live alpha support, and the ordinary task
payload construct the strict source-guided operand readings internally.
Executable success would therefore reflect to a source `UnifyResolution`,
so the source clash forces the exact sealed failure constructor.  The result
intentionally records, rather than erases, the remaining granularity
mismatch: the independent leaf emits branch completion and becomes terminal,
while the sealed machine pulls its next alternative inside the same step.
Choice/resource correspondence must close that wrapper seam before a
whole-state bisimulation theorem is claimed. -/
theorem unify_failure_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
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
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Metta.Atom)
        (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst),
      state.control.cur =
          some (spelling.goal executableLeft executableRight ::
            executableTail, runtime) ∧
        RawStep session
          (.task scope (.unify left right :: references) current)
          [.completed] .none session (.terminal .completed) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (unifyFailureSuccessor state)) ∧
        (unifyFailureSuccessor state).persistent =
          state.persistent := by
  rcases agreement with
    ⟨executables, runtime, _persistent, currentControl, payload⟩
  rcases payload.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, executableTail,
      executableShape, leftAgreement, rightAgreement, _tailControl⟩
  subst executables
  have aliasSafe :
      CurrentUnifyOperandsAliasSafe current left right :=
    CurrentUnifyOperandsAliasSafe.of_booleanAliasSafe
      currentSafe leftAliasSafe rightAliasSafe
  have strictOperands :=
    payload.strictUnifyOperands_of_currentAliasSafe
      leftAgreement rightAgreement leftSupported rightSupported aliasSafe
  have failed :=
    payload.unifyB_eq_none_of_no_resolution strictOperands clash
  exact
    ⟨spelling, executableLeft, executableRight, executableTail, runtime,
      currentControl,
      RawStep.taskUnifyFailure scope left right references current session
        clash,
      executable_unify_failure_step state spelling executableLeft
        executableRight executableTail runtime currentControl failed,
      unifyFailureSuccessor_persistent state⟩

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
