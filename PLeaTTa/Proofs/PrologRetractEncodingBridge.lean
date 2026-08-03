-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetractEncodingBridge
Purpose: Relate decoder-origin independent retract syntax to the private
  executable Prolog-compound representation and transport source unifiers
  into the actual executable unifier.
Trusted boundary: none
Main exports: DecoderGoalAlphaAgrees, DecoderClauseAlphaAgrees,
  RetractSyntaxRuntimeReading, unifyB_complete_of_computed_retract_mgu,
  computesDenotationalMgu_exists_of_unifyB_retract_success
[SPEC metta.pl:279-280] PeTTa retracts the first clause whose copied syntax
  unifies with the requested pattern; this module isolates the corresponding
  representation and unifier seam without claiming the surrounding scan.
-/
import PLeaTTa.Proofs.PrologGoalAlpha
import PLeaTTa.Proofs.PrologMguBridge
import PLeaTTa.Proofs.PrologRuntimeDecode

namespace PLeaTTa.PrologRetractEncodingBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.DatabaseActions
open PrologStateBridge
open PrologPrefilterBridge
open PrologMguBridge
open PrologMguValuation
open PrologGoalAlpha
open PrologCanonicalRuntimeReading
open PrologRuntimeDecode

/-!
`CanonicalRuntimeAgrees` intentionally has no general Prolog-compound
constructor: ordinary values give `partial/2` and source booleans special
runtime representations.  Retraction, however, unifies a private syntax tree
whose reserved `$clause` and `$goal.*` nodes are data, not ordinary values.

The relations below keep that context explicit.  Only reserved syntax nodes
are introduced here; every actual value field is delegated back to
`CanonicalRuntimeAgrees`.  In particular a predicate literally named `true`
stays `.sym "true"`, while a value atom `true` remains `.sym "True"`.
-/

/-- Ordered alpha term agreement appends without changing either side's
position or multiplicity. -/
theorem AlphaTermsAgree.append
    {alpha : List (LogicVar × String)}
    {leftReferences rightReferences : List Term}
    {leftExecutables rightExecutables : List Atom}
    (left : AlphaTermsAgree alpha leftReferences leftExecutables)
    (right : AlphaTermsAgree alpha rightReferences rightExecutables) :
    AlphaTermsAgree alpha (leftReferences ++ rightReferences)
      (leftExecutables ++ rightExecutables) := by
  induction left with
  | nil => simpa using right
  | cons head tail inductionHypothesis =>
      simpa using AlphaTermsAgree.cons head inductionHypothesis

/-- Alpha agreement for exactly the goal fragment emitted by the two
`Predicate/2` body decoders.  The executable call constructor is fixed by the
actual grounding-table lookup through `predicateRelationGoal`; no duplicate
dispatch classifier is admitted here. -/
inductive DecoderGoalAlphaAgrees (gt : GroundingTable)
    (alpha : List (LogicVar × String)) :
    PeTTaSpec.PrologCore.Goal → PLeaTTa.Goal → Prop where
  | unify {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : AlphaTermAgrees alpha referenceLeft executableLeft)
      (right : AlphaTermAgrees alpha referenceRight executableRight) :
      DecoderGoalAlphaAgrees gt alpha
        (.unify referenceLeft referenceRight)
        (.eq executableLeft executableRight)
  | relation {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      (arguments :
        AlphaTermsAgree alpha referenceArguments executableArguments)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      DecoderGoalAlphaAgrees gt alpha
        (.call predicate (referenceArguments ++ [referenceResult]))
        (PLeaTTa.predicateRelationGoal gt predicate executableArguments
          executableResult)

/-- Ordered decoder-body counterpart.  The source decoder has already
flattened conjunctions, so no structural-stuttering constructor belongs in
this relation. -/
inductive DecoderGoalsAlphaAgrees (gt : GroundingTable)
    (alpha : List (LogicVar × String)) :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | nil : DecoderGoalsAlphaAgrees gt alpha [] []
  | cons {reference : PeTTaSpec.PrologCore.Goal}
      {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (head : DecoderGoalAlphaAgrees gt alpha reference executable)
      (tail : DecoderGoalsAlphaAgrees gt alpha references executables) :
      DecoderGoalsAlphaAgrees gt alpha
        (reference :: references) (executable :: executables)

/-- Decoder provenance is a strict refinement of the general runtime-alpha
goal relation. -/
theorem DecoderGoalAlphaAgrees.toAlphaGoalAgrees
    {gt : GroundingTable} {alpha : List (LogicVar × String)}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : PLeaTTa.Goal}
    (agreement : DecoderGoalAlphaAgrees gt alpha reference executable) :
    AlphaGoalAgrees alpha 0 reference executable := by
  cases agreement with
  | unify left right =>
      exact .unify left right
  | @relation predicate referenceArguments referenceResult
      executableArguments executableResult arguments result =>
      unfold PLeaTTa.predicateRelationGoal
      split
      · exact .builtin arguments result
      · exact .definedCall arguments result

/-- List projection retains exact order and multiplicity. -/
theorem DecoderGoalsAlphaAgrees.toAlphaGoalsAgree
    {gt : GroundingTable} {alpha : List (LogicVar × String)}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : DecoderGoalsAlphaAgrees gt alpha references executables) :
    AlphaGoalsAgree alpha 0 references executables := by
  induction agreement with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons head.toAlphaGoalAgrees inductionHypothesis

mutual

/-- Runtime representation of the reserved canonical retract-syntax nodes.
Value leaves remain in `CanonicalRuntimeAgrees`; therefore this relation
cannot create a second representation of ordinary partial values or Boolean
atoms. -/
inductive RetractSyntaxRuntimeAgrees
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | goalUnify {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
      (left : CanonicalRuntimeAgrees alpha leftTree leftAtom)
      (right : CanonicalRuntimeAgrees alpha rightTree rightAtom) :
      RetractSyntaxRuntimeAgrees alpha
        (.node (.compound "$goal.unify") [leftTree, rightTree])
        (prologCompoundC "$goal.unify" (chainOf [leftAtom, rightAtom]))
  | goalCall {predicate : String} {argumentsTree : Tree}
      {argumentsAtom : Atom}
      (arguments :
        CanonicalRuntimeAgrees alpha argumentsTree argumentsAtom) :
      RetractSyntaxRuntimeAgrees alpha
        (.node (.compound "$goal.call")
          [.node (.atom predicate) [], argumentsTree])
        (prologCompoundC "$goal.call"
          (chainOf [.sym predicate, argumentsAtom]))
  | clause {predicate : String} {argumentsTree bodyTree : Tree}
      {argumentsAtom bodyAtom : Atom}
      (arguments :
        CanonicalRuntimeAgrees alpha argumentsTree argumentsAtom)
      (body : RetractSyntaxListRuntimeAgrees alpha bodyTree bodyAtom) :
      RetractSyntaxRuntimeAgrees alpha
        (.node (.compound "$clause")
          [.node (.atom predicate) [], argumentsTree, bodyTree])
        (prologCompoundC "$clause"
          (chainOf [.sym predicate, argumentsAtom, bodyAtom]))

/-- Proper-list representation used only for a list of reserved goal-syntax
nodes. -/
inductive RetractSyntaxListRuntimeAgrees
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | nil :
      RetractSyntaxListRuntimeAgrees alpha (.node .nil []) nilA
  | cons {headTree tailTree : Tree} {headAtom tailAtom : Atom}
      (head : RetractSyntaxRuntimeAgrees alpha headTree headAtom)
      (tail : RetractSyntaxListRuntimeAgrees alpha tailTree tailAtom) :
      RetractSyntaxListRuntimeAgrees alpha
        (.node .cons [headTree, tailTree]) (consC headAtom tailAtom)

end

mutual

/-- Source-guided inverse reading for reserved retract syntax.  Ordinary
value leaves use the functional runtime reading, while predicate-name slots
remain literal metadata and are therefore intentionally not interpreted as
Boolean values. -/
inductive RetractSyntaxRuntimeReading
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | goalUnify {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
      (left : CanonicalRuntimeReading alpha leftTree leftAtom)
      (right : CanonicalRuntimeReading alpha rightTree rightAtom) :
      RetractSyntaxRuntimeReading alpha
        (.node (.compound "$goal.unify") [leftTree, rightTree])
        (prologCompoundC "$goal.unify" (chainOf [leftAtom, rightAtom]))
  | goalCall {predicate : String} {argumentsTree : Tree}
      {argumentsAtom : Atom}
      (arguments :
        CanonicalRuntimeReading alpha argumentsTree argumentsAtom) :
      RetractSyntaxRuntimeReading alpha
        (.node (.compound "$goal.call")
          [.node (.atom predicate) [], argumentsTree])
        (prologCompoundC "$goal.call"
          (chainOf [.sym predicate, argumentsAtom]))
  | clause {predicate : String} {argumentsTree bodyTree : Tree}
      {argumentsAtom bodyAtom : Atom}
      (arguments :
        CanonicalRuntimeReading alpha argumentsTree argumentsAtom)
      (body : RetractSyntaxListRuntimeReading alpha bodyTree bodyAtom) :
      RetractSyntaxRuntimeReading alpha
        (.node (.compound "$clause")
          [.node (.atom predicate) [], argumentsTree, bodyTree])
        (prologCompoundC "$clause"
          (chainOf [.sym predicate, argumentsAtom, bodyAtom]))

/-- Proper-list companion to `RetractSyntaxRuntimeReading`. -/
inductive RetractSyntaxListRuntimeReading
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | nil :
      RetractSyntaxListRuntimeReading alpha (.node .nil []) nilA
  | cons {headTree tailTree : Tree} {headAtom tailAtom : Atom}
      (head : RetractSyntaxRuntimeReading alpha headTree headAtom)
      (tail : RetractSyntaxListRuntimeReading alpha tailTree tailAtom) :
      RetractSyntaxListRuntimeReading alpha
        (.node .cons [headTree, tailTree]) (consC headAtom tailAtom)

end

mutual

/-- Alias safety for the value slots of reserved retract syntax.  Metadata
predicate names are deliberately excluded: a predicate literally named
`True` is unambiguous even though a value with that runtime spelling is the
normalized Boolean. -/
def RetractSyntaxValueAliasSafe : Tree → Prop
  | .node (.compound "$goal.unify") [left, right] =>
      NoRuntimeBooleanAliases left ∧ NoRuntimeBooleanAliases right
  | .node (.compound "$goal.call")
      [.node (.atom _) [], arguments] =>
      NoRuntimeBooleanAliases arguments
  | .node (.compound "$clause")
      [.node (.atom _) [], arguments, body] =>
      NoRuntimeBooleanAliases arguments ∧
        RetractSyntaxListValueAliasSafe body
  | _ => False

/-- Proper-list companion to `RetractSyntaxValueAliasSafe`. -/
def RetractSyntaxListValueAliasSafe : Tree → Prop
  | .node .nil [] => True
  | .node .cons [head, tail] =>
      RetractSyntaxValueAliasSafe head ∧
        RetractSyntaxListValueAliasSafe tail
  | _ => False

end


mutual

/-- The strict reading remains a valid forward representation. -/
theorem RetractSyntaxRuntimeReading.toAgrees
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxRuntimeReading alpha tree atom) :
    RetractSyntaxRuntimeAgrees alpha tree atom := by
  cases reading with
  | goalUnify left right =>
      exact .goalUnify left.toCanonicalRuntimeAgrees
        right.toCanonicalRuntimeAgrees
  | goalCall arguments =>
      exact .goalCall arguments.toCanonicalRuntimeAgrees
  | clause arguments body =>
      exact .clause arguments.toCanonicalRuntimeAgrees body.toAgrees

/-- Proper-list projection to the broad forward representation. -/
theorem RetractSyntaxListRuntimeReading.toAgrees
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxListRuntimeReading alpha tree atom) :
    RetractSyntaxListRuntimeAgrees alpha tree atom := by
  cases reading with
  | nil => exact .nil
  | cons head tail => exact .cons head.toAgrees tail.toAgrees

end


mutual

/-- Broad decoder agreement becomes the unique source-guided reading once
only its ordinary value slots are known Boolean-alias-safe. -/
theorem RetractSyntaxRuntimeAgrees.toReading
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (agreement : RetractSyntaxRuntimeAgrees alpha tree atom)
    (safe : RetractSyntaxValueAliasSafe tree) :
    RetractSyntaxRuntimeReading alpha tree atom := by
  cases agreement with
  | goalUnify left right =>
      simp only [RetractSyntaxValueAliasSafe] at safe
      exact .goalUnify
        (PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
          left safe.1)
        (PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
          right safe.2)
  | goalCall arguments =>
      simp only [RetractSyntaxValueAliasSafe] at safe
      exact .goalCall
        (PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
          arguments safe)
  | clause arguments body =>
      simp only [RetractSyntaxValueAliasSafe] at safe
      exact .clause
        (PrologCanonicalRuntimeReading.CanonicalRuntimeAgrees.toCanonicalRuntimeReading
          arguments safe.1)
        (body.toReading safe.2)

/-- Proper-list conversion to the strict source-guided reading. -/
theorem RetractSyntaxListRuntimeAgrees.toReading
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (agreement : RetractSyntaxListRuntimeAgrees alpha tree atom)
    (safe : RetractSyntaxListValueAliasSafe tree) :
    RetractSyntaxListRuntimeReading alpha tree atom := by
  cases agreement with
  | nil => exact .nil
  | cons head tail =>
      simp only [RetractSyntaxListValueAliasSafe] at safe
      exact .cons (head.toReading safe.1) (tail.toReading safe.2)

end


mutual

/-- Exact canonical decoder equation for every source-guided reserved syntax
node.  This is the structural inverse used by runtime-success reflection; it
does not assert that arbitrary runtime expressions are source syntax. -/
theorem RetractSyntaxRuntimeReading.decodeAlphaAtom
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxRuntimeReading alpha tree atom) :
    decodeAlphaAtom alpha atom = tree := by
  cases reading with
  | @goalUnify leftTree rightTree leftAtom rightAtom left right =>
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_prologCompound (alphaInverse alpha)
        "$goal.unify" [leftAtom, rightAtom] (by decide) (by decide)]
      simp only [List.map]
      rw [decodeRuntimeAtom_eq_of_reading (alphaInverse_on shared) left,
        decodeRuntimeAtom_eq_of_reading (alphaInverse_on shared) right]
  | @goalCall predicate argumentsTree argumentsAtom arguments =>
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_retractGoalCall]
      rw [decodeRuntimeAtom_eq_of_reading
        (alphaInverse_on shared) arguments]
  | @clause predicate argumentsTree bodyTree argumentsAtom bodyAtom
      arguments body =>
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_retractClause]
      rw [decodeRuntimeAtom_eq_of_reading
        (alphaInverse_on shared) arguments]
      have bodyEq :
          decodeRuntimeAtom (alphaInverse alpha) bodyAtom = bodyTree := by
        simpa [decodeAlphaAtom] using
          RetractSyntaxListRuntimeReading.decodeAlphaAtom shared body
      rw [bodyEq]

/-- Proper-list decoder exactness retains every reserved goal occurrence in
order and with multiplicity. -/
theorem RetractSyntaxListRuntimeReading.decodeAlphaAtom
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxListRuntimeReading alpha tree atom) :
    decodeAlphaAtom alpha atom = tree := by
  cases reading with
  | nil =>
      simp [decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
        nilA]
  | @cons headTree tailTree headAtom tailAtom head tail =>
      unfold decodeAlphaAtom
      simp only [decodeRuntimeAtom, consC, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize]
      have headEq :
          (RuntimeShape.ofAtom (alphaInverse alpha) headAtom).normalize =
            headTree := by
        simpa [decodeAlphaAtom, decodeRuntimeAtom] using
          RetractSyntaxRuntimeReading.decodeAlphaAtom shared head
      have tailEq :
          (RuntimeShape.ofAtom (alphaInverse alpha) tailAtom).normalize =
            tailTree := by
        simpa [decodeAlphaAtom, decodeRuntimeAtom] using
          RetractSyntaxListRuntimeReading.decodeAlphaAtom shared tail
      rw [headEq, tailEq]

end

/-- Pointwise alpha agreement represents the corresponding proper-list tree
through the ordinary value relation. -/
theorem AlphaTermsAgree.canonicalListRuntimeAgrees
    {alpha : List (LogicVar × String)} {terms : List Term}
    {atoms : List Atom}
    (agreement : AlphaTermsAgree alpha terms atoms) :
    CanonicalRuntimeAgrees alpha
      (Tree.prologList (Terms.denote terms) none) (chainOf atoms) := by
  induction agreement with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          head)
        inductionHypothesis

/-- The exact reserved syntax generated for one decoder-origin goal. -/
theorem DecoderGoalAlphaAgrees.syntaxRuntimeAgrees
    {gt : GroundingTable} {alpha : List (LogicVar × String)}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : PLeaTTa.Goal}
    (agreement : DecoderGoalAlphaAgrees gt alpha reference executable) :
    RetractSyntaxRuntimeAgrees alpha
      (Term.denote (goalSyntaxTerm reference))
      (PLeaTTa.retractGoalSyntaxAtom executable) := by
  cases agreement with
  | unify left right =>
      exact .goalUnify
        (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          left)
        (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          right)
  | @relation predicate referenceArguments referenceResult
      executableArguments executableResult arguments result =>
      have payload :
          AlphaTermsAgree alpha
            (referenceArguments ++ [referenceResult])
            (executableArguments ++ [executableResult]) :=
        PLeaTTa.PrologRetractEncodingBridge.AlphaTermsAgree.append
          arguments (.cons result .nil)
      unfold PLeaTTa.predicateRelationGoal
      split <;>
        exact .goalCall
          (PLeaTTa.PrologRetractEncodingBridge.AlphaTermsAgree.canonicalListRuntimeAgrees
            payload)

/-- Goal-list syntax uses one present cons cell per decoder-origin goal; no
answer, goal, or duplicate can disappear in the encoding. -/
theorem DecoderGoalsAlphaAgrees.syntaxListRuntimeAgrees
    {gt : GroundingTable} {alpha : List (LogicVar × String)}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : DecoderGoalsAlphaAgrees gt alpha references executables) :
    RetractSyntaxListRuntimeAgrees alpha
      (Tree.prologList (Terms.denote (goalsSyntaxTerms references)) none)
      (PLeaTTa.retractGoalsSyntaxAtom executables) := by
  induction agreement with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons head.syntaxRuntimeAgrees inductionHypothesis

/-- Complete alpha agreement for one decoder-origin clause.  The head is
output-last, while the body relation carries the strictly smaller decoder
provenance rather than arbitrary compiler control. -/
structure DecoderClauseAlphaAgrees (gt : GroundingTable)
    (alpha : List (LogicVar × String))
    (reference : LocalClause) (functor : String)
    (executable : PLeaTTa.Clause) : Prop where
  predicate : reference.predicate = functor
  arguments :
    AlphaTermsAgree alpha reference.arguments
      (executable.params ++ [executable.result])
  body : DecoderGoalsAlphaAgrees gt alpha reference.body executable.body

/-- The independent complete clause syntax and private executable syntax are
the same reserved canonical tree under one alpha graph. -/
theorem DecoderClauseAlphaAgrees.syntaxRuntimeAgrees
    {gt : GroundingTable} {alpha : List (LogicVar × String)}
    {reference : LocalClause} {functor : String}
    {executable : PLeaTTa.Clause}
    (agreement :
      DecoderClauseAlphaAgrees gt alpha reference functor executable) :
    RetractSyntaxRuntimeAgrees alpha
      (Term.denote (clauseSyntaxTerm reference))
      (PLeaTTa.retractClauseSyntaxAtom functor executable) := by
  change RetractSyntaxRuntimeAgrees alpha
    (.node (.compound "$clause")
      [.node (.atom reference.predicate) [],
        Tree.prologList (Terms.denote reference.arguments) none,
        Tree.prologList
          (Terms.denote (goalsSyntaxTerms reference.body)) none])
    (prologCompoundC "$clause"
      (chainOf [.sym functor,
        chainOf (executable.params ++ [executable.result]),
        PLeaTTa.retractGoalsSyntaxAtom executable.body]))
  rw [agreement.predicate]
  exact .clause
    (PLeaTTa.PrologRetractEncodingBridge.AlphaTermsAgree.canonicalListRuntimeAgrees
      agreement.arguments)
    (PLeaTTa.PrologRetractEncodingBridge.DecoderGoalsAlphaAgrees.syntaxListRuntimeAgrees
      agreement.body)

/-! ## Substitution transport and actual executable unification -/

/-- Deep executable substitution commutes with the private proper-list
spine. -/
private theorem subst_chainOf (runtime : Subst) (atoms : List Atom) :
    PLeaTTa.subst runtime (chainOf atoms) =
      chainOf (atoms.map (PLeaTTa.subst runtime)) := by
  induction atoms with
  | nil => simp [chainOf, nilA]
  | cons head tail inductionHypothesis =>
      change
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (chainOf (tail.map (PLeaTTa.subst runtime)))
      rw [show
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (PLeaTTa.subst runtime (chainOf tail)) by
              simp [consC, PLeaTTa.subst_expr]]
      rw [inductionHypothesis]

mutual

/-- A canonical/runtime valuation transports through every reserved syntax
node without giving the valuation any authority over its tag or predicate
name. -/
theorem RetractSyntaxRuntimeAgrees.apply
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (agreement : RetractSyntaxRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime) :
    RetractSyntaxRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  cases agreement with
  | goalUnify left right =>
      simpa [TreeSubstitution.apply_node, prologCompoundC,
        prologCompoundTagA, PLeaTTa.subst_expr, subst_chainOf] using
        (RetractSyntaxRuntimeAgrees.goalUnify
          (canonicalRuntimeAgrees_apply left valuation)
          (canonicalRuntimeAgrees_apply right valuation))
  | goalCall arguments =>
      simpa [TreeSubstitution.apply_node, prologCompoundC,
        prologCompoundTagA, PLeaTTa.subst_expr, subst_chainOf] using
        (RetractSyntaxRuntimeAgrees.goalCall
          (canonicalRuntimeAgrees_apply arguments valuation))
  | clause arguments body =>
      simpa [TreeSubstitution.apply_node, prologCompoundC,
        prologCompoundTagA, PLeaTTa.subst_expr, subst_chainOf] using
        (RetractSyntaxRuntimeAgrees.clause
          (canonicalRuntimeAgrees_apply arguments valuation)
          (RetractSyntaxListRuntimeAgrees.apply body valuation))

/-- Proper goal-syntax lists transport cell-for-cell. -/
theorem RetractSyntaxListRuntimeAgrees.apply
    {alpha : List (LogicVar × String)} {tree : Tree} {atom : Atom}
    (agreement : RetractSyntaxListRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime) :
    RetractSyntaxListRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  cases agreement with
  | nil =>
      simpa [nilA] using
        (RetractSyntaxListRuntimeAgrees.nil (alpha := alpha))
  | cons head tail =>
      simpa [TreeSubstitution.apply_node, consC,
        PLeaTTa.subst_expr] using
        (RetractSyntaxListRuntimeAgrees.cons
          (RetractSyntaxRuntimeAgrees.apply head valuation)
          (RetractSyntaxListRuntimeAgrees.apply tail valuation))

end

mutual

/-- The closed canonical valuation extracted from one executable result
commutes through every source-guided reserved retract-syntax node.  Runtime
substitution may affect only value leaves; private tags and metadata names
remain fixed. -/
theorem RetractSyntaxRuntimeReading.decodedGroundValuation_apply
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha) (runtime : Subst)
    {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxRuntimeReading alpha tree atom) :
    TreeSubstitution.apply
        (decodedGroundValuation alpha runtime) tree =
      groundTree
        (decodeAlphaAtom alpha (PLeaTTa.subst runtime atom)) := by
  cases reading with
  | @goalUnify leftTree rightTree leftAtom rightAtom left right =>
      have leftEq :=
        decodedGroundValuation_apply_of_reading shared runtime left
      have rightEq :=
        decodedGroundValuation_apply_of_reading shared runtime right
      have substEq :
          PLeaTTa.subst runtime
              (prologCompoundC "$goal.unify"
                (chainOf [leftAtom, rightAtom])) =
            prologCompoundC "$goal.unify"
              (chainOf [PLeaTTa.subst runtime leftAtom,
                PLeaTTa.subst runtime rightAtom]) := by
        simp [prologCompoundC, prologCompoundTagA,
          PLeaTTa.subst_expr, subst_chainOf]
      rw [substEq]
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_prologCompound (alphaInverse alpha)
        "$goal.unify"
        [PLeaTTa.subst runtime leftAtom,
          PLeaTTa.subst runtime rightAtom]
        (by decide) (by decide)]
      simp only [List.map]
      simp [TreeSubstitution.apply_node,
        TreeSubstitution.applyTrees_cons, groundTree, groundTrees,
        decodeAlphaAtom, leftEq, rightEq]
  | @goalCall predicate argumentsTree argumentsAtom arguments =>
      have argumentsEq :=
        decodedGroundValuation_apply_of_reading shared runtime arguments
      have substEq :
          PLeaTTa.subst runtime
              (prologCompoundC "$goal.call"
                (chainOf [.sym predicate, argumentsAtom])) =
            prologCompoundC "$goal.call"
              (chainOf [.sym predicate,
                PLeaTTa.subst runtime argumentsAtom]) := by
        simp [prologCompoundC, prologCompoundTagA,
          PLeaTTa.subst_expr, subst_chainOf]
      rw [substEq]
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_retractGoalCall]
      simp [TreeSubstitution.apply_node,
        TreeSubstitution.applyTrees_cons, groundTree, groundTrees,
        decodeAlphaAtom, argumentsEq]
  | @clause predicate argumentsTree bodyTree argumentsAtom bodyAtom
      arguments body =>
      have argumentsEq :=
        decodedGroundValuation_apply_of_reading shared runtime arguments
      have bodyEq :=
        RetractSyntaxListRuntimeReading.decodedGroundValuation_apply
          shared runtime body
      have substEq :
          PLeaTTa.subst runtime
              (prologCompoundC "$clause"
                (chainOf [.sym predicate, argumentsAtom, bodyAtom])) =
            prologCompoundC "$clause"
              (chainOf [.sym predicate,
                PLeaTTa.subst runtime argumentsAtom,
                PLeaTTa.subst runtime bodyAtom]) := by
        simp [prologCompoundC, prologCompoundTagA,
          PLeaTTa.subst_expr, subst_chainOf]
      rw [substEq]
      unfold decodeAlphaAtom
      rw [decodeRuntimeAtom_retractClause]
      simp [TreeSubstitution.apply_node,
        TreeSubstitution.applyTrees_cons, groundTree, groundTrees,
        decodeAlphaAtom, argumentsEq, bodyEq]

/-- Proper-list companion to the reserved-syntax valuation theorem. -/
theorem RetractSyntaxListRuntimeReading.decodedGroundValuation_apply
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha) (runtime : Subst)
    {tree : Tree} {atom : Atom}
    (reading : RetractSyntaxListRuntimeReading alpha tree atom) :
    TreeSubstitution.apply
        (decodedGroundValuation alpha runtime) tree =
      groundTree
        (decodeAlphaAtom alpha (PLeaTTa.subst runtime atom)) := by
  cases reading with
  | nil =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
        PLeaTTa.subst_gnd, nilA]
  | @cons headTree tailTree headAtom tailAtom head tail =>
      have headEq :=
        RetractSyntaxRuntimeReading.decodedGroundValuation_apply
          shared runtime head
      have tailEq :=
        RetractSyntaxListRuntimeReading.decodedGroundValuation_apply
          shared runtime tail
      simp [TreeSubstitution.apply_node,
        TreeSubstitution.applyTrees_cons, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize,
        consC, PLeaTTa.subst_expr, headEq, tailEq]

end

/-- Comparator equivalence is preserved by the private proper-list spine. -/
private theorem chainOf_equivalent {left right : List Atom}
    (equivalent :
      AtomsEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical
      (chainOf left) (chainOf right) := by
  induction left generalizing right with
  | nil =>
      cases equivalent
      exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | cons leftHead leftTail inductionHypothesis =>
      cases equivalent with
      | cons head tail =>
          exact .expression
            (.cons (.symbol "#c")
              (.cons head (.cons (inductionHypothesis tail) .nil)))

/-- A shared private compound tag lifts equivalence of the encoded argument
spine. -/
private theorem prologCompoundC_equivalent (functor : String)
    {left right : Atom}
    (arguments :
      AtomEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical
      (prologCompoundC functor left) (prologCompoundC functor right) := by
  exact .expression
    (.cons (.ground (PLeaTTa.prologGroundIdentical_self _))
      (.cons (.symbol functor) (.cons arguments .nil)))

mutual

/-- Equal reserved syntax trees have equivalent runtime representations.
Keeping the two tree indices distinct until the equality is consumed avoids
dependent elimination over reserved string tags; unequal constructors are
refuted by the tree equality itself.  The nontrivial value leaves are
delegated to the existing canonical-value theorem. -/
theorem RetractSyntaxRuntimeAgrees.equivalent_of_tree_eq
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {leftTree rightTree : Tree} {left right : Atom}
    (leftAgreement : RetractSyntaxRuntimeAgrees alpha leftTree left)
    (rightAgreement : RetractSyntaxRuntimeAgrees alpha rightTree right)
    (treeEq : leftTree = rightTree) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical left right := by
  cases leftAgreement with
  | goalUnify leftValue rightValue =>
      cases rightAgreement with
      | goalUnify otherLeft otherRight =>
          simp at treeEq
          rcases treeEq with ⟨rfl, rfl⟩
          apply prologCompoundC_equivalent
          apply chainOf_equivalent
          exact .cons
            (CanonicalRuntimeAgrees.equivalent_of_same
              functional leftValue otherLeft)
            (.cons
              (CanonicalRuntimeAgrees.equivalent_of_same
                functional rightValue otherRight)
              .nil)
      | goalCall _ => simp at treeEq
      | clause _ _ => simp at treeEq
  | goalCall arguments =>
      cases rightAgreement with
      | goalUnify _ _ => simp at treeEq
      | goalCall otherArguments =>
          simp at treeEq
          rcases treeEq with ⟨rfl, rfl⟩
          apply prologCompoundC_equivalent
          apply chainOf_equivalent
          exact .cons (.symbol _)
            (.cons
              (CanonicalRuntimeAgrees.equivalent_of_same
                functional arguments otherArguments)
              .nil)
      | clause _ _ => simp at treeEq
  | clause arguments body =>
      cases rightAgreement with
      | goalUnify _ _ => simp at treeEq
      | goalCall _ => simp at treeEq
      | clause otherArguments otherBody =>
          simp at treeEq
          rcases treeEq with ⟨rfl, rfl, rfl⟩
          apply prologCompoundC_equivalent
          apply chainOf_equivalent
          exact .cons (.symbol _)
            (.cons
              (CanonicalRuntimeAgrees.equivalent_of_same
                functional arguments otherArguments)
              (.cons
                (RetractSyntaxListRuntimeAgrees.equivalent_of_tree_eq
                  functional body otherBody rfl)
                .nil))

/-- Equal proper-list syntax trees have equivalent runtime spines. -/
theorem RetractSyntaxListRuntimeAgrees.equivalent_of_tree_eq
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {leftTree rightTree : Tree} {left right : Atom}
    (leftAgreement : RetractSyntaxListRuntimeAgrees alpha leftTree left)
    (rightAgreement : RetractSyntaxListRuntimeAgrees alpha rightTree right)
    (treeEq : leftTree = rightTree) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical left right := by
  cases leftAgreement with
  | nil =>
      cases rightAgreement with
      | nil => exact .ground (PLeaTTa.prologGroundIdentical_self _)
      | cons _ _ => simp at treeEq
  | cons head tail =>
      cases rightAgreement with
      | nil => simp at treeEq
      | cons otherHead otherTail =>
          simp at treeEq
          rcases treeEq with ⟨rfl, rfl⟩
          exact .expression
            (.cons (.symbol "#c")
              (.cons
                (RetractSyntaxRuntimeAgrees.equivalent_of_tree_eq
                  functional head otherHead rfl)
                (.cons
                  (RetractSyntaxListRuntimeAgrees.equivalent_of_tree_eq
                    functional tail otherTail rfl)
                  .nil)))

end

/-- A canonical source solution represented under the shared alpha graph is
an actual unifier of the two private syntax atoms after the current executable
binding.  This reaches `unifyB`; it is not a claim about an abstract unifier
parameter. -/
theorem unifyB_complete_of_normalized_retract_syntax
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha leftTree
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeAgrees alpha rightTree
      (PLeaTTa.subst base rightAtom))
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeSubstitution.apply canonical leftTree =
        TreeSubstitution.apply canonical rightTree) :
    ∃ result, PLeaTTa.unifyB base leftAtom rightAtom = some result := by
  have leftApplied := left.apply valuation
  have rightApplied := right.apply valuation
  have equivalent :=
    RetractSyntaxRuntimeAgrees.equivalent_of_tree_eq
      functional leftApplied rightApplied unifies
  exact PLeaTTa.unifyB_complete_of_prolog_equivalent_unifier
    base leftAtom rightAtom runtime equivalent

/-- Forward half of decoder-origin clash agreement.  A computed source MGU,
once its canonical valuation and the two normalized syntax representations
are supplied by the surrounding state bridge, forces the actual executable
`unifyB` call to succeed.  The reverse half is proved below using the stricter
source-guided reading, whose Boolean-alias premise is necessary for failure
reflection. -/
theorem unifyB_complete_of_computed_retract_mgu
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha (Term.denote leftTerm)
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeAgrees alpha (Term.denote rightTerm)
      (PLeaTTa.subst base rightAtom))
    {binding : Substitution}
    (computed : ComputesDenotationalMgu [(leftTerm, rightTerm)] binding)
    {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote binding) runtime) :
    ∃ result, PLeaTTa.unifyB base leftAtom rightAtom = some result := by
  apply unifyB_complete_of_normalized_retract_syntax base functional
    left right valuation
  exact computed.isMostGeneral.1 (leftTerm, rightTerm) (by simp)

/-! ## Actual executable success reflects to source success -/

/-- Comparator-equivalent substituted reserved syntax is unified by the
closed canonical valuation extracted from that same executable substitution.
The strict source-guided reading is load-bearing: broad Boolean-alias
agreement would make this implication false. -/
theorem decodedGroundValuation_unifies_retract_of_equivalent
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha) (runtime : Subst)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeReading alpha leftTree leftAtom)
    (right : RetractSyntaxRuntimeReading alpha rightTree rightAtom)
    (equivalent :
      AtomEquivalentWith PLeaTTa.prologGroundIdentical
        (PLeaTTa.subst runtime leftAtom)
        (PLeaTTa.subst runtime rightAtom)) :
    TreeUnifiesEquations
      (decodedGroundValuation alpha runtime)
      [(leftTree, rightTree)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  rw [left.decodedGroundValuation_apply shared runtime,
    right.decodedGroundValuation_apply shared runtime]
  exact congrArg groundTree
    (decodeRuntimeAtom_eq_of_equivalent
      (alphaInverse alpha) equivalent)

/-- Every semantic runtime MGU over source-guided reserved syntax supplies a
genuine ordered canonical MGU.  Runtime association-list orientation is
discarded only after its semantic unifier content constructs the canonical
candidate. -/
theorem orderedTreeMgu_exists_of_retract_runtime_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeReading alpha leftTree leftAtom)
    (right : RetractSyntaxRuntimeReading alpha rightTree rightAtom)
    {runtime : Subst}
    (runtimeMgu :
      PLeaTTa.RuntimeIsMguWith PLeaTTa.prologGroundIdentical runtime
        [(leftAtom, rightAtom)]) :
    ∃ canonical,
      OrderedTreeMgu [(leftTree, rightTree)] canonical := by
  have equivalent := runtimeMgu.1 (leftAtom, rightAtom) (by simp)
  exact
    OrderedTreeMgu.complete
      (decodedGroundValuation alpha runtime)
      (decodedGroundValuation_unifies_retract_of_equivalent
        shared runtime left right equivalent)

/-- Source-term specialization of reserved-syntax runtime reflection. -/
theorem computesDenotationalMgu_exists_of_retract_runtime_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeReading alpha
      (Term.denote leftTerm) leftAtom)
    (right : RetractSyntaxRuntimeReading alpha
      (Term.denote rightTerm) rightAtom)
    {runtime : Subst}
    (runtimeMgu :
      PLeaTTa.RuntimeIsMguWith PLeaTTa.prologGroundIdentical runtime
        [(leftAtom, rightAtom)]) :
    ∃ binding, ComputesDenotationalMgu [(leftTerm, rightTerm)] binding := by
  obtain ⟨canonical, derivation⟩ :=
    orderedTreeMgu_exists_of_retract_runtime_mgu
      shared left right runtimeMgu
  exact
    ⟨TreeSubstitution.reify canonical,
      ⟨canonical,
        by simpa [denoteEquations] using derivation,
        rfl⟩⟩

/-- A successful actual `unifyB` call on the already-base-substituted
source-guided retract encodings forces independent source MGU success.  This
is the reverse half needed to rule out an executable scan selecting an
earlier occurrence which the source scan rejects. -/
theorem computesDenotationalMgu_exists_of_unifyB_retract_success
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeReading alpha (Term.denote leftTerm)
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeReading alpha (Term.denote rightTerm)
      (PLeaTTa.subst base rightAtom))
    {result : Subst}
    (returned : PLeaTTa.unifyB base leftAtom rightAtom = some result) :
    ∃ binding, ComputesDenotationalMgu [(leftTerm, rightTerm)] binding := by
  obtain ⟨generated, _generatedEq, runtimeMgu, _installed⟩ :=
    PLeaTTa.unifyB_result_has_generated_mgu
      base leftAtom rightAtom result returned
  exact
    computesDenotationalMgu_exists_of_retract_runtime_mgu
      shared left right runtimeMgu

/-- Contrapositive scan form: an independently proved source clash forces
the actual executable unifier to return `none`, not merely to lack a chosen
result witness. -/
theorem unifyB_none_of_no_computed_retract_mgu
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeReading alpha (Term.denote leftTerm)
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeReading alpha (Term.denote rightTerm)
      (PLeaTTa.subst base rightAtom))
    (clash :
      ¬ ∃ binding,
        ComputesDenotationalMgu [(leftTerm, rightTerm)] binding) :
    PLeaTTa.unifyB base leftAtom rightAtom = none := by
  cases returned : PLeaTTa.unifyB base leftAtom rightAtom with
  | none => rfl
  | some result =>
      exact False.elim
        (clash
          (computesDenotationalMgu_exists_of_unifyB_retract_success
            base shared left right returned))

/-! ## Anti-vacuity: an actual non-reflexive reserved-syntax success -/

private def reflectedIdentity : LogicVar := .source "reflected-x"

private def reflectedAlpha : List (LogicVar × String) :=
  [(reflectedIdentity, "runtime-x")]

private def reflectedLeftTerm : Term :=
  .compound "$goal.unify"
    [.variable reflectedIdentity, .atom "anchor"]

private def reflectedRightTerm : Term :=
  .compound "$goal.unify"
    [.atom "value", .atom "anchor"]

private def reflectedLeftAtom : Atom :=
  prologCompoundC "$goal.unify"
    (chainOf [.var "runtime-x", .sym "anchor"])

private def reflectedRightAtom : Atom :=
  prologCompoundC "$goal.unify"
    (chainOf [.sym "value", .sym "anchor"])

private theorem reflectedAlpha_shared : SharedRuntimeAlpha reflectedAlpha := by
  constructor <;>
    intro <;>
    simp_all [reflectedAlpha]

private theorem reflectedLeftReading :
    RetractSyntaxRuntimeReading reflectedAlpha
      (Term.denote reflectedLeftTerm) reflectedLeftAtom := by
  exact .goalUnify
    (.variable (by simp [reflectedAlpha, reflectedIdentity]))
    (.atom (by decide) (by decide) (by decide) (by decide))

private theorem reflectedRightReading :
    RetractSyntaxRuntimeReading reflectedAlpha
      (Term.denote reflectedRightTerm) reflectedRightAtom := by
  exact .goalUnify
    (.atom (by decide) (by decide) (by decide) (by decide))
    (.atom (by decide) (by decide) (by decide) (by decide))

/- Executable anti-vacuity for the reflection theorem below: this is a real
non-reflexive `unifyB` call, and it binds the runtime variable to `value`.
Keeping the computation as a guard avoids turning the implementation's
bounded-round evaluator into part of the proof interface. -/
#guard PLeaTTa.unifyB [] reflectedLeftAtom reflectedRightAtom ==
  some [("runtime-x", .sym "value")]

/-- Every result returned by the concrete non-reflexive guard above reflects
to an independently stated denotational MGU.  The theorem is deliberately
parametric in the executable substitution: the adjacent guard establishes
that the premise is inhabited and pins the current executable result. -/
theorem actual_unifyB_success_reflects_nontrivial_retract_mgu
    {result : Subst}
    (returned :
      PLeaTTa.unifyB [] reflectedLeftAtom reflectedRightAtom = some result) :
    ∃ binding,
      ComputesDenotationalMgu
        [(reflectedLeftTerm, reflectedRightTerm)] binding :=
  computesDenotationalMgu_exists_of_unifyB_retract_success
    [] reflectedAlpha_shared
    (by simpa using reflectedLeftReading)
    (by simpa using reflectedRightReading)
    returned

end PLeaTTa.PrologRetractEncodingBridge
