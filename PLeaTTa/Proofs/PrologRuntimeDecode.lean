-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRuntimeDecode
Purpose: Decode exact runtime term identity back into the supported
  canonical Prolog tree algebra.
Trusted boundary: none
Main exports:
  RuntimeShape,
  decodeRuntimeAtom,
  decodeRuntimeAtom_eq_of_equivalent,
  CanonicalRuntimeReading.decodeRuntimeAtom
-/
import PLeaTTa.Proofs.PrologCanonicalRuntimeReading
import PLeaTTa.Proofs.PrologMguExecutableOpenFactor

namespace PLeaTTa.PrologRuntimeDecode

open Metta (Atom Ground)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologCanonicalRuntimeReading
open PrologMguExecutableOpenFactor
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguValuation
open PrologPrefilterBridge

/-!
Runtime unification is sound for `AtomEquivalentWith
prologGroundIdentical`, not for Lean equality of raw atoms: distinct IEEE
NaN payloads denote the same SWI-Prolog term.  Conversely, the broad
`CanonicalRuntimeAgrees` relation has no inverse because accepted source
aliases such as `True` and `true` share one runtime spelling.

The bridge below separates those two concerns.

* `RuntimeShape` quotes an atom using the exact `PrologGroundIdentity` key.
  Comparator-equivalent atoms therefore have literally equal shapes.
* `RuntimeShape.normalize` interprets only the private PeTTa encodings and
  normalizes runtime booleans.  Unsupported host grounds and generic runtime
  expressions receive conservative, well-formed canonical placeholders.

Only the forward implication from runtime equivalence to decoded equality is
claimed.  The normalization is intentionally not injective on unsupported
host data; failure reflection needs one canonical unifier witness, not a
fictional source syntax for every host payload.
-/

/-- Exact structural runtime identity, with executable variable names
already interpreted in the independent canonical namespace. -/
inductive RuntimeShape where
  | symbol (name : String)
  | variable (identity : LogicVar)
  | ground (identity : PLeaTTa.PrologGroundIdentity)
  | expression (children : List RuntimeShape)
deriving Repr

mutual

/-- Quote one runtime atom into exact SWI-Prolog term identity. -/
def RuntimeShape.ofAtom
    (variableIdentity : String → LogicVar) : Atom → RuntimeShape
  | .sym name => .symbol name
  | .var name => .variable (variableIdentity name)
  | .gnd payload =>
      .ground (PLeaTTa.PrologGroundIdentity.ofGround payload)
  | .expr atoms => .expression (RuntimeShape.ofAtoms variableIdentity atoms)

/-- Ordered-list counterpart of `RuntimeShape.ofAtom`. -/
def RuntimeShape.ofAtoms
    (variableIdentity : String → LogicVar) : List Atom → List RuntimeShape
  | [] => []
  | atom :: atoms =>
      RuntimeShape.ofAtom variableIdentity atom ::
        RuntimeShape.ofAtoms variableIdentity atoms

end

@[simp] theorem RuntimeShape.ofAtoms_eq_map
    (variableIdentity : String → LogicVar) (atoms : List Atom) :
    RuntimeShape.ofAtoms variableIdentity atoms =
      atoms.map (RuntimeShape.ofAtom variableIdentity) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      simp [RuntimeShape.ofAtoms, inductionHypothesis]

mutual

/-- Canonical interpretation of one exact runtime shape.

The two private external tags and the `#c` cell are recognized before the
generic fallbacks.  A symbol used as the functor slot of `partial/2` remains
literal even when it is spelled `True`; boolean normalization applies only
to value positions. -/
def RuntimeShape.normalize : RuntimeShape → Tree
  | .symbol "True" => .node (.atom "true") []
  | .symbol "False" => .node (.atom "false") []
  | .symbol name => .node (.atom name) []
  | .variable identity => .variable identity
  | .ground (.integer value) => .node (.integer value) []
  | .ground (.floating value) => .node (.float value) []
  | .ground (.string value) => .node (.string value) []
  | .ground (.external "PLeaTTa.internal" "nil") => .node .nil []
  | .ground _ => .node (.compound "$runtime-ground") []
  | .expression
      [.ground (.external "PLeaTTa.internal" "partial"),
        .symbol head, arguments] =>
      .node (.compound "partial")
        [.node (.atom head) [], RuntimeShape.normalize arguments]
  | .expression [.symbol "#c", head, tail] =>
      .node .cons
        [RuntimeShape.normalize head, RuntimeShape.normalize tail]
  | .expression children =>
      .node (.compound "$runtime-expression")
        (RuntimeShape.normalizeList children)

/-- Ordered-list counterpart of `RuntimeShape.normalize`. -/
def RuntimeShape.normalizeList : List RuntimeShape → List Tree
  | [] => []
  | shape :: shapes =>
      RuntimeShape.normalize shape :: RuntimeShape.normalizeList shapes

end

@[simp] theorem RuntimeShape.normalizeList_eq_map
    (shapes : List RuntimeShape) :
    RuntimeShape.normalizeList shapes =
      shapes.map RuntimeShape.normalize := by
  induction shapes with
  | nil => rfl
  | cons shape shapes inductionHypothesis =>
      simp [RuntimeShape.normalizeList, inductionHypothesis]

/-- Total canonical interpretation of one runtime atom relative to a chosen
inverse spelling for executable variables. -/
def decodeRuntimeAtom
    (variableIdentity : String → LogicVar) (atom : Atom) : Tree :=
  (RuntimeShape.ofAtom variableIdentity atom).normalize

mutual

/-- Comparator-equivalent runtime atoms quote to the same exact runtime
shape.  The float case uses the explicit SWI identity key, so distinct NaN
payloads need no raw-Float equality assumption. -/
theorem RuntimeShape.ofAtom_eq_of_equivalent
    (variableIdentity : String → LogicVar)
    {left right : Atom}
    (equivalent :
      PLeaTTa.AtomEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    RuntimeShape.ofAtom variableIdentity left =
      RuntimeShape.ofAtom variableIdentity right := by
  cases equivalent with
  | symbol name =>
      rfl
  | «variable» name =>
      rfl
  | @ground left right identical =>
      simp only [RuntimeShape.ofAtom, RuntimeShape.ground.injEq]
      exact
        (PLeaTTa.prologGroundIdentical_eq_true_iff left right).1 identical
  | expression children =>
      simp only [RuntimeShape.ofAtom, RuntimeShape.expression.injEq]
      exact RuntimeShape.ofAtoms_eq_of_equivalent
        variableIdentity children

/-- Ordered-list companion to `RuntimeShape.ofAtom_eq_of_equivalent`. -/
theorem RuntimeShape.ofAtoms_eq_of_equivalent
    (variableIdentity : String → LogicVar)
    {left right : List Atom}
    (equivalent :
      PLeaTTa.AtomsEquivalentWith
        PLeaTTa.prologGroundIdentical left right) :
    RuntimeShape.ofAtoms variableIdentity left =
      RuntimeShape.ofAtoms variableIdentity right := by
  cases equivalent with
  | nil =>
      rfl
  | cons head tail =>
      exact congrArg₂ List.cons
        (RuntimeShape.ofAtom_eq_of_equivalent variableIdentity head)
        (RuntimeShape.ofAtoms_eq_of_equivalent variableIdentity tail)

end

/-- Runtime term identity implies literal equality of canonical decodings.
This is the reflection direction needed to transport an executable unifier
back into one independent canonical unifier witness. -/
theorem decodeRuntimeAtom_eq_of_equivalent
    (variableIdentity : String → LogicVar)
    {left right : Atom}
    (equivalent :
      PLeaTTa.AtomEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    decodeRuntimeAtom variableIdentity left =
      decodeRuntimeAtom variableIdentity right := by
  unfold decodeRuntimeAtom
  rw [RuntimeShape.ofAtom_eq_of_equivalent variableIdentity equivalent]

/-! ## Exactness on the supported PeTTa runtime reading -/

/-- A chosen variable-name inverse is exact on the finite shared alpha
graph. -/
def VariableInverseOn
    (alpha : List (LogicVar × String))
    (variableIdentity : String → LogicVar) : Prop :=
  ∀ {identity name}, (identity, name) ∈ alpha →
    variableIdentity name = identity

/-- Total inverse of one finite alpha graph.  The fallback is unreachable
for every runtime variable covered by the graph; it keeps the decoder total
on arbitrary host atoms without introducing an extra partiality seam. -/
noncomputable def alphaInverse
    (alpha : List (LogicVar × String)) (name : String) : LogicVar := by
  classical
  exact
    if covered : RuntimeAlphaCovers alpha name then
      Classical.choose covered
    else
      .source ("$runtime:" ++ name)

/-- Inverse functionality of the shared alpha graph makes the chosen
runtime-name inverse exact on every live pair. -/
theorem alphaInverse_eq_of_linked
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha) :
    alphaInverse alpha name = identity := by
  have covered : RuntimeAlphaCovers alpha name :=
    ⟨identity, linked⟩
  rw [alphaInverse, dif_pos covered]
  exact
    shared.backward (Classical.choose_spec covered) linked

/-- The chosen finite inverse satisfies the exact decoder premise. -/
theorem alphaInverse_on
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha) :
    VariableInverseOn alpha (alphaInverse alpha) := by
  intro identity name linked
  exact alphaInverse_eq_of_linked shared linked

/-- Canonical decoding specialized to the unique inverse of a finite shared
alpha graph. -/
noncomputable def decodeAlphaAtom
    (alpha : List (LogicVar × String)) (atom : Atom) : Tree :=
  decodeRuntimeAtom (alphaInverse alpha) atom

/-- The total decoder is a left inverse of the source-guided supported
runtime reading.  The source-guided relation, rather than the broad forward
relation, is load-bearing at the boolean aliases. -/
theorem decodeRuntimeAtom_eq_of_reading
    {alpha : List (LogicVar × String)}
    {variableIdentity : String → LogicVar}
    (inverse : VariableInverseOn alpha variableIdentity)
    {tree : Tree} {atom : Atom}
    (reading : CanonicalRuntimeReading alpha tree atom) :
    decodeRuntimeAtom variableIdentity atom = tree := by
  induction reading with
  | «variable» linked =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, inverse linked]
  | atom notLowerTrue notLowerFalse notRuntimeTrue notRuntimeFalse =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | trueAtom =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | falseAtom =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | integer value =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | float value =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | string value =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | @partialValue head argumentsTree encodedArguments arguments
      inductionHypothesis =>
      simpa [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize,
        PLeaTTa.PrologGroundIdentity.ofGround,
        partialC, partialTagA] using inductionHypothesis
  | nil =>
      simp [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
        nilA]
  | @cons headTree tailTree headAtom tailAtom head tail headIH tailIH =>
      change
        (RuntimeShape.ofAtom variableIdentity headAtom).normalize =
          headTree at headIH
      change
        (RuntimeShape.ofAtom variableIdentity tailAtom).normalize =
          tailTree at tailIH
      simp only [decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize, consC]
      rw [headIH, tailIH]

/-- The alpha-specialized decoder is exact on every supported source-guided
reading. -/
theorem decodeAlphaAtom_eq_of_reading
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {tree : Tree} {atom : Atom}
    (reading : CanonicalRuntimeReading alpha tree atom) :
    decodeAlphaAtom alpha atom = tree := by
  exact decodeRuntimeAtom_eq_of_reading (alphaInverse_on shared) reading

/-! ## A closed canonical valuation extracted from one runtime result -/

mutual

/-- Structural grounding removes every canonical variable. -/
theorem groundTree_variables_false (tree : Tree) :
    TreeVariablesSatisfy (fun _ => False) (groundTree tree) := by
  cases tree with
  | «variable» identity =>
      trivial
  | node symbol children =>
      exact groundTrees_variables_false children

/-- Ordered-list companion to `groundTree_variables_false`. -/
theorem groundTrees_variables_false (trees : List Tree) :
    TreesVariablesSatisfy (fun _ => False) (groundTrees trees) := by
  cases trees with
  | nil =>
      trivial
  | cons tree trees =>
      exact
        ⟨groundTree_variables_false tree,
          groundTrees_variables_false trees⟩

end

/-- Forward functionality makes duplicate-free alpha pairs have
duplicate-free canonical projections. -/
theorem AlphaForwardFunctional.fst_nodup_of_nodup
    {alpha : List (LogicVar × String)}
    (forward : AlphaForwardFunctional alpha)
    (nodup : alpha.Nodup) :
    (alpha.map Prod.fst).Nodup := by
  induction alpha with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headIdentity, headName⟩
      rw [List.nodup_cons] at nodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro identityMember
        rw [List.mem_map] at identityMember
        obtain
          ⟨⟨identity, name⟩, pairMember, identityEq⟩ :=
          identityMember
        simp only at identityEq
        subst identity
        have nameEq : headName = name :=
          forward
            (identity := headIdentity)
            (left := headName) (right := name)
            (by exact List.mem_cons_self)
            (by exact List.mem_cons_of_mem _ pairMember)
        subst name
        exact nodup.1 pairMember
      · apply inductionHypothesis
        · intro identity left right leftMember rightMember
          exact forward
            (identity := identity) (left := left) (right := right)
            (List.mem_cons_of_mem _ leftMember)
            (List.mem_cons_of_mem _ rightMember)
        · exact nodup.2

/-- Exact duplicate removal therefore yields a unique canonical domain. -/
private theorem eraseDups_nodup_pairs :
    ∀ alpha : List (LogicVar × String), alpha.eraseDups.Nodup
  | [] => by
      simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup_pairs
          (tail.filter (fun pair => !pair == head))
termination_by alpha => alpha.length
decreasing_by
  have lengthBound :=
    List.length_filter_le
      (fun pair : LogicVar × String => !pair == head) tail
  simp only [List.length_cons]
  omega

theorem AlphaForwardFunctional.eraseDups_fst_nodup
    {alpha : List (LogicVar × String)}
    (forward : AlphaForwardFunctional alpha) :
    (alpha.eraseDups.map Prod.fst).Nodup := by
  apply AlphaForwardFunctional.fst_nodup_of_nodup
  · intro identity left right leftMember rightMember
    exact forward
      (List.mem_eraseDups.mp leftMember)
      (List.mem_eraseDups.mp rightMember)
  · exact eraseDups_nodup_pairs alpha

/-- Closed canonical image of every alpha-linked variable under an actual
runtime substitution.  Exact duplicate graph pairs are erased; the value is
the structurally grounded decoder image of deep executable substitution. -/
noncomputable def decodedGroundValuation
    (alpha : List (LogicVar × String))
    (runtime : Metta.Subst) : TreeSubstitution :=
  alpha.eraseDups.map fun pair =>
    (pair.1,
      groundTree
        (decodeAlphaAtom alpha
          (PLeaTTa.subst runtime (.var pair.2))))

@[simp] theorem decodedGroundValuation_keys
    (alpha : List (LogicVar × String)) (runtime : Metta.Subst) :
    TreeSubstitution.keys (decodedGroundValuation alpha runtime) =
      alpha.eraseDups.map Prod.fst := by
  simp [decodedGroundValuation, TreeSubstitution.keys, List.map_map]

/-- Every replacement in the decoded valuation is closed by construction. -/
theorem decodedGroundValuation_replacement_closed
    (alpha : List (LogicVar × String)) (runtime : Metta.Subst) :
    ∀ entry, entry ∈ decodedGroundValuation alpha runtime →
      TreeVariablesSatisfy (fun _ => False) entry.2 := by
  intro entry member
  simp only [decodedGroundValuation, List.mem_map] at member
  obtain ⟨pair, _pairMember, rfl⟩ := member
  exact groundTree_variables_false _

/-- A finite substitution with a unique domain and closed replacements is
topological independently of association-list order. -/
theorem TreeSubstitutionTopological.of_closed
    {binding : TreeSubstitution}
    (nodup : (TreeSubstitution.keys binding).Nodup)
    (closed :
      ∀ entry, entry ∈ binding →
        TreeVariablesSatisfy (fun _ => False) entry.2) :
    TreeSubstitutionTopological binding := by
  constructor
  · exact nodup
  · intro entry member
    exact TreeVariablesSatisfy.mono
      (fun identity impossible => False.elim impossible)
      (closed entry member)

/-- The canonical valuation extracted from a runtime result is topological.
This theorem depends only on exact alpha functionality and structural
grounding, not on the runtime result's association-list orientation. -/
theorem decodedGroundValuation_topological
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    (runtime : Metta.Subst) :
    TreeSubstitutionTopological
      (decodedGroundValuation alpha runtime) := by
  apply TreeSubstitutionTopological.of_closed
  · rw [decodedGroundValuation_keys]
    exact
      AlphaForwardFunctional.eraseDups_fst_nodup shared.forward
  · exact decodedGroundValuation_replacement_closed alpha runtime

/-- Applying the extracted canonical valuation to any live alpha identity
returns exactly the grounded decoded runtime image of its executable name. -/
theorem decodedGroundValuation_apply_variable
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    (runtime : Metta.Subst)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha) :
    TreeSubstitution.apply
        (decodedGroundValuation alpha runtime) (.variable identity) =
      groundTree
        (decodeAlphaAtom alpha
          (PLeaTTa.subst runtime (.var name))) := by
  let value :=
    groundTree
      (decodeAlphaAtom alpha
        (PLeaTTa.subst runtime (.var name)))
  have pairMember : (identity, name) ∈ alpha.eraseDups :=
    List.mem_eraseDups.mpr linked
  have member :
      (identity, value) ∈ decodedGroundValuation alpha runtime := by
    apply List.mem_map.mpr
    exact ⟨(identity, name), pairMember, rfl⟩
  have topological :=
    decodedGroundValuation_topological shared runtime
  have valueOutside :
      TreeVariablesSatisfy
        (fun candidate =>
          candidate ∉
            TreeSubstitution.keys
              (decodedGroundValuation alpha runtime))
        value :=
    TreeVariablesSatisfy.mono
      (fun identity impossible => False.elim impossible)
      (groundTree_variables_false _)
  rw [
    topological.apply_variable_eq_apply_value_of_mem member,
    TreeSubstitution.apply_eq_self_of_variables_outside valueOutside]

/-- Source-guided decoding lifts the pointwise closed valuation through every
supported PeTTa term constructor.  The right side uses the actual deep
runtime substitution; no executable association-list spelling is assumed on
the canonical side. -/
theorem decodedGroundValuation_apply_of_reading
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    (runtime : Metta.Subst)
    {tree : Tree} {atom : Atom}
    (reading : CanonicalRuntimeReading alpha tree atom) :
    TreeSubstitution.apply
        (decodedGroundValuation alpha runtime) tree =
      groundTree
        (decodeAlphaAtom alpha (PLeaTTa.subst runtime atom)) := by
  induction reading with
  | «variable» linked =>
      exact
        decodedGroundValuation_apply_variable shared runtime linked
  | atom notLowerTrue notLowerFalse notRuntimeTrue notRuntimeFalse =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | trueAtom =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | falseAtom =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize]
  | integer value =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | float value =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | string value =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround]
  | @partialValue head argumentsTree encodedArguments arguments
      inductionHypothesis =>
      simpa [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize,
        PLeaTTa.PrologGroundIdentity.ofGround,
        partialC, partialTagA, PLeaTTa.subst_expr] using
        inductionHypothesis
  | nil =>
      simp [TreeSubstitution.apply_node, groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
        nilA]
  | @cons headTree tailTree headAtom tailAtom head tail headIH tailIH =>
      simp [TreeSubstitution.apply_node, TreeSubstitution.applyTrees_cons,
        groundTree, groundTrees,
        decodeAlphaAtom, decodeRuntimeAtom, RuntimeShape.ofAtom,
        RuntimeShape.ofAtoms, RuntimeShape.normalize,
        consC, PLeaTTa.subst_expr, headIH, tailIH]

/-! ## Runtime success reflects to one genuine source unifier -/

/-- Comparator-equivalent runtime terms with supported source-guided
readings are unified by the closed canonical valuation extracted from the
same runtime substitution. -/
theorem decodedGroundValuation_unifies_of_equivalent
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    (runtime : Metta.Subst)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (leftReading :
      CanonicalRuntimeReading alpha leftTree leftAtom)
    (rightReading :
      CanonicalRuntimeReading alpha rightTree rightAtom)
    (equivalent :
      PLeaTTa.AtomEquivalentWith PLeaTTa.prologGroundIdentical
        (PLeaTTa.subst runtime leftAtom)
        (PLeaTTa.subst runtime rightAtom)) :
    TreeUnifiesEquations
      (decodedGroundValuation alpha runtime)
      [(leftTree, rightTree)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  rw [
    decodedGroundValuation_apply_of_reading shared runtime leftReading,
    decodedGroundValuation_apply_of_reading shared runtime rightReading]
  exact congrArg groundTree
    (decodeRuntimeAtom_eq_of_equivalent
      (alphaInverse alpha) equivalent)

/-- Any successful executable semantic MGU on supported source-guided
readings therefore supplies an independent ordered canonical MGU.  The
runtime association-list orientation is erased only after its semantic
unifier content has produced a concrete canonical candidate. -/
theorem orderedTreeMgu_exists_of_runtime_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (leftReading :
      CanonicalRuntimeReading alpha leftTree leftAtom)
    (rightReading :
      CanonicalRuntimeReading alpha rightTree rightAtom)
    {runtime : Metta.Subst}
    (runtimeMgu :
      PLeaTTa.RuntimeIsMguWith PLeaTTa.prologGroundIdentical runtime
        [(leftAtom, rightAtom)]) :
    ∃ canonical,
      OrderedTreeMgu [(leftTree, rightTree)] canonical := by
  have equivalent :=
    runtimeMgu.1 (leftAtom, rightAtom) (by simp)
  exact
    OrderedTreeMgu.complete
      (decodedGroundValuation alpha runtime)
      (decodedGroundValuation_unifies_of_equivalent
        shared runtime leftReading rightReading equivalent)

/-- Specialization to source terms: executable MGU success yields an actual
typed source substitution computed by the independent ordered algorithm. -/
theorem computesDenotationalMgu_exists_of_runtime_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {left right : Term} {leftAtom rightAtom : Atom}
    (leftReading :
      CanonicalRuntimeReading alpha (Term.denote left) leftAtom)
    (rightReading :
      CanonicalRuntimeReading alpha (Term.denote right) rightAtom)
    {runtime : Metta.Subst}
    (runtimeMgu :
      PLeaTTa.RuntimeIsMguWith PLeaTTa.prologGroundIdentical runtime
        [(leftAtom, rightAtom)]) :
    ∃ binding, ComputesDenotationalMgu [(left, right)] binding := by
  obtain ⟨canonical, derivation⟩ :=
    orderedTreeMgu_exists_of_runtime_mgu
      shared leftReading rightReading runtimeMgu
  have computed :
      ComputesDenotationalMgu
        [(left, right)] (TreeSubstitution.reify canonical) := by
    exact
      ⟨canonical,
        by simpa [denoteEquations] using derivation,
        rfl⟩
  exact ⟨TreeSubstitution.reify canonical, computed⟩

/-- At the local goal layer, one executable MGU over the already-substituted
operands constructs a genuine `UnifyResolution`; runtime success therefore
cannot coexist with the independent failure premise. -/
theorem unifyResolution_exists_of_runtime_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {current : PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    {left right : Term} {leftAtom rightAtom : Atom}
    (leftReading :
      CanonicalRuntimeReading alpha
        (Term.denote (current.applyTerm left)) leftAtom)
    (rightReading :
      CanonicalRuntimeReading alpha
        (Term.denote (current.applyTerm right)) rightAtom)
    {runtime : Metta.Subst}
    (runtimeMgu :
      PLeaTTa.RuntimeIsMguWith PLeaTTa.prologGroundIdentical runtime
        [(leftAtom, rightAtom)]) :
    ∃ result,
      PeTTaSpec.PrologCore.GoalSemantics.UnifyResolution
        current left right result := by
  obtain ⟨extension, computed⟩ :=
    computesDenotationalMgu_exists_of_runtime_mgu
      shared leftReading rightReading runtimeMgu
  exact
    ⟨extension ++ current,
      ⟨extension, computed, rfl⟩⟩

/-! ## Anti-vacuity at the three reserved encodings -/

private def identityVariable (name : String) : LogicVar := .source name

/-- Runtime boolean normalization is real: the decoder does not preserve the
literal executable spelling. -/
theorem runtime_true_decodes_to_lowercase :
    decodeRuntimeAtom identityVariable (.sym "True") =
        .node (.atom "true") [] ∧
      decodeRuntimeAtom identityVariable (.sym "True") ≠
        .node (.atom "True") [] := by
  simp [decodeRuntimeAtom, RuntimeShape.ofAtom, RuntimeShape.normalize]

/-- The private nil sentinel decodes as the empty-list constructor, while
the forgeable source symbol remains an ordinary atom. -/
theorem runtime_nil_and_source_nil_decode_differently :
    decodeRuntimeAtom identityVariable nilA = .node .nil [] ∧
      decodeRuntimeAtom identityVariable (.sym "#nil") =
        .node (.atom "#nil") [] ∧
      decodeRuntimeAtom identityVariable nilA ≠
        decodeRuntimeAtom identityVariable (.sym "#nil") := by
  simp [decodeRuntimeAtom, RuntimeShape.ofAtom, RuntimeShape.normalize,
    PLeaTTa.PrologGroundIdentity.ofGround, nilA]

/-- The private partial compound decodes as `partial/2`, not as a generic
three-child expression or a proper-list spine. -/
theorem runtime_partial_decodes_as_compound :
    decodeRuntimeAtom identityVariable (partialC "f" nilA) =
      .node (.compound "partial")
        [.node (.atom "f") [], .node .nil []] := by
  simp [decodeRuntimeAtom, RuntimeShape.ofAtom, RuntimeShape.ofAtoms,
    RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
    partialC, partialTagA, nilA]

/-- Broad runtime agreement is insufficient for failure reflection.

Both the literal source atom `True` and the canonical boolean atom `true`
are accepted at the same executable spelling, but their distinct rigid roots
have no canonical unifier.  The strict source-guided reading premise used by
the failure bridge is therefore load-bearing rather than proof decoration. -/
theorem broad_true_alias_is_not_failure_reflecting :
    CanonicalRuntimeAgrees []
        (.node (.atom "True") []) (.sym "True") ∧
      CanonicalRuntimeReading []
        (.node (.atom "true") []) (.sym "True") ∧
      ¬ ∃ binding,
        TreeUnifiesEquations binding
          [(.node (.atom "True") [], .node (.atom "true") [])] := by
  constructor
  · exact literal_runtime_true_is_excluded.1
  constructor
  · exact .trueAtom
  · rintro ⟨binding, unifies⟩
    have clash :=
      unifies
        ((.node (.atom "True") []), (.node (.atom "true") []))
        (by simp)
    simp [TreeSubstitution.apply_node] at clash

end PLeaTTa.PrologRuntimeDecode
