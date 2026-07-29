/-
Module: PLeaTTa.PeTTaSpec.PrologTermAlgebra
Purpose: Canonical first-order denotation for independent Prolog terms.
Trusted boundary: none
Main exports: Tree, Term.denote, TreeSubstitution, DenotationalUnifier
-/
import PLeaTTa.PeTTaSpec.OpenSubstitution

namespace PLeaTTa.PeTTaSpec.PrologCore.Canonical

open OpenSubstitution

/-!
`PrologCore.Term` preserves the reader's convenient proper/dotted-list
presentation.  That presentation is not itself the free first-order term
algebra: after substituting `X = [b]`, the syntax `[a|X]` can contain a nested
list tail even though Prolog observes the canonical list `[a,b]`.

This module gives every source term a canonical tree denotation.  Lists are
expanded to ordinary `[]/0` and `./2` nodes, so unification below this layer
cannot mistake two presentations of the same Prolog term for different
values.  This definition is independent of PLeaTTa's executable `Atom`
encoding and of SWI-Prolog.
-/

/-- Rigid symbols in the canonical first-order signature.  Arity is carried
by the child list; well-formed denotations below always use arity zero for
grounds, the source arity for compounds, and arities zero/two for lists. -/
inductive RigidSymbol where
  | atom (name : String)
  | integer (value : Int)
  | float (value : PLeaTTa.PrologFloatIdentity)
  | string (value : String)
  | compound (functor : String)
  | nil
  | cons
deriving Repr, Inhabited, DecidableEq

/-- Canonical free first-order trees used by the resolver's unification
specification. -/
inductive Tree where
  | variable (identity : LogicVar)
  | node (symbol : RigidSymbol) (children : List Tree)
deriving Repr, Inhabited

/-- Canonical list-cell expansion.  An empty dotted prefix denotes its tail,
and every nonempty prefix becomes a chain of binary cons nodes. -/
def Tree.prologList : List Tree → Option Tree → Tree
  | [], none => .node .nil []
  | [], some tail => tail
  | head :: items, tail =>
      .node .cons [head, Tree.prologList items tail]

mutual

/-- Well-formed canonical trees are precisely those in the image of source
`Term` denotation: grounds have no children, compounds have well-formed
children, and list symbols have arity zero/two. -/
inductive Tree.WellFormed : Tree → Prop where
  | variable (identity : LogicVar) : Tree.WellFormed (.variable identity)
  | atom (name : String) : Tree.WellFormed (.node (.atom name) [])
  | integer (value : Int) : Tree.WellFormed (.node (.integer value) [])
  | float (value : PLeaTTa.PrologFloatIdentity) :
      Tree.WellFormed (.node (.float value) [])
  | string (value : String) : Tree.WellFormed (.node (.string value) [])
  | compound (functor : String) (children : List Tree)
      (formed : Trees.WellFormed children) :
      Tree.WellFormed (.node (.compound functor) children)
  | nil : Tree.WellFormed (.node .nil [])
  | cons (head tail : Tree) (headFormed : Tree.WellFormed head)
      (tailFormed : Tree.WellFormed tail) :
      Tree.WellFormed (.node .cons [head, tail])

/-- Ordered well-formed canonical children. -/
inductive Trees.WellFormed : List Tree → Prop where
  | nil : Trees.WellFormed []
  | cons (tree : Tree) (trees : List Tree)
      (head : Tree.WellFormed tree) (tail : Trees.WellFormed trees) :
      Trees.WellFormed (tree :: trees)

end

mutual

/-- Canonical reification.  Malformed rigid arities map to a distinguished
source atom; the round-trip theorem below is intentionally conditioned on
`Tree.WellFormed`, so this fallback can never launder malformed syntax. -/
def Tree.reify : Tree → Term
  | .variable identity => .variable identity
  | .node (.atom name) _ => .atom name
  | .node (.integer value) _ => .integer value
  | .node (.float value) _ => .float value
  | .node (.string value) _ => .string value
  | .node (.compound functor) children =>
      .compound functor (Trees.reify children)
  | .node .nil _ => .list [] none
  | .node .cons [head, tail] => Term.prepend (Tree.reify head) (Tree.reify tail)
  | .node .cons _ => .atom "$malformed-cons"

/-- Ordered reification of canonical children. -/
def Trees.reify : List Tree → List Term
  | [] => []
  | tree :: trees => Tree.reify tree :: Trees.reify trees

end

mutual

/-- Canonical denotation of one independent Prolog term. -/
def Term.denote : Term → Tree
  | .variable identity => .variable identity
  | .atom name => .node (.atom name) []
  | .integer value => .node (.integer value) []
  | .float value => .node (.float value) []
  | .string value => .node (.string value) []
  | .compound functor arguments =>
      .node (.compound functor) (Terms.denote arguments)
  | .list items none => Tree.prologList (Terms.denote items) none
  | .list items (some tail) =>
      Tree.prologList (Terms.denote items) (some (Term.denote tail))

/-- Ordered denotation of independent terms. -/
def Terms.denote : List Term → List Tree
  | [] => []
  | term :: terms => Term.denote term :: Terms.denote terms

end

/-- Source list prepending denotes one canonical cons cell regardless of
whether the source tail was already represented as a list. -/
theorem Term.denote_prepend (head tail : Term) :
    Term.denote (Term.prepend head tail) =
      .node .cons [Term.denote head, Term.denote tail] := by
  cases tail with
  | list items finalTail => cases finalTail <;> rfl
  | _ => rfl

/-- Well-formedness predicate for an optional dotted-list tail. -/
def OptionalTreeWellFormed : Option Tree → Prop
  | none => True
  | some tail => tail.WellFormed

/-- Canonical list construction preserves well-formedness. -/
theorem Tree.prologList_wellFormed {items : List Tree} {tail : Option Tree}
    (itemsFormed : Trees.WellFormed items)
    (tailFormed : OptionalTreeWellFormed tail) :
    (Tree.prologList items tail).WellFormed := by
  induction items generalizing tail with
  | nil =>
      cases tail with
      | none => exact .nil
      | some finalTail => exact tailFormed
  | cons head items induction =>
      cases itemsFormed with
      | cons _ _ headFormed tailItems =>
          exact .cons head (Tree.prologList items tail) headFormed
            (induction tailItems tailFormed)

mutual

/-- Every independent source term denotes a well-formed canonical tree. -/
theorem Term.denote_wellFormed : (term : Term) →
    (Term.denote term).WellFormed
  | .variable identity => .variable identity
  | .atom name => .atom name
  | .integer value => .integer value
  | .float value => .float value
  | .string value => .string value
  | .compound functor arguments =>
      .compound functor (Terms.denote arguments)
        (Terms.denote_wellFormed arguments)
  | .list items none =>
      Tree.prologList_wellFormed (Terms.denote_wellFormed items) trivial
  | .list items (some tail) =>
      Tree.prologList_wellFormed (Terms.denote_wellFormed items)
        (Term.denote_wellFormed tail)

/-- Ordered source terms denote well-formed canonical children. -/
theorem Terms.denote_wellFormed : (terms : List Term) →
    Trees.WellFormed (Terms.denote terms)
  | [] => .nil
  | term :: terms => .cons (Term.denote term) (Terms.denote terms)
      (Term.denote_wellFormed term) (Terms.denote_wellFormed terms)

end

/-- Reifying a well-formed canonical tree and denoting it again is exact. -/
theorem Tree.denote_reify {tree : Tree} (formed : tree.WellFormed) :
    Term.denote (Tree.reify tree) = tree := by
  exact Tree.WellFormed.rec
    (motive_1 := fun tree _ => Term.denote (Tree.reify tree) = tree)
    (motive_2 := fun trees _ => Terms.denote (Trees.reify trees) = trees)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ childrenRoundTrip => by
      simp only [Tree.reify, Term.denote, childrenRoundTrip])
    rfl
    (fun head tail _ _ headRoundTrip tailRoundTrip => by
      simp only [Tree.reify]
      rw [Term.denote_prepend, headRoundTrip, tailRoundTrip])
    rfl
    (fun _ _ _ _ headRoundTrip tailRoundTrip => by
      simp only [Trees.reify, Terms.denote, headRoundTrip, tailRoundTrip])
    formed

/-- Ordered round-trip companion. -/
theorem Trees.denote_reify {trees : List Tree}
    (formed : Trees.WellFormed trees) :
    Terms.denote (Trees.reify trees) = trees := by
  exact Trees.WellFormed.rec
    (motive_1 := fun tree _ => Term.denote (Tree.reify tree) = tree)
    (motive_2 := fun trees _ => Terms.denote (Trees.reify trees) = trees)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ childrenRoundTrip => by
      simp only [Tree.reify, Term.denote, childrenRoundTrip])
    rfl
    (fun head tail _ _ headRoundTrip tailRoundTrip => by
      simp only [Tree.reify]
      rw [Term.denote_prepend, headRoundTrip, tailRoundTrip])
    rfl
    (fun _ _ _ _ headRoundTrip tailRoundTrip => by
      simp only [Trees.reify, Terms.denote, headRoundTrip, tailRoundTrip])
    formed

/-- Every well-formed rigid node has well-formed ordered children. -/
theorem Tree.WellFormed.children {symbol : RigidSymbol}
    {children : List Tree} (formed : Tree.WellFormed (.node symbol children)) :
    Trees.WellFormed children := by
  cases formed with
  | atom | integer | float | string | nil => exact .nil
  | compound _ _ childrenFormed => exact childrenFormed
  | cons head tail headFormed tailFormed =>
      exact .cons head [tail] headFormed
        (.cons tail [] tailFormed .nil)

theorem Trees.WellFormed.head {tree : Tree} {trees : List Tree}
    (formed : Trees.WellFormed (tree :: trees)) : tree.WellFormed := by
  cases formed
  assumption

theorem Trees.WellFormed.tail {tree : Tree} {trees : List Tree}
    (formed : Trees.WellFormed (tree :: trees)) :
    Trees.WellFormed trees := by
  cases formed
  assumption

mutual

/-- Capture-free replacement in one canonical tree. -/
def Tree.instantiateOne (source : LogicVar) (replacement : Tree) :
    Tree → Tree
  | .variable identity =>
      if identity = source then replacement else .variable identity
  | .node symbol children =>
      .node symbol (Trees.instantiateOne source replacement children)

/-- Ordered replacement in canonical tree children. -/
def Trees.instantiateOne (source : LogicVar) (replacement : Tree) :
    List Tree → List Tree
  | [] => []
  | tree :: trees =>
      Tree.instantiateOne source replacement tree ::
        Trees.instantiateOne source replacement trees

end

/-- Tree replacement commutes with canonical list-cell expansion. -/
theorem Tree.instantiateOne_prologList (source : LogicVar)
    (replacement : Tree) (items : List Tree) (tail : Option Tree) :
    Tree.instantiateOne source replacement (Tree.prologList items tail) =
      Tree.prologList (Trees.instantiateOne source replacement items)
        (tail.map (Tree.instantiateOne source replacement)) := by
  induction items with
  | nil => cases tail <;> rfl
  | cons head items induction =>
      simp only [Tree.prologList, Tree.instantiateOne,
        Trees.instantiateOne]
      rw [induction]

mutual

/-- Boolean occurrence in the canonical first-order algebra. -/
def Tree.occurs (identity : LogicVar) : Tree → Bool
  | .variable candidate => decide (candidate = identity)
  | .node _ children => Trees.occurs identity children

/-- Ordered occurrence in canonical children. -/
def Trees.occurs (identity : LogicVar) : List Tree → Bool
  | [] => false
  | tree :: trees =>
      Tree.occurs identity tree || Trees.occurs identity trees

end

mutual

/-- Structural weight of a finite canonical tree.  Variables and rigid roots
both contribute one; child weights are added in source order. -/
def Tree.weight : Tree → Nat
  | .variable _ => 1
  | .node _ children => 1 + Trees.weight children

/-- Additive structural weight of ordered children. -/
def Trees.weight : List Tree → Nat
  | [] => 0
  | tree :: trees => Tree.weight tree + Trees.weight trees

end

@[simp] theorem Tree.weight_positive (tree : Tree) :
    0 < tree.weight := by
  cases tree <;> simp only [Tree.weight] <;> omega

mutual

/-- Replacing an absent variable leaves a canonical tree unchanged. -/
theorem Tree.instantiateOne_eq_self_of_occurs_false
    (source : LogicVar) (replacement : Tree) :
    (tree : Tree) → Tree.occurs source tree = false →
      Tree.instantiateOne source replacement tree = tree
  | .variable identity, absent => by
      simp only [Tree.occurs, decide_eq_false_iff_not] at absent
      simp [Tree.instantiateOne, absent]
  | .node symbol children, absent => by
      simp only [Tree.occurs] at absent
      simp only [Tree.instantiateOne, Tree.node.injEq, true_and]
      exact Trees.instantiateOne_eq_self_of_occurs_false source replacement
        children absent

/-- Ordered companion to absence-preserving replacement. -/
theorem Trees.instantiateOne_eq_self_of_occurs_false
    (source : LogicVar) (replacement : Tree) :
    (trees : List Tree) → Trees.occurs source trees = false →
      Trees.instantiateOne source replacement trees = trees
  | [], _ => rfl
  | tree :: trees, absent => by
      simp only [Trees.occurs, Bool.or_eq_false_iff] at absent
      simp only [Trees.instantiateOne, List.cons.injEq]
      exact ⟨Tree.instantiateOne_eq_self_of_occurs_false source replacement
          tree absent.1,
        Trees.instantiateOne_eq_self_of_occurs_false source replacement
          trees absent.2⟩

end

/-- Finite substitutions over canonical trees. -/
abbrev TreeSubstitution := List (LogicVar × Tree)

namespace TreeSubstitution

mutual

/-- Sequential application, with newer extensions at the list head, matching
`OpenSubstitution.Substitution.applyTerm`. -/
def apply : TreeSubstitution → Tree → Tree
  | [], tree => tree
  | (source, replacement) :: bindings, tree =>
      Tree.instantiateOne source replacement (apply bindings tree)

/-- Ordered application to canonical tree children. -/
def applyTrees : TreeSubstitution → List Tree → List Tree
  | [], trees => trees
  | (source, replacement) :: bindings, trees =>
      Trees.instantiateOne source replacement (applyTrees bindings trees)

end

@[simp] theorem apply_node (bindings : TreeSubstitution)
    (symbol : RigidSymbol) (children : List Tree) :
    apply bindings (.node symbol children) =
      .node symbol (applyTrees bindings children) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [apply, applyTrees, induction, Tree.instantiateOne]

@[simp] theorem applyTrees_cons (bindings : TreeSubstitution)
    (tree : Tree) (trees : List Tree) :
    applyTrees bindings (tree :: trees) =
      apply bindings tree :: applyTrees bindings trees := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [apply, applyTrees, induction, Trees.instantiateOne]

@[simp] theorem applyTrees_nil (bindings : TreeSubstitution) :
    applyTrees bindings [] = [] := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [applyTrees, induction, Trees.instantiateOne]

/-- Prepending an extension applies the older state first and then the new
extension. -/
theorem apply_append (extension bindings : TreeSubstitution) (tree : Tree) :
    apply (extension ++ bindings) tree =
      apply extension (apply bindings tree) := by
  induction extension with
  | nil => rfl
  | cons binding extension induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [List.cons_append, apply, induction]

mutual

/-- Any substitution that identifies one variable and one replacement absorbs
that replacement throughout every larger canonical tree. -/
theorem apply_instantiateOne_of_unifier (bindings : TreeSubstitution)
    (source : LogicVar) (replacement : Tree)
    (identifies : apply bindings (.variable source) =
      apply bindings replacement) :
    (tree : Tree) →
      apply bindings (Tree.instantiateOne source replacement tree) =
        apply bindings tree
  | .variable identity => by
      by_cases same : identity = source
      · subst identity
        simpa [Tree.instantiateOne] using identifies.symm
      · simp [Tree.instantiateOne, same]
  | .node symbol children => by
      simp only [Tree.instantiateOne, apply_node, Tree.node.injEq, true_and]
      exact applyTrees_instantiateOne_of_unifier bindings source replacement
        identifies children

/-- Ordered companion to substitution absorption. -/
theorem applyTrees_instantiateOne_of_unifier
    (bindings : TreeSubstitution) (source : LogicVar) (replacement : Tree)
    (identifies : apply bindings (.variable source) =
      apply bindings replacement) :
    (trees : List Tree) →
      applyTrees bindings
          (Trees.instantiateOne source replacement trees) =
        applyTrees bindings trees
  | [] => rfl
  | tree :: trees => by
      simp only [Trees.instantiateOne, applyTrees_cons, List.cons.injEq]
      exact ⟨apply_instantiateOne_of_unifier bindings source replacement
          identifies tree,
        applyTrees_instantiateOne_of_unifier bindings source replacement
          identifies trees⟩

end

end TreeSubstitution

/-!
The occurs check is semantically necessary for finite trees, not merely an
algorithmic convention.  The following mutually recursive bounds show that
if `X` occurs in `t`, then every finite substitution leaves the image of `X`
no larger than the image of `t`.  At a proper occurrence under a rigid node,
the inequality is strict, ruling out a finite solution of `X = t`.
-/

mutual

theorem Tree.apply_variable_weight_le_of_occurs_true
    (bindings : TreeSubstitution) (source : LogicVar) :
    (tree : Tree) → Tree.occurs source tree = true →
      Tree.weight (TreeSubstitution.apply bindings (.variable source)) ≤
        Tree.weight (TreeSubstitution.apply bindings tree)
  | .variable identity, present => by
      simp only [Tree.occurs, decide_eq_true_eq] at present
      subst identity
      exact Nat.le_refl _
  | .node symbol children, present => by
      have childBound :=
        Trees.apply_variable_weight_le_of_occurs_true bindings source
          children present
      simp only [TreeSubstitution.apply_node, Tree.weight]
      omega

theorem Trees.apply_variable_weight_le_of_occurs_true
    (bindings : TreeSubstitution) (source : LogicVar) :
    (trees : List Tree) → Trees.occurs source trees = true →
      Tree.weight (TreeSubstitution.apply bindings (.variable source)) ≤
        Trees.weight (TreeSubstitution.applyTrees bindings trees)
  | [], present => by simp [Trees.occurs] at present
  | tree :: trees, present => by
      simp only [Trees.occurs, Bool.or_eq_true] at present
      simp only [TreeSubstitution.applyTrees_cons, Trees.weight]
      rcases present with headPresent | tailPresent
      · have headBound :=
          Tree.apply_variable_weight_le_of_occurs_true bindings source tree
            headPresent
        omega
      · have tailBound :=
          Trees.apply_variable_weight_le_of_occurs_true bindings source
            trees tailPresent
        omega

end


/-- A proper finite occurrence makes the substituted right side strictly
larger than the substituted variable under every finite substitution. -/
theorem Tree.apply_variable_weight_lt_of_occurs_true_of_ne
    (bindings : TreeSubstitution) (source : LogicVar) :
    (tree : Tree) → Tree.occurs source tree = true →
      tree ≠ .variable source →
      Tree.weight (TreeSubstitution.apply bindings (.variable source)) <
        Tree.weight (TreeSubstitution.apply bindings tree)
  | .variable identity, present, different => by
      simp only [Tree.occurs, decide_eq_true_eq] at present
      subst identity
      exact False.elim (different rfl)
  | .node symbol children, present, _ => by
      have childBound :=
        Trees.apply_variable_weight_le_of_occurs_true bindings source
          children present
      simp only [TreeSubstitution.apply_node, Tree.weight]
      omega

/-- Finite first-order trees have no cyclic unifier. -/
theorem Tree.no_finite_unifier_of_occurs_true
    (bindings : TreeSubstitution) (source : LogicVar) (tree : Tree)
    (present : Tree.occurs source tree = true)
    (different : tree ≠ .variable source) :
    TreeSubstitution.apply bindings (.variable source) ≠
      TreeSubstitution.apply bindings tree := by
  intro equality
  have strict := Tree.apply_variable_weight_lt_of_occurs_true_of_ne
    bindings source tree present different
  rw [equality] at strict
  exact (Nat.lt_irrefl _ strict)

/-! ### Reifiable substitutions and closure of well-formed trees -/

/-- Every replacement carried by a canonical substitution is well formed. -/
def TreeSubstitution.WellFormed (bindings : TreeSubstitution) : Prop :=
  ∀ entry, entry ∈ bindings → entry.2.WellFormed

theorem TreeSubstitution.wellFormed_nil :
    TreeSubstitution.WellFormed [] := by
  intro entry member
  simp at member

theorem TreeSubstitution.WellFormed.singleton (source : LogicVar)
    {replacement : Tree} (formed : replacement.WellFormed) :
    TreeSubstitution.WellFormed [(source, replacement)] := by
  intro entry member
  simp only [List.mem_singleton] at member
  subst entry
  exact formed

theorem TreeSubstitution.WellFormed.append
    {extension bindings : TreeSubstitution}
    (extensionFormed : extension.WellFormed)
    (bindingsFormed : bindings.WellFormed) :
    (extension ++ bindings).WellFormed := by
  intro entry member
  rcases List.mem_append.mp member with left | right
  · exact extensionFormed entry left
  · exact bindingsFormed entry right

/-- Canonical substitutions reify pointwise to source substitutions. -/
def TreeSubstitution.reify : TreeSubstitution →
    OpenSubstitution.Substitution
  | [] => []
  | (source, replacement) :: bindings =>
      (source, Tree.reify replacement) :: TreeSubstitution.reify bindings

theorem TreeSubstitution.WellFormed.tail
    {entry : LogicVar × Tree} {bindings : TreeSubstitution}
    (formed : TreeSubstitution.WellFormed (entry :: bindings)) :
    TreeSubstitution.WellFormed bindings := by
  intro candidate member
  exact formed candidate (by simp [member])

theorem TreeSubstitution.WellFormed.head
    {entry : LogicVar × Tree} {bindings : TreeSubstitution}
    (formed : TreeSubstitution.WellFormed (entry :: bindings)) :
    entry.2.WellFormed :=
  formed entry (by simp)

/-- One replacement preserves canonical well-formedness. -/
theorem Tree.instantiateOne_wellFormed (source : LogicVar)
    {replacement : Tree} (replacementFormed : replacement.WellFormed)
    {tree : Tree} (formed : tree.WellFormed) :
    (Tree.instantiateOne source replacement tree).WellFormed := by
  exact Tree.WellFormed.rec
    (motive_1 := fun tree _ =>
      (Tree.instantiateOne source replacement tree).WellFormed)
    (motive_2 := fun trees _ =>
      Trees.WellFormed (Trees.instantiateOne source replacement trees))
    (fun identity => by
      by_cases same : identity = source
      · simpa [Tree.instantiateOne, same] using replacementFormed
      · simpa [Tree.instantiateOne, same] using
          (Tree.WellFormed.variable identity))
    (fun name => .atom name)
    (fun value => .integer value)
    (fun value => .float value)
    (fun value => .string value)
    (fun functor _ _ childrenFormed => .compound functor _ childrenFormed)
    .nil
    (fun head tail _ _ headFormed tailFormed =>
      .cons _ _ headFormed tailFormed)
    .nil
    (fun tree trees _ _ headFormed tailFormed =>
      .cons _ _ headFormed tailFormed)
    formed

/-- Ordered companion to replacement closure. -/
theorem Trees.instantiateOne_wellFormed (source : LogicVar)
    {replacement : Tree} (replacementFormed : replacement.WellFormed)
    {trees : List Tree} (formed : Trees.WellFormed trees) :
    Trees.WellFormed
      (Trees.instantiateOne source replacement trees) := by
  exact Trees.WellFormed.rec
    (motive_1 := fun tree _ =>
      (Tree.instantiateOne source replacement tree).WellFormed)
    (motive_2 := fun trees _ =>
      Trees.WellFormed (Trees.instantiateOne source replacement trees))
    (fun identity => by
      by_cases same : identity = source
      · simpa [Tree.instantiateOne, same] using replacementFormed
      · simpa [Tree.instantiateOne, same] using
          (Tree.WellFormed.variable identity))
    (fun name => .atom name)
    (fun value => .integer value)
    (fun value => .float value)
    (fun value => .string value)
    (fun functor _ _ childrenFormed => .compound functor _ childrenFormed)
    .nil
    (fun head tail _ _ headFormed tailFormed =>
      .cons _ _ headFormed tailFormed)
    .nil
    (fun tree trees _ _ headFormed tailFormed =>
      .cons _ _ headFormed tailFormed)
    formed

/-- Applying a well-formed substitution to a well-formed tree stays inside
the source-reifiable algebra. -/
theorem TreeSubstitution.apply_wellFormed {bindings : TreeSubstitution}
    (bindingsFormed : bindings.WellFormed) {tree : Tree}
    (treeFormed : tree.WellFormed) :
    (TreeSubstitution.apply bindings tree).WellFormed := by
  induction bindings with
  | nil => exact treeFormed
  | cons entry bindings induction =>
      rcases entry with ⟨source, replacement⟩
      exact Tree.instantiateOne_wellFormed source bindingsFormed.head
        (induction bindingsFormed.tail)

/-- Ordered application closure. -/
theorem TreeSubstitution.applyTrees_wellFormed
    {bindings : TreeSubstitution} (bindingsFormed : bindings.WellFormed)
    {trees : List Tree} (treesFormed : Trees.WellFormed trees) :
    Trees.WellFormed (TreeSubstitution.applyTrees bindings trees) := by
  induction bindings with
  | nil => exact treesFormed
  | cons entry bindings induction =>
      rcases entry with ⟨source, replacement⟩
      exact Trees.instantiateOne_wellFormed source bindingsFormed.head
        (induction bindingsFormed.tail)

/-- Denote every replacement in an independent finite substitution. -/
def Substitution.denote : OpenSubstitution.Substitution → TreeSubstitution
  | [] => []
  | (source, replacement) :: bindings =>
      (source, Term.denote replacement) :: Substitution.denote bindings

theorem Substitution.denote_append
    (extension bindings : OpenSubstitution.Substitution) :
    Substitution.denote (extension ++ bindings) =
      Substitution.denote extension ++ Substitution.denote bindings := by
  induction extension with
  | nil => rfl
  | cons binding extension induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [List.cons_append, Substitution.denote, induction]

/-- Reification is a right inverse on well-formed canonical substitutions. -/
theorem TreeSubstitution.denote_reify {bindings : TreeSubstitution}
    (formed : bindings.WellFormed) :
    Substitution.denote (TreeSubstitution.reify bindings) = bindings := by
  induction bindings with
  | nil => rfl
  | cons entry bindings induction =>
      rcases entry with ⟨source, replacement⟩
      simp only [TreeSubstitution.reify, Substitution.denote,
        List.cons.injEq]
      constructor
      · exact Prod.ext rfl (Tree.denote_reify formed.head)
      · exact induction formed.tail

mutual

/-- Canonical denotation commutes with one capture-free source-term
replacement. -/
theorem Term.denote_instantiateOne (source : LogicVar) (replacement : Term) :
    (term : Term) →
    Term.denote
        (OpenSubstitution.Term.instantiateOne source replacement term) =
      Tree.instantiateOne source (Term.denote replacement)
        (Term.denote term)
  | .variable identity => by
      by_cases same : identity = source <;>
        simp [OpenSubstitution.Term.instantiateOne, Term.denote,
          Tree.instantiateOne, same]
  | .atom _ => rfl
  | .integer _ => rfl
  | .float _ => rfl
  | .string _ => rfl
  | .compound functor arguments => by
      simp only [OpenSubstitution.Term.instantiateOne, Term.denote,
        Tree.instantiateOne]
      rw [Terms.denote_instantiateOne]
  | .list items none => by
      simp only [OpenSubstitution.Term.instantiateOne, Term.denote]
      rw [Tree.instantiateOne_prologList, Terms.denote_instantiateOne]
      rfl
  | .list items (some tail) => by
      simp only [OpenSubstitution.Term.instantiateOne, Term.denote]
      rw [Tree.instantiateOne_prologList, Terms.denote_instantiateOne,
        Term.denote_instantiateOne]
      rfl

/-- Ordered companion to `Term.denote_instantiateOne`. -/
theorem Terms.denote_instantiateOne (source : LogicVar)
    (replacement : Term) : (terms : List Term) →
    Terms.denote
        (OpenSubstitution.Terms.instantiateOne source replacement terms) =
      Trees.instantiateOne source (Term.denote replacement)
        (Terms.denote terms)
  | [] => rfl
  | term :: terms => by
      simp only [OpenSubstitution.Terms.instantiateOne, Terms.denote,
        Trees.instantiateOne]
      rw [Term.denote_instantiateOne, Terms.denote_instantiateOne]

end


/-- Applying a finite source substitution and then denoting is exactly the
same as denoting the substitution and applying it in the canonical algebra.
This is the bridge needed to use canonical MGU results in source goals. -/
theorem Substitution.denote_applyTerm
    (bindings : OpenSubstitution.Substitution) (term : Term) :
    Term.denote (OpenSubstitution.Substitution.applyTerm bindings term) =
      TreeSubstitution.apply (Substitution.denote bindings)
        (Term.denote term) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [OpenSubstitution.Substitution.applyTerm,
        Substitution.denote, TreeSubstitution.apply]
      rw [Term.denote_instantiateOne, induction]

/-! ### The representation bug this layer prevents -/

def dottedListWitness : Term :=
  .list [.atom "a"] (some (.variable (.source "X")))

def properListReplacement : Term := .list [.atom "b"] none

def properListExpected : Term := .list [.atom "a", .atom "b"] none

/-- Raw syntax substitution does not flatten a substituted proper-list tail.
This is why raw `Term` equality is not an adequate definition of Prolog
unification for lists. -/
theorem raw_substitution_is_not_canonical :
    OpenSubstitution.Substitution.applyTerm
        [(.source "X", properListReplacement)] dottedListWitness ≠
      properListExpected := by
  simp [dottedListWitness, properListReplacement, properListExpected,
    OpenSubstitution.Substitution.applyTerm, Term.instantiateOne]

/-- Canonical denotation identifies the same substitution witness exactly as
Prolog does: `[a|X], X=[b]` denotes `[a,b]`. -/
theorem denotation_closes_proper_list_tail :
    Term.denote (OpenSubstitution.Substitution.applyTerm
        [(.source "X", properListReplacement)] dottedListWitness) =
      Term.denote properListExpected := by
  rfl

/-- A finite source substitution unifies two terms when their canonical
first-order denotations agree. -/
def DenotationalUnifier (binding : OpenSubstitution.Substitution)
    (left right : Term) : Prop :=
  TreeSubstitution.apply (Substitution.denote binding) (Term.denote left) =
    TreeSubstitution.apply (Substitution.denote binding) (Term.denote right)

/-- Pointwise canonical unification of an ordered equation sequence. -/
def DenotationalUnifiesEquations
    (binding : OpenSubstitution.Substitution)
    (equations : List (Term × Term)) : Prop :=
  ∀ equation, equation ∈ equations →
    DenotationalUnifier binding equation.1 equation.2

/-- `specific` factors through `general` in the canonical term algebra.  The
residual is allowed to be a canonical-tree substitution because factorization
is a semantic property, not a promise that every residual spelling came from
reader syntax. -/
def DenotationalFactorsThrough
    (specific general : OpenSubstitution.Substitution) : Prop :=
  ∃ residual : TreeSubstitution, ∀ tree,
    TreeSubstitution.apply (Substitution.denote specific) tree =
      TreeSubstitution.apply residual
        (TreeSubstitution.apply (Substitution.denote general) tree)

/-- Most-general unifier in canonical Prolog term semantics. -/
def IsDenotationalMgu (binding : OpenSubstitution.Substitution)
    (equations : List (Term × Term)) : Prop :=
  DenotationalUnifiesEquations binding equations ∧
    ∀ candidate, DenotationalUnifiesEquations candidate equations →
      DenotationalFactorsThrough candidate binding

/-- Two ordered equation collections have exactly the same canonical
unifiers. -/
def SameDenotationalUnifiers (left right : List (Term × Term)) : Prop :=
  ∀ binding, DenotationalUnifiesEquations binding left ↔
    DenotationalUnifiesEquations binding right

/-- Canonical MGU status transports across extensional equality of unifier
sets. -/
theorem IsDenotationalMgu.transport
    {binding : OpenSubstitution.Substitution}
    {left right : List (Term × Term)}
    (mostGeneral : IsDenotationalMgu binding left)
    (same : SameDenotationalUnifiers left right) :
    IsDenotationalMgu binding right := by
  constructor
  · exact (same binding).mp mostGeneral.1
  · intro candidate candidateUnifies
    exact mostGeneral.2 candidate ((same candidate).mpr candidateUnifies)

/-- Reversing one equation preserves its complete canonical unifier set. -/
theorem singleEquation_symm_same_denotational_unifiers (left right : Term) :
    SameDenotationalUnifiers [(left, right)] [(right, left)] := by
  intro binding
  constructor <;> intro unifies equation member
  · simp only [List.mem_singleton] at member
    subst equation
    have forward := unifies (left, right) (by simp)
    exact forward.symm
  · simp only [List.mem_singleton] at member
    subst equation
    have backward := unifies (right, left) (by simp)
    exact backward.symm

/-- Eliminating one absent variable is an MGU in canonical Prolog semantics.
Unlike the older syntactic theorem, this statement remains valid when the
replacement is a proper list used as the tail of a dotted list. -/
theorem singleton_variable_is_denotational_mgu
    (source : LogicVar) (value : Term)
    (absent : Tree.occurs source (Term.denote value) = false) :
    IsDenotationalMgu [(source, value)] [(.variable source, value)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    unfold DenotationalUnifier
    simp only [Substitution.denote, TreeSubstitution.apply,
      Term.denote, Tree.instantiateOne, ite_true]
    exact (Tree.instantiateOne_eq_self_of_occurs_false source
      (Term.denote value) (Term.denote value) absent).symm
  · intro candidate candidateUnifies
    have identifies :
        TreeSubstitution.apply (Substitution.denote candidate)
            (.variable source) =
          TreeSubstitution.apply (Substitution.denote candidate)
            (Term.denote value) := by
      exact candidateUnifies (.variable source, value) (by simp)
    refine ⟨Substitution.denote candidate, ?_⟩
    intro tree
    change TreeSubstitution.apply (Substitution.denote candidate) tree =
      TreeSubstitution.apply (Substitution.denote candidate)
        (Tree.instantiateOne source (Term.denote value) tree)
    exact (TreeSubstitution.apply_instantiateOne_of_unifier
      (Substitution.denote candidate) source (Term.denote value)
      identifies tree).symm

/-- Distinct rigid atoms have no canonical unifier. -/
theorem distinct_atoms_have_no_denotational_unifier (left right : String)
    (different : left ≠ right) :
    ¬ ∃ binding, DenotationalUnifier binding (.atom left) (.atom right) := by
  rintro ⟨binding, unifies⟩
  unfold DenotationalUnifier at unifies
  simp only [Term.denote, TreeSubstitution.apply_node] at unifies
  injection unifies with symbols
  exact different (RigidSymbol.atom.inj symbols)

end PLeaTTa.PeTTaSpec.PrologCore.Canonical
