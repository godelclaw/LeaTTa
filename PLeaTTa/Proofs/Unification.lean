-- SPDX-License-Identifier: Apache-2.0

/-
Proof-facing invariants for the actual first-order unifier used by PLeaTTa.
The central invariant is elimination order: a recorded target contains no
previously eliminated variable, so every dependency that is eventually bound
appears earlier in the final substitution order.
-/
import PLeaTTa.Machine
import MettaHyperonFull.Proofs.Basic

namespace PLeaTTa

open Metta (Atom Ground Subst)

def AtomAvoids (b : Subst) (a : Atom) : Prop :=
  ∀ name, name ∈ a.vars → Metta.Subst.lookup b name = none

private def ConstraintAvoids (b : Subst) (constraint : String × Atom) : Prop :=
  Metta.Subst.lookup b constraint.1 = none ∧ AtomAvoids b constraint.2

private def ConstraintsAvoid (b : Subst)
    (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints → ConstraintAvoids b constraint

private theorem constraintsAvoid_nil (b : Subst) :
    ConstraintsAvoid b [] := by
  simp [ConstraintsAvoid]

private theorem constraintsAvoid_singleton (b : Subst) (name : String)
    (value : Atom) (hname : Metta.Subst.lookup b name = none)
    (hvalue : AtomAvoids b value) :
    ConstraintsAvoid b [(name, value)] := by
  simpa [ConstraintsAvoid, ConstraintAvoids] using And.intro hname hvalue

private theorem ConstraintsAvoid.append (b : Subst)
    (left right : List (String × Atom))
    (hleft : ConstraintsAvoid b left) (hright : ConstraintsAvoid b right) :
    ConstraintsAvoid b (left ++ right) := by
  intro constraint hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft constraint hmem
  · exact hright constraint hmem

private theorem atomAvoids_expr_iff (b : Subst) (atoms : List Atom) :
    AtomAvoids b (Atom.expr atoms) ↔
      ∀ child ∈ atoms, AtomAvoids b child := by
  constructor
  · intro h child hchild name hname
    apply h name
    simp only [Atom.vars]
    rw [List.mem_flatten]
    exact ⟨child.vars, List.mem_map_of_mem hchild, hname⟩
  · intro h name hname
    simp only [Atom.vars] at hname
    rw [List.mem_flatten] at hname
    rcases hname with ⟨variableList, hvariableList, hname⟩
    rcases List.mem_map.mp hvariableList with ⟨child, hchild, rfl⟩
    exact h child hchild name hname

mutual

private theorem decomposeEqWith_avoids (groundEq : Ground → Ground → Bool)
    (b : Subst) (left right : Atom)
    (constraints : List (String × Atom))
    (hleft : AtomAvoids b left) (hright : AtomAvoids b right)
    (hdecompose :
      Metta.Unify.decomposeEqWith groundEq left right = some constraints) :
    ConstraintsAvoid b constraints := by
  cases left with
  | sym leftName =>
      cases right with
      | sym rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          · cases hdecompose
            exact constraintsAvoid_nil b
          · contradiction
      | var name =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hright name (by simp [Atom.vars])
          · simp [AtomAvoids, Atom.vars]
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | var name =>
      cases right with
      | sym rightName =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hleft name (by simp [Atom.vars])
          · simp [AtomAvoids, Atom.vars]
      | var rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          by_cases heq : name = rightName
          · have hbeq : (name == rightName) = true := by simp [heq]
            rw [hbeq] at hdecompose
            cases hdecompose
            exact constraintsAvoid_nil b
          · have hbeq : (name == rightName) = false := by simp [heq]
            rw [hbeq] at hdecompose
            cases hdecompose
            apply constraintsAvoid_singleton
            · exact hleft name (by simp [Atom.vars])
            · intro dependency hdependency
              simpa [Atom.vars] using
                hright dependency hdependency
      | gnd ground =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hleft name (by simp [Atom.vars])
          · simp [AtomAvoids, Atom.vars]
      | expr atoms =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hleft name (by simp [Atom.vars])
          · exact hright
  | gnd leftGround =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hright name (by simp [Atom.vars])
          · simp [AtomAvoids, Atom.vars]
      | gnd rightGround =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          · cases hdecompose
            exact constraintsAvoid_nil b
          · contradiction
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | expr leftAtoms =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          apply constraintsAvoid_singleton
          · exact hright name (by simp [Atom.vars])
          · exact hleft
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr rightAtoms =>
          exact decomposeListWith_avoids groundEq b leftAtoms rightAtoms
            constraints
            (atomAvoids_expr_iff b leftAtoms |>.mp hleft)
            (atomAvoids_expr_iff b rightAtoms |>.mp hright) hdecompose

private theorem decomposeListWith_avoids
    (groundEq : Ground → Ground → Bool) (b : Subst)
    (left right : List Atom) (constraints : List (String × Atom))
    (hleft : ∀ child ∈ left, AtomAvoids b child)
    (hright : ∀ child ∈ right, AtomAvoids b child)
    (hdecompose :
      Metta.Unify.decomposeListWith groundEq left right = some constraints) :
    ConstraintsAvoid b constraints := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          cases hdecompose
          exact constraintsAvoid_nil b
      | cons rightHead rightTail =>
          simp [Metta.Unify.decomposeListWith] at hdecompose
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [Metta.Unify.decomposeListWith] at hdecompose
      | cons rightHead rightTail =>
          simp only [Metta.Unify.decomposeListWith] at hdecompose
          cases hhead :
              Metta.Unify.decomposeEqWith groundEq leftHead rightHead with
          | none => simp [hhead] at hdecompose
          | some headConstraints =>
              cases htail :
                  Metta.Unify.decomposeListWith groundEq leftTail rightTail with
              | none => simp [hhead, htail] at hdecompose
              | some tailConstraints =>
                  simp [hhead, htail] at hdecompose
                  cases hdecompose
                  apply ConstraintsAvoid.append
                  · apply decomposeEqWith_avoids groundEq b leftHead rightHead
                    · exact hleft leftHead (by simp)
                    · exact hright rightHead (by simp)
                    · exact hhead
                  · apply decomposeListWith_avoids groundEq b leftTail rightTail
                    · intro child hchild
                      exact hleft child (by simp [hchild])
                    · intro child hchild
                      exact hright child (by simp [hchild])
                    · exact htail

end

/-- Finite witness that identifies every copied variable with its source.
    Duplicate source occurrences are removed before materializing bindings. -/
def freshVariantWitness (fresh : String → String)
    (allowed : List String) : Subst :=
  allowed.eraseDups.map (fun source => (fresh source, Atom.var source))

private theorem freshVariantWitness_lookup_fresh_aux
    (fresh : String → String) (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right) :
    ∀ source, source ∈ allowed →
      Metta.Subst.lookup
        (allowed.map (fun item => (fresh item, Atom.var item)))
        (fresh source) = some (Atom.var source) := by
  intro source hsource
  induction allowed with
  | nil => simp at hsource
  | cons head tail ih =>
      by_cases heq : source = head
      · subst head
        simp [Metta.Subst.lookup]
      · have htail : source ∈ tail := by simpa [heq] using hsource
        have hfreshNe : fresh source ≠ fresh head := by
          intro hfresh
          exact heq (hinjective source (by simp [htail]) head (by simp)
            hfresh)
        have hbeq : (fresh source == fresh head) = false := by
          simp [hfreshNe]
        simp only [List.map_cons, Metta.Subst.lookup, hbeq,
          Bool.false_eq_true, if_false]
        exact ih (by
          intro left hleft right hright hequal
          exact hinjective left (by simp [hleft]) right (by simp [hright])
            hequal) htail

theorem freshVariantWitness_lookup_fresh (fresh : String → String)
    (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (source : String) (hsource : source ∈ allowed) :
    Metta.Subst.lookup (freshVariantWitness fresh allowed) (fresh source) =
      some (Atom.var source) := by
  apply freshVariantWitness_lookup_fresh_aux fresh allowed.eraseDups
  · intro left hleft right hright hequal
    exact hinjective left (by simpa using hleft) right (by simpa using hright)
      hequal
  · simpa using hsource

private theorem freshVariantWitness_lookup_source_none_aux
    (fresh : String → String) (allowed : List String) (target : String)
    (hdisjoint : ∀ source, source ∈ allowed → fresh source ≠ target) :
    Metta.Subst.lookup
      (allowed.map (fun source => (fresh source, Atom.var source))) target =
        none := by
  induction allowed with
  | nil => simp [Metta.Subst.lookup]
  | cons head tail ih =>
      have hne : target ≠ fresh head := Ne.symm (hdisjoint head (by simp))
      have hbeq : (target == fresh head) = false := by simp [hne]
      simp only [List.map_cons, Metta.Subst.lookup, hbeq,
        Bool.false_eq_true, if_false]
      exact ih (by
        intro source hsource
        exact hdisjoint source (by simp [hsource]))

theorem freshVariantWitness_lookup_source_none (fresh : String → String)
    (allowed : List String)
    (hdisjoint : ∀ copied, copied ∈ allowed →
      ∀ source, source ∈ allowed → fresh copied ≠ source)
    (source : String) (hsource : source ∈ allowed) :
    Metta.Subst.lookup (freshVariantWitness fresh allowed) source = none := by
  apply freshVariantWitness_lookup_source_none_aux fresh allowed.eraseDups
    source
  intro copied hcopied
  exact hdisjoint copied (by simpa using hcopied) source hsource

private theorem freshVariantWitness_lookup_shape_aux
    (fresh : String → String) (allowed : List String)
    (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup
      (allowed.map (fun source => (fresh source, Atom.var source))) name =
        some value) :
    ∃ source, source ∈ allowed ∧ name = fresh source ∧
      value = Atom.var source := by
  induction allowed with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons head tail ih =>
      by_cases heq : name = fresh head
      · subst name
        simp only [List.map_cons, Metta.Subst.lookup, beq_self_eq_true,
          if_true, Option.some.injEq] at hlookup
        subst value
        exact ⟨head, by simp, rfl, rfl⟩
      · have hbeq : (name == fresh head) = false := by simp [heq]
        simp only [List.map_cons, Metta.Subst.lookup, hbeq,
          Bool.false_eq_true, if_false] at hlookup
        obtain ⟨source, hsource, hname, hvalue⟩ := ih hlookup
        exact ⟨source, by simp [hsource], hname, hvalue⟩

theorem freshVariantWitness_lookup_shape (fresh : String → String)
    (allowed : List String) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup (freshVariantWitness fresh allowed) name =
      some value) :
    ∃ source, source ∈ allowed ∧ name = fresh source ∧
      value = Atom.var source := by
  obtain ⟨source, hsource, hname, hvalue⟩ :=
    freshVariantWitness_lookup_shape_aux fresh allowed.eraseDups name value
      hlookup
  exact ⟨source, by simpa using hsource, hname, hvalue⟩

private theorem nodup_map_string_of_injective (f : String → String) :
    ∀ items : List String, items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        f left = f right → left = right) →
      (items.map f).Nodup := by
  intro items hnodup hinjective
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.nodup_cons] at hnodup ⊢
      constructor
      · intro mapped hmem hequal
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
        have : head = source := hinjective head (by simp) source
          (by simp [hsource]) hequal
        subst source
        exact hnodup.1 hsource
      · exact ih hnodup.2 (by
          intro left hleft right hright hequal
          exact hinjective left (by simp [hleft]) right (by simp [hright])
            hequal)

private theorem eraseDups_nodup_string : (items : List String) →
    items.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_eraseDups] at hmem
        simp at hmem
      · exact eraseDups_nodup_string
          (tail.filter (fun item => !item == head))
termination_by items => items.length
decreasing_by
  have hlength := List.length_filter_le (fun item : String => !item == head)
    tail
  simp only [List.length_cons]
  omega

private theorem lookup_ne_none_key_mem (binding : Subst) (name : String)
    (hlookup : Metta.Subst.lookup binding name ≠ none) :
    name ∈ binding.map Prod.fst := by
  induction binding with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases heq : name = key
      · simp [heq]
      · have hbeq : (name == key) = false := by simp [heq]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        simp [ih hlookup]

/-- The finite fresh-variant witness is acyclic: copied variables form the
    domain and every range variable lies outside that domain. -/
def freshVariantWitness_topological (fresh : String → String)
    (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ copied, copied ∈ allowed →
      ∀ source, source ∈ allowed → fresh copied ≠ source) :
    SubstTopological (freshVariantWitness fresh allowed) := by
  let unique := allowed.eraseDups
  let order := unique.map fresh
  refine
    { order := order
      nodup := ?_
      domain := ?_
      decreases := ?_ }
  · apply nodup_map_string_of_injective fresh unique
      (eraseDups_nodup_string allowed)
    intro left hleft right hright hequal
    exact hinjective left (by simpa [unique] using hleft) right
      (by simpa [unique] using hright) hequal
  · intro name
    constructor
    · intro hname hnone
      obtain ⟨source, hsource, hequal⟩ := List.mem_map.mp hname
      subst name
      have hlookup := freshVariantWitness_lookup_fresh fresh allowed hinjective
        source (by simpa [unique] using hsource)
      simp [hlookup] at hnone
    · intro hlookup
      have hkey : name ∈
          (freshVariantWitness fresh allowed).map Prod.fst :=
        lookup_ne_none_key_mem _ name hlookup
      simpa [freshVariantWitness, order, unique, List.map_map,
        Function.comp_def] using hkey
  · intro bound value dependency hbound hdependency hdependencyLookup
    obtain ⟨source, hsource, hboundName, hvalue⟩ :=
      freshVariantWitness_lookup_shape fresh allowed bound value hbound
    subst bound
    subst value
    simp only [Atom.vars, List.mem_singleton] at hdependency
    subst dependency
    exact False.elim (hdependencyLookup
      (freshVariantWitness_lookup_source_none fresh allowed hdisjoint source
        hsource))

private def EquationsAvoid (b : Subst)
    (equations : List (Atom × Atom)) : Prop :=
  ∀ equation, equation ∈ equations →
    AtomAvoids b equation.1 ∧ AtomAvoids b equation.2

private theorem decomposeAllWith_avoids
    (groundEq : Ground → Ground → Bool) (b : Subst)
    (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (hequations : EquationsAvoid b equations)
    (hdecompose :
      Metta.Unify.decomposeAllWith groundEq equations = some constraints) :
    ConstraintsAvoid b constraints := by
  induction equations generalizing constraints with
  | nil =>
      cases hdecompose
      exact constraintsAvoid_nil b
  | cons equation rest ih =>
      rcases equation with ⟨left, right⟩
      simp only [Metta.Unify.decomposeAllWith] at hdecompose
      cases hhead : Metta.Unify.decomposeEqWith groundEq left right with
      | none => simp [hhead] at hdecompose
      | some headConstraints =>
          cases hrest : Metta.Unify.decomposeAllWith groundEq rest with
          | none => simp [hhead, hrest] at hdecompose
          | some restConstraints =>
              simp [hhead, hrest] at hdecompose
              cases hdecompose
              apply ConstraintsAvoid.append
              · apply decomposeEqWith_avoids groundEq b left right
                · exact (hequations (left, right) (by simp)).1
                · exact (hequations (left, right) (by simp)).2
                · exact hhead
              · apply ih
                · intro pair hpair
                  exact hequations pair (by simp [hpair])
                · exact hrest

private theorem decomposeAll_avoids (b : Subst)
    (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (hequations : EquationsAvoid b equations)
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints) :
    ConstraintsAvoid b constraints := by
  apply decomposeAllWith_avoids Metta.Ground.equiv b equations constraints
    hequations
  simpa [Metta.Unify.decomposeAllWith_groundEquiv] using hdecompose

private theorem not_mem_vars_of_occurs_eq_false (name : String) (a : Atom)
    (hoccurs : Metta.Subst.occurs name a = false) :
    name ∉ a.vars := by
  induction a with
  | sym symbol => simp [Atom.vars]
  | var varName => simpa [Metta.Subst.occurs, Atom.vars] using hoccurs
  | gnd ground => simp [Atom.vars]
  | expr atoms atomIH =>
      simp only [Metta.Subst.occurs] at hoccurs
      simp only [Atom.vars]
      rw [List.mem_flatten]
      intro hmem
      rcases hmem with ⟨variableList, hvariableList, hname⟩
      rcases List.mem_map.mp hvariableList with ⟨child, hchild, rfl⟩
      have hchildOccurs : Metta.Subst.occurs name child = false := by
        have hall := List.any_eq_false.mp hoccurs
        simpa only [Bool.not_eq_true] using
          (hall ⟨child, hchild⟩ (by simp))
      exact atomIH child hchild hchildOccurs hname

private theorem atomAvoids_cons_target (b : Subst) (name : String)
    (target : Atom) (hname : name ∉ target.vars)
    (htarget : AtomAvoids b target) :
    AtomAvoids ((name, target) :: b) target := by
  intro dependency hdependency
  by_cases heq : dependency = name
  · subst dependency
    exact False.elim (hname hdependency)
  · have hlookup := htarget dependency hdependency
    simpa [Metta.Subst.lookup, heq] using hlookup

private theorem atomAvoids_apply_singleton (b : Subst) (name : String)
    (target a : Atom) (hname : name ∉ target.vars)
    (htarget : AtomAvoids b target) (ha : AtomAvoids b a) :
    AtomAvoids ((name, target) :: b)
      (Metta.Subst.apply [(name, target)] a) := by
  induction a with
  | sym symbol => simp [Metta.Subst.apply, AtomAvoids, Atom.vars]
  | var varName =>
      by_cases heq : varName = name
      · subst varName
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using
          atomAvoids_cons_target b name target hname htarget
      · have hvariable : Metta.Subst.lookup b varName = none :=
          ha varName (by simp [Atom.vars])
        simp [Metta.Subst.apply, Metta.Subst.lookup, heq, AtomAvoids,
          Atom.vars, hvariable]
  | gnd ground => simp [Metta.Subst.apply, AtomAvoids, Atom.vars]
  | expr atoms atomIH =>
      simp only [Metta.Subst.apply]
      apply (atomAvoids_expr_iff ((name, target) :: b)
        (atoms.map (Metta.Subst.apply [(name, target)]))).2
      intro child hchild
      rcases List.mem_map.mp hchild with ⟨source, hsource, rfl⟩
      exact atomIH source hsource
        ((atomAvoids_expr_iff b atoms).1 ha source hsource)

private theorem constraintMap_equationsAvoid (b : Subst) (name : String)
    (target : Atom) (constraints : List (String × Atom))
    (hname : name ∉ target.vars) (htarget : AtomAvoids b target)
    (hconstraints : ConstraintsAvoid b constraints) :
    EquationsAvoid ((name, target) :: b)
      (constraints.map fun constraint =>
        (Metta.Subst.apply [(name, target)] (Atom.var constraint.1),
          Metta.Subst.apply [(name, target)] constraint.2)) := by
  intro equation hequation
  rcases List.mem_map.mp hequation with ⟨constraint, hconstraint, rfl⟩
  rcases constraint with ⟨source, value⟩
  have havoids := hconstraints (source, value) hconstraint
  constructor
  · apply atomAvoids_apply_singleton b name target (Atom.var source)
      hname htarget
    intro dependency hdependency
    simp only [Atom.vars, List.mem_singleton] at hdependency
    subst dependency
    exact havoids.1
  · exact atomAvoids_apply_singleton b name target value hname htarget
      havoids.2

private theorem erase_eq_self_of_lookup_none (b : Subst) (name : String)
    (hlookup : Metta.Subst.lookup b name = none) :
    Metta.Subst.erase b name = b := by
  induction b with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases heq : name = key
      · subst key
        simp [Metta.Subst.lookup] at hlookup
      · have hbeq : (name == key) = false := by simp [heq]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true,
          if_false] at hlookup
        have hkeep : (key != name) = true := by simp [Ne.symm heq]
        simp only [Metta.Subst.erase, List.filter_cons]
        rw [if_pos hkeep]
        congr 1
        exact ih hlookup

/-- Prefixing a fresh, acyclic binding preserves a substitution's topological
order.  This is the reusable certificate for the singleton bindings produced
when a fresh result variable captures a term. -/
def SubstTopological.cons_of_fresh (b : Subst)
    (topological : SubstTopological b) (name : String) (target : Atom)
    (hlookup : Metta.Subst.lookup b name = none)
    (hname : name ∉ target.vars)
    (htarget : AtomAvoids b target) :
    SubstTopological ((name, target) :: b) := by
  have hnameOrder : name ∉ topological.order := by
    intro hmem
    exact (topological.domain name).1 hmem hlookup
  refine
    { order := name :: topological.order
      nodup := List.nodup_cons.mpr ⟨hnameOrder, topological.nodup⟩
      domain := ?_
      decreases := ?_ }
  · intro source
    by_cases heq : source = name
    · subst source
      simp [Metta.Subst.lookup]
    · have hbeq : (source == name) = false := by simp [heq]
      simp only [List.mem_cons, Metta.Subst.lookup, hbeq,
        Bool.false_eq_true, if_false]
      constructor
      · intro hmem
        rcases hmem with hmem | hmem
        · exact False.elim (heq hmem)
        · exact (topological.domain source).1 hmem
      · intro hbound
        exact Or.inr ((topological.domain source).2 hbound)
  · intro source value dependency hsource hdependency hdependencyBound
    by_cases hsourceName : source = name
    · subst source
      have hvalue : value = target := by
        have htargetValue : target = value := by
          simpa [Metta.Subst.lookup] using hsource
        exact htargetValue.symm
      subst value
      by_cases hdependencyName : dependency = name
      · subst dependency
        exact False.elim (hname hdependency)
      · have hdependencyOld :
            Metta.Subst.lookup b dependency ≠ none := by
          simpa [Metta.Subst.lookup, hdependencyName] using hdependencyBound
        exact False.elim
          (hdependencyOld (htarget dependency hdependency))
    · have hsourceOld : Metta.Subst.lookup b source = some value := by
        simpa [Metta.Subst.lookup, hsourceName] using hsource
      by_cases hdependencyName : dependency = name
      · subst dependency
        simp only [List.idxOf_cons_self]
        rw [List.idxOf_cons]
        have hbeq : (name == source) = false := by
          simp [Ne.symm hsourceName]
        rw [hbeq]
        exact Nat.zero_lt_succ _
      · have hdependencyOld :
            Metta.Subst.lookup b dependency ≠ none := by
          simpa [Metta.Subst.lookup, hdependencyName] using hdependencyBound
        have hdecreases := topological.decreases source value dependency
          hsourceOld hdependency hdependencyOld
        have hsourceBeq : (name == source) = false := by
          simp [Ne.symm hsourceName]
        have hdependencyBeq : (name == dependency) = false := by
          simp [Ne.symm hdependencyName]
        simpa [List.idxOf_cons, hsourceBeq, hdependencyBeq] using
          Nat.add_lt_add_right hdecreases 1

/-- The empty runtime substitution has the canonical empty elimination
order. -/
def emptySubstTopological : SubstTopological ([] : Subst) := by
  refine
    { order := []
      nodup := List.nodup_nil
      domain := ?_
      decreases := ?_ }
  · intro name
    simp [Metta.Subst.lookup]
  · intro source value dependency hsource
    simp [Metta.Subst.lookup] at hsource

/-- The actual elimination loop constructs a topological substitution.  The
    proof follows `unifyRounds` round-for-round: decomposition cannot introduce
    a previously eliminated variable; the occurs check excludes a self edge;
    and single-binding application removes the newly eliminated variable from
    the next worklist. -/
def unifyRoundsWith_topological (groundEq : Ground → Ground → Bool)
    (fuel : Nat) (equations : List (Atom × Atom))
    (b result : Subst) (topological : SubstTopological b)
    (hequations : EquationsAvoid b equations)
    (hresult :
      Metta.Unify.unifyRoundsWith groundEq fuel equations b = some result) :
    SubstTopological result := by
  induction fuel generalizing equations b result with
  | zero =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              exact topological
          | cons constraint rest => simp [hdecompose] at hresult
  | succ fuel ih =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              exact topological
          | cons constraint rest =>
              rcases constraint with ⟨name, target⟩
              by_cases hoccurs : Metta.Subst.occurs name target = true
              · simp [hdecompose, hoccurs] at hresult
              · have hoccursFalse :
                    Metta.Subst.occurs name target = false := by
                  cases hvalue : Metta.Subst.occurs name target with
                  | false => rfl
                  | true => exact False.elim (hoccurs hvalue)
                have hconstraints :
                    ConstraintsAvoid b ((name, target) :: rest) :=
                  decomposeAllWith_avoids groundEq b equations
                    ((name, target) :: rest) hequations hdecompose
                have hhead := hconstraints (name, target) (by simp)
                have hname : name ∉ target.vars :=
                  not_mem_vars_of_occurs_eq_false name target hoccursFalse
                have hextend : Metta.Subst.extend b name target =
                    (name, target) :: b := by
                  simp [Metta.Subst.extend,
                    erase_eq_self_of_lookup_none b name hhead.1]
                have hnextTopological :
                    SubstTopological ((name, target) :: b) :=
                  SubstTopological.cons_of_fresh b topological name target
                    hhead.1 hname hhead.2
                have hrest : ConstraintsAvoid b rest := by
                  intro constraint hconstraint
                  exact hconstraints constraint (by simp [hconstraint])
                have hnextEquations :
                    EquationsAvoid ((name, target) :: b)
                      (rest.map fun constraint =>
                        (Metta.Subst.apply [(name, target)]
                            (Atom.var constraint.1),
                          Metta.Subst.apply [(name, target)] constraint.2)) :=
                  constraintMap_equationsAvoid b name target rest hname
                    hhead.2 hrest
                simp only [hdecompose, hoccursFalse, Bool.false_eq_true,
                  if_false] at hresult
                rw [hextend] at hresult
                exact ih _ _ _ hnextTopological hnextEquations hresult

/-- Legacy specialization of `unifyRoundsWith_topological` to Hyperon's
ordinary ground equivalence. -/
def unifyRounds_topological (fuel : Nat)
    (equations : List (Atom × Atom)) (b result : Subst)
    (topological : SubstTopological b)
    (hequations : EquationsAvoid b equations)
    (hresult : Metta.Unify.unifyRounds fuel equations b = some result) :
    SubstTopological result := by
  apply unifyRoundsWith_topological Metta.Ground.equiv fuel equations b result
    topological hequations
  simpa [Metta.Unify.unifyRoundsWith_groundEquiv] using hresult

/-- Every successful `unifyTop` result carries the elimination-order
    certificate needed by deep substitution and liveness trimming. -/
def unifyTopWith_topological (groundEq : Ground → Ground → Bool)
    (left right : Atom) (result : Subst)
    (hresult : Metta.Unify.unifyTopWith groundEq left right = some result) :
    SubstTopological result := by
  apply unifyRoundsWith_topological groundEq
      (Atom.size left + Atom.size right) [(left, right)] [] result
      emptySubstTopological
  · intro equation hequation
    simp only [List.mem_singleton] at hequation
    subst equation
    constructor <;> simp [AtomAvoids, Metta.Subst.lookup]
  · exact hresult

/-- Legacy specialization of `unifyTopWith_topological` to Hyperon's
ordinary ground equivalence. -/
def unifyTop_topological (left right : Atom) (result : Subst)
    (hresult : Metta.Unify.unifyTop left right = some result) :
    SubstTopological result := by
  apply unifyTopWith_topological Metta.Ground.equiv left right result
  simpa [Metta.Unify.unifyTopWith_groundEquiv] using hresult

private theorem atomAvoids_apply_singleton_external (external : Subst)
    (name : String) (target a : Atom)
    (htarget : AtomAvoids external target) (ha : AtomAvoids external a) :
    AtomAvoids external (Metta.Subst.apply [(name, target)] a) := by
  induction a with
  | sym symbol => simp [Metta.Subst.apply, AtomAvoids, Atom.vars]
  | var varName =>
      by_cases heq : varName = name
      · subst varName
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using htarget
      · have hvar : Metta.Subst.lookup external varName = none :=
          ha varName (by simp [Atom.vars])
        simp [Metta.Subst.apply, Metta.Subst.lookup, heq, AtomAvoids,
          Atom.vars, hvar]
  | gnd ground => simp [Metta.Subst.apply, AtomAvoids, Atom.vars]
  | expr atoms atomIH =>
      simp only [Metta.Subst.apply]
      apply (atomAvoids_expr_iff external
        (atoms.map (Metta.Subst.apply [(name, target)]))).2
      intro child hchild
      rcases List.mem_map.mp hchild with ⟨source, hsource, rfl⟩
      exact atomIH source hsource
        ((atomAvoids_expr_iff external atoms).1 ha source hsource)

private theorem constraintMap_equationsAvoid_external (external : Subst)
    (name : String) (target : Atom)
    (constraints : List (String × Atom))
    (htarget : AtomAvoids external target)
    (hconstraints : ConstraintsAvoid external constraints) :
    EquationsAvoid external
      (constraints.map fun constraint =>
        (Metta.Subst.apply [(name, target)] (Atom.var constraint.1),
          Metta.Subst.apply [(name, target)] constraint.2)) := by
  intro equation hequation
  rcases List.mem_map.mp hequation with ⟨constraint, hconstraint, rfl⟩
  rcases constraint with ⟨source, value⟩
  have havoids := hconstraints (source, value) hconstraint
  constructor
  · apply atomAvoids_apply_singleton_external external name target
      (Atom.var source) htarget
    intro dependency hdependency
    simp only [Atom.vars, List.mem_singleton] at hdependency
    subst dependency
    exact havoids.1
  · exact atomAvoids_apply_singleton_external external name target value
      htarget havoids.2

def SubstEntriesAvoid (external generated : Subst) : Prop :=
  ∀ binding, binding ∈ generated →
    Metta.Subst.lookup external binding.1 = none ∧
      AtomAvoids external binding.2

private theorem SubstEntriesAvoid.extend (external generated : Subst)
    (name : String) (target : Atom)
    (hgenerated : SubstEntriesAvoid external generated)
    (hname : Metta.Subst.lookup external name = none)
    (htarget : AtomAvoids external target) :
    SubstEntriesAvoid external (Metta.Subst.extend generated name target) := by
  intro binding hbinding
  simp only [Metta.Subst.extend, List.mem_cons] at hbinding
  rcases hbinding with hbinding | hbinding
  · subst binding
    exact ⟨hname, htarget⟩
  · change binding ∈ generated.filter (fun entry => entry.1 != name) at hbinding
    exact hgenerated binding (List.mem_filter.mp hbinding).1

private theorem unifyRoundsWith_avoidsExternal
    (groundEq : Ground → Ground → Bool) (external : Subst) (fuel : Nat)
    (equations : List (Atom × Atom)) (generated result : Subst)
    (hequations : EquationsAvoid external equations)
    (hgenerated : SubstEntriesAvoid external generated)
    (hresult :
      Metta.Unify.unifyRoundsWith groundEq fuel equations generated =
        some result) :
    SubstEntriesAvoid external result := by
  induction fuel generalizing equations generated result with
  | zero =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              exact hgenerated
          | cons constraint rest => simp [hdecompose] at hresult
  | succ fuel ih =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              exact hgenerated
          | cons constraint rest =>
              rcases constraint with ⟨name, target⟩
              by_cases hoccurs : Metta.Subst.occurs name target = true
              · simp [hdecompose, hoccurs] at hresult
              · have hoccursFalse :
                    Metta.Subst.occurs name target = false := by
                  cases hvalue : Metta.Subst.occurs name target with
                  | false => rfl
                  | true => exact False.elim (hoccurs hvalue)
                have hconstraints :
                    ConstraintsAvoid external ((name, target) :: rest) :=
                  decomposeAllWith_avoids groundEq external equations
                    ((name, target) :: rest) hequations hdecompose
                have hhead := hconstraints (name, target) (by simp)
                have hrest : ConstraintsAvoid external rest := by
                  intro binding hbinding
                  exact hconstraints binding (by simp [hbinding])
                have hnextEquations : EquationsAvoid external
                    (rest.map fun constraint =>
                      (Metta.Subst.apply [(name, target)]
                          (Atom.var constraint.1),
                        Metta.Subst.apply [(name, target)] constraint.2)) :=
                  constraintMap_equationsAvoid_external external name target
                    rest hhead.2 hrest
                have hnextGenerated : SubstEntriesAvoid external
                    (Metta.Subst.extend generated name target) :=
                  SubstEntriesAvoid.extend external generated name target
                    hgenerated hhead.1 hhead.2
                simp only [hdecompose, hoccursFalse, Bool.false_eq_true,
                  if_false] at hresult
                exact ih _ _ _ hnextEquations hnextGenerated hresult

private theorem unifyTopWith_avoidsExternal
    (groundEq : Ground → Ground → Bool) (external : Subst)
    (left right : Atom) (result : Subst)
    (hleft : AtomAvoids external left) (hright : AtomAvoids external right)
    (hresult : Metta.Unify.unifyTopWith groundEq left right = some result) :
    SubstEntriesAvoid external result := by
  apply unifyRoundsWith_avoidsExternal groundEq external
      (Atom.size left + Atom.size right) [(left, right)] [] result
  · intro equation hequation
    simp only [List.mem_singleton] at hequation
    subst equation
    exact ⟨hleft, hright⟩
  · simp [SubstEntriesAvoid]
  · exact hresult

private theorem unifyTop_avoidsExternal (external : Subst)
    (left right : Atom) (result : Subst)
    (hleft : AtomAvoids external left) (hright : AtomAvoids external right)
    (hresult : Metta.Unify.unifyTop left right = some result) :
    SubstEntriesAvoid external result := by
  apply unifyTopWith_avoidsExternal Metta.Ground.equiv external left right
    result hleft hright
  simpa [Metta.Unify.unifyTopWith_groundEquiv] using hresult

/-- The unifier never invents variable names: every key or target variable
in a successful result occurs in one of the two input atoms. -/
theorem unifyTopWith_substVars_origin
    (groundEq : Ground → Ground → Bool) (left right : Atom) (result : Subst)
    (hresult : Metta.Unify.unifyTopWith groundEq left right = some result)
    (name : String) (hname : name ∈ resolutionSubstVars result) :
    name ∈ left.vars ∨ name ∈ right.vars := by
  by_cases hleftOrigin : name ∈ left.vars
  · exact Or.inl hleftOrigin
  by_cases hrightOrigin : name ∈ right.vars
  · exact Or.inr hrightOrigin
  let external : Subst := [(name, Atom.sym "#resolution-origin")]
  have hleft : AtomAvoids external left := by
    intro candidate hcandidate
    have hne : candidate ≠ name := by
      intro heq
      subst candidate
      exact hleftOrigin hcandidate
    simp [external, Metta.Subst.lookup, hne]
  have hright : AtomAvoids external right := by
    intro candidate hcandidate
    have hne : candidate ≠ name := by
      intro heq
      subst candidate
      exact hrightOrigin hcandidate
    simp [external, Metta.Subst.lookup, hne]
  have havoids := unifyTopWith_avoidsExternal groundEq external left right
    result hleft hright hresult
  simp only [resolutionSubstVars, List.mem_flatMap] at hname
  obtain ⟨binding, hbinding, hmember⟩ := hname
  have hentry := havoids binding hbinding
  rcases binding with ⟨key, value⟩
  simp only [List.mem_cons] at hmember
  rcases hmember with hkey | hvalue
  · subst key
    simpa [external, Metta.Subst.lookup] using hentry.1
  · have := hentry.2 name hvalue
    simp [external, Metta.Subst.lookup] at this

/-- Legacy specialization of variable-origin preservation to Hyperon's
ordinary ground equivalence. -/
theorem unifyTop_substVars_origin (left right : Atom) (result : Subst)
    (hresult : Metta.Unify.unifyTop left right = some result)
    (name : String) (hname : name ∈ resolutionSubstVars result) :
    name ∈ left.vars ∨ name ∈ right.vars := by
  apply unifyTopWith_substVars_origin Metta.Ground.equiv left right result
  · simpa [Metta.Unify.unifyTopWith_groundEquiv] using hresult
  · exact hname

private theorem substLookup_mem (binding : Subst) (source : String)
    (value : Atom) (hlookup : Metta.Subst.lookup binding source = some value) :
    (source, value) ∈ binding := by
  induction binding with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, target⟩
      by_cases heq : source = key
      · subst key
        simp [Metta.Subst.lookup] at hlookup
        subst target
        simp
      · simp [Metta.Subst.lookup, heq] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

private theorem resolutionSubstVars_target_of_lookup (binding : Subst)
    (source : String) (value : Atom)
    (hlookup : Metta.Subst.lookup binding source = some value)
    (name : String) (hname : name ∈ value.vars) :
    name ∈ resolutionSubstVars binding := by
  simp only [resolutionSubstVars, List.mem_flatMap]
  exact ⟨(source, value), substLookup_mem binding source value hlookup,
    by simp [hname]⟩

private theorem resolutionSubstVars_range_origin (binding : Subst)
    (name : String)
    (hname : name ∈ binding.flatMap (fun entry => entry.2.vars)) :
    name ∈ resolutionSubstVars binding := by
  simp only [List.mem_flatMap] at hname
  obtain ⟨entry, hentry, htarget⟩ := hname
  simp only [resolutionSubstVars, List.mem_flatMap]
  exact ⟨entry, hentry, by simp [htarget]⟩

/-- One-pass substitution cannot invent variable names. -/
theorem substApply_vars_origin (binding : Subst) :
    ∀ atom name, name ∈ (Metta.Subst.apply binding atom).vars →
      name ∈ atom.vars ∨ name ∈ resolutionSubstVars binding := by
  intro atom
  induction atom with
  | sym symbol => simp [Metta.Subst.apply, Atom.vars]
  | gnd ground => simp [Metta.Subst.apply, Atom.vars]
  | var source =>
      intro name hname
      cases hlookup : Metta.Subst.lookup binding source with
      | none =>
          simp only [Metta.Subst.apply, hlookup, Option.getD_none,
            Atom.vars, List.mem_singleton] at hname ⊢
          exact Or.inl hname
      | some value =>
          simp only [Metta.Subst.apply, hlookup, Option.getD_some] at hname
          exact Or.inr
            (resolutionSubstVars_target_of_lookup binding source value
              hlookup name hname)
  | expr atoms ih =>
      intro name hname
      simp only [Metta.Subst.apply, Atom.vars, List.mem_flatten,
        List.mem_map] at hname
      obtain ⟨variableList, ⟨substituted, hsubstituted, rfl⟩,
        hname⟩ := hname
      obtain ⟨source, hsource, rfl⟩ := hsubstituted
      rcases ih source hsource name hname with horigin | hbinding
      · exact Or.inl (by
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨source.vars, ⟨source, hsource, rfl⟩, horigin⟩)
      · exact Or.inr hbinding

/-- Substitution composition carries only variables from its two inputs. -/
theorem substCompose_vars_origin (generated existing : Subst)
    (name : String)
    (hname : name ∈ resolutionSubstVars
      (Metta.Subst.compose generated existing)) :
    name ∈ resolutionSubstVars generated ∨
      name ∈ resolutionSubstVars existing := by
  simp only [resolutionSubstVars, List.mem_flatMap] at hname
  obtain ⟨binding, hbinding, hmember⟩ := hname
  simp only [Metta.Subst.compose, List.mem_append] at hbinding
  rcases hbinding with hexisting | hgenerated
  · obtain ⟨sourceBinding, hsourceBinding, rfl⟩ :=
      List.mem_map.mp hexisting
    rcases sourceBinding with ⟨source, value⟩
    simp only [List.mem_cons] at hmember
    rcases hmember with hsource | hvalue
    · subst name
      exact Or.inr (by
        simp only [resolutionSubstVars, List.mem_flatMap]
        exact ⟨(source, value), hsourceBinding, by simp⟩)
    · rcases substApply_vars_origin generated value name hvalue with
        horigin | hgeneratedVar
      · exact Or.inr (by
          simp only [resolutionSubstVars, List.mem_flatMap]
          exact ⟨(source, value), hsourceBinding, by simp [horigin]⟩)
      · exact Or.inl hgeneratedVar
  · exact Or.inl (by
      simp only [resolutionSubstVars, List.mem_flatMap]
      exact ⟨binding, hgenerated, hmember⟩)

/-- Every substitution returned by the PeTTa exact-ground entry point is
produced by the comparator-parametric structural unifier itself. -/
theorem unifyTopExact_some_underlying (left right : Atom) (result : Subst)
    (exactResult : unifyTopExact left right = some result) :
    Metta.Unify.unifyTopWith prologGroundIdentical left right =
      some result := by
  simpa [unifyTopExact] using exactResult

/-- Every atom is compatible with itself at the PeTTa dialect boundary.  This
property is independent of host-ground equality: compatibility records term
constructor shape, not equality of payloads already checked by the shared
unifier. -/
theorem pettaUnifyCompatible_self (atom : Atom) :
    pettaUnifyCompatible atom atom = true := by
  induction atom with
  | sym name => rfl
  | var name => rfl
  | gnd ground => cases ground <;> rfl
  | expr atoms children =>
      simp only [pettaUnifyCompatible]
      induction atoms with
      | nil => rfl
      | cons head tail tailIH =>
          simp only [pettaUnifyCompatibleList, Bool.and_eq_true]
          exact ⟨children head (by simp), tailIH (fun item member =>
            children item (by simp [member]))⟩

/-- The PeTTa entry point is the exact-ground structural unifier.  The
propositional equality premise is retained because callers use this theorem
as the handoff from an independent exact witness. -/
theorem unifyTopExact_of_underlying_exact (left right : Atom)
    (result : Subst)
    (underlying :
      Metta.Unify.unifyTopWith prologGroundIdentical left right =
        some result)
    (_exact : subst result left = subst result right) :
    unifyTopExact left right = some result := by
  simpa [unifyTopExact] using underlying

/-- A reflexive executable variable equation succeeds with the empty exact
unifier.  Alias-ledger resolution uses this case for repeated sources after
the current substitution has already identified both sides. -/
theorem unifyTopExact_var_self (name : String) :
    unifyTopExact (.var name) (.var name) = some [] := by
  apply unifyTopExact_of_underlying_exact (.var name) (.var name) []
  · have positive :
        0 < Atom.size (.var name) + Atom.size (.var name) := by
      simp [Atom.size]
    obtain ⟨fuel, fuelEquation⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    unfold Metta.Unify.unifyTopWith
    rw [fuelEquation]
    simp [Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith]
  · rfl

/-- Unification under an existing binding carries only variables already
present in that binding or in the two source atoms. -/
theorem unifyB_substVars_origin (binding : Subst) (left right : Atom)
    (result : Subst) (hresult : unifyB binding left right = some result)
    (name : String) (hname : name ∈ resolutionSubstVars result) :
    name ∈ resolutionSubstVars binding ∨
      name ∈ left.vars ∨ name ∈ right.vars := by
  unfold unifyB at hresult
  cases hexact : unifyTopExact (subst binding left)
      (subst binding right) with
  | none => simp [hexact] at hresult
  | some generated =>
      have hunify : Metta.Unify.unifyTopWith prologGroundIdentical
          (subst binding left) (subst binding right) = some generated :=
        unifyTopExact_some_underlying _ _ _ hexact
      cases generated with
      | nil =>
          simp [hexact] at hresult
          subst result
          exact Or.inl hname
      | cons entry rest =>
          simp [hexact] at hresult
          subst result
          rcases substCompose_vars_origin (entry :: rest) binding name hname
              with hgenerated | hexisting
          · rcases unifyTopWith_substVars_origin prologGroundIdentical
                (subst binding left) (subst binding right)
                (entry :: rest) hunify name hgenerated with
              hleft | hright
            · rcases subst_vars_origin binding left name hleft with
                hsource | hrange
              · exact Or.inr (Or.inl hsource)
              · exact Or.inl
                  (resolutionSubstVars_range_origin binding name hrange)
            · rcases subst_vars_origin binding right name hright with
                hsource | hrange
              · exact Or.inr (Or.inr hsource)
              · exact Or.inl
                  (resolutionSubstVars_range_origin binding name hrange)
          · exact Or.inl hexisting

/-- Liveness trimming removes bindings but never introduces a key or target
variable absent from the untrimmed substitution. -/
theorem trimFor_substVars_origin (goals : List Goal) (qterm : Atom)
    (binding : Subst) (name : String)
    (hname : name ∈ resolutionSubstVars (trimFor goals qterm binding)) :
    name ∈ resolutionSubstVars binding := by
  have hsublist : List.Sublist (trimFor goals qterm binding) binding := by
    unfold trimFor trimSubst
    exact filterLiveSubst_sublist _ _ _
  simp only [resolutionSubstVars, List.mem_flatMap] at hname ⊢
  obtain ⟨entry, hentry, hmember⟩ := hname
  exact ⟨entry, hsublist.subset hentry, hmember⟩

theorem SubstEntriesAvoid.lookup (external generated : Subst)
    (havoid : SubstEntriesAvoid external generated)
    (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup generated name = some value) :
    Metta.Subst.lookup external name = none ∧ AtomAvoids external value := by
  induction generated with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      by_cases heq : name = key
      · subst key
        have htargetValue : target = value := by
          simpa [Metta.Subst.lookup] using hlookup
        subst value
        exact havoid (name, target) (by simp)
      · have hbeq : (name == key) = false := by simp [heq]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true,
          if_false] at hlookup
        apply ih
        · intro entry hentry
          exact havoid entry (by simp [hentry])
        · exact hlookup

private theorem lookup_append_local (left right : Subst) (name : String) :
    Metta.Subst.lookup (left ++ right) name =
      (Metta.Subst.lookup left name).orElse
        (fun _ => Metta.Subst.lookup right name) := by
  induction left with
  | nil => simp [Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [List.cons_append, Metta.Subst.lookup]
      by_cases hkey : (name == key) = true
      · rw [if_pos hkey, if_pos hkey]
        simp
      · rw [if_neg hkey, if_neg hkey]
        exact ih

private theorem lookup_map_values_local (transform : Atom → Atom)
    (b : Subst) (name : String) :
    Metta.Subst.lookup (b.map fun entry => (entry.1, transform entry.2)) name =
      (Metta.Subst.lookup b name).map transform := by
  induction b with
  | nil => simp [Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [List.map_cons, Metta.Subst.lookup]
      by_cases hkey : (name == key) = true
      · rw [if_pos hkey, if_pos hkey]
        simp
      · rw [if_neg hkey, if_neg hkey]
        exact ih

theorem lookup_compose (generated base : Subst) (name : String) :
    Metta.Subst.lookup (Metta.Subst.compose generated base) name =
      match Metta.Subst.lookup base name with
      | some value => some (Metta.Subst.apply generated value)
      | none => Metta.Subst.lookup generated name := by
  unfold Metta.Subst.compose
  rw [lookup_append_local, lookup_map_values_local]
  cases Metta.Subst.lookup base name <;> rfl

private theorem apply_variable_origin (generated : Subst) :
    ∀ a dependency, dependency ∈ (Metta.Subst.apply generated a).vars →
      (dependency ∈ a.vars ∧
          Metta.Subst.lookup generated dependency = none) ∨
        ∃ source value, source ∈ a.vars ∧
          Metta.Subst.lookup generated source = some value ∧
          dependency ∈ value.vars := by
  intro a
  induction a with
  | sym symbol => simp [Metta.Subst.apply, Atom.vars]
  | var source =>
      intro dependency hdependency
      simp only [Metta.Subst.apply] at hdependency
      cases hlookup : Metta.Subst.lookup generated source with
      | none =>
          simp only [Option.getD, hlookup, Atom.vars,
            List.mem_singleton] at hdependency
          subst dependency
          exact Or.inl ⟨by simp [Atom.vars], hlookup⟩
      | some value =>
          simp [hlookup] at hdependency
          exact Or.inr ⟨source, value, by simp [Atom.vars], hlookup,
            hdependency⟩
  | gnd ground => simp [Metta.Subst.apply, Atom.vars]
  | expr atoms atomIH =>
      intro dependency hdependency
      simp only [Metta.Subst.apply, Atom.vars] at hdependency
      rw [List.mem_flatten] at hdependency
      rcases hdependency with ⟨variableList, hvariableList, hdependency⟩
      rcases List.mem_map.mp hvariableList with
        ⟨substitutedChild, hsubstitutedChild, rfl⟩
      rcases List.mem_map.mp hsubstitutedChild with
        ⟨child, hchild, rfl⟩
      rcases atomIH child hchild dependency hdependency with
        hfree | ⟨source, value, hsource, hlookup, hvalue⟩
      · exact Or.inl ⟨by
          simp only [Atom.vars]
          rw [List.mem_flatten]
          exact ⟨child.vars, List.mem_map_of_mem hchild, hfree.1⟩,
          hfree.2⟩
      · exact Or.inr ⟨source, value, by
          simp only [Atom.vars]
          rw [List.mem_flatten]
          exact ⟨child.vars, List.mem_map_of_mem hchild, hsource⟩,
          hlookup, hvalue⟩

def SubstTopological.compose_of_avoids (base generated : Subst)
    (baseTopological : SubstTopological base)
    (generatedTopological : SubstTopological generated)
    (havoid : SubstEntriesAvoid base generated) :
    SubstTopological (Metta.Subst.compose generated base) := by
  have generatedNotMemOfBaseLookup (name : String) (value : Atom)
      (hlookup : Metta.Subst.lookup base name = some value) :
      name ∉ generatedTopological.order := by
    intro hmem
    have hbound := (generatedTopological.domain name).1 hmem
    cases hgenerated : Metta.Subst.lookup generated name with
    | none => exact hbound hgenerated
    | some generatedValue =>
        have hbaseNone :=
          (SubstEntriesAvoid.lookup base generated havoid name
            generatedValue hgenerated).1
        rw [hlookup] at hbaseNone
        contradiction
  refine
    { order := generatedTopological.order ++ baseTopological.order
      nodup := ?_
      domain := ?_
      decreases := ?_ }
  · apply List.nodup_append.mpr
    refine ⟨generatedTopological.nodup, baseTopological.nodup, ?_⟩
    intro generatedName hgeneratedName baseName hbaseName heq
    subst baseName
    have hgeneratedBound :=
      (generatedTopological.domain generatedName).1 hgeneratedName
    cases hgenerated : Metta.Subst.lookup generated generatedName with
    | none => exact hgeneratedBound hgenerated
    | some generatedValue =>
        have hbaseNone :=
          (SubstEntriesAvoid.lookup base generated havoid generatedName
            generatedValue hgenerated).1
        exact (baseTopological.domain generatedName).1 hbaseName hbaseNone
  · intro name
    rw [List.mem_append, generatedTopological.domain name,
      baseTopological.domain name, lookup_compose]
    cases Metta.Subst.lookup base name <;>
      cases Metta.Subst.lookup generated name <;> simp
  · intro source value dependency hsource hdependency hdependencyBound
    rw [lookup_compose generated base source] at hsource
    rw [lookup_compose generated base dependency] at hdependencyBound
    cases hbaseSource : Metta.Subst.lookup base source with
    | none =>
        rw [hbaseSource] at hsource
        have hsourceAvoid :=
          SubstEntriesAvoid.lookup base generated havoid source value hsource
        have hdependencyBase : Metta.Subst.lookup base dependency = none :=
          hsourceAvoid.2 dependency hdependency
        rw [hdependencyBase] at hdependencyBound
        have hsourceMem : source ∈ generatedTopological.order :=
          (generatedTopological.domain source).2 (by simp [hsource])
        have hdependencyMem : dependency ∈ generatedTopological.order :=
          (generatedTopological.domain dependency).2 hdependencyBound
        have hdecreases := generatedTopological.decreases source value
          dependency hsource hdependency hdependencyBound
        simpa [List.idxOf_append, hsourceMem, hdependencyMem] using hdecreases
    | some baseValue =>
        rw [hbaseSource] at hsource
        have hvalue : value = Metta.Subst.apply generated baseValue :=
          Option.some.inj hsource.symm
        subst value
        have hsourceNotGenerated :=
          generatedNotMemOfBaseLookup source baseValue hbaseSource
        rcases apply_variable_origin generated baseValue dependency hdependency
          with hfree | ⟨generatedSource, generatedValue, hgeneratedSource,
            hgeneratedLookup, hgeneratedDependency⟩
        · cases hbaseDependency : Metta.Subst.lookup base dependency with
          | none =>
              rw [hbaseDependency] at hdependencyBound
              exact False.elim (hdependencyBound hfree.2)
          | some dependencyValue =>
              have hdependencyNotGenerated :=
                generatedNotMemOfBaseLookup dependency dependencyValue
                  hbaseDependency
              have hdecreases := baseTopological.decreases source baseValue
                dependency hbaseSource hfree.1 (by simp [hbaseDependency])
              simpa [List.idxOf_append, hsourceNotGenerated,
                hdependencyNotGenerated] using
                Nat.add_lt_add_right hdecreases
                  generatedTopological.order.length
        · have hgeneratedAvoid :=
            SubstEntriesAvoid.lookup base generated havoid generatedSource
              generatedValue hgeneratedLookup
          have hdependencyBase : Metta.Subst.lookup base dependency = none :=
            hgeneratedAvoid.2 dependency hgeneratedDependency
          rw [hdependencyBase] at hdependencyBound
          have hdependencyMem : dependency ∈ generatedTopological.order :=
            (generatedTopological.domain dependency).2 hdependencyBound
          have hdependencyRank : generatedTopological.order.idxOf dependency <
              generatedTopological.order.length :=
            List.idxOf_lt_length_of_mem hdependencyMem
          simp only [List.idxOf_append, hdependencyMem,
            hsourceNotGenerated, if_true, if_false]
          omega

/-- `unifyB` preserves the elimination-order certificate.  The unifier runs
    on the fully resolved images of its arguments, so its generated domain and
    ranges avoid the old domain; the two certificates can therefore be stacked
    with the new unifier block before the old block. -/
def unifyB_topological (b : Subst) (left right : Atom) (result : Subst)
    (topological : SubstTopological b)
    (hresult : unifyB b left right = some result) :
    SubstTopological result := by
  unfold unifyB at hresult
  cases hexact : unifyTopExact (subst b left) (subst b right) with
  | none => simp [hexact] at hresult
  | some generated =>
      have hunify : Metta.Unify.unifyTopWith prologGroundIdentical
          (subst b left) (subst b right) = some generated :=
        unifyTopExact_some_underlying _ _ _ hexact
      cases generated with
      | nil =>
          simp [hexact] at hresult
          subst result
          exact topological
      | cons binding rest =>
          have hgeneratedTopological :
              SubstTopological (binding :: rest) :=
            unifyTopWith_topological prologGroundIdentical (subst b left)
              (subst b right)
              (binding :: rest) hunify
          have hleft : AtomAvoids b (subst b left) := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain b topological left
              name hname
          have hright : AtomAvoids b (subst b right) := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain b topological right
              name hname
          have hgeneratedAvoid : SubstEntriesAvoid b (binding :: rest) :=
            unifyTopWith_avoidsExternal prologGroundIdentical b
              (subst b left) (subst b right) (binding :: rest) hleft hright
              hunify
          simp [hexact] at hresult
          subst result
          exact SubstTopological.compose_of_avoids b (binding :: rest)
            topological hgeneratedTopological hgeneratedAvoid

/-- A successful `unifyB` result semantically extends its incoming
    substitution.  Deep substitution by the result absorbs an earlier deep
    substitution by `base`; this is the denotational extension property
    needed to carry equations established by earlier specialization guards
    through later guards. -/
theorem unifyB_absorbs_base (base : Subst) (left right : Atom)
    (result : Subst) (baseTopological : SubstTopological base)
    (hresult : unifyB base left right = some result) (atom : Atom) :
    subst result (subst base atom) = subst result atom := by
  unfold unifyB at hresult
  cases hexact : unifyTopExact (subst base left) (subst base right) with
  | none => simp [hexact] at hresult
  | some generated =>
      have hunify : Metta.Unify.unifyTopWith prologGroundIdentical
          (subst base left) (subst base right) = some generated :=
        unifyTopExact_some_underlying _ _ _ hexact
      cases generated with
      | nil =>
          simp [hexact] at hresult
          subst result
          have hbaseDenotes : SubstLookupDenotes base base := by
            intro name value hlookup
            exact baseTopological.subst_var_of_lookup base name value hlookup
          exact subst_subst_of_lookupDenotes base base hbaseDenotes atom
      | cons binding rest =>
          let generated : Subst := binding :: rest
          have hgeneratedTopological : SubstTopological generated :=
            unifyTopWith_topological prologGroundIdentical (subst base left)
              (subst base right) generated hunify
          have hleftAvoid : AtomAvoids base (subst base left) := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain base baseTopological
              left name hname
          have hrightAvoid : AtomAvoids base (subst base right) := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain base baseTopological
              right name hname
          have hgeneratedAvoid : SubstEntriesAvoid base generated :=
            unifyTopWith_avoidsExternal prologGroundIdentical base
              (subst base left) (subst base right) generated hleftAvoid
              hrightAvoid hunify
          simp [hexact] at hresult
          subst result
          let composed := Metta.Subst.compose generated base
          have hcomposedTopological : SubstTopological composed :=
            SubstTopological.compose_of_avoids base generated
              baseTopological hgeneratedTopological hgeneratedAvoid
          have hgeneratedDenotes :
              SubstLookupDenotes composed generated := by
            intro name value hlookup
            have havoid := SubstEntriesAvoid.lookup base generated
              hgeneratedAvoid name value hlookup
            have hcomposedLookup :
                Metta.Subst.lookup composed name = some value := by
              rw [lookup_compose]
              simp [havoid.1, hlookup]
            exact hcomposedTopological.subst_var_of_lookup composed name value
              hcomposedLookup
          have hbaseDenotes : SubstLookupDenotes composed base := by
            intro name value hlookup
            have hcomposedLookup : Metta.Subst.lookup composed name =
                some (Metta.Subst.apply generated value) := by
              rw [lookup_compose, hlookup]
            have hlookupDenotation :=
              hcomposedTopological.subst_var_of_lookup composed name
                (Metta.Subst.apply generated value) hcomposedLookup
            exact hlookupDenotation.trans
              (subst_apply_of_lookupDenotes composed generated
                hgeneratedDenotes value)
          exact subst_subst_of_lookupDenotes composed base hbaseDenotes atom

/-- Every denotational equality already established by the incoming
    substitution survives a successful later unification. -/
theorem unifyB_preserves_denotation (base : Subst) (left right : Atom)
    (result : Subst) (baseTopological : SubstTopological base)
    (hresult : unifyB base left right = some result)
    (x y : Atom) (hequal : subst base x = subst base y) :
    subst result x = subst result y := by
  calc
    subst result x = subst result (subst base x) :=
      (unifyB_absorbs_base base left right result baseTopological hresult x).symm
    _ = subst result (subst base y) := congrArg (subst result) hequal
    _ = subst result y :=
      unifyB_absorbs_base base left right result baseTopological hresult y

/-! ## Exact soundness on exactly unifiable inputs -/

/-- A deep substitution propositionally unifies every equation in a list. -/
private def DeepUnifies (binding : Subst)
    (equations : List (Atom × Atom)) : Prop :=
  ∀ equation, equation ∈ equations →
    subst binding equation.1 = subst binding equation.2

/-- A deep substitution propositionally realizes every variable constraint. -/
private def DeepRealizesConstraints (binding : Subst)
    (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    subst binding (Atom.var constraint.1) = subst binding constraint.2

/-- Every lookup already present in `before` remains identical in `after`. -/
private def LookupExtends (after before : Subst) : Prop :=
  ∀ name value, Metta.Subst.lookup before name = some value →
    Metta.Subst.lookup after name = some value

private structure ExactUnifyEvidence (result base : Subst)
    (equations : List (Atom × Atom)) where
  topological : SubstTopological result
  unifies : DeepUnifies result equations
  lookupExtension : LookupExtends result base

private theorem atomSize_le_sum_of_mem_unification {atom : Atom} :
    (atoms : List Atom) → atom ∈ atoms →
      atom.size ≤ (atoms.map Atom.size).sum
  | [], hmem => by simp at hmem
  | head :: tail, hmem => by
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (atomSize_le_sum_of_mem_unification tail htail)
          (Nat.le_add_left _ _)

/-- Deep substitution fixes any atom whose remaining variables are outside
its lookup domain. This is a substitution theorem, shared by resolution and
specialization proofs. -/
theorem subst_eq_self_of_domain_free (binding : Subst) :
    (atom : Atom) →
      (∀ name, name ∈ atom.vars →
        Metta.Subst.lookup binding name = none) →
      subst binding atom = atom
  | .sym name, _ => by simp
  | .var name, free => subst_var_of_lookup_none binding name
      (free name (by simp [Atom.vars]))
  | .gnd ground, _ => by simp
  | .expr atoms, free => by
      simp only [subst_expr, Atom.expr.injEq]
      rw [List.map_congr_left (fun child childMem => by
        apply subst_eq_self_of_domain_free binding child
        intro name nameMem
        apply free name
        simp only [Atom.vars]
        rw [List.mem_flatten]
        exact ⟨child.vars, List.mem_map_of_mem childMem, nameMem⟩)]
      simp
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_unification atoms childMem)

/-- Applying one equation as a one-pass substitution is invisible to any
    deep substitution that already realizes that equation. -/
private theorem subst_apply_singleton_of_eq (runtime : Subst)
    (name : String) (target : Atom)
    (heq : subst runtime (Atom.var name) = subst runtime target) :
    (atom : Atom) →
      subst runtime (Metta.Subst.apply [(name, target)] atom) =
        subst runtime atom
  | .sym symbol => by simp [Metta.Subst.apply]
  | .gnd ground => by simp [Metta.Subst.apply]
  | .var varName => by
      by_cases hname : varName = name
      · subst varName
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using heq.symm
      · simp [Metta.Subst.apply, Metta.Subst.lookup, hname]
  | .expr atoms => by
      simp only [Metta.Subst.apply, subst_expr, Atom.expr.injEq,
        List.map_map]
      rw [List.map_congr_left]
      intro child hchild
      exact subst_apply_singleton_of_eq runtime name target heq child
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_unification atoms hchild)

mutual

/-- Exact unification of an equation propositionally realizes every variable
    constraint produced by structural decomposition. -/
private theorem decomposeEqWith_deepRealizes
    (groundEq : Ground → Ground → Bool) (witness : Subst)
    (left right : Atom) (constraints : List (String × Atom))
    (heq : subst witness left = subst witness right)
    (hdecompose :
      Metta.Unify.decomposeEqWith groundEq left right = some constraints) :
    DeepRealizesConstraints witness constraints := by
  cases left with
  | sym leftName =>
      cases right with
      | sym rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          · cases hdecompose
            simp [DeepRealizesConstraints]
          · contradiction
      | var name =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq.symm
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | var name =>
      cases right with
      | sym rightName =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq
      | var rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          · cases hdecompose
            simp [DeepRealizesConstraints]
          · cases hdecompose
            intro constraint hmem
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact heq
      | gnd ground =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq
      | expr atoms =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq
  | gnd leftGround =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq.symm
      | gnd rightGround =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          · cases hdecompose
            simp [DeepRealizesConstraints]
          · contradiction
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | expr leftAtoms =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          intro constraint hmem
          simp only [List.mem_singleton] at hmem
          cases hmem
          exact heq.symm
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr rightAtoms =>
          simp only [subst_expr, Atom.expr.injEq] at heq
          exact decomposeListWith_deepRealizes groundEq witness leftAtoms
            rightAtoms constraints heq hdecompose

private theorem decomposeListWith_deepRealizes
    (groundEq : Ground → Ground → Bool) (witness : Subst)
    (left right : List Atom) (constraints : List (String × Atom))
    (heq : left.map (subst witness) = right.map (subst witness))
    (hdecompose :
      Metta.Unify.decomposeListWith groundEq left right = some constraints) :
    DeepRealizesConstraints witness constraints := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          cases hdecompose
          simp [DeepRealizesConstraints]
      | cons rightHead rightTail => simp at heq
  | cons leftHead leftTail =>
      cases right with
      | nil => simp at heq
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at heq
          simp only [Metta.Unify.decomposeListWith] at hdecompose
          cases hhead :
              Metta.Unify.decomposeEqWith groundEq leftHead rightHead with
          | none => simp [hhead] at hdecompose
          | some headConstraints =>
              cases htail :
                  Metta.Unify.decomposeListWith groundEq leftTail rightTail with
              | none => simp [hhead, htail] at hdecompose
              | some tailConstraints =>
                  simp [hhead, htail] at hdecompose
                  cases hdecompose
                  intro constraint hmem
                  rcases List.mem_append.mp hmem with hmem | hmem
                  · exact decomposeEqWith_deepRealizes groundEq witness
                      leftHead rightHead headConstraints heq.1 hhead constraint
                      hmem
                  · exact decomposeListWith_deepRealizes groundEq witness
                      leftTail rightTail tailConstraints heq.2 htail constraint
                      hmem

end

/-- Exact unification of every input equation realizes the flattened
    constraint list returned by `decomposeAll`. -/
private theorem decomposeAllWith_deepRealizes
    (groundEq : Ground → Ground → Bool) (witness : Subst)
    (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (hunifies : DeepUnifies witness equations)
    (hdecompose :
      Metta.Unify.decomposeAllWith groundEq equations = some constraints) :
    DeepRealizesConstraints witness constraints := by
  induction equations generalizing constraints with
  | nil =>
      cases hdecompose
      simp [DeepRealizesConstraints]
  | cons equation rest ih =>
      rcases equation with ⟨left, right⟩
      simp only [Metta.Unify.decomposeAllWith] at hdecompose
      cases hhead : Metta.Unify.decomposeEqWith groundEq left right with
      | none => simp [hhead] at hdecompose
      | some headConstraints =>
          cases hrest : Metta.Unify.decomposeAllWith groundEq rest with
          | none => simp [hhead, hrest] at hdecompose
          | some restConstraints =>
              simp [hhead, hrest] at hdecompose
              cases hdecompose
              intro constraint hmem
              rcases List.mem_append.mp hmem with hmem | hmem
              · exact decomposeEqWith_deepRealizes groundEq witness left right
                  headConstraints (hunifies (left, right) (by simp)) hhead
                  constraint hmem
              · exact ih restConstraints
                  (fun pair hpair => hunifies pair (by simp [hpair])) hrest
                  constraint hmem

mutual

/-- If the input equation has some exact unifier, realizing its decomposed
    variable constraints is enough to recover propositional equality for the
    original equation.  The witness rules out a `Ground.equiv`-only clash. -/
private theorem decomposeEqWith_exact_of_realized
    (groundEq : Ground → Ground → Bool) (witness result : Subst)
    (left right : Atom) (constraints : List (String × Atom))
    (hwitness : subst witness left = subst witness right)
    (hdecompose :
      Metta.Unify.decomposeEqWith groundEq left right = some constraints)
    (hrealizes : DeepRealizesConstraints result constraints) :
    subst result left = subst result right := by
  cases left with
  | sym leftName =>
      cases right with
      | sym rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          next heq =>
            have hname : leftName = rightName := by simpa using heq
            subst rightName
            rfl
          next hne => contradiction
      | var name =>
          cases hdecompose
          exact (hrealizes (name, Atom.sym leftName) (by simp)).symm
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | var name =>
      cases right with
      | sym rightName =>
          cases hdecompose
          exact hrealizes (name, Atom.sym rightName) (by simp)
      | var rightName =>
          simp only [Metta.Unify.decomposeEqWith] at hdecompose
          split at hdecompose
          next heq =>
            have hname : name = rightName := by simpa using heq
            subst rightName
            rfl
          next hne =>
            cases hdecompose
            exact hrealizes (name, Atom.var rightName) (by simp)
      | gnd ground =>
          cases hdecompose
          exact hrealizes (name, Atom.gnd ground) (by simp)
      | expr atoms =>
          cases hdecompose
          exact hrealizes (name, Atom.expr atoms) (by simp)
  | gnd leftGround =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          exact (hrealizes (name, Atom.gnd leftGround) (by simp)).symm
      | gnd rightGround =>
          simpa using hwitness
      | expr atoms => simp [Metta.Unify.decomposeEqWith] at hdecompose
  | expr leftAtoms =>
      cases right with
      | sym rightName => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | var name =>
          cases hdecompose
          exact (hrealizes (name, Atom.expr leftAtoms) (by simp)).symm
      | gnd ground => simp [Metta.Unify.decomposeEqWith] at hdecompose
      | expr rightAtoms =>
          simp only [subst_expr, Atom.expr.injEq] at hwitness ⊢
          exact decomposeListWith_exact_of_realized groundEq witness result
            leftAtoms rightAtoms constraints hwitness hdecompose hrealizes

private theorem decomposeListWith_exact_of_realized
    (groundEq : Ground → Ground → Bool) (witness result : Subst)
    (left right : List Atom) (constraints : List (String × Atom))
    (hwitness : left.map (subst witness) = right.map (subst witness))
    (hdecompose :
      Metta.Unify.decomposeListWith groundEq left right = some constraints)
    (hrealizes : DeepRealizesConstraints result constraints) :
    left.map (subst result) = right.map (subst result) := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at hwitness
  | cons leftHead leftTail =>
      cases right with
      | nil => simp at hwitness
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at hwitness ⊢
          simp only [Metta.Unify.decomposeListWith] at hdecompose
          cases hhead :
              Metta.Unify.decomposeEqWith groundEq leftHead rightHead with
          | none => simp [hhead] at hdecompose
          | some headConstraints =>
              cases htail :
                  Metta.Unify.decomposeListWith groundEq leftTail rightTail with
              | none => simp [hhead, htail] at hdecompose
              | some tailConstraints =>
                  simp [hhead, htail] at hdecompose
                  cases hdecompose
                  have hheadRealizes :
                      DeepRealizesConstraints result headConstraints := by
                    intro constraint hmem
                    exact hrealizes constraint
                      (List.mem_append_left tailConstraints hmem)
                  have htailRealizes :
                      DeepRealizesConstraints result tailConstraints := by
                    intro constraint hmem
                    exact hrealizes constraint
                      (List.mem_append_right headConstraints hmem)
                  exact ⟨
                    decomposeEqWith_exact_of_realized groundEq witness result
                      leftHead rightHead headConstraints hwitness.1 hhead
                      hheadRealizes,
                    decomposeListWith_exact_of_realized groundEq witness result
                      leftTail rightTail tailConstraints hwitness.2 htail
                      htailRealizes⟩

end

/-- Reconstruct exact equality for every equation from realized flattened
    constraints, using an exact witness only to exclude runtime-numeric slack. -/
private theorem decomposeAllWith_exact_of_realized
    (groundEq : Ground → Ground → Bool) (witness result : Subst)
    (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (hwitness : DeepUnifies witness equations)
    (hdecompose :
      Metta.Unify.decomposeAllWith groundEq equations = some constraints)
    (hrealizes : DeepRealizesConstraints result constraints) :
    DeepUnifies result equations := by
  induction equations generalizing constraints with
  | nil => simp [DeepUnifies]
  | cons equation rest ih =>
      rcases equation with ⟨left, right⟩
      simp only [Metta.Unify.decomposeAllWith] at hdecompose
      cases hhead : Metta.Unify.decomposeEqWith groundEq left right with
      | none => simp [hhead] at hdecompose
      | some headConstraints =>
          cases hrest : Metta.Unify.decomposeAllWith groundEq rest with
          | none => simp [hhead, hrest] at hdecompose
          | some restConstraints =>
              simp [hhead, hrest] at hdecompose
              cases hdecompose
              have hheadRealizes :
                  DeepRealizesConstraints result headConstraints := by
                intro constraint hmem
                exact hrealizes constraint
                  (List.mem_append_left restConstraints hmem)
              have hrestRealizes :
                  DeepRealizesConstraints result restConstraints := by
                intro constraint hmem
                exact hrealizes constraint
                  (List.mem_append_right headConstraints hmem)
              intro pair hpair
              simp only [List.mem_cons] at hpair
              rcases hpair with hpair | hpair
              · cases hpair
                exact decomposeEqWith_exact_of_realized groundEq witness result
                  left right headConstraints (hwitness (left, right) (by simp))
                  hhead hheadRealizes
              · exact ih restConstraints
                  (fun item hitem => hwitness item (by simp [hitem])) hrest
                  hrestRealizes pair hpair

/-- The actual elimination loop is propositionally sound whenever its input
    equations have a propositional unifier.  Runtime-only numeric equality
    remains available on other inputs, but cannot leak into this theorem. -/
private def unifyRoundsWith_exact_sound_of_unifier
    (groundEq : Ground → Ground → Bool) (fuel : Nat)
    (equations : List (Atom × Atom)) (base result witness : Subst)
    (baseTopological : SubstTopological base)
    (hequations : EquationsAvoid base equations)
    (hwitness : DeepUnifies witness equations)
    (hresult :
      Metta.Unify.unifyRoundsWith groundEq fuel equations base =
        some result) :
    ExactUnifyEvidence result base equations := by
  induction fuel generalizing equations base result with
  | zero =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              have hrealizes : DeepRealizesConstraints base [] := by
                simp [DeepRealizesConstraints]
              exact ⟨baseTopological,
                decomposeAllWith_exact_of_realized groundEq witness base
                  equations [] hwitness hdecompose hrealizes,
                fun name value hlookup => hlookup⟩
          | cons constraint rest => simp [hdecompose] at hresult
  | succ fuel ih =>
      simp only [Metta.Unify.unifyRoundsWith] at hresult
      cases hdecompose : Metta.Unify.decomposeAllWith groundEq equations with
      | none => simp [hdecompose] at hresult
      | some constraints =>
          cases constraints with
          | nil =>
              simp [hdecompose] at hresult
              subst result
              have hrealizes : DeepRealizesConstraints base [] := by
                simp [DeepRealizesConstraints]
              exact ⟨baseTopological,
                decomposeAllWith_exact_of_realized groundEq witness base
                  equations [] hwitness hdecompose hrealizes,
                fun name value hlookup => hlookup⟩
          | cons constraint rest =>
              rcases constraint with ⟨name, target⟩
              by_cases hoccurs : Metta.Subst.occurs name target = true
              · simp [hdecompose, hoccurs] at hresult
              · have hoccursFalse :
                    Metta.Subst.occurs name target = false := by
                  cases hvalue : Metta.Subst.occurs name target with
                  | false => rfl
                  | true => exact False.elim (hoccurs hvalue)
                have hconstraints :
                    ConstraintsAvoid base ((name, target) :: rest) :=
                  decomposeAllWith_avoids groundEq base equations
                    ((name, target) :: rest) hequations hdecompose
                have hheadAvoid := hconstraints (name, target) (by simp)
                have hname : name ∉ target.vars :=
                  not_mem_vars_of_occurs_eq_false name target hoccursFalse
                have hextend : Metta.Subst.extend base name target =
                    (name, target) :: base := by
                  simp [Metta.Subst.extend,
                    erase_eq_self_of_lookup_none base name hheadAvoid.1]
                have hnextTopological :
                    SubstTopological ((name, target) :: base) :=
                  SubstTopological.cons_of_fresh base baseTopological name
                    target hheadAvoid.1 hname hheadAvoid.2
                have hrestAvoid : ConstraintsAvoid base rest := by
                  intro item hitem
                  exact hconstraints item (by simp [hitem])
                let nextEquations := rest.map fun item =>
                  (Metta.Subst.apply [(name, target)] (Atom.var item.1),
                    Metta.Subst.apply [(name, target)] item.2)
                have hnextAvoid : EquationsAvoid
                    ((name, target) :: base) nextEquations := by
                  exact constraintMap_equationsAvoid base name target rest
                    hname hheadAvoid.2 hrestAvoid
                have hwitnessConstraints :
                    DeepRealizesConstraints witness
                      ((name, target) :: rest) :=
                  decomposeAllWith_deepRealizes groundEq witness equations
                    ((name, target) :: rest) hwitness hdecompose
                have hwitnessHead :
                    subst witness (Atom.var name) = subst witness target :=
                  hwitnessConstraints (name, target) (by simp)
                have hwitnessNext : DeepUnifies witness nextEquations := by
                  intro equation hequation
                  simp only [nextEquations, List.mem_map] at hequation
                  obtain ⟨item, hitem, rfl⟩ := hequation
                  have hitemEq := hwitnessConstraints item (by simp [hitem])
                  calc
                    subst witness
                        (Metta.Subst.apply [(name, target)]
                          (Atom.var item.1)) =
                        subst witness (Atom.var item.1) :=
                      subst_apply_singleton_of_eq witness name target
                        hwitnessHead (Atom.var item.1)
                    _ = subst witness item.2 := hitemEq
                    _ = subst witness
                        (Metta.Subst.apply [(name, target)] item.2) :=
                      (subst_apply_singleton_of_eq witness name target
                        hwitnessHead item.2).symm
                simp only [hdecompose, hoccursFalse, Bool.false_eq_true,
                  if_false] at hresult
                rw [hextend] at hresult
                have hrecursive := ih nextEquations
                  ((name, target) :: base) result hnextTopological hnextAvoid
                  hwitnessNext hresult
                rcases hrecursive with
                  ⟨resultTopological, hresultNext, hlookupNext⟩
                have hlookupHead :
                    Metta.Subst.lookup result name = some target := by
                  apply hlookupNext name target
                  simp [Metta.Subst.lookup]
                have hheadExact :
                    subst result (Atom.var name) = subst result target :=
                  resultTopological.subst_var_of_lookup result name target
                    hlookupHead
                have hresultConstraints : DeepRealizesConstraints result
                    ((name, target) :: rest) := by
                  intro item hitem
                  simp only [List.mem_cons] at hitem
                  rcases hitem with hitem | hitem
                  · cases hitem
                    exact hheadExact
                  · have hmapped :
                        (Metta.Subst.apply [(name, target)]
                            (Atom.var item.1),
                          Metta.Subst.apply [(name, target)] item.2) ∈
                          nextEquations := by
                        simpa [nextEquations] using
                          (List.mem_map_of_mem (f := fun entry : String × Atom =>
                            (Metta.Subst.apply [(name, target)]
                                (Atom.var entry.1),
                              Metta.Subst.apply [(name, target)] entry.2))
                            hitem)
                    have hnextEq := hresultNext _ hmapped
                    calc
                      subst result (Atom.var item.1) =
                          subst result
                            (Metta.Subst.apply [(name, target)]
                              (Atom.var item.1)) :=
                        (subst_apply_singleton_of_eq result name target
                          hheadExact (Atom.var item.1)).symm
                      _ = subst result
                            (Metta.Subst.apply [(name, target)] item.2) :=
                        hnextEq
                      _ = subst result item.2 :=
                        subst_apply_singleton_of_eq result name target
                          hheadExact item.2
                have hresultEquations : DeepUnifies result equations :=
                  decomposeAllWith_exact_of_realized groundEq witness result
                    equations ((name, target) :: rest) hwitness hdecompose
                    hresultConstraints
                have hlookupBase : LookupExtends result base := by
                  intro source value hlookup
                  apply hlookupNext source value
                  by_cases hsource : source = name
                  · subst source
                    rw [hheadAvoid.1] at hlookup
                    contradiction
                  · simpa [Metta.Subst.lookup, hsource] using hlookup
                exact ⟨resultTopological, hresultEquations, hlookupBase⟩

/-- Exact-input soundness for the concrete unifier.  This deliberately does
    not claim propositional soundness for every successful call: `1` and
    `1.0` are runtime-equivalent but have no exact unifier. -/
theorem unifyTopWith_exact_sound_of_exact_unifier
    (groundEq : Ground → Ground → Bool) (left right : Atom)
    (result witness : Subst)
    (hwitness : subst witness left = subst witness right)
    (hresult : Metta.Unify.unifyTopWith groundEq left right = some result) :
    subst result left = subst result right := by
  have hproof := unifyRoundsWith_exact_sound_of_unifier groundEq
    (Atom.size left + Atom.size right) [(left, right)] [] result witness
    emptySubstTopological (by
      intro equation hequation
      simp only [List.mem_singleton] at hequation
      subst equation
      constructor <;> simp [AtomAvoids, Metta.Subst.lookup])
    (by
      intro equation hequation
      simp only [List.mem_singleton] at hequation
      subst equation
      exact hwitness)
    hresult
  exact hproof.unifies (left, right) (by simp)

/-- Legacy specialization of exact-witness soundness to Hyperon's ordinary
ground equivalence. -/
theorem unifyTop_exact_sound_of_exact_unifier (left right : Atom)
    (result witness : Subst)
    (hwitness : subst witness left = subst witness right)
    (hresult : Metta.Unify.unifyTop left right = some result) :
    subst result left = subst result right := by
  apply unifyTopWith_exact_sound_of_exact_unifier Metta.Ground.equiv left
    right result witness hwitness
  simpa [Metta.Unify.unifyTopWith_groundEquiv] using hresult

/-- A concrete exact unifier witnesses acceptance of any candidate produced
by the shared unifier.  This packages the unifier's exact-input soundness with
the PeTTa numeric-constructor filter for callers that already carry a semantic
witness. -/
theorem unifyTopExact_of_exact_witness (left right : Atom)
    (result witness : Subst)
    (witnessExact : subst witness left = subst witness right)
    (underlying :
      Metta.Unify.unifyTopWith prologGroundIdentical left right =
        some result) :
    unifyTopExact left right = some result := by
  apply unifyTopExact_of_underlying_exact left right result underlying
  exact unifyTopWith_exact_sound_of_exact_unifier prologGroundIdentical left
    right result witness witnessExact underlying

/-- Exact-input soundness lifted through the machine's current-binding
    composition.  The proof uses denotational absorption of both component
    substitutions; it does not pretend one-pass `Subst.apply_compose` is a
    theorem about deep substitution. -/
theorem unifyB_exact_sound_of_exact_unifier (base : Subst)
    (left right : Atom) (result witness : Subst)
    (baseTopological : SubstTopological base)
    (hwitness :
      subst witness (subst base left) = subst witness (subst base right))
    (hresult : unifyB base left right = some result) :
    subst result left = subst result right := by
  unfold unifyB at hresult
  let resolvedLeft := subst base left
  let resolvedRight := subst base right
  cases hexact : unifyTopExact resolvedLeft resolvedRight with
  | none => simp [resolvedLeft, resolvedRight, hexact] at hresult
  | some generated =>
      have hunify : Metta.Unify.unifyTopWith prologGroundIdentical
          resolvedLeft resolvedRight = some generated :=
        unifyTopExact_some_underlying _ _ _ hexact
      cases generated with
      | nil =>
          simp [resolvedLeft, resolvedRight, hexact] at hresult
          subst result
          have hexact := unifyTopWith_exact_sound_of_exact_unifier
            prologGroundIdentical resolvedLeft resolvedRight [] witness
            hwitness hunify
          simpa [resolvedLeft, resolvedRight] using hexact
      | cons binding rest =>
          let generated : Subst := binding :: rest
          have hgeneratedTopological : SubstTopological generated :=
            unifyTopWith_topological prologGroundIdentical resolvedLeft
              resolvedRight generated hunify
          have hleftAvoid : AtomAvoids base resolvedLeft := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain base baseTopological
              left name (by simpa [resolvedLeft] using hname)
          have hrightAvoid : AtomAvoids base resolvedRight := by
            intro name hname
            exact SubstTopological.subst_resolvesDomain base baseTopological
              right name (by simpa [resolvedRight] using hname)
          have hgeneratedAvoid : SubstEntriesAvoid base generated :=
            unifyTopWith_avoidsExternal prologGroundIdentical base resolvedLeft
              resolvedRight generated hleftAvoid hrightAvoid hunify
          simp [resolvedLeft, resolvedRight, hexact] at hresult
          subst result
          let composed := Metta.Subst.compose generated base
          have hcomposedTopological : SubstTopological composed :=
            SubstTopological.compose_of_avoids base generated
              baseTopological hgeneratedTopological hgeneratedAvoid
          have hgeneratedDenotes :
              SubstLookupDenotes composed generated := by
            intro name value hlookup
            have havoid := SubstEntriesAvoid.lookup base generated
              hgeneratedAvoid name value hlookup
            have hcomposedLookup :
                Metta.Subst.lookup composed name = some value := by
              rw [lookup_compose]
              simp [havoid.1, hlookup]
            exact hcomposedTopological.subst_var_of_lookup composed name value
              hcomposedLookup
          have hbaseDenotes : SubstLookupDenotes composed base := by
            intro name value hlookup
            have hcomposedLookup : Metta.Subst.lookup composed name =
                some (Metta.Subst.apply generated value) := by
              rw [lookup_compose, hlookup]
            have hlookupDenotation :=
              hcomposedTopological.subst_var_of_lookup composed name
                (Metta.Subst.apply generated value) hcomposedLookup
            exact hlookupDenotation.trans
              (subst_apply_of_lookupDenotes composed generated
                hgeneratedDenotes value)
          have hgeneratedExact :=
            unifyTopWith_exact_sound_of_exact_unifier prologGroundIdentical
              resolvedLeft resolvedRight generated witness hwitness hunify
          have hlifted := congrArg (subst composed) hgeneratedExact
          calc
            subst composed left = subst composed (subst base left) :=
              (subst_subst_of_lookupDenotes composed base hbaseDenotes
                left).symm
            _ = subst composed (subst generated (subst base left)) :=
              (subst_subst_of_lookupDenotes composed generated
                hgeneratedDenotes (subst base left)).symm
            _ = subst composed (subst generated (subst base right)) := by
              simpa [resolvedLeft, resolvedRight] using hlifted
            _ = subst composed (subst base right) :=
              subst_subst_of_lookupDenotes composed generated
                hgeneratedDenotes (subst base right)
            _ = subst composed right :=
              subst_subst_of_lookupDenotes composed base hbaseDenotes right

/-! ## Exact completeness of the executable unifier -/

/-- Structural recursor exposing induction hypotheses for every child of an
    expression atom. -/
@[elab_as_elim]
private def unificationAtomRecAux {motive : Atom → Prop}
    (sym : ∀ name, motive (.sym name))
    («variable» : ∀ name, motive (.var name))
    (ground : ∀ value, motive (.gnd value))
    (expression :
      ∀ atoms, (∀ atom ∈ atoms, motive atom) → motive (.expr atoms)) :
    (atom : Atom) → motive atom
  | .sym name => sym name
  | .var name => «variable» name
  | .gnd value => ground value
  | .expr atoms =>
      expression atoms fun atom _member =>
        unificationAtomRecAux sym «variable» ground expression atom
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  have memberBound :=
    atomSize_le_sum_of_mem_unification atoms _member
  omega

/-- Every runtime atom contains no more variable occurrences than structural
    nodes.  Duplicate occurrences are retained on the left: this is the
    deliberately cheap upper bound used by `unifyTopWith`'s fuel argument. -/
private theorem atom_vars_length_le_size (atom : Atom) :
    atom.vars.length ≤ atom.size := by
  induction atom using unificationAtomRecAux with
  | sym => simp [Atom.vars, Atom.size]
  | «variable» => simp [Atom.vars, Atom.size]
  | ground => simp [Atom.vars, Atom.size]
  | expression atoms hypotheses =>
      simp only [Atom.vars, Atom.size, List.length_flatten, List.map_map]
      have sumBoundAux :
          ∀ items : List Atom,
            (∀ atom, atom ∈ items → atom.vars.length ≤ atom.size) →
            (items.map (fun atom => atom.vars.length)).sum ≤
              (items.map Atom.size).sum := by
        intro items pointwise
        induction items with
        | nil => simp
        | cons item items induction =>
            simp only [List.map_cons, List.sum_cons]
            exact Nat.add_le_add
              (pointwise item (by simp))
              (induction (fun atom member =>
                pointwise atom (by simp [member])))
      have sumBound :=
        sumBoundAux atoms hypotheses
      change
        (atoms.map (fun atom => atom.vars.length)).sum ≤
          1 + (atoms.map Atom.size).sum
      omega

/-- A finite deep substitution cannot erase an occurrence of a variable
    beneath a rigid runtime node. -/
private theorem subst_variable_size_le_of_mem_vars
    (bindings : Subst) (source : String) :
    (atom : Atom) → source ∈ atom.vars →
      (subst bindings (.var source)).size ≤ (subst bindings atom).size
  | .sym _, member => by simp [Atom.vars] at member
  | .var name, member => by
      simp only [Atom.vars, List.mem_singleton] at member
      subst name
      exact Nat.le_refl _
  | .gnd _, member => by simp [Atom.vars] at member
  | .expr atoms, member => by
      simp only [Atom.vars, List.mem_flatten, List.mem_map] at member
      obtain ⟨variableList, ⟨child, childMember, rfl⟩, sourceMember⟩ := member
      have childBound :=
        subst_variable_size_le_of_mem_vars bindings source child sourceMember
      simp only [subst_expr, Atom.size]
      have childSize :
          (subst bindings child).size ≤
            ((atoms.map (subst bindings)).map Atom.size).sum :=
        atomSize_le_sum_of_mem_unification
          (atoms.map (subst bindings))
          (List.mem_map.mpr ⟨child, childMember, rfl⟩)
      omega

/-- A proper finite occurrence is strictly larger after every finite deep
    substitution.  This is the runtime counterpart of the canonical
    `Tree.no_finite_unifier_of_occurs_true` theorem. -/
private theorem subst_variable_size_lt_of_mem_vars_of_ne
    (bindings : Subst) (source : String) :
    (atom : Atom) → source ∈ atom.vars → atom ≠ .var source →
      (subst bindings (.var source)).size < (subst bindings atom).size
  | .sym _, member, _ => by simp [Atom.vars] at member
  | .var name, member, different => by
      simp only [Atom.vars, List.mem_singleton] at member
      subst name
      exact False.elim (different rfl)
  | .gnd _, member, _ => by simp [Atom.vars] at member
  | .expr atoms, member, _ => by
      simp only [Atom.vars, List.mem_flatten, List.mem_map] at member
      obtain ⟨variableList, ⟨child, childMember, rfl⟩, sourceMember⟩ := member
      have childBound :=
        subst_variable_size_le_of_mem_vars bindings source child sourceMember
      simp only [subst_expr, Atom.size]
      have childSize :
          (subst bindings child).size ≤
            ((atoms.map (subst bindings)).map Atom.size).sum :=
        atomSize_le_sum_of_mem_unification
          (atoms.map (subst bindings))
          (List.mem_map.mpr ⟨child, childMember, rfl⟩)
      omega

/-- Boolean occurrence is membership in the executable atom's occurrence
    list. -/
private theorem mem_vars_of_occurs_eq_true (source : String) :
    (atom : Atom) → Metta.Subst.occurs source atom = true →
      source ∈ atom.vars
  | .sym _, present => by simp [Metta.Subst.occurs] at present
  | .var name, present => by
      simpa [Metta.Subst.occurs, Atom.vars] using present
  | .gnd _, present => by simp [Metta.Subst.occurs] at present
  | .expr atoms, present => by
      simp only [Metta.Subst.occurs, List.any_eq_true] at present
      obtain ⟨child, childPresent⟩ := present
      simp only [Atom.vars, List.mem_flatten, List.mem_map]
      exact ⟨child.val.vars, ⟨child.val, child.property, rfl⟩,
        mem_vars_of_occurs_eq_true source child.val childPresent.2⟩
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  have memberBound :=
    atomSize_le_sum_of_mem_unification atoms child.property
  omega

/-- Finite executable atoms have no cyclic exact unifier. -/
private theorem no_exact_unifier_of_occurs_true
    (bindings : Subst) (source : String) (atom : Atom)
    (present : Metta.Subst.occurs source atom = true)
    (different : atom ≠ .var source) :
    subst bindings (.var source) ≠ subst bindings atom := by
  intro equality
  have member := mem_vars_of_occurs_eq_true source atom present
  have strict :=
    subst_variable_size_lt_of_mem_vars_of_ne bindings source atom member
      different
  rw [equality] at strict
  exact Nat.lt_irrefl _ strict

/-- Variables of one decomposed constraint all originate in the input
    equation, and the constraint is never the reflexive equation it would
    have discarded during decomposition. -/
private def ConstraintSupported (allowed : List String)
    (constraint : String × Atom) : Prop :=
  constraint.1 ∈ allowed ∧
    (∀ name, name ∈ constraint.2.vars → name ∈ allowed) ∧
    constraint.2 ≠ .var constraint.1

private def ConstraintsSupported (allowed : List String)
    (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    ConstraintSupported allowed constraint

private theorem ConstraintsSupported.append
    (allowed : List String) (left right : List (String × Atom))
    (leftSupported : ConstraintsSupported allowed left)
    (rightSupported : ConstraintsSupported allowed right) :
    ConstraintsSupported allowed (left ++ right) := by
  intro constraint member
  rcases List.mem_append.mp member with member | member
  · exact leftSupported constraint member
  · exact rightSupported constraint member

mutual

/-- Structural decomposition preserves the complete finite variable support
    and never emits a reflexive variable constraint. -/
private theorem decomposeEqWith_supported
    (groundEq : Ground → Ground → Bool) (allowed : List String) :
    ∀ (left right : Atom) (constraints : List (String × Atom)),
      (∀ name, name ∈ left.vars → name ∈ allowed) →
      (∀ name, name ∈ right.vars → name ∈ allowed) →
      Metta.Unify.decomposeEqWith groundEq left right = some constraints →
      ConstraintsSupported allowed constraints
  | .sym leftName, .sym rightName, constraints, _, _, decomposed => by
      simp only [Metta.Unify.decomposeEqWith] at decomposed
      split at decomposed
      · cases decomposed
        simp [ConstraintsSupported]
      · contradiction
  | .sym leftName, .var name, constraints, _, rightSupported,
      decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨rightSupported name (by simp [Atom.vars]), ?_, ?_⟩
      · simp [Atom.vars]
      · intro impossible
        cases impossible
  | .sym _, .gnd _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .sym _, .expr _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .var name, .sym symbol, constraints, leftSupported, _, decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨leftSupported name (by simp [Atom.vars]), ?_, ?_⟩
      · simp [Atom.vars]
      · intro impossible
        cases impossible
  | .var name, .var target, constraints, leftSupported, rightSupported,
      decomposed => by
      simp only [Metta.Unify.decomposeEqWith] at decomposed
      split at decomposed
      next same =>
        cases decomposed
        simp [ConstraintsSupported]
      next different =>
        cases decomposed
        intro constraint member
        simp only [List.mem_singleton] at member
        subst constraint
        refine ⟨leftSupported name (by simp [Atom.vars]), ?_, ?_⟩
        · intro candidateName candidateMember
          simp only [Atom.vars, List.mem_singleton] at candidateMember
          subst candidateName
          exact rightSupported target (by simp [Atom.vars])
        · have namesDifferent : name ≠ target := by
            intro names
            subst target
            exact different (by simp)
          intro equality
          injection equality with reversed
          exact namesDifferent reversed.symm
  | .var name, .gnd ground, constraints, leftSupported, _, decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨leftSupported name (by simp [Atom.vars]), ?_, ?_⟩
      · simp [Atom.vars]
      · intro impossible
        cases impossible
  | .var name, .expr atoms, constraints, leftSupported, rightSupported,
      decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨leftSupported name (by simp [Atom.vars]), rightSupported, ?_⟩
      intro impossible
      cases impossible
  | .gnd _, .sym _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .gnd ground, .var name, constraints, leftSupported, rightSupported,
      decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨rightSupported name (by simp [Atom.vars]), ?_, ?_⟩
      · exact leftSupported
      · intro impossible
        cases impossible
  | .gnd leftGround, .gnd rightGround, constraints, _, _, decomposed => by
      simp only [Metta.Unify.decomposeEqWith] at decomposed
      split at decomposed
      · cases decomposed
        simp [ConstraintsSupported]
      · contradiction
  | .gnd _, .expr _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .expr _, .sym _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .expr atoms, .var name, constraints, leftSupported, rightSupported,
      decomposed => by
      cases decomposed
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      refine ⟨rightSupported name (by simp [Atom.vars]), leftSupported, ?_⟩
      intro impossible
      cases impossible
  | .expr _, .gnd _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeEqWith] at decomposed
  | .expr left, .expr right, constraints, leftSupported, rightSupported,
      decomposed =>
      decomposeListWith_supported groundEq allowed left right constraints
        (by
          intro atom atomMember name nameMember
          apply leftSupported name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨atom.vars, ⟨atom, atomMember, rfl⟩, nameMember⟩)
        (by
          intro atom atomMember name nameMember
          apply rightSupported name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨atom.vars, ⟨atom, atomMember, rfl⟩, nameMember⟩)
        decomposed

private theorem decomposeListWith_supported
    (groundEq : Ground → Ground → Bool) (allowed : List String) :
    ∀ (left right : List Atom) (constraints : List (String × Atom)),
      (∀ atom, atom ∈ left →
        ∀ name, name ∈ atom.vars → name ∈ allowed) →
      (∀ atom, atom ∈ right →
        ∀ name, name ∈ atom.vars → name ∈ allowed) →
      Metta.Unify.decomposeListWith groundEq left right = some constraints →
      ConstraintsSupported allowed constraints
  | [], [], constraints, _, _, decomposed => by
      cases decomposed
      simp [ConstraintsSupported]
  | [], _ :: _, _, _, _, decomposed => by
      simp [Metta.Unify.decomposeListWith] at decomposed
  | _ :: _, [], _, _, _, decomposed => by
      simp [Metta.Unify.decomposeListWith] at decomposed
  | leftHead :: leftTail, rightHead :: rightTail, constraints,
      leftSupported, rightSupported, decomposed => by
      simp only [Metta.Unify.decomposeListWith] at decomposed
      cases headDecomposition :
          Metta.Unify.decomposeEqWith groundEq leftHead rightHead with
      | none => simp [headDecomposition] at decomposed
      | some headConstraints =>
          cases tailDecomposition :
              Metta.Unify.decomposeListWith groundEq leftTail rightTail with
          | none => simp [headDecomposition, tailDecomposition] at decomposed
          | some tailConstraints =>
              simp [headDecomposition, tailDecomposition] at decomposed
              cases decomposed
              exact ConstraintsSupported.append allowed headConstraints
                tailConstraints
                (decomposeEqWith_supported groundEq allowed leftHead rightHead
                  headConstraints
                  (fun name member =>
                    leftSupported leftHead (by simp) name member)
                  (fun name member =>
                    rightSupported rightHead (by simp) name member)
                  headDecomposition)
                (decomposeListWith_supported groundEq allowed leftTail
                  rightTail tailConstraints
                  (fun atom member =>
                    leftSupported atom (by simp [member]))
                  (fun atom member =>
                    rightSupported atom (by simp [member]))
                  tailDecomposition)

end

/-- Worklist decomposition preserves the same support invariant. -/
private theorem decomposeAllWith_supported
    (groundEq : Ground → Ground → Bool) (allowed : List String)
    (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (supported :
      ∀ equation, equation ∈ equations →
        (∀ name, name ∈ equation.1.vars → name ∈ allowed) ∧
        (∀ name, name ∈ equation.2.vars → name ∈ allowed))
    (decomposed :
      Metta.Unify.decomposeAllWith groundEq equations = some constraints) :
    ConstraintsSupported allowed constraints := by
  induction equations generalizing constraints with
  | nil =>
      cases decomposed
      simp [ConstraintsSupported]
  | cons equation rest induction =>
      rcases equation with ⟨left, right⟩
      simp only [Metta.Unify.decomposeAllWith] at decomposed
      cases headDecomposition :
          Metta.Unify.decomposeEqWith groundEq left right with
      | none => simp [headDecomposition] at decomposed
      | some headConstraints =>
          cases tailDecomposition :
              Metta.Unify.decomposeAllWith groundEq rest with
          | none => simp [headDecomposition, tailDecomposition] at decomposed
          | some tailConstraints =>
              simp [headDecomposition, tailDecomposition] at decomposed
              cases decomposed
              exact ConstraintsSupported.append allowed headConstraints
                tailConstraints
                (decomposeEqWith_supported groundEq allowed left right
                  headConstraints
                  (supported (left, right) (by simp)).1
                  (supported (left, right) (by simp)).2
                  headDecomposition)
                (induction tailConstraints
                  (fun item member =>
                    supported item (by simp [member]))
                  tailDecomposition)

mutual

/-- A reflexive ground comparator lets every exactly unifiable finite atom
    pair decompose; no host-numeric equivalence is used. -/
private theorem decomposeEqWith_exists_of_exact_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (witness : Subst) :
    ∀ (left right : Atom),
      subst witness left = subst witness right →
      ∃ constraints,
        Metta.Unify.decomposeEqWith groundEq left right = some constraints
  | .sym leftName, .sym rightName, equal => by
      have names : leftName = rightName := by simpa using equal
      subst rightName
      exact ⟨[], by simp [Metta.Unify.decomposeEqWith]⟩
  | .sym leftName, .var name, _ => by
      exact ⟨[(name, .sym leftName)], rfl⟩
  | .sym _, .gnd _, equal => by simp at equal
  | .sym _, .expr _, equal => by simp [subst_expr] at equal
  | .var name, right, _ => by
      cases right with
      | var target =>
          by_cases same : name = target
          · subst target
            exact ⟨[], by simp [Metta.Unify.decomposeEqWith]⟩
          · exact ⟨[(name, .var target)], by
              simp [Metta.Unify.decomposeEqWith, same]⟩
      | sym symbol => exact ⟨[(name, .sym symbol)], rfl⟩
      | gnd ground => exact ⟨[(name, .gnd ground)], rfl⟩
      | expr atoms => exact ⟨[(name, .expr atoms)], rfl⟩
  | .gnd _, .sym _, equal => by simp at equal
  | .gnd ground, .var name, _ => by
      exact ⟨[(name, .gnd ground)], rfl⟩
  | .gnd leftGround, .gnd rightGround, equal => by
      have grounds : leftGround = rightGround := by simpa using equal
      subst rightGround
      exact ⟨[], by
        simp [Metta.Unify.decomposeEqWith, groundReflexive]⟩
  | .gnd _, .expr _, equal => by simp [subst_expr] at equal
  | .expr _, .sym _, equal => by simp [subst_expr] at equal
  | .expr atoms, .var name, _ => by
      exact ⟨[(name, .expr atoms)], rfl⟩
  | .expr _, .gnd _, equal => by simp [subst_expr] at equal
  | .expr left, .expr right, equal => by
      simp only [subst_expr, Atom.expr.injEq] at equal
      exact decomposeListWith_exists_of_exact_unifier groundEq
        groundReflexive witness left right equal

private theorem decomposeListWith_exists_of_exact_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (witness : Subst) :
    ∀ (left right : List Atom),
      left.map (subst witness) = right.map (subst witness) →
      ∃ constraints,
        Metta.Unify.decomposeListWith groundEq left right = some constraints
  | [], [], _ => ⟨[], rfl⟩
  | [], _ :: _, equal => by simp at equal
  | _ :: _, [], equal => by simp at equal
  | leftHead :: leftTail, rightHead :: rightTail, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨headConstraints, headDecomposition⟩ :=
        decomposeEqWith_exists_of_exact_unifier groundEq groundReflexive
          witness leftHead rightHead equal.1
      obtain ⟨tailConstraints, tailDecomposition⟩ :=
        decomposeListWith_exists_of_exact_unifier groundEq groundReflexive
          witness leftTail rightTail equal.2
      exact ⟨headConstraints ++ tailConstraints, by
        simp [Metta.Unify.decomposeListWith, headDecomposition,
          tailDecomposition]⟩

end

/-- Exact unifiability makes whole-worklist decomposition total. -/
private theorem decomposeAllWith_exists_of_exact_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (witness : Subst) (equations : List (Atom × Atom))
    (unifies : DeepUnifies witness equations) :
    ∃ constraints,
      Metta.Unify.decomposeAllWith groundEq equations = some constraints := by
  induction equations with
  | nil => exact ⟨[], rfl⟩
  | cons equation rest induction =>
      rcases equation with ⟨left, right⟩
      obtain ⟨headConstraints, headDecomposition⟩ :=
        decomposeEqWith_exists_of_exact_unifier groundEq groundReflexive
          witness left right (unifies (left, right) (by simp))
      obtain ⟨tailConstraints, tailDecomposition⟩ :=
        induction (fun item member => unifies item (by simp [member]))
      exact ⟨headConstraints ++ tailConstraints, by
        simp [Metta.Unify.decomposeAllWith, headDecomposition,
          tailDecomposition]⟩

/-- Variables introduced by one singleton application come either from an
    untouched source occurrence or from the replacement. -/
private theorem mem_vars_apply_singleton
    (source : String) (replacement : Atom) :
    (atom : Atom) → (name : String) →
      name ∈ (Metta.Subst.apply [(source, replacement)] atom).vars →
      (name ∈ atom.vars ∧ name ≠ source) ∨ name ∈ replacement.vars
  | .sym _, name, member => by simp [Metta.Subst.apply, Atom.vars] at member
  | .var original, name, member => by
      by_cases same : original = source
      · subst original
        right
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using member
      · left
        have nameEq : name = original := by
          simpa [Metta.Subst.apply, Metta.Subst.lookup, same, Atom.vars]
            using member
        subst name
        exact ⟨by simp [Atom.vars], same⟩
  | .gnd _, name, member => by simp [Metta.Subst.apply, Atom.vars] at member
  | .expr atoms, name, member => by
      simp only [Metta.Subst.apply, Atom.vars, List.mem_flatten] at member
      obtain ⟨variableList, variableListMember, nameMember⟩ := member
      obtain ⟨appliedChild, appliedChildMember, rfl⟩ :=
        List.mem_map.mp variableListMember
      obtain ⟨child, childMember, rfl⟩ :=
        List.mem_map.mp appliedChildMember
      rcases mem_vars_apply_singleton source replacement child name
          nameMember with original | replacementMember
      · left
        exact ⟨by
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, childMember, rfl⟩, original.1⟩,
          original.2⟩
      · exact Or.inr replacementMember

/-- Applying an acyclic supported replacement removes the selected variable
    while preserving every other variable inside the old finite support. -/
private theorem apply_singleton_vars_within_erase
    (allowed : List String) (source : String) (replacement atom : Atom)
    (replacementAllowed :
      ∀ name, name ∈ replacement.vars → name ∈ allowed)
    (sourceAbsent : source ∉ replacement.vars)
    (atomAllowed : ∀ name, name ∈ atom.vars → name ∈ allowed) :
    ∀ name,
      name ∈ (Metta.Subst.apply [(source, replacement)] atom).vars →
        name ∈ allowed.erase source := by
  intro name member
  rcases mem_vars_apply_singleton source replacement atom name member with
    original | replacementMember
  · exact (List.mem_erase_of_ne original.2).2
      (atomAllowed name original.1)
  · have different : name ≠ source := by
      intro same
      subst name
      exact sourceAbsent replacementMember
    exact (List.mem_erase_of_ne different).2
      (replacementAllowed name replacementMember)

/-- One list of distinct variable names supports every equation in a
    unification worklist. -/
private def EquationsSupported (allowed : List String)
    (equations : List (Atom × Atom)) : Prop :=
  ∀ equation, equation ∈ equations →
    (∀ name, name ∈ equation.1.vars → name ∈ allowed) ∧
    (∀ name, name ∈ equation.2.vars → name ∈ allowed)

/-- Every variable in the singleton-substituted residual worklist lies in
    the old support with the eliminated source removed. -/
private theorem constraintMap_supported_after_erase
    (allowed : List String) (source : String) (replacement : Atom)
    (rest : List (String × Atom))
    (headSupported : ConstraintSupported allowed (source, replacement))
    (sourceAbsent : source ∉ replacement.vars)
    (restSupported : ConstraintsSupported allowed rest) :
    EquationsSupported (allowed.erase source)
      (rest.map fun item =>
        (Metta.Subst.apply [(source, replacement)] (.var item.1),
          Metta.Subst.apply [(source, replacement)] item.2)) := by
  intro equation member
  simp only [List.mem_map] at member
  obtain ⟨constraint, constraintMember, rfl⟩ := member
  have supported := restSupported constraint constraintMember
  constructor
  · exact apply_singleton_vars_within_erase allowed source replacement
      (.var constraint.1) headSupported.2.1
      sourceAbsent
      (by
        intro name nameMember
        simp only [Atom.vars, List.mem_singleton] at nameMember
        subst name
        exact supported.1)
  · exact apply_singleton_vars_within_erase allowed source replacement
      constraint.2 headSupported.2.1
      sourceAbsent
      supported.2.1

/-- Erasing a member of a duplicate-free support strictly lowers its
    cardinality. -/
private theorem length_erase_lt_of_mem_nodup
    {name : String} {names : List String}
    (member : name ∈ names) (_nodup : names.Nodup) :
    (names.erase name).length < names.length := by
  have lengthEq := List.length_erase_add_one member
  omega

/-- The actual fuel-bounded elimination loop succeeds whenever a finite exact
    unifier exists and `fuel` covers a duplicate-free support for every
    remaining variable.  This is a verified algorithm theorem: neither
    success nor a result substitution is assumed. -/
private theorem unifyRoundsWith_complete_of_exact_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (fuel : Nat) (allowed : List String) (equations : List (Atom × Atom))
    (base witness : Subst)
    (allowedNodup : allowed.Nodup)
    (supported : EquationsSupported allowed equations)
    (fuelEnough : allowed.length ≤ fuel)
    (unifies : DeepUnifies witness equations) :
    ∃ result,
      Metta.Unify.unifyRoundsWith groundEq fuel equations base =
        some result := by
  induction fuel generalizing allowed equations base with
  | zero =>
      have allowedEmpty : allowed = [] := by
        exact List.eq_nil_of_length_eq_zero (by omega)
      obtain ⟨constraints, decomposed⟩ :=
        decomposeAllWith_exists_of_exact_unifier groundEq groundReflexive
          witness equations unifies
      have constraintsSupported :=
        decomposeAllWith_supported groundEq allowed equations constraints
          supported decomposed
      have constraintsEmpty : constraints = [] := by
        cases constraints with
        | nil => rfl
        | cons constraint rest =>
            have sourceAllowed :=
              (constraintsSupported constraint (by simp)).1
            rw [allowedEmpty] at sourceAllowed
            contradiction
      subst constraints
      exact ⟨base, by
        simp [Metta.Unify.unifyRoundsWith, decomposed]⟩
  | succ fuel induction =>
      obtain ⟨constraints, decomposed⟩ :=
        decomposeAllWith_exists_of_exact_unifier groundEq groundReflexive
          witness equations unifies
      have constraintsSupported :=
        decomposeAllWith_supported groundEq allowed equations constraints
          supported decomposed
      cases constraints with
      | nil =>
          exact ⟨base, by
            simp [Metta.Unify.unifyRoundsWith, decomposed]⟩
      | cons constraint rest =>
          rcases constraint with ⟨source, replacement⟩
          have headSupported :=
            constraintsSupported (source, replacement) (by simp)
          have restSupported : ConstraintsSupported allowed rest := by
            intro item member
            exact constraintsSupported item (by simp [member])
          have realized :=
            decomposeAllWith_deepRealizes groundEq witness equations
              ((source, replacement) :: rest) unifies decomposed
          have headExact :
              subst witness (.var source) = subst witness replacement :=
            realized (source, replacement) (by simp)
          have occursFalse :
              Metta.Subst.occurs source replacement = false := by
            cases occurs : Metta.Subst.occurs source replacement with
            | false => rfl
            | true =>
                exact False.elim
                  ((no_exact_unifier_of_occurs_true witness source replacement
                    occurs headSupported.2.2) headExact)
          let nextEquations := rest.map fun item =>
            (Metta.Subst.apply [(source, replacement)] (.var item.1),
              Metta.Subst.apply [(source, replacement)] item.2)
          have nextSupported :
              EquationsSupported (allowed.erase source) nextEquations := by
            exact constraintMap_supported_after_erase allowed source
              replacement rest headSupported
              (not_mem_vars_of_occurs_eq_false source replacement occursFalse)
              restSupported
          have nextNodup : (allowed.erase source).Nodup :=
            allowedNodup.erase source
          have nextFuelEnough :
              (allowed.erase source).length ≤ fuel := by
            have sourceAllowed : source ∈ allowed := headSupported.1
            have shorter : (allowed.erase source).length < allowed.length :=
              length_erase_lt_of_mem_nodup sourceAllowed allowedNodup
            omega
          have nextUnifies : DeepUnifies witness nextEquations := by
            intro equation equationMember
            simp only [nextEquations, List.mem_map] at equationMember
            obtain ⟨item, itemMember, rfl⟩ := equationMember
            have itemExact := realized item (by simp [itemMember])
            calc
              subst witness
                  (Metta.Subst.apply [(source, replacement)]
                    (.var item.1)) =
                  subst witness (.var item.1) :=
                subst_apply_singleton_of_eq witness source replacement
                  headExact (.var item.1)
              _ = subst witness item.2 := itemExact
              _ = subst witness
                  (Metta.Subst.apply [(source, replacement)] item.2) :=
                (subst_apply_singleton_of_eq witness source replacement
                  headExact item.2).symm
          obtain ⟨result, resultEq⟩ :=
            induction (allowed.erase source) nextEquations
              (Metta.Subst.extend base source replacement)
              nextNodup nextSupported nextFuelEnough nextUnifies
          exact ⟨result, by
            simpa [Metta.Unify.unifyRoundsWith, decomposed, occursFalse,
              nextEquations] using resultEq⟩

/-- The concrete executable first-order algorithm is complete on every
    finitely exactly unifiable input when its ground comparator is reflexive.
    In particular, fuel exhaustion cannot turn a genuine unifier into
    failure. -/
theorem unifyTopWith_complete_of_exact_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (left right : Atom) (witness : Subst)
    (exact : subst witness left = subst witness right) :
    ∃ result,
      Metta.Unify.unifyTopWith groundEq left right = some result := by
  let allowed := (left.vars ++ right.vars).dedup
  have allowedNodup : allowed.Nodup := List.nodup_dedup _
  have supported : EquationsSupported allowed [(left, right)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    constructor
    · intro name nameMember
      exact List.mem_dedup.mpr
        (List.mem_append_left right.vars nameMember)
    · intro name nameMember
      exact List.mem_dedup.mpr
        (List.mem_append_right left.vars nameMember)
  have fuelEnough :
      allowed.length ≤ left.size + right.size := by
    have dedupBound : allowed.length ≤ (left.vars ++ right.vars).length :=
      List.Sublist.length_le (List.dedup_sublist _)
    simp only [List.length_append] at dedupBound
    exact Nat.le_trans dedupBound
      (Nat.add_le_add (atom_vars_length_le_size left)
        (atom_vars_length_le_size right))
  unfold Metta.Unify.unifyTopWith
  exact unifyRoundsWith_complete_of_exact_unifier groundEq groundReflexive
    (left.size + right.size) allowed [(left, right)] [] witness
    allowedNodup supported fuelEnough (by
      intro equation member
      simp only [List.mem_singleton] at member
      subst equation
      exact exact)

/-- PeTTa's exact-ground specialization inherits constructive completeness,
    including reflexive NaN identity and finite occurs-check rejection. -/
theorem unifyTopExact_complete_of_exact_unifier
    (left right : Atom) (witness : Subst)
    (exact : subst witness left = subst witness right) :
    ∃ result, unifyTopExact left right = some result := by
  exact unifyTopWith_complete_of_exact_unifier prologGroundIdentical
    prologGroundIdentical_self left right witness exact

/-- Completeness lifted through the current binding: a finite exact witness
    for the normalized pair constructs an actual `unifyB` successor. -/
theorem unifyB_complete_of_exact_unifier
    (base : Subst) (left right : Atom) (witness : Subst)
    (exact :
      subst witness (subst base left) = subst witness (subst base right)) :
    ∃ result, unifyB base left right = some result := by
  obtain ⟨generated, generatedEq⟩ :=
    unifyTopExact_complete_of_exact_unifier
      (subst base left) (subst base right) witness exact
  cases generated with
  | nil =>
      exact ⟨base, by simp [unifyB, generatedEq]⟩
  | cons binding rest =>
      exact ⟨Metta.Subst.compose (binding :: rest) base, by
        simp [unifyB, generatedEq]⟩

/-- A repeated variable beneath a rigid node exercises both decomposition
    rounds and substitution propagation.  Completeness produces a real,
    nonempty executable result; exact-input soundness proves that result is
    not merely an arbitrary successful return. -/
theorem unifyTopExact_repeated_nested_complete_nontrivial :
    let left :=
      Atom.expr
        [.sym "p", .var "X", .expr [.sym "f", .var "X"]]
    let right :=
      Atom.expr
        [.sym "p", .sym "a", .expr [.sym "f", .sym "a"]]
    ∃ result,
      unifyTopExact left right = some result ∧
        subst result left = subst result right ∧
        result ≠ [] := by
  let left :=
    Atom.expr
      [.sym "p", .var "X", .expr [.sym "f", .var "X"]]
  let right :=
    Atom.expr
      [.sym "p", .sym "a", .expr [.sym "f", .sym "a"]]
  let witness : Subst := [("X", .sym "a")]
  have witnessExact : subst witness left = subst witness right := by
    simp [left, right, witness, subst, substN, Metta.Subst.lookup]
  obtain ⟨result, resultEq⟩ :=
    unifyTopExact_complete_of_exact_unifier left right witness witnessExact
  have underlying :=
    unifyTopExact_some_underlying left right result resultEq
  have resultExact :=
    unifyTopWith_exact_sound_of_exact_unifier prologGroundIdentical
      left right result witness witnessExact underlying
  have resultNonempty : result ≠ [] := by
    intro empty
    subst result
    simp [left, right, subst, substN, Metta.Subst.lookup] at resultExact
  exact ⟨result, resultEq, resultExact, resultNonempty⟩

/-- A finite self-occurrence has no exact substitution witness.  This
    semantic discriminator rules out proving completeness by accepting
    rational-tree cycles. -/
theorem finite_self_occurs_has_no_exact_unifier (source : String) :
    ¬ ∃ witness : Subst,
      subst witness (.var source) =
        subst witness (.expr [.sym "f", .var source]) := by
  rintro ⟨witness, exact⟩
  exact
    (no_exact_unifier_of_occurs_true witness source
      (.expr [.sym "f", .var source])
      (by simp [Metta.Subst.occurs])
      (by intro impossible; cases impossible)) exact

/-- The executable follows the finite-tree semantics on the same
    discriminator: its occurs check rejects the cyclic equation. -/
theorem unifyTopExact_self_occurs_rejected (source : String) :
    unifyTopExact (.var source)
      (.expr [.sym "f", .var source]) = none := by
  simp [unifyTopExact, Metta.Unify.unifyTopWith, Atom.size,
    Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith, Metta.Subst.occurs]

/-! ## Comparator-respecting completeness

Raw `Atom` equality is stronger than the identity relation passed to the
unifier.  In particular, SWI-Prolog identifies all IEEE NaN payloads while
Lean `Float` equality does not.  The following layer proves the executable
algorithm complete against the structural `AtomEquivalentWith` relation, so
the cross-representation Prolog bridge need not silently exclude NaN. -/

/-- One deep substitution unifies an ordered equation worklist modulo the
same grounded-leaf comparator used by the executable unifier. -/
def DeepEquivalentUnifies
    (groundEq : Ground → Ground → Bool) (binding : Subst)
    (equations : List (Atom × Atom)) : Prop :=
  ∀ equation, equation ∈ equations →
    AtomEquivalentWith groundEq
      (subst binding equation.1) (subst binding equation.2)

/-- Comparator-respecting realization of a flattened variable-constraint
worklist. -/
private def DeepEquivalentRealizes
    (groundEq : Ground → Ground → Bool) (binding : Subst)
    (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    AtomEquivalentWith groundEq
      (subst binding (.var constraint.1))
      (subst binding constraint.2)

mutual

  /-- Applying one variable equation is invisible modulo structural
  equivalence to any deep substitution that already realizes it. -/
  private theorem subst_apply_singleton_equivalent
      (groundEq : Ground → Ground → Bool)
      (groundReflexive : ∀ ground, groundEq ground ground = true)
      (groundSymmetric :
        ∀ {left right : Ground}, groundEq left right = true →
          groundEq right left = true)
      (runtime : Subst) (name : String) (target : Atom)
      (equivalent :
        AtomEquivalentWith groundEq
          (subst runtime (.var name)) (subst runtime target)) :
      (atom : Atom) →
        AtomEquivalentWith groundEq
          (subst runtime (Metta.Subst.apply [(name, target)] atom))
          (subst runtime atom)
    | .sym symbol => by
        simpa [Metta.Subst.apply] using
          (AtomEquivalentWith.symbol (groundEq := groundEq) symbol)
    | .gnd ground => by
        simpa [Metta.Subst.apply] using
          (AtomEquivalentWith.ground (groundEq := groundEq)
            (groundReflexive ground))
    | .var variableName => by
        by_cases same : variableName = name
        · subst variableName
          simpa [Metta.Subst.apply, Metta.Subst.lookup] using
            equivalent.symm groundSymmetric
        · simp only [Metta.Subst.apply, Metta.Subst.lookup]
          have nameCheck : (variableName == name) = false := by
            simpa [beq_iff_eq] using same
          rw [nameCheck]
          exact AtomEquivalentWith.refl groundReflexive
            (subst runtime (.var variableName))
    | .expr atoms => by
        simp only [Metta.Subst.apply, subst_expr]
        exact .expression
          (substs_apply_singleton_equivalent groundEq groundReflexive
            groundSymmetric runtime name target equivalent atoms)

  /-- Ordered-list companion to
  `subst_apply_singleton_equivalent`. -/
  private theorem substs_apply_singleton_equivalent
      (groundEq : Ground → Ground → Bool)
      (groundReflexive : ∀ ground, groundEq ground ground = true)
      (groundSymmetric :
        ∀ {left right : Ground}, groundEq left right = true →
          groundEq right left = true)
      (runtime : Subst) (name : String) (target : Atom)
      (equivalent :
        AtomEquivalentWith groundEq
          (subst runtime (.var name)) (subst runtime target)) :
      (atoms : List Atom) →
        AtomsEquivalentWith groundEq
          ((atoms.map (Metta.Subst.apply [(name, target)])).map
            (subst runtime))
          (atoms.map (subst runtime))
    | [] => .nil
    | atom :: atoms => .cons
        (subst_apply_singleton_equivalent groundEq groundReflexive
          groundSymmetric runtime name target equivalent atom)
        (substs_apply_singleton_equivalent groundEq groundReflexive
          groundSymmetric runtime name target equivalent atoms)

end

mutual

  /-- Comparator-respecting unification of one equation realizes every
  variable constraint produced by structural decomposition. -/
  private theorem decomposeEqWith_equivalentRealizes
      (groundEq : Ground → Ground → Bool)
      (groundSymmetric :
        ∀ {left right : Ground}, groundEq left right = true →
          groundEq right left = true)
      (witness : Subst) (left right : Atom)
      (constraints : List (String × Atom))
      (equivalent :
        AtomEquivalentWith groundEq
          (subst witness left) (subst witness right))
      (decomposed :
        Metta.Unify.decomposeEqWith groundEq left right =
          some constraints) :
      DeepEquivalentRealizes groundEq witness constraints := by
    cases left with
    | sym leftName =>
        simp only [subst_sym] at equivalent
        cases right with
        | sym rightName =>
            simp only [subst_sym] at equivalent
            cases equivalent
            simp [Metta.Unify.decomposeEqWith] at decomposed
            subst constraints
            simp [DeepEquivalentRealizes]
        | var name =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            simpa using equivalent.symm groundSymmetric
        | gnd ground =>
            simp only [subst_gnd] at equivalent
            cases equivalent
        | expr atoms =>
            simp only [subst_expr] at equivalent
            cases equivalent
    | var name =>
        cases right with
        | sym rightName =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            exact equivalent
        | var rightName =>
            simp only [Metta.Unify.decomposeEqWith] at decomposed
            split at decomposed
            next same =>
              have names : name = rightName := by simpa using same
              subst rightName
              cases decomposed
              simp [DeepEquivalentRealizes]
            next different =>
              cases decomposed
              intro constraint member
              simp only [List.mem_singleton] at member
              cases member
              exact equivalent
        | gnd ground =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            exact equivalent
        | expr atoms =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            exact equivalent
    | gnd leftGround =>
        simp only [subst_gnd] at equivalent
        cases right with
        | sym rightName =>
            simp only [subst_sym] at equivalent
            cases equivalent
        | var name =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            simpa using equivalent.symm groundSymmetric
        | gnd rightGround =>
            simp only [subst_gnd] at equivalent
            cases equivalent with
            | ground identical =>
                simp [Metta.Unify.decomposeEqWith, identical] at decomposed
                subst constraints
                simp [DeepEquivalentRealizes]
        | expr atoms =>
            simp only [subst_expr] at equivalent
            cases equivalent
    | expr leftAtoms =>
        simp only [subst_expr] at equivalent
        cases right with
        | sym rightName =>
            simp only [subst_sym] at equivalent
            cases equivalent
        | var name =>
            cases decomposed
            intro constraint member
            simp only [List.mem_singleton] at member
            cases member
            simpa using equivalent.symm groundSymmetric
        | gnd ground =>
            simp only [subst_gnd] at equivalent
            cases equivalent
        | expr rightAtoms =>
            simp only [subst_expr] at equivalent
            cases equivalent with
            | expression children =>
                exact decomposeListWith_equivalentRealizes groundEq
                  groundSymmetric witness leftAtoms rightAtoms constraints
                  children decomposed

  /-- Ordered-list companion to
  `decomposeEqWith_equivalentRealizes`. -/
  private theorem decomposeListWith_equivalentRealizes
      (groundEq : Ground → Ground → Bool)
      (groundSymmetric :
        ∀ {left right : Ground}, groundEq left right = true →
          groundEq right left = true)
      (witness : Subst) (left right : List Atom)
      (constraints : List (String × Atom))
      (equivalent :
        AtomsEquivalentWith groundEq
          (left.map (subst witness)) (right.map (subst witness)))
      (decomposed :
        Metta.Unify.decomposeListWith groundEq left right =
          some constraints) :
      DeepEquivalentRealizes groundEq witness constraints := by
    cases left with
    | nil =>
        cases right with
        | nil =>
            cases decomposed
            simp [DeepEquivalentRealizes]
        | cons rightHead rightTail => cases equivalent
    | cons leftHead leftTail =>
        cases right with
        | nil => cases equivalent
        | cons rightHead rightTail =>
            cases equivalent with
            | cons headEquivalent tailEquivalent =>
                simp only [Metta.Unify.decomposeListWith] at decomposed
                cases headDecomposition :
                    Metta.Unify.decomposeEqWith groundEq leftHead rightHead with
                | none => simp [headDecomposition] at decomposed
                | some headConstraints =>
                    cases tailDecomposition :
                        Metta.Unify.decomposeListWith groundEq
                          leftTail rightTail with
                    | none =>
                        simp [headDecomposition, tailDecomposition]
                          at decomposed
                    | some tailConstraints =>
                        simp [headDecomposition, tailDecomposition]
                          at decomposed
                        cases decomposed
                        intro constraint member
                        rcases List.mem_append.mp member with
                          headMember | tailMember
                        · exact
                            decomposeEqWith_equivalentRealizes groundEq
                              groundSymmetric witness leftHead rightHead
                              headConstraints headEquivalent
                              headDecomposition constraint headMember
                        · exact
                            decomposeListWith_equivalentRealizes groundEq
                              groundSymmetric witness leftTail rightTail
                              tailConstraints tailEquivalent
                              tailDecomposition constraint tailMember

end

/-- Comparator-respecting unification of every input equation realizes the
flattened structural constraint worklist. -/
private theorem decomposeAllWith_equivalentRealizes
    (groundEq : Ground → Ground → Bool)
    (groundSymmetric :
      ∀ {left right : Ground}, groundEq left right = true →
        groundEq right left = true)
    (witness : Subst) (equations : List (Atom × Atom))
    (constraints : List (String × Atom))
    (unifies : DeepEquivalentUnifies groundEq witness equations)
    (decomposed :
      Metta.Unify.decomposeAllWith groundEq equations = some constraints) :
    DeepEquivalentRealizes groundEq witness constraints := by
  induction equations generalizing constraints with
  | nil =>
      cases decomposed
      simp [DeepEquivalentRealizes]
  | cons equation rest induction =>
      rcases equation with ⟨left, right⟩
      simp only [Metta.Unify.decomposeAllWith] at decomposed
      cases headDecomposition :
          Metta.Unify.decomposeEqWith groundEq left right with
      | none => simp [headDecomposition] at decomposed
      | some headConstraints =>
          cases tailDecomposition :
              Metta.Unify.decomposeAllWith groundEq rest with
          | none => simp [headDecomposition, tailDecomposition] at decomposed
          | some tailConstraints =>
              simp [headDecomposition, tailDecomposition] at decomposed
              cases decomposed
              intro constraint member
              rcases List.mem_append.mp member with
                headMember | tailMember
              · exact decomposeEqWith_equivalentRealizes groundEq
                  groundSymmetric witness left right headConstraints
                  (unifies (left, right) (by simp)) headDecomposition
                  constraint headMember
              · exact induction tailConstraints
                  (fun item itemMember =>
                    unifies item (by simp [itemMember]))
                  tailDecomposition constraint tailMember

mutual

  /-- Structural equivalence under the chosen ground comparator makes
  decomposition total; unlike the raw-equality theorem, this admits
  comparator-identical but propositionally distinct grounds. -/
  private theorem decomposeEqWith_exists_of_equivalent_unifier
      (groundEq : Ground → Ground → Bool) (witness : Subst) :
      ∀ (left right : Atom),
        AtomEquivalentWith groundEq
          (subst witness left) (subst witness right) →
        ∃ constraints,
          Metta.Unify.decomposeEqWith groundEq left right =
            some constraints
    | .sym leftName, .sym rightName, equivalent => by
        simp only [subst_sym] at equivalent
        cases equivalent
        exact ⟨[], by simp [Metta.Unify.decomposeEqWith]⟩
    | .sym leftName, .var name, _ =>
        ⟨[(name, .sym leftName)], rfl⟩
    | .sym leftName, .gnd ground, equivalent => by
        simp only [subst_sym, subst_gnd] at equivalent
        cases equivalent
    | .sym leftName, .expr atoms, equivalent => by
        simp only [subst_sym, subst_expr] at equivalent
        cases equivalent
    | .var name, right, _ => by
        cases right with
        | var target =>
            by_cases same : name = target
            · subst target
              exact ⟨[], by simp [Metta.Unify.decomposeEqWith]⟩
            · exact ⟨[(name, .var target)], by
                simp [Metta.Unify.decomposeEqWith, same]⟩
        | sym symbol => exact ⟨[(name, .sym symbol)], rfl⟩
        | gnd ground => exact ⟨[(name, .gnd ground)], rfl⟩
        | expr atoms => exact ⟨[(name, .expr atoms)], rfl⟩
    | .gnd leftGround, .sym rightName, equivalent => by
        simp only [subst_gnd, subst_sym] at equivalent
        cases equivalent
    | .gnd ground, .var name, _ =>
        ⟨[(name, .gnd ground)], rfl⟩
    | .gnd leftGround, .gnd rightGround, equivalent => by
        simp only [subst_gnd] at equivalent
        cases equivalent with
        | ground identical =>
            exact ⟨[], by
              simp [Metta.Unify.decomposeEqWith, identical]⟩
    | .gnd leftGround, .expr atoms, equivalent => by
        simp only [subst_gnd, subst_expr] at equivalent
        cases equivalent
    | .expr atoms, .sym rightName, equivalent => by
        simp only [subst_expr, subst_sym] at equivalent
        cases equivalent
    | .expr atoms, .var name, _ =>
        ⟨[(name, .expr atoms)], rfl⟩
    | .expr atoms, .gnd ground, equivalent => by
        simp only [subst_expr, subst_gnd] at equivalent
        cases equivalent
    | .expr left, .expr right, equivalent => by
        simp only [subst_expr] at equivalent
        cases equivalent with
        | expression children =>
            exact decomposeListWith_exists_of_equivalent_unifier
              groundEq witness left right children

  /-- Ordered-list companion to
  `decomposeEqWith_exists_of_equivalent_unifier`. -/
  private theorem decomposeListWith_exists_of_equivalent_unifier
      (groundEq : Ground → Ground → Bool) (witness : Subst) :
      ∀ (left right : List Atom),
        AtomsEquivalentWith groundEq
          (left.map (subst witness)) (right.map (subst witness)) →
        ∃ constraints,
          Metta.Unify.decomposeListWith groundEq left right =
            some constraints
    | [], [], _ => ⟨[], rfl⟩
    | [], _ :: _, equivalent => by cases equivalent
    | _ :: _, [], equivalent => by cases equivalent
    | leftHead :: leftTail, rightHead :: rightTail, equivalent => by
        cases equivalent with
        | cons headEquivalent tailEquivalent =>
            obtain ⟨headConstraints, headDecomposition⟩ :=
              decomposeEqWith_exists_of_equivalent_unifier groundEq witness
                leftHead rightHead headEquivalent
            obtain ⟨tailConstraints, tailDecomposition⟩ :=
              decomposeListWith_exists_of_equivalent_unifier groundEq witness
                leftTail rightTail tailEquivalent
            exact ⟨headConstraints ++ tailConstraints, by
              simp [Metta.Unify.decomposeListWith, headDecomposition,
                tailDecomposition]⟩

end

/-- Comparator-respecting unifiability makes whole-worklist decomposition
total. -/
private theorem decomposeAllWith_exists_of_equivalent_unifier
    (groundEq : Ground → Ground → Bool) (witness : Subst)
    (equations : List (Atom × Atom))
    (unifies : DeepEquivalentUnifies groundEq witness equations) :
    ∃ constraints,
      Metta.Unify.decomposeAllWith groundEq equations = some constraints := by
  induction equations with
  | nil => exact ⟨[], rfl⟩
  | cons equation rest induction =>
      rcases equation with ⟨left, right⟩
      obtain ⟨headConstraints, headDecomposition⟩ :=
        decomposeEqWith_exists_of_equivalent_unifier groundEq witness
          left right (unifies (left, right) (by simp))
      obtain ⟨tailConstraints, tailDecomposition⟩ :=
        induction (fun item member => unifies item (by simp [member]))
      exact ⟨headConstraints ++ tailConstraints, by
        simp [Metta.Unify.decomposeAllWith, headDecomposition,
          tailDecomposition]⟩

/-- A proper finite occurrence cannot be unified even modulo a structural
ground comparator: equivalence preserves shape and therefore finite size. -/
private theorem no_equivalent_unifier_of_occurs_true
    (groundEq : Ground → Ground → Bool)
    (bindings : Subst) (source : String) (atom : Atom)
    (present : Metta.Subst.occurs source atom = true)
    (different : atom ≠ .var source)
    (equivalent :
      AtomEquivalentWith groundEq
        (subst bindings (.var source)) (subst bindings atom)) :
    False := by
  have member := mem_vars_of_occurs_eq_true source atom present
  have strict :=
    subst_variable_size_lt_of_mem_vars_of_ne bindings source atom member
      different
  have sameSize := equivalent.size_eq
  omega

/-- The actual fuel-bounded elimination loop succeeds whenever a finite
comparator-respecting unifier exists.  Ground equivalence must itself be an
equivalence relation; every other part of the relation is structural and
fixed by `AtomEquivalentWith`. -/
private theorem unifyRoundsWith_complete_of_equivalent_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (groundSymmetric :
      ∀ {left right : Ground}, groundEq left right = true →
        groundEq right left = true)
    (groundTransitive :
      ∀ {first second third : Ground},
        groundEq first second = true →
        groundEq second third = true →
        groundEq first third = true)
    (fuel : Nat) (allowed : List String)
    (equations : List (Atom × Atom)) (base witness : Subst)
    (allowedNodup : allowed.Nodup)
    (supported : EquationsSupported allowed equations)
    (fuelEnough : allowed.length ≤ fuel)
    (unifies : DeepEquivalentUnifies groundEq witness equations) :
    ∃ result,
      Metta.Unify.unifyRoundsWith groundEq fuel equations base =
        some result := by
  induction fuel generalizing allowed equations base with
  | zero =>
      have allowedEmpty : allowed = [] := by
        exact List.eq_nil_of_length_eq_zero (by omega)
      obtain ⟨constraints, decomposed⟩ :=
        decomposeAllWith_exists_of_equivalent_unifier groundEq witness
          equations unifies
      have constraintsSupported :=
        decomposeAllWith_supported groundEq allowed equations constraints
          supported decomposed
      have constraintsEmpty : constraints = [] := by
        cases constraints with
        | nil => rfl
        | cons constraint rest =>
            have sourceAllowed :=
              (constraintsSupported constraint (by simp)).1
            rw [allowedEmpty] at sourceAllowed
            contradiction
      subst constraints
      exact ⟨base, by
        simp [Metta.Unify.unifyRoundsWith, decomposed]⟩
  | succ fuel induction =>
      obtain ⟨constraints, decomposed⟩ :=
        decomposeAllWith_exists_of_equivalent_unifier groundEq witness
          equations unifies
      have constraintsSupported :=
        decomposeAllWith_supported groundEq allowed equations constraints
          supported decomposed
      cases constraints with
      | nil =>
          exact ⟨base, by
            simp [Metta.Unify.unifyRoundsWith, decomposed]⟩
      | cons constraint rest =>
          rcases constraint with ⟨source, replacement⟩
          have headSupported :=
            constraintsSupported (source, replacement) (by simp)
          have restSupported : ConstraintsSupported allowed rest := by
            intro item member
            exact constraintsSupported item (by simp [member])
          have realized :=
            decomposeAllWith_equivalentRealizes groundEq groundSymmetric
              witness equations ((source, replacement) :: rest)
              unifies decomposed
          have headEquivalent :
              AtomEquivalentWith groundEq
                (subst witness (.var source))
                (subst witness replacement) :=
            realized (source, replacement) (by simp)
          have occursFalse :
              Metta.Subst.occurs source replacement = false := by
            cases occurs : Metta.Subst.occurs source replacement with
            | false => rfl
            | true =>
                exact False.elim
                  (no_equivalent_unifier_of_occurs_true groundEq witness
                    source replacement occurs headSupported.2.2
                    headEquivalent)
          let nextEquations := rest.map fun item =>
            (Metta.Subst.apply [(source, replacement)] (.var item.1),
              Metta.Subst.apply [(source, replacement)] item.2)
          have nextSupported :
              EquationsSupported (allowed.erase source) nextEquations := by
            exact constraintMap_supported_after_erase allowed source
              replacement rest headSupported
              (not_mem_vars_of_occurs_eq_false source replacement occursFalse)
              restSupported
          have nextNodup : (allowed.erase source).Nodup :=
            allowedNodup.erase source
          have nextFuelEnough :
              (allowed.erase source).length ≤ fuel := by
            have sourceAllowed : source ∈ allowed := headSupported.1
            have shorter : (allowed.erase source).length < allowed.length :=
              length_erase_lt_of_mem_nodup sourceAllowed allowedNodup
            omega
          have nextUnifies :
              DeepEquivalentUnifies groundEq witness nextEquations := by
            intro equation equationMember
            simp only [nextEquations, List.mem_map] at equationMember
            obtain ⟨item, itemMember, rfl⟩ := equationMember
            have itemEquivalent := realized item (by simp [itemMember])
            have leftInvisible :=
              subst_apply_singleton_equivalent groundEq groundReflexive
                groundSymmetric witness source replacement headEquivalent
                (.var item.1)
            have rightInvisible :=
              subst_apply_singleton_equivalent groundEq groundReflexive
                groundSymmetric witness source replacement headEquivalent
                item.2
            have throughOriginal :=
              AtomEquivalentWith.trans (groundEq := groundEq)
                groundTransitive leftInvisible itemEquivalent
            have rightBack :=
              AtomEquivalentWith.symm (groundEq := groundEq)
                groundSymmetric rightInvisible
            exact AtomEquivalentWith.trans (groundEq := groundEq)
              groundTransitive throughOriginal rightBack
          obtain ⟨result, resultEq⟩ :=
            induction (allowed.erase source) nextEquations
              (Metta.Subst.extend base source replacement)
              nextNodup nextSupported nextFuelEnough nextUnifies
          exact ⟨result, by
            simpa [Metta.Unify.unifyRoundsWith, decomposed, occursFalse,
              nextEquations] using resultEq⟩

/-- The concrete comparator-parametric first-order algorithm is complete for
every finite witness under the structural equivalence induced by an
equivalence-relation ground comparator.  This is strictly more general than
`unifyTopWith_complete_of_exact_unifier`: comparator-identical grounded
leaves need not be propositionally equal Lean values. -/
theorem unifyTopWith_complete_of_equivalent_unifier
    (groundEq : Ground → Ground → Bool)
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    (groundSymmetric :
      ∀ {left right : Ground}, groundEq left right = true →
        groundEq right left = true)
    (groundTransitive :
      ∀ {first second third : Ground},
        groundEq first second = true →
        groundEq second third = true →
        groundEq first third = true)
    (left right : Atom) (witness : Subst)
    (equivalent :
      AtomEquivalentWith groundEq
        (subst witness left) (subst witness right)) :
    ∃ result,
      Metta.Unify.unifyTopWith groundEq left right = some result := by
  let allowed := (left.vars ++ right.vars).dedup
  have allowedNodup : allowed.Nodup := List.nodup_dedup _
  have supported : EquationsSupported allowed [(left, right)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    constructor
    · intro name nameMember
      exact List.mem_dedup.mpr
        (List.mem_append_left right.vars nameMember)
    · intro name nameMember
      exact List.mem_dedup.mpr
        (List.mem_append_right left.vars nameMember)
  have fuelEnough :
      allowed.length ≤ left.size + right.size := by
    have dedupBound : allowed.length ≤ (left.vars ++ right.vars).length :=
      List.Sublist.length_le (List.dedup_sublist _)
    simp only [List.length_append] at dedupBound
    exact Nat.le_trans dedupBound
      (Nat.add_le_add (atom_vars_length_le_size left)
        (atom_vars_length_le_size right))
  unfold Metta.Unify.unifyTopWith
  exact unifyRoundsWith_complete_of_equivalent_unifier
    groundEq groundReflexive groundSymmetric groundTransitive
    (left.size + right.size) allowed [(left, right)] [] witness
    allowedNodup supported fuelEnough (by
      intro equation member
      simp only [List.mem_singleton] at member
      subst equation
      exact equivalent)

/-- PeTTa's exact Prolog-ground specialization is complete for the actual
SWI term-identity relation, including distinct IEEE NaN payloads that share
the single Prolog `nan` identity. -/
theorem unifyTopExact_complete_of_prolog_equivalent_unifier
    (left right : Atom) (witness : Subst)
    (equivalent :
      AtomEquivalentWith prologGroundIdentical
        (subst witness left) (subst witness right)) :
    ∃ result, unifyTopExact left right = some result := by
  exact unifyTopWith_complete_of_equivalent_unifier
    prologGroundIdentical prologGroundIdentical_self
    (fun identical => prologGroundIdentical_symm identical)
    (fun firstSecond secondThird =>
      prologGroundIdentical_trans firstSecond secondThird)
    left right witness equivalent

/-- Comparator-respecting completeness lifted through the machine's current
binding. -/
theorem unifyB_complete_of_prolog_equivalent_unifier
    (base : Subst) (left right : Atom) (witness : Subst)
    (equivalent :
      AtomEquivalentWith prologGroundIdentical
        (subst witness (subst base left))
        (subst witness (subst base right))) :
    ∃ result, unifyB base left right = some result := by
  obtain ⟨generated, generatedEq⟩ :=
    unifyTopExact_complete_of_prolog_equivalent_unifier
      (subst base left) (subst base right) witness equivalent
  cases generated with
  | nil =>
      exact ⟨base, by simp [unifyB, generatedEq]⟩
  | cons binding rest =>
      exact ⟨Metta.Subst.compose (binding :: rest) base, by
        simp [unifyB, generatedEq]⟩

/-- Any two IEEE NaN payloads denote the one SWI-Prolog `nan` term.  The
payload hypotheses are explicit because Lean's primitive `Float` operations
are opaque to kernel reduction; executable concrete-bit guards live in
`Regression.lean`. -/
theorem nan_payloads_are_prolog_equivalent
    (left right : Float)
    (leftNan : left.isNaN = true)
    (rightNan : right.isNaN = true) :
    AtomEquivalentWith prologGroundIdentical
      (.gnd (.float left)) (.gnd (.float right)) := by
  apply AtomEquivalentWith.ground
  simp [prologGroundIdentical, PrologFloatIdentity.ofFloat,
    leftNan, rightNan]

/-- The stronger completeness theorem reaches the NaN discriminator:
payload equality is neither assumed nor needed for the executable unifier to
accept the two grounds through their one Prolog identity. -/
theorem unifyTopExact_nan_payloads_complete
    (left right : Float)
    (leftNan : left.isNaN = true)
    (rightNan : right.isNaN = true) :
    ∃ result,
      unifyTopExact (.gnd (.float left)) (.gnd (.float right)) =
        some result := by
  apply unifyTopExact_complete_of_prolog_equivalent_unifier
    (.gnd (.float left)) (.gnd (.float right)) []
  simpa using
    (nan_payloads_are_prolog_equivalent
      left right leftNan rightNan)

/-! ## Fresh structural variants -/

mutual

/-- `copied` is obtained from `source` by the single variable renaming
    `fresh`.  Ground leaves are unchanged; the PeTTa/Prolog comparator is
    reflexive for every executable ground payload, including NaN. -/
inductive FreshVariant (fresh : String → String) : Atom → Atom → Prop where
  | sym (name : String) :
      FreshVariant fresh (Atom.sym name) (Atom.sym name)
  | varSame (name : String) :
      FreshVariant fresh (Atom.var name) (Atom.var name)
  | var (name : String) (hne : fresh name ≠ name) :
      FreshVariant fresh (Atom.var (fresh name)) (Atom.var name)
  | gnd (ground : Metta.Ground) :
      FreshVariant fresh (Atom.gnd ground) (Atom.gnd ground)
  | expr {copied source : List Atom} :
      FreshVariantList fresh copied source →
      FreshVariant fresh (Atom.expr copied) (Atom.expr source)

/-- Pointwise list relation for one shared fresh-variable map.  Reusing the
    same function across the list records residual-variable sharing rather
    than validating each occurrence independently. -/
inductive FreshVariantList (fresh : String → String) :
    List Atom → List Atom → Prop where
  | nil : FreshVariantList fresh [] []
  | cons {copied source copiedRest sourceRest} :
      FreshVariant fresh copied source →
      FreshVariantList fresh copiedRest sourceRest →
      FreshVariantList fresh (copied :: copiedRest)
        (source :: sourceRest)

end

mutual

/-- Substitution on the copied side preserves the structural-variant
    relation when source variables remain free and each copied variable is
    either still fresh or has already been identified with its source by an
    earlier guard. -/
theorem FreshVariant.subst_left {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (base : Subst)
    (hsourceFixed : ∀ name, name ∈ source.vars →
      subst base (Atom.var name) = Atom.var name)
    (hfreshState : ∀ name, name ∈ source.vars →
      subst base (Atom.var (fresh name)) = Atom.var (fresh name) ∨
        subst base (Atom.var (fresh name)) = Atom.var name) :
    FreshVariant fresh (subst base copied) source := by
  cases variant with
  | sym name => simpa using FreshVariant.sym (fresh := fresh) name
  | varSame name =>
      simpa [hsourceFixed name (by simp [Atom.vars])] using
        FreshVariant.varSame (fresh := fresh) name
  | var name hne =>
      rcases hfreshState name (by simp [Atom.vars]) with hstill | halready
      · simpa [hstill] using FreshVariant.var (fresh := fresh) name hne
      · simpa [halready] using FreshVariant.varSame (fresh := fresh) name
  | gnd ground =>
      simpa using FreshVariant.gnd (fresh := fresh) ground
  | @expr copiedAtoms sourceAtoms variants =>
      have hchildren : FreshVariantList fresh
          (copiedAtoms.map (subst base)) sourceAtoms := by
        apply variants.subst_left base
        · intro name hname
          exact hsourceFixed name (by simpa [Atom.vars] using hname)
        · intro name hname
          exact hfreshState name (by simpa [Atom.vars] using hname)
      simpa [subst_expr] using FreshVariant.expr hchildren

/-- List companion to `FreshVariant.subst_left`. -/
theorem FreshVariantList.subst_left {fresh : String → String}
    {copied source : List Atom}
    (variants : FreshVariantList fresh copied source) (base : Subst)
    (hsourceFixed : ∀ name,
      name ∈ (source.map Atom.vars).flatten →
        subst base (Atom.var name) = Atom.var name)
    (hfreshState : ∀ name,
      name ∈ (source.map Atom.vars).flatten →
        subst base (Atom.var (fresh name)) = Atom.var (fresh name) ∨
          subst base (Atom.var (fresh name)) = Atom.var name) :
    FreshVariantList fresh (copied.map (subst base)) source := by
  cases variants with
  | nil => exact .nil
  | @cons copiedHead sourceHead copiedTail sourceTail head tail =>
      apply FreshVariantList.cons
      · apply head.subst_left base
        · intro name hname
          apply hsourceFixed name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inl hname
        · intro name hname
          apply hfreshState name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inl hname
      · apply tail.subst_left base
        · intro name hname
          apply hsourceFixed name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inr hname
        · intro name hname
          apply hfreshState name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inr hname

end

mutual

/-- One-pass application of the canonical finite witness turns the copied
    side of a structural variant back into its source exactly. -/
theorem FreshVariant.apply_witness {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (allowed : List String)
    (hsubset : ∀ name, name ∈ source.vars → name ∈ allowed)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ copiedName, copiedName ∈ allowed →
      ∀ sourceName, sourceName ∈ allowed →
        fresh copiedName ≠ sourceName) :
    Metta.Subst.apply (freshVariantWitness fresh allowed) copied = source := by
  cases variant with
  | sym name => simp [Metta.Subst.apply]
  | varSame name =>
      have hname : name ∈ allowed := hsubset name (by simp [Atom.vars])
      have hlookup := freshVariantWitness_lookup_source_none fresh allowed
        hdisjoint name hname
      simp [Metta.Subst.apply, hlookup]
  | var name hne =>
      have hname : name ∈ allowed := hsubset name (by simp [Atom.vars])
      have hlookup := freshVariantWitness_lookup_fresh fresh allowed hinjective
        name hname
      simp [Metta.Subst.apply, hlookup]
  | gnd ground => simp [Metta.Subst.apply]
  | @expr copiedAtoms sourceAtoms variants =>
      have hchildren :
          copiedAtoms.map
              (Metta.Subst.apply (freshVariantWitness fresh allowed)) =
            sourceAtoms := by
        exact variants.apply_witness allowed (by
          intro name hname
          apply hsubset name
          simpa [Atom.vars] using hname) hinjective hdisjoint
      simpa [Metta.Subst.apply] using congrArg Atom.expr hchildren

/-- List companion to `FreshVariant.apply_witness`. -/
theorem FreshVariantList.apply_witness {fresh : String → String}
    {copied source : List Atom}
    (variants : FreshVariantList fresh copied source)
    (allowed : List String)
    (hsubset : ∀ name, name ∈ (source.map Atom.vars).flatten →
      name ∈ allowed)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ copiedName, copiedName ∈ allowed →
      ∀ sourceName, sourceName ∈ allowed →
        fresh copiedName ≠ sourceName) :
    copied.map (Metta.Subst.apply (freshVariantWitness fresh allowed)) =
      source := by
  cases variants with
  | nil => rfl
  | @cons copiedHead sourceHead copiedTail sourceTail head tail =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply head.apply_witness allowed
        · intro name hname
          apply hsubset name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inl hname
        · exact hinjective
        · exact hdisjoint
      · apply tail.apply_witness allowed
        · intro name hname
          apply hsubset name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inr hname
        · exact hinjective
        · exact hdisjoint

end

/-- Every structural fresh variant has a concrete finite substitution that
    propositionally identifies the copied and source atoms. -/
theorem FreshVariant.exact_witness {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ copiedName, copiedName ∈ source.vars →
      ∀ sourceName, sourceName ∈ source.vars →
        fresh copiedName ≠ sourceName) :
    ∃ witness,
      subst witness copied = subst witness source := by
  let witness := freshVariantWitness fresh source.vars
  have happly : Metta.Subst.apply witness copied = source := by
    exact variant.apply_witness source.vars (by simp) hinjective hdisjoint
  have htopological : SubstTopological witness := by
    exact freshVariantWitness_topological fresh source.vars hinjective
      hdisjoint
  have hdenotes : SubstLookupDenotes witness witness := by
    intro name value hlookup
    exact htopological.subst_var_of_lookup witness name value hlookup
  have hinvisible := subst_apply_of_lookupDenotes witness witness hdenotes copied
  refine ⟨witness, ?_⟩
  rw [happly] at hinvisible
  exact hinvisible.symm

/-- Every constraint produced by decomposing a fresh variant is oriented
    from a copied variable toward its source variable. -/
def FreshVariantConstraints (fresh : String → String)
    (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    ∃ source, constraint = (fresh source, Atom.var source)

/-- The oriented constraints are drawn from variable occurrences of the
    source term, not from an unrelated ambient namespace. -/
def FreshVariantConstraintsIn (fresh : String → String)
    (allowed : List String) (constraints : List (String × Atom)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    ∃ source, constraint = (fresh source, Atom.var source) ∧
      source ∈ allowed

theorem FreshVariantConstraintsIn.shape (fresh : String → String)
    (allowed : List String) (constraints : List (String × Atom))
    (hin : FreshVariantConstraintsIn fresh allowed constraints) :
    FreshVariantConstraints fresh constraints := by
  intro constraint hmem
  obtain ⟨source, hconstraint, hsource⟩ := hin constraint hmem
  exact ⟨source, hconstraint⟩

theorem FreshVariantConstraints.append (fresh : String → String)
    (left right : List (String × Atom))
    (hleft : FreshVariantConstraints fresh left)
    (hright : FreshVariantConstraints fresh right) :
    FreshVariantConstraints fresh (left ++ right) := by
  intro constraint hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft constraint hmem
  · exact hright constraint hmem

/-- Recover the source variable from an oriented fresh-variant constraint.
    The fallback branch is unreachable under `FreshVariantConstraints` but
    keeps this projection total. -/
def freshConstraintSource (constraint : String × Atom) : String :=
  match constraint.2 with
  | Atom.var source => source
  | _ => constraint.1

/-- A constraint list whose every entry is an oriented fresh-to-source
    variable equation, with its source drawn from `remaining`. -/
inductive FreshConstraintList (fresh : String → String)
    (remaining : List String) : List (String × Atom) → Prop where
  | nil : FreshConstraintList fresh remaining []
  | cons (source : String) (hsource : source ∈ remaining)
      {tail : List (String × Atom)} :
      FreshConstraintList fresh remaining tail →
      FreshConstraintList fresh remaining
        ((fresh source, Atom.var source) :: tail)

/-- The extensional constraint-shape fact can be reified as the inductive
    list relation used by the elimination proof. -/
theorem FreshVariantConstraints.toFreshConstraintList
    (fresh : String → String) (remaining : List String)
    (constraints : List (String × Atom))
    (hshape : FreshVariantConstraints fresh constraints)
    (hremaining : ∀ constraint, constraint ∈ constraints →
      freshConstraintSource constraint ∈ remaining) :
    FreshConstraintList fresh remaining constraints := by
  induction constraints with
  | nil => exact .nil
  | cons constraint tail ih =>
      obtain ⟨source, hconstraint⟩ := hshape constraint (by simp)
      subst constraint
      apply FreshConstraintList.cons source
      · exact hremaining (fresh source, Atom.var source) (by simp)
      · apply ih
        · intro item hitem
          exact hshape item (by simp [hitem])
        · intro item hitem
          exact hremaining item (by simp [hitem])

/-- Reify a fresh-variant constraint list using its source occurrences.  The
    list intentionally retains duplicates: it is a simple fuel upper bound,
    while repeated occurrences disappear as reflexive equations. -/
theorem FreshVariantConstraints.toFreshConstraintList_sources
    (fresh : String → String) (constraints : List (String × Atom))
    (hshape : FreshVariantConstraints fresh constraints) :
    FreshConstraintList fresh
      (constraints.map freshConstraintSource) constraints := by
  apply hshape.toFreshConstraintList fresh
  intro constraint hmem
  simp only [List.mem_map]
  exact ⟨constraint, hmem, rfl⟩

theorem FreshVariantConstraintsIn.source_mem_of_projection
    (fresh : String → String) (allowed : List String)
    (constraints : List (String × Atom))
    (hin : FreshVariantConstraintsIn fresh allowed constraints)
    (source : String)
    (hsource : source ∈ constraints.map freshConstraintSource) :
    source ∈ allowed := by
  obtain ⟨constraint, hconstraint, hequal⟩ := List.mem_map.mp hsource
  obtain ⟨origin, horigin, horiginAllowed⟩ :=
    hin constraint hconstraint
  subst constraint
  simp only [freshConstraintSource] at hequal
  subst source
  exact horiginAllowed

/-- Worklist equations encountered after one or more fresh-variable
    eliminations.  Repeated residual occurrences become literal `same`
    equations; unprocessed occurrences retain their left-fresh orientation. -/
inductive FreshEquationList (fresh : String → String)
    (remaining : List String) : List (Atom × Atom) → Prop where
  | nil : FreshEquationList fresh remaining []
  | same (source : String) {tail : List (Atom × Atom)} :
      FreshEquationList fresh remaining tail →
      FreshEquationList fresh remaining
        ((Atom.var source, Atom.var source) :: tail)
  | fresh (source : String) (hsource : source ∈ remaining)
      {tail : List (Atom × Atom)} :
      FreshEquationList fresh remaining tail →
      FreshEquationList fresh remaining
        ((Atom.var (fresh source), Atom.var source) :: tail)

mutual

/-- Structural decomposition of a fresh variant cannot clash and exposes
    only left-oriented fresh-to-source variable constraints. -/
theorem FreshVariant.decompose {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source) :
    ∃ constraints,
      Metta.Unify.decomposeEqWith prologGroundIdentical copied source =
          some constraints ∧
        FreshVariantConstraints fresh constraints ∧
        FreshVariantConstraintsIn fresh source.vars constraints ∧
        constraints.length ≤ source.size := by
  cases variant with
  | sym name =>
      exact ⟨[], by simp [Metta.Unify.decomposeEqWith], by
        simp [FreshVariantConstraints], by
        simp [FreshVariantConstraintsIn], by simp [Atom.size]⟩
  | varSame name =>
      exact ⟨[], by simp [Metta.Unify.decomposeEqWith], by
        simp [FreshVariantConstraints], by
        simp [FreshVariantConstraintsIn], by simp [Atom.size]⟩
  | var name hne =>
      refine ⟨[(fresh name, Atom.var name)], ?_, ?_⟩
      · simp [Metta.Unify.decomposeEqWith, hne]
      · constructor
        · intro constraint hmem
          simp only [List.mem_singleton] at hmem
          subst constraint
          exact ⟨name, rfl⟩
        · constructor
          · intro constraint hmem
            simp only [List.mem_singleton] at hmem
            subst constraint
            exact ⟨name, rfl, by simp [Atom.vars]⟩
          · simp [Atom.size]
  | gnd ground =>
      exact ⟨[], by simp [Metta.Unify.decomposeEqWith], by
        simp [FreshVariantConstraints], by
        simp [FreshVariantConstraintsIn], by simp [Atom.size]⟩
  | expr variants =>
      obtain ⟨constraints, hdecompose, hconstraints, hin, hlength⟩ :=
        variants.decompose
      exact ⟨constraints, hdecompose, hconstraints, by
        simpa [Atom.vars] using hin, by
        simp only [Atom.size]
        omega⟩

/-- List decomposition preserves the same oriented-constraint invariant. -/
theorem FreshVariantList.decompose {fresh : String → String}
    {copied source : List Atom}
    (variants : FreshVariantList fresh copied source) :
    ∃ constraints,
      Metta.Unify.decomposeListWith prologGroundIdentical copied source =
          some constraints ∧
        FreshVariantConstraints fresh constraints ∧
        FreshVariantConstraintsIn fresh
          ((source.map Atom.vars).flatten) constraints ∧
        constraints.length ≤ (source.map Atom.size).sum := by
  cases variants with
  | nil =>
      exact ⟨[], rfl, by simp [FreshVariantConstraints], by
        simp [FreshVariantConstraintsIn], by simp⟩
  | cons head tail =>
      obtain ⟨headConstraints, hhead, hheadConstraints, hheadIn,
          hheadLength⟩ :=
        head.decompose
      obtain ⟨tailConstraints, htail, htailConstraints, htailIn,
          htailLength⟩ :=
        tail.decompose
      refine ⟨headConstraints ++ tailConstraints, ?_, ?_, ?_, ?_⟩
      · simp [Metta.Unify.decomposeListWith, hhead, htail]
      · exact FreshVariantConstraints.append fresh headConstraints
          tailConstraints hheadConstraints htailConstraints
      · intro constraint hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · obtain ⟨sourceName, hconstraint, hsource⟩ :=
            hheadIn constraint hmem
          exact ⟨sourceName, hconstraint, by
            simp only [List.map_cons, List.flatten_cons, List.mem_append]
            exact Or.inl hsource⟩
        · obtain ⟨sourceName, hconstraint, hsource⟩ :=
            htailIn constraint hmem
          exact ⟨sourceName, hconstraint, by
            simp only [List.map_cons, List.flatten_cons, List.mem_append]
            exact Or.inr hsource⟩
      · simp only [List.length_append, List.map_cons, List.sum_cons]
        omega

end

/-- Decomposing a post-elimination fresh worklist returns exactly another
    oriented fresh constraint list. -/
theorem FreshEquationList.decompose {fresh : String → String}
    {remaining : List String} {equations : List (Atom × Atom)}
    (hdisjoint : ∀ source, source ∈ remaining →
      ∀ target, target ∈ remaining → fresh source ≠ target)
    (related : FreshEquationList fresh remaining equations) :
    ∃ constraints,
      Metta.Unify.decomposeAllWith prologGroundIdentical equations =
          some constraints ∧
        FreshConstraintList fresh remaining constraints := by
  induction related with
  | nil => exact ⟨[], rfl, .nil⟩
  | same source tail ih =>
      obtain ⟨constraints, hdecompose, hconstraints⟩ := ih
      exact ⟨constraints, by
        simp [Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
          hdecompose],
        hconstraints⟩
  | fresh source hsource tail ih =>
      obtain ⟨constraints, hdecompose, hconstraints⟩ := ih
      have hne : fresh source ≠ source :=
        hdisjoint source hsource source hsource
      refine ⟨(fresh source, Atom.var source) :: constraints, ?_, ?_⟩
      · simp [Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
          hne, hdecompose]
      · exact .cons source hsource hconstraints

/-- After eliminating the head fresh variable, every remaining constraint
    is either the same fresh equation or, for a repeated source occurrence,
    a literal reflexive equation. -/
theorem FreshConstraintList.afterBinding {fresh : String → String}
    {remaining : List String} {constraints : List (String × Atom)}
    (hinjective : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ source, source ∈ remaining →
      ∀ target, target ∈ remaining → fresh source ≠ target)
    (chosen : String) (hchosen : chosen ∈ remaining)
    (related : FreshConstraintList fresh remaining constraints) :
    FreshEquationList fresh (remaining.erase chosen)
      (constraints.map fun constraint =>
        (Metta.Subst.apply [(fresh chosen, Atom.var chosen)]
            (Atom.var constraint.1),
          Metta.Subst.apply [(fresh chosen, Atom.var chosen)] constraint.2)) := by
  induction related with
  | nil => exact .nil
  | cons source hsource tail ih =>
      have hfreshChosenSource : fresh chosen ≠ source :=
        hdisjoint chosen hchosen source hsource
      by_cases heq : source = chosen
      · subst source
        have hfreshChosen : fresh chosen ≠ chosen :=
          hdisjoint chosen hchosen chosen hchosen
        have hhead :
            (Metta.Subst.apply [(fresh chosen, Atom.var chosen)]
                (Atom.var (fresh chosen)),
              Metta.Subst.apply [(fresh chosen, Atom.var chosen)]
                (Atom.var chosen)) =
              (Atom.var chosen, Atom.var chosen) := by
          simp [Metta.Subst.apply, Metta.Subst.lookup,
            Ne.symm hfreshChosen]
        rw [List.map_cons, hhead]
        exact .same chosen ih
      · have hfreshDistinct : fresh source ≠ fresh chosen := by
          exact fun hequal => heq
            (hinjective source hsource chosen hchosen hequal)
        have hsourceRemaining : source ∈ remaining.erase chosen := by
          exact (List.mem_erase_of_ne heq).2 hsource
        have hhead :
            (Metta.Subst.apply [(fresh chosen, Atom.var chosen)]
                (Atom.var (fresh source)),
              Metta.Subst.apply [(fresh chosen, Atom.var chosen)]
                (Atom.var source)) =
              (Atom.var (fresh source), Atom.var source) := by
          simp [Metta.Subst.apply, Metta.Subst.lookup, hfreshDistinct,
            Ne.symm hfreshChosenSource]
        rw [List.map_cons, hhead]
        exact .fresh source hsourceRemaining ih

private theorem length_erase_lt_of_mem_string (name : String) :
    (names : List String) → name ∈ names →
      (names.erase name).length < names.length
  | [], hmem => by simp at hmem
  | head :: tail, hmem => by
      by_cases heq : name = head
      · subst head
        simp
      · have htail : name ∈ tail := by simpa [heq] using hmem
        have ih := length_erase_lt_of_mem_string name tail htail
        have hhead : head ≠ name := Ne.symm heq
        have hbeq : (head == name) = false := by simp [hhead]
        simp only [List.erase, hbeq, List.length_cons]
        omega

/-- Every generated entry is exactly a fresh-to-source variable binding. -/
def FreshGenerated (fresh : String → String) (allowed : List String)
    (generated : Subst) : Prop :=
  ∀ entry, entry ∈ generated →
    ∃ source, source ∈ allowed ∧
      entry = (fresh source, Atom.var source)

theorem FreshGenerated.extend (fresh : String → String)
    (allowed : List String) (generated : Subst)
    (hgenerated : FreshGenerated fresh allowed generated)
    (source : String) (hsource : source ∈ allowed) :
    FreshGenerated fresh allowed
      (Metta.Subst.extend generated (fresh source) (Atom.var source)) := by
  intro entry hentry
  simp only [Metta.Subst.extend, List.mem_cons] at hentry
  rcases hentry with hentry | hentry
  · subst entry
    exact ⟨source, hsource, rfl⟩
  · exact hgenerated entry (List.mem_filter.mp hentry).1

/-- A name outside the image of every permitted source is absent from a
    generated fresh-variant substitution. -/
theorem FreshGenerated.lookup_none_of_forbidden (fresh : String → String)
    (allowed : List String) (generated : Subst)
    (hgenerated : FreshGenerated fresh allowed generated)
    (name : String)
    (hforbidden : ∀ source, source ∈ allowed → fresh source ≠ name) :
    Metta.Subst.lookup generated name = none := by
  induction generated with
  | nil => simp [Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      obtain ⟨source, hsource, hkey⟩ :=
        hgenerated (key, value) (by simp)
      have hkeyOnly : key = fresh source := by
        exact congrArg Prod.fst hkey
      have hnameKey : name ≠ key := by
        rw [hkeyOnly]
        exact Ne.symm (hforbidden source hsource)
      have hrestGenerated : FreshGenerated fresh allowed rest := by
        intro tailEntry htailEntry
        exact hgenerated tailEntry (by simp [htailEntry])
      have hbeq : (name == key) = false := by simp [hnameKey]
      simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
      exact ih hrestGenerated

/-- Every successful lookup in a generated variant substitution exposes the
    exact fresh-to-source binding retained by `FreshGenerated`. -/
theorem FreshGenerated.lookup_shape (fresh : String → String)
    (allowed : List String) (generated : Subst)
    (hgenerated : FreshGenerated fresh allowed generated)
    (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup generated name = some value) :
    ∃ source, source ∈ allowed ∧ name = fresh source ∧
      value = Atom.var source := by
  induction generated with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, target⟩
      by_cases heq : name = key
      · subst key
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst target
        obtain ⟨source, hsource, hentry⟩ :=
          hgenerated (name, value) (by simp)
        have hname := congrArg Prod.fst hentry
        have hvalue := congrArg Prod.snd hentry
        exact ⟨source, hsource, hname, hvalue⟩
      · have hbeq : (name == key) = false := by simp [heq]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        apply ih
        · intro tailEntry htailEntry
          exact hgenerated tailEntry (by simp [htailEntry])
        · exact hlookup

/-- The actual fuel-bounded elimination loop succeeds on an oriented fresh
    worklist.  The proof follows the executable loop: each nontrivial round
    removes one source from `remaining`, while repeated occurrences turn
    into reflexive equations and consume no additional elimination round. -/
theorem FreshEquationList.unifyRounds_succeeds {fresh : String → String}
    (remaining : List String) (equations : List (Atom × Atom))
    (related : FreshEquationList fresh remaining equations)
    (hinjective : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ source, source ∈ remaining →
      ∀ target, target ∈ remaining → fresh source ≠ target)
    (fuel : Nat) (hfuel : remaining.length ≤ fuel)
    (generated : Subst) (allowed : List String)
    (hremainingAllowed : ∀ source, source ∈ remaining →
      source ∈ allowed)
    (hgenerated : FreshGenerated fresh allowed generated) :
    ∃ result,
      Metta.Unify.unifyRoundsWith prologGroundIdentical fuel equations
          generated = some result ∧
        FreshGenerated fresh allowed result := by
  induction fuel generalizing remaining equations generated with
  | zero =>
      cases remaining with
      | nil =>
          obtain ⟨constraints, hdecompose, hconstraints⟩ :=
            related.decompose (by simp)
          cases hconstraints with
          | nil =>
              exact ⟨generated, by
                simp [Metta.Unify.unifyRoundsWith, hdecompose], hgenerated⟩
          | cons source hsource tail => simp at hsource
      | cons head tail => simp at hfuel
  | succ fuel ih =>
      obtain ⟨constraints, hdecompose, hconstraints⟩ :=
        related.decompose hdisjoint
      cases hconstraints with
      | nil =>
          exact ⟨generated, by
            simp [Metta.Unify.unifyRoundsWith, hdecompose], hgenerated⟩
      | @cons source hsource tail htail =>
          have hfreshSource : fresh source ≠ source :=
            hdisjoint source hsource source hsource
          have hoccurs :
              Metta.Subst.occurs (fresh source) (Atom.var source) = false := by
            simp [Metta.Subst.occurs, hfreshSource]
          let nextEquations := tail.map fun constraint =>
            (Metta.Subst.apply [(fresh source, Atom.var source)]
                (Atom.var constraint.1),
              Metta.Subst.apply [(fresh source, Atom.var source)]
                constraint.2)
          have hnextRelated : FreshEquationList fresh
              (remaining.erase source) nextEquations := by
            exact htail.afterBinding hinjective hdisjoint source hsource
          have hnextDisjoint : ∀ left, left ∈ remaining.erase source →
              ∀ right, right ∈ remaining.erase source →
                fresh left ≠ right := by
            intro left hleft right hright
            exact hdisjoint left (List.mem_of_mem_erase hleft) right
              (List.mem_of_mem_erase hright)
          have hnextInjective : ∀ left,
              left ∈ remaining.erase source →
              ∀ right, right ∈ remaining.erase source →
                fresh left = fresh right → left = right := by
            intro left hleft right hright hequal
            exact hinjective left (List.mem_of_mem_erase hleft) right
              (List.mem_of_mem_erase hright) hequal
          have hnextFuel : (remaining.erase source).length ≤ fuel := by
            have herase := length_erase_lt_of_mem_string source remaining
              hsource
            omega
          have hnextRemainingAllowed : ∀ item,
              item ∈ remaining.erase source → item ∈ allowed := by
            intro item hitem
            exact hremainingAllowed item (List.mem_of_mem_erase hitem)
          have hnextGenerated : FreshGenerated fresh allowed
              (Metta.Subst.extend generated (fresh source)
                (Atom.var source)) := by
            exact FreshGenerated.extend fresh allowed generated hgenerated
              source (hremainingAllowed source hsource)
          obtain ⟨result, hresult, hresultGenerated⟩ :=
            ih (remaining.erase source)
            nextEquations hnextRelated hnextInjective hnextDisjoint hnextFuel
            (Metta.Subst.extend generated (fresh source)
              (Atom.var source)) hnextRemainingAllowed hnextGenerated
          refine ⟨result, ?_, hresultGenerated⟩
          simpa [Metta.Unify.unifyRoundsWith, hdecompose, hoccurs,
            nextEquations] using hresult

private theorem atom_size_positive (atom : Atom) : 0 < atom.size := by
  cases atom <;> simp only [Atom.size] <;> omega

/-- First-order unification succeeds for every reflexive fresh structural
    variant, and every generated key comes from the copied side.  Unlike a
    general completeness theorem, this follows the exact oriented constraint
    class generated by clause-local alpha-copying and handles shared vars. -/
theorem FreshVariant.unifyTop_succeeds_with_domain
    {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical copied source =
          some result ∧
      FreshGenerated fresh source.vars result := by
  obtain ⟨constraints, hdecompose, hshape, hin, hlength⟩ :=
    variant.decompose
  let remaining := constraints.map freshConstraintSource
  have hconstraintList : FreshConstraintList fresh remaining constraints :=
    hshape.toFreshConstraintList_sources fresh constraints
  have hremainingSource : ∀ name, name ∈ remaining → name ∈ source.vars := by
    intro name hname
    exact hin.source_mem_of_projection fresh source.vars constraints name
      hname
  have hremainingDisjoint : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining → fresh left ≠ right := by
    intro left hleft right hright
    exact hdisjoint left (hremainingSource left hleft) right
      (hremainingSource right hright)
  have hremainingInjective : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left = fresh right → left = right := by
    intro left hleft right hright hequal
    exact hinjective left (hremainingSource left hleft) right
      (hremainingSource right hright) hequal
  cases constraints with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      unfold Metta.Unify.unifyTopWith
      generalize copied.size + source.size = fuel
      cases fuel <;>
        simp [Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
          hdecompose]
      simp [FreshGenerated]
  | cons constraint tail =>
      cases hconstraintList with
      | @cons selected hselected _ htail =>
          have hfreshSelected : fresh selected ≠ selected :=
            hremainingDisjoint selected hselected selected hselected
          have hoccurs : Metta.Subst.occurs (fresh selected)
              (Atom.var selected) = false := by
            simp [Metta.Subst.occurs, hfreshSelected]
          let nextEquations := tail.map fun item =>
            (Metta.Subst.apply [(fresh selected, Atom.var selected)]
                (Atom.var item.1),
              Metta.Subst.apply [(fresh selected, Atom.var selected)] item.2)
          have hnextRelated : FreshEquationList fresh
              (remaining.erase selected) nextEquations := by
            exact htail.afterBinding hremainingInjective
              hremainingDisjoint selected hselected
          have hnextDisjoint : ∀ left,
              left ∈ remaining.erase selected →
              ∀ right, right ∈ remaining.erase selected →
                fresh left ≠ right := by
            intro left hleft right hright
            exact hremainingDisjoint left (List.mem_of_mem_erase hleft) right
              (List.mem_of_mem_erase hright)
          generalize hfuel : copied.size + source.size = totalFuel
          have htotalPositive : 0 < totalFuel := by
            rw [← hfuel]
            have := atom_size_positive source
            omega
          cases totalFuel with
          | zero => omega
          | succ fuel =>
              have hnextFuel : (remaining.erase selected).length ≤ fuel := by
                have herase := length_erase_lt_of_mem_string selected
                  remaining hselected
                have hremainingLength : remaining.length = tail.length + 1 := by
                  simp [remaining]
                have hsourceBound : tail.length + 1 ≤ source.size := by
                  simpa using hlength
                omega
              have hinitialGenerated : FreshGenerated fresh source.vars
                  (Metta.Subst.extend [] (fresh selected)
                    (Atom.var selected)) := by
                have hempty : FreshGenerated fresh source.vars [] := by
                  simp [FreshGenerated]
                exact FreshGenerated.extend fresh source.vars [] hempty
                  selected (hremainingSource selected hselected)
              obtain ⟨result, hresult, hresultGenerated⟩ :=
                hnextRelated.unifyRounds_succeeds
                  (remaining.erase selected) nextEquations (by
                    intro left hleft right hright hequal
                    exact hremainingInjective left
                      (List.mem_of_mem_erase hleft) right
                      (List.mem_of_mem_erase hright) hequal)
                  hnextDisjoint fuel hnextFuel
                  (Metta.Subst.extend [] (fresh selected)
                    (Atom.var selected)) source.vars (by
                      intro item hitem
                      exact hremainingSource item
                        (List.mem_of_mem_erase hitem))
                    hinitialGenerated
              refine ⟨result, ?_, hresultGenerated⟩
              unfold Metta.Unify.unifyTopWith
              rw [hfuel]
              simpa [Metta.Unify.unifyRoundsWith,
                Metta.Unify.decomposeAllWith,
                hdecompose, hoccurs, nextEquations] using hresult

/-- The PeTTa exact-ground unifier accepts every structural fresh variant,
including variants containing NaN ground leaves. -/
theorem FreshVariant.unifyTopExact_succeeds_with_domain
    {fresh : String → String} {copied source : Atom}
    (variant : FreshVariant fresh copied source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right) :
    ∃ result, unifyTopExact copied source = some result ∧
      FreshGenerated fresh source.vars result := by
  obtain ⟨result, underlying, generated⟩ :=
    variant.unifyTop_succeeds_with_domain hinjective hdisjoint
  obtain ⟨witness, witnessExact⟩ :=
    variant.exact_witness hinjective hdisjoint
  have resultExact : subst result copied = subst result source :=
    unifyTopWith_exact_sound_of_exact_unifier prologGroundIdentical copied
      source result witness witnessExact underlying
  exact ⟨result,
    unifyTopExact_of_underlying_exact copied source result underlying
      resultExact,
    generated⟩

/-- Existence-only projection used by callers that do not need the generated
    domain certificate. -/
theorem FreshVariant.unifyTop_succeeds {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical copied source =
        some result := by
  obtain ⟨result, hresult, hdomain⟩ :=
    variant.unifyTop_succeeds_with_domain hinjective hdisjoint
  exact ⟨result, hresult⟩

mutual

/-- Runtime-reflexive atoms decompose against themselves without generating
    constraints.  This is the reflexive branch needed when a caller has
    already instantiated both sides of an alpha-copy pair. -/
theorem fresh_decomposeEq_self_of_equiv (atom : Atom)
    (hreflexive : Metta.Atom.equiv atom atom = true) :
    Metta.Unify.decomposeEq atom atom = some [] := by
  cases atom with
  | sym name => simp [Metta.Unify.decomposeEq]
  | var name => simp [Metta.Unify.decomposeEq]
  | gnd ground =>
      have hground : Metta.Ground.equiv ground ground = true := by
        simpa [Metta.Atom.equiv] using hreflexive
      simp [Metta.Unify.decomposeEq, hground]
  | expr atoms =>
      simp only [Metta.Atom.equiv] at hreflexive
      simpa [Metta.Unify.decomposeEq] using
        fresh_decomposeList_self_of_equiv atoms hreflexive

/-- List companion to `fresh_decomposeEq_self_of_equiv`. -/
theorem fresh_decomposeList_self_of_equiv (atoms : List Atom)
    (hreflexive : Metta.Atom.equivList atoms atoms = true) :
    Metta.Unify.decomposeList atoms atoms = some [] := by
  cases atoms with
  | nil => rfl
  | cons head tail =>
      simp only [Metta.Atom.equivList, Bool.and_eq_true] at hreflexive
      simp [Metta.Unify.decomposeList,
        fresh_decomposeEq_self_of_equiv head hreflexive.1,
        fresh_decomposeList_self_of_equiv tail hreflexive.2]

end

/-- One-pass singleton substitution is invisible when its key does not occur
    in the atom. -/
theorem apply_singleton_eq_self_of_not_mem (name : String) (target : Atom) :
    (atom : Atom) → name ∉ atom.vars →
      Metta.Subst.apply [(name, target)] atom = atom
  | .sym symbol, _ => by simp [Metta.Subst.apply]
  | .var source, hnotmem => by
      have hne : source ≠ name := by
        intro hequal
        apply hnotmem
        simp [Atom.vars, hequal]
      simp [Metta.Subst.apply, Metta.Subst.lookup, hne]
  | .gnd ground, _ => by simp [Metta.Subst.apply]
  | .expr atoms, hnotmem => by
      simp only [Metta.Subst.apply, Atom.expr.injEq]
      rw [List.map_congr_left (fun child hchild => by
        apply apply_singleton_eq_self_of_not_mem name target child
        intro hname
        apply hnotmem
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩)]
      simp
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_unification atoms hchild)

mutual

/-- A copied alpha-variant after the caller has possibly instantiated source
    residuals.  An unresolved copied variable remains on the left; an
    already shared residual is represented by the reflexive constructor. -/
inductive FreshInstance (fresh : String → String)
    (resolve : String → Atom) (allowed : List String) :
    Atom → Atom → Prop where
  | same (atom : Atom) :
      FreshInstance fresh resolve allowed atom atom
  | var (source : String) (hsource : source ∈ allowed)
      (havoids : fresh source ∉ (resolve source).vars) :
      FreshInstance fresh resolve allowed
        (Atom.var (fresh source)) (resolve source)
  | expr {copied source : List Atom} :
      FreshInstanceList fresh resolve allowed copied source →
      FreshInstance fresh resolve allowed
        (Atom.expr copied) (Atom.expr source)

/-- List companion to `FreshInstance`. -/
inductive FreshInstanceList (fresh : String → String)
    (resolve : String → Atom) (allowed : List String) :
    List Atom → List Atom → Prop where
  | nil : FreshInstanceList fresh resolve allowed [] []
  | cons {copiedHead sourceHead copiedTail sourceTail} :
      FreshInstance fresh resolve allowed copiedHead sourceHead →
      FreshInstanceList fresh resolve allowed copiedTail sourceTail →
      FreshInstanceList fresh resolve allowed
        (copiedHead :: copiedTail) (sourceHead :: sourceTail)

end

mutual

/-- Exact Prolog decomposition is reflexive on every atom, including atoms
containing NaN ground leaves. -/
theorem prolog_decomposeEq_self :
    ∀ atom : Atom,
      Metta.Unify.decomposeEqWith prologGroundIdentical atom atom = some []
  | .sym name => by simp [Metta.Unify.decomposeEqWith]
  | .var name => by simp [Metta.Unify.decomposeEqWith]
  | .gnd ground => by simp [Metta.Unify.decomposeEqWith]
  | .expr atoms => by
      simpa [Metta.Unify.decomposeEqWith] using
        prolog_decomposeList_self atoms

/-- List companion to `prolog_decomposeEq_self`. -/
theorem prolog_decomposeList_self :
    ∀ atoms : List Atom,
      Metta.Unify.decomposeListWith prologGroundIdentical atoms atoms =
        some []
  | [] => rfl
  | atom :: rest => by
      simp [Metta.Unify.decomposeListWith, prolog_decomposeEq_self atom,
        prolog_decomposeList_self rest]

end

/-- Exact PeTTa/Prolog unification is reflexive for every atom. -/
theorem unifyTopExact_self (atom : Atom) :
    unifyTopExact atom atom = some [] := by
  unfold unifyTopExact Metta.Unify.unifyTopWith
  generalize atom.size + atom.size = fuel
  cases fuel with
  | zero =>
      simp [Metta.Unify.unifyRoundsWith,
        Metta.Unify.decomposeAllWith, prolog_decomposeEq_self]
  | succ remaining =>
      simp [Metta.Unify.unifyRoundsWith,
        Metta.Unify.decomposeAllWith, prolog_decomposeEq_self]

/-- Decomposed instantiated-copy constraints, paired with their source index
    so arbitrary resolved targets need not be inverted. -/
inductive FreshResolvedConstraintList (fresh : String → String)
    (resolve : String → Atom) :
    List String → List (String × Atom) → Prop where
  | nil : FreshResolvedConstraintList fresh resolve [] []
  | cons (source : String) {sources : List String}
      {constraints : List (String × Atom)} :
      FreshResolvedConstraintList fresh resolve sources constraints →
      FreshResolvedConstraintList fresh resolve (source :: sources)
        ((fresh source, resolve source) :: constraints)

theorem FreshResolvedConstraintList.append (fresh : String → String)
    (resolve : String → Atom) {leftSources rightSources : List String}
    {left right : List (String × Atom)}
    (hleft : FreshResolvedConstraintList fresh resolve leftSources left)
    (hright : FreshResolvedConstraintList fresh resolve rightSources right) :
    FreshResolvedConstraintList fresh resolve
      (leftSources ++ rightSources) (left ++ right) := by
  induction hleft with
  | nil => simpa using hright
  | cons source related ih =>
      simpa using FreshResolvedConstraintList.cons source ih

mutual

/-- Structural decomposition of an instantiated alpha-copy produces only
    fresh-to-current-source constraints and cannot clash. -/
theorem FreshInstance.decompose {fresh : String → String}
    {resolve : String → Atom} {allowed : List String}
    {copied source : Atom}
    (related : FreshInstance fresh resolve allowed copied source) :
    ∃ sources constraints,
      Metta.Unify.decomposeEqWith prologGroundIdentical copied source =
          some constraints ∧
        FreshResolvedConstraintList fresh resolve sources constraints ∧
        constraints.length ≤ copied.size ∧
        (∀ item, item ∈ sources → item ∈ allowed) := by
  cases related with
  | same =>
      exact ⟨[], [], prolog_decomposeEq_self copied, .nil, by simp, by simp⟩
  | var source hsource havoids =>
      refine ⟨[source], [(fresh source, resolve source)], ?_,
        .cons source .nil, by simp [Atom.size], by simp [hsource]⟩
      cases htarget : resolve source with
      | sym symbol => simp [Metta.Unify.decomposeEqWith]
      | var target =>
          have hnames : fresh source ≠ target := by
            intro hequal
            apply havoids
            simp [htarget, Atom.vars, hequal]
          simp [Metta.Unify.decomposeEqWith, hnames]
      | gnd ground => simp [Metta.Unify.decomposeEqWith]
      | expr atoms => simp [Metta.Unify.decomposeEqWith]
  | expr instances =>
      obtain ⟨sources, constraints, hdecompose, hrelated, hlength,
          hsources⟩ :=
        instances.decompose
      exact ⟨sources, constraints, hdecompose, hrelated, by
        simp only [Atom.size]
        omega, hsources⟩

/-- List decomposition for instantiated alpha-copies. -/
theorem FreshInstanceList.decompose {fresh : String → String}
    {resolve : String → Atom} {allowed : List String}
    {copied source : List Atom}
    (instances : FreshInstanceList fresh resolve allowed copied source) :
    ∃ sources constraints,
      Metta.Unify.decomposeListWith prologGroundIdentical copied source =
          some constraints ∧
        FreshResolvedConstraintList fresh resolve sources constraints ∧
        constraints.length ≤ (copied.map Atom.size).sum ∧
        (∀ item, item ∈ sources → item ∈ allowed) := by
  cases instances with
  | nil => exact ⟨[], [], rfl, .nil, by simp, by simp⟩
  | cons head tail =>
      obtain ⟨headSources, headConstraints, hhead, hheadRelated,
          hheadLength, hheadSources⟩ := head.decompose
      obtain ⟨tailSources, tailConstraints, htail, htailRelated,
          htailLength, htailSources⟩ := tail.decompose
      refine ⟨headSources ++ tailSources, headConstraints ++ tailConstraints,
        ?_, ?_, ?_, ?_⟩
      · simp [Metta.Unify.decomposeListWith, hhead, htail]
      · exact hheadRelated.append fresh resolve htailRelated
      · simp only [List.length_append, List.map_cons, List.sum_cons]
        omega
      · intro item hitem
        rcases List.mem_append.mp hitem with hitem | hitem
        · exact hheadSources item hitem
        · exact htailSources item hitem

end

/-- Worklist after eliminating zero or more instantiated fresh variables. -/
inductive FreshResolvedEquationList (fresh : String → String)
    (resolve : String → Atom) (remaining : List String) :
    List (Atom × Atom) → Prop where
  | nil : FreshResolvedEquationList fresh resolve remaining []
  | same (source : String) {tail : List (Atom × Atom)} :
      FreshResolvedEquationList fresh resolve remaining tail →
      FreshResolvedEquationList fresh resolve remaining
        ((resolve source, resolve source) :: tail)
  | fresh (source : String) (hsource : source ∈ remaining)
      {tail : List (Atom × Atom)} :
      FreshResolvedEquationList fresh resolve remaining tail →
      FreshResolvedEquationList fresh resolve remaining
        ((Atom.var (fresh source), resolve source) :: tail)

/-- Decomposition of an instantiated fresh worklist preserves its exact
    oriented constraint list. -/
theorem FreshResolvedEquationList.decompose
    {fresh : String → String} {resolve : String → Atom}
    {remaining : List String} {equations : List (Atom × Atom)}
    (havoids : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left ∉ (resolve right).vars)
    (related : FreshResolvedEquationList fresh resolve remaining equations) :
    ∃ sources constraints,
      Metta.Unify.decomposeAllWith prologGroundIdentical equations =
          some constraints ∧
        FreshResolvedConstraintList fresh resolve sources constraints ∧
        (∀ source, source ∈ sources → source ∈ remaining) := by
  induction related with
  | nil => exact ⟨[], [], rfl, .nil, by simp⟩
  | same source tail ih =>
      obtain ⟨sources, constraints, hdecompose, hconstraints, hsources⟩ := ih
      exact ⟨sources, constraints, by
        simp [Metta.Unify.decomposeAllWith,
          prolog_decomposeEq_self (resolve source),
          hdecompose], hconstraints, hsources⟩
  | fresh source hsource tail ih =>
      obtain ⟨sources, constraints, hdecompose, hconstraints, hsources⟩ := ih
      have hnotmem := havoids source hsource source hsource
      have hhead :
          Metta.Unify.decomposeEqWith prologGroundIdentical
              (Atom.var (fresh source)) (resolve source) =
            some [(fresh source, resolve source)] := by
        cases htarget : resolve source with
        | sym symbol => simp [Metta.Unify.decomposeEqWith]
        | var target =>
            have hne : fresh source ≠ target := by
              intro hequal
              apply hnotmem
              simp [htarget, Atom.vars, hequal]
            simp [Metta.Unify.decomposeEqWith, hne]
        | gnd ground => simp [Metta.Unify.decomposeEqWith]
        | expr atoms => simp [Metta.Unify.decomposeEqWith]
      exact ⟨source :: sources, (fresh source, resolve source) :: constraints, by
        simp [Metta.Unify.decomposeAllWith, hhead, hdecompose],
        .cons source hconstraints, by
          intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact hsource
          · exact hsources item hitem⟩

/-- Eliminating one instantiated fresh constraint turns repeated occurrences
    into reflexive equations and leaves all other targets unchanged. -/
theorem FreshResolvedConstraintList.afterBinding
    {fresh : String → String} {resolve : String → Atom}
    {remaining sources : List String}
    {constraints : List (String × Atom)}
    (hinjective : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left ∉ (resolve right).vars)
    (chosen : String) (hchosen : chosen ∈ remaining)
    (related : FreshResolvedConstraintList fresh resolve sources constraints)
    (hsources : ∀ source, source ∈ sources → source ∈ remaining) :
    FreshResolvedEquationList fresh resolve (remaining.erase chosen)
      (constraints.map fun constraint =>
        (Metta.Subst.apply [(fresh chosen, resolve chosen)]
            (Atom.var constraint.1),
          Metta.Subst.apply [(fresh chosen, resolve chosen)] constraint.2)) := by
  induction related with
  | nil => exact .nil
  | cons source tail ih =>
      have hsource : source ∈ remaining := hsources source (by simp)
      have htargetFixed : Metta.Subst.apply [(fresh chosen, resolve chosen)]
          (resolve source) = resolve source :=
        apply_singleton_eq_self_of_not_mem (fresh chosen) (resolve chosen)
          (resolve source) (havoids chosen hchosen source hsource)
      have ihTail := ih (fun item hitem => hsources item (by simp [hitem]))
      by_cases hequal : source = chosen
      · subst source
        have hleft : Metta.Subst.apply [(fresh chosen, resolve chosen)]
            (Atom.var (fresh chosen)) = resolve chosen := by
          simp [Metta.Subst.apply, Metta.Subst.lookup]
        simp only [List.map_cons]
        rw [hleft, htargetFixed]
        exact .same chosen ihTail
      · have hfreshNe : fresh source ≠ fresh chosen := by
          intro hnames
          exact hequal (hinjective source hsource chosen hchosen hnames)
        have hleft : Metta.Subst.apply [(fresh chosen, resolve chosen)]
            (Atom.var (fresh source)) = Atom.var (fresh source) := by
          simp [Metta.Subst.apply, Metta.Subst.lookup, hfreshNe]
        have hsourceRemaining : source ∈ remaining.erase chosen :=
          (List.mem_erase_of_ne hequal).2 hsource
        simp only [List.map_cons]
        rw [hleft, htargetFixed]
        exact .fresh source hsourceRemaining ihTail

/-- Generated instantiated-variant bindings have only fresh-copy keys and
    point to the current denotation of their indexed source residual. -/
def FreshResolvedGenerated (fresh : String → String)
    (resolve : String → Atom) (allowed : List String)
    (generated : Subst) : Prop :=
  ∀ entry, entry ∈ generated →
    ∃ source, source ∈ allowed ∧
      entry = (fresh source, resolve source)

theorem FreshResolvedGenerated.extend (fresh : String → String)
    (resolve : String → Atom) (allowed : List String)
    (generated : Subst)
    (hgenerated : FreshResolvedGenerated fresh resolve allowed generated)
    (source : String) (hsource : source ∈ allowed) :
    FreshResolvedGenerated fresh resolve allowed
      (Metta.Subst.extend generated (fresh source) (resolve source)) := by
  intro entry hentry
  simp only [Metta.Subst.extend, List.mem_cons] at hentry
  rcases hentry with hentry | hentry
  · subst entry
    exact ⟨source, hsource, rfl⟩
  · exact hgenerated entry (List.mem_filter.mp hentry).1

theorem FreshResolvedGenerated.lookup_none_of_forbidden
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String) (generated : Subst)
    (hgenerated : FreshResolvedGenerated fresh resolve allowed generated)
    (name : String)
    (hforbidden : ∀ source, source ∈ allowed → fresh source ≠ name) :
    Metta.Subst.lookup generated name = none := by
  induction generated with
  | nil => simp [Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      obtain ⟨source, hsource, hentry⟩ :=
        hgenerated (key, value) (by simp)
      have hkey : key = fresh source := congrArg Prod.fst hentry
      have hne : name ≠ key := by
        rw [hkey]
        exact Ne.symm (hforbidden source hsource)
      have htail : FreshResolvedGenerated fresh resolve allowed rest := by
        intro tailEntry htailEntry
        exact hgenerated tailEntry (by simp [htailEntry])
      have hbeq : (name == key) = false := by simp [hne]
      simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
      exact ih htail

theorem FreshResolvedGenerated.lookup_shape
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String) (generated : Subst)
    (hgenerated : FreshResolvedGenerated fresh resolve allowed generated)
    (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup generated name = some value) :
    ∃ source, source ∈ allowed ∧ name = fresh source ∧
      value = resolve source := by
  induction generated with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, target⟩
      by_cases hequal : name = key
      · subst key
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst target
        obtain ⟨source, hsource, hentry⟩ :=
          hgenerated (name, value) (by simp)
        exact ⟨source, hsource, congrArg Prod.fst hentry,
          congrArg Prod.snd hentry⟩
      · have hbeq : (name == key) = false := by simp [hequal]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        apply ih
        · intro tailEntry htailEntry
          exact hgenerated tailEntry (by simp [htailEntry])
        · exact hlookup

/-- The source-index and constraint lists of an instantiated fresh
    decomposition have identical lengths. -/
theorem FreshResolvedConstraintList.length_eq
    {fresh : String → String} {resolve : String → Atom}
    {sources : List String} {constraints : List (String × Atom)}
    (related : FreshResolvedConstraintList fresh resolve sources constraints) :
    sources.length = constraints.length := by
  induction related with
  | nil => rfl
  | cons source tail ih => simp [ih]

/-- Boolean occurs-check completeness for the syntactic variable list. -/
theorem occurs_eq_false_of_not_mem_vars (name : String) :
    (atom : Atom) → name ∉ atom.vars →
      Metta.Subst.occurs name atom = false
  | .sym symbol, _ => by simp [Metta.Subst.occurs]
  | .var source, hnotmem => by
      have hne : name ≠ source := by
        simpa [Atom.vars] using hnotmem
      simp [Metta.Subst.occurs, hne]
  | .gnd ground, _ => by simp [Metta.Subst.occurs]
  | .expr atoms, hnotmem => by
      simp only [Metta.Subst.occurs]
      apply List.any_eq_false.mpr
      intro child hchildAttached
      have hchildFalse := occurs_eq_false_of_not_mem_vars name child.val (by
        intro hname
        apply hnotmem
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.val.vars, ⟨child.val, child.property, rfl⟩, hname⟩)
      simpa only [Bool.not_eq_true] using hchildFalse
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_unification atoms child.property)

/-- The executable elimination loop succeeds for instantiated alpha-copy
    constraints. -/
theorem FreshResolvedEquationList.unifyRounds_succeeds
    {fresh : String → String} {resolve : String → Atom}
    (remaining : List String) (equations : List (Atom × Atom))
    (related : FreshResolvedEquationList fresh resolve remaining equations)
    (hinjective : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ remaining →
      ∀ right, right ∈ remaining →
        fresh left ∉ (resolve right).vars)
    (fuel : Nat) (hfuel : remaining.length ≤ fuel)
    (generated : Subst) (allowed : List String)
    (hremainingAllowed : ∀ source, source ∈ remaining →
      source ∈ allowed)
    (hgenerated : FreshResolvedGenerated fresh resolve allowed generated) :
    ∃ result,
      Metta.Unify.unifyRoundsWith prologGroundIdentical fuel equations
          generated = some result ∧
        FreshResolvedGenerated fresh resolve allowed result := by
  induction fuel generalizing remaining equations generated with
  | zero =>
      cases remaining with
      | nil =>
          obtain ⟨sources, constraints, hdecompose, hconstraints, hsources⟩ :=
            related.decompose (by simp)
          cases hconstraints with
          | nil =>
              exact ⟨generated, by
                simp [Metta.Unify.unifyRoundsWith, hdecompose], hgenerated⟩
          | cons source tail =>
              have himpossible : source ∈ ([] : List String) :=
                hsources source (by simp)
              simp at himpossible
      | cons head tail => simp at hfuel
  | succ fuel ih =>
      obtain ⟨sources, constraints, hdecompose, hconstraints, hsources⟩ :=
        related.decompose havoids
      cases hconstraints with
      | nil =>
          exact ⟨generated, by
            simp [Metta.Unify.unifyRoundsWith, hdecompose], hgenerated⟩
      | @cons source sourceTail constraintTail htail =>
          have hsource : source ∈ remaining := hsources source (by simp)
          have hnotmem := havoids source hsource source hsource
          have hoccurs :
              Metta.Subst.occurs (fresh source) (resolve source) = false :=
            occurs_eq_false_of_not_mem_vars (fresh source) (resolve source)
              hnotmem
          let nextEquations := constraintTail.map fun constraint =>
            (Metta.Subst.apply [(fresh source, resolve source)]
                (Atom.var constraint.1),
              Metta.Subst.apply [(fresh source, resolve source)] constraint.2)
          have hsourceTail : ∀ item, item ∈ sourceTail →
              item ∈ remaining := by
            intro item hitem
            exact hsources item (by simp [hitem])
          have hnextRelated : FreshResolvedEquationList fresh resolve
              (remaining.erase source) nextEquations := by
            exact htail.afterBinding hinjective havoids source hsource
              hsourceTail
          have hnextInjective : ∀ left,
              left ∈ remaining.erase source →
              ∀ right, right ∈ remaining.erase source →
                fresh left = fresh right → left = right := by
            intro left hleft right hright hequal
            exact hinjective left (List.mem_of_mem_erase hleft) right
              (List.mem_of_mem_erase hright) hequal
          have hnextAvoids : ∀ left,
              left ∈ remaining.erase source →
              ∀ right, right ∈ remaining.erase source →
                fresh left ∉ (resolve right).vars := by
            intro left hleft right hright
            exact havoids left (List.mem_of_mem_erase hleft) right
              (List.mem_of_mem_erase hright)
          have hnextFuel : (remaining.erase source).length ≤ fuel := by
            have herase := length_erase_lt_of_mem_string source remaining
              hsource
            omega
          have hnextAllowed : ∀ item,
              item ∈ remaining.erase source → item ∈ allowed := by
            intro item hitem
            exact hremainingAllowed item (List.mem_of_mem_erase hitem)
          have hnextGenerated : FreshResolvedGenerated fresh resolve allowed
              (Metta.Subst.extend generated (fresh source)
                (resolve source)) := by
            exact hgenerated.extend fresh resolve allowed generated source
              (hremainingAllowed source hsource)
          obtain ⟨result, hresult, hresultGenerated⟩ :=
            ih (remaining.erase source) nextEquations hnextRelated
              hnextInjective hnextAvoids hnextFuel
              (Metta.Subst.extend generated (fresh source) (resolve source))
              hnextAllowed hnextGenerated
          refine ⟨result, ?_, hresultGenerated⟩
          simpa [Metta.Unify.unifyRoundsWith, hdecompose, hoccurs,
            nextEquations] using hresult

/-- First-order unification succeeds after arbitrary caller instantiation of
    the source residuals, while generated keys remain confined to the copied
    alpha-variant. -/
theorem FreshInstance.unifyTop_succeeds_with_domain
    {fresh : String → String} {resolve : String → Atom}
    {allowed : List String} {copied source : Atom}
    (related : FreshInstance fresh resolve allowed copied source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical copied source =
          some result ∧
      FreshResolvedGenerated fresh resolve allowed result := by
  obtain ⟨sources, constraints, hdecompose, hconstraints, hlength,
      hsources⟩ := related.decompose
  have hsourcesInjective : ∀ left, left ∈ sources →
      ∀ right, right ∈ sources →
        fresh left = fresh right → left = right := by
    intro left hleft right hright hequal
    exact hinjective left (hsources left hleft) right (hsources right hright)
      hequal
  have hsourcesAvoids : ∀ left, left ∈ sources →
      ∀ right, right ∈ sources →
        fresh left ∉ (resolve right).vars := by
    intro left hleft right hright
    exact havoids left (hsources left hleft) right (hsources right hright)
  cases constraints with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · unfold Metta.Unify.unifyTopWith
        generalize copied.size + source.size = fuel
        cases fuel <;>
          simp [Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
            hdecompose]
      · simp [FreshResolvedGenerated]
  | cons constraint constraintTail =>
      cases hconstraints with
      | @cons selected sourceTail _ htail =>
          have hselected : selected ∈ selected :: sourceTail := by simp
          have hnotmem := hsourcesAvoids selected hselected selected hselected
          have hoccurs : Metta.Subst.occurs (fresh selected)
              (resolve selected) = false :=
            occurs_eq_false_of_not_mem_vars (fresh selected)
              (resolve selected) hnotmem
          let nextEquations := constraintTail.map fun item =>
            (Metta.Subst.apply [(fresh selected, resolve selected)]
                (Atom.var item.1),
              Metta.Subst.apply [(fresh selected, resolve selected)] item.2)
          have hnextRelated : FreshResolvedEquationList fresh resolve
              ((selected :: sourceTail).erase selected) nextEquations := by
            exact htail.afterBinding hsourcesInjective hsourcesAvoids
              selected hselected (by
                intro item hitem
                exact List.mem_cons_of_mem selected hitem)
          generalize hfuel : copied.size + source.size = totalFuel
          have htotalPositive : 0 < totalFuel := by
            rw [← hfuel]
            have := atom_size_positive copied
            omega
          cases totalFuel with
          | zero => omega
          | succ fuel =>
              have hsourcesLength :
                  (selected :: sourceTail).length =
                    constraintTail.length + 1 := by
                simpa using
                  (FreshResolvedConstraintList.length_eq (.cons selected htail))
              have hnextFuel :
                  ((selected :: sourceTail).erase selected).length ≤ fuel := by
                have herase := length_erase_lt_of_mem_string selected
                  (selected :: sourceTail) hselected
                have hconstraintBound :
                    constraintTail.length + 1 ≤ copied.size := by
                  simpa using hlength
                omega
              have hinitialGenerated : FreshResolvedGenerated fresh resolve
                  allowed (Metta.Subst.extend [] (fresh selected)
                    (resolve selected)) := by
                have hempty : FreshResolvedGenerated fresh resolve allowed [] := by
                  simp [FreshResolvedGenerated]
                exact hempty.extend fresh resolve allowed [] selected
                  (hsources selected hselected)
              obtain ⟨result, hresult, hresultGenerated⟩ :=
                hnextRelated.unifyRounds_succeeds
                  ((selected :: sourceTail).erase selected) nextEquations
                  (by
                    intro left hleft right hright hequal
                    exact hsourcesInjective left
                      (List.mem_of_mem_erase hleft) right
                      (List.mem_of_mem_erase hright) hequal)
                  (by
                    intro left hleft right hright
                    exact hsourcesAvoids left (List.mem_of_mem_erase hleft)
                      right (List.mem_of_mem_erase hright))
                  fuel hnextFuel
                  (Metta.Subst.extend [] (fresh selected) (resolve selected))
                  allowed (by
                    intro item hitem
                    exact hsources item (List.mem_of_mem_erase hitem))
                  hinitialGenerated
              refine ⟨result, ?_, hresultGenerated⟩
              unfold Metta.Unify.unifyTopWith
              rw [hfuel]
              simpa [Metta.Unify.unifyRoundsWith,
                Metta.Unify.decomposeAllWith,
                hdecompose, hoccurs, nextEquations] using hresult

mutual

/-- Instantiating both sides of a raw structural alpha-variant yields the
    generalized `FreshInstance` relation, even when caller head narrowing has
    already instantiated source residuals. -/
theorem FreshVariant.instantiate {fresh : String → String}
    {copied source : Atom} (variant : FreshVariant fresh copied source)
    (runtime : Subst) (allowed : List String)
    (hsources : ∀ name, name ∈ source.vars → name ∈ allowed)
    (hstate : ∀ name, name ∈ allowed →
      Metta.Subst.lookup runtime (fresh name) = none ∨
        subst runtime (Atom.var (fresh name)) =
          subst runtime (Atom.var name))
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (subst runtime (Atom.var right)).vars) :
    FreshInstance fresh (fun name => subst runtime (Atom.var name)) allowed
      (subst runtime copied) (subst runtime source) := by
  cases variant with
  | sym name =>
      simpa using (FreshInstance.same (fresh := fresh)
        (resolve := fun name => subst runtime (Atom.var name))
        (allowed := allowed) (Atom.sym name))
  | varSame name =>
      exact .same (subst runtime (Atom.var name))
  | var name hne =>
      have hname := hsources name (by simp [Atom.vars])
      rcases hstate name hname with hnone | hequal
      · have hfixed := subst_var_of_lookup_none runtime (fresh name) hnone
        rw [hfixed]
        exact .var name hname (havoids name hname name hname)
      · rw [hequal]
        exact .same (subst runtime (Atom.var name))
  | gnd ground =>
      simpa using (FreshInstance.same (fresh := fresh)
        (resolve := fun name => subst runtime (Atom.var name))
        (allowed := allowed) (Atom.gnd ground))
  | @expr copiedAtoms sourceAtoms variants =>
      have children : FreshInstanceList fresh
          (fun name => subst runtime (Atom.var name)) allowed
          (copiedAtoms.map (subst runtime))
          (sourceAtoms.map (subst runtime)) := by
        apply variants.instantiate runtime allowed
        · intro name hname
          apply hsources name
          simpa [Atom.vars] using hname
        · exact hstate
        · exact havoids
      simpa [subst_expr] using FreshInstance.expr children

/-- List companion to `FreshVariant.instantiate`. -/
theorem FreshVariantList.instantiate {fresh : String → String}
    {copied source : List Atom}
    (variants : FreshVariantList fresh copied source)
    (runtime : Subst) (allowed : List String)
    (hsources : ∀ name, name ∈ (source.map Atom.vars).flatten →
      name ∈ allowed)
    (hstate : ∀ name, name ∈ allowed →
      Metta.Subst.lookup runtime (fresh name) = none ∨
        subst runtime (Atom.var (fresh name)) =
          subst runtime (Atom.var name))
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (subst runtime (Atom.var right)).vars) :
    FreshInstanceList fresh (fun name => subst runtime (Atom.var name)) allowed
      (copied.map (subst runtime)) (source.map (subst runtime)) := by
  cases variants with
  | nil => exact .nil
  | @cons copiedHead sourceHead copiedTail sourceTail head tail =>
      apply FreshInstanceList.cons
      · apply head.instantiate runtime allowed
        · intro name hname
          apply hsources name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inl hname
        · exact hstate
        · exact havoids
      · apply tail.instantiate runtime allowed
        · intro name hname
          apply hsources name
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          exact Or.inr hname
        · exact hstate
        · exact havoids

end

/-- Canonical finite witness for an instantiated alpha-copy. -/
def freshResolvedWitness (fresh : String → String)
    (resolve : String → Atom) (allowed : List String) : Subst :=
  allowed.eraseDups.map (fun source => (fresh source, resolve source))

private theorem freshResolvedWitness_lookup_fresh_aux
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right) :
    ∀ source, source ∈ allowed →
      Metta.Subst.lookup
        (allowed.map (fun item => (fresh item, resolve item)))
        (fresh source) = some (resolve source) := by
  intro source hsource
  induction allowed with
  | nil => simp at hsource
  | cons head tail ih =>
      by_cases hequal : source = head
      · subst head
        simp [Metta.Subst.lookup]
      · have htail : source ∈ tail := by simpa [hequal] using hsource
        have hfreshNe : fresh source ≠ fresh head := by
          intro hnames
          exact hequal (hinjective source (by simp [htail]) head (by simp)
            hnames)
        have hbeq : (fresh source == fresh head) = false := by
          simp [hfreshNe]
        simp only [List.map_cons, Metta.Subst.lookup, hbeq,
          Bool.false_eq_true, if_false]
        exact ih (by
          intro left hleft right hright hnames
          exact hinjective left (by simp [hleft]) right (by simp [hright])
            hnames) htail

theorem freshResolvedWitness_lookup_fresh (fresh : String → String)
    (resolve : String → Atom) (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (source : String) (hsource : source ∈ allowed) :
    Metta.Subst.lookup (freshResolvedWitness fresh resolve allowed)
      (fresh source) = some (resolve source) := by
  apply freshResolvedWitness_lookup_fresh_aux fresh resolve allowed.eraseDups
  · intro left hleft right hright hnames
    exact hinjective left (by simpa using hleft) right (by simpa using hright)
      hnames
  · simpa using hsource

theorem freshResolvedWitness_generated (fresh : String → String)
    (resolve : String → Atom) (allowed : List String) :
    FreshResolvedGenerated fresh resolve allowed
      (freshResolvedWitness fresh resolve allowed) := by
  intro entry hentry
  unfold freshResolvedWitness at hentry
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hentry
  exact ⟨source, by simpa using hsource, rfl⟩

/-- One-pass substitution fixes an atom when none of its variables is in the
    substitution domain. -/
theorem apply_eq_self_of_lookup_none (binding : Subst) :
    (atom : Atom) →
      (∀ name, name ∈ atom.vars →
        Metta.Subst.lookup binding name = none) →
      Metta.Subst.apply binding atom = atom
  | .sym symbol, _ => by simp [Metta.Subst.apply]
  | .var name, hfree => by
      simp [Metta.Subst.apply, hfree name (by simp [Atom.vars])]
  | .gnd ground, _ => by simp [Metta.Subst.apply]
  | .expr atoms, hfree => by
      simp only [Metta.Subst.apply, Atom.expr.injEq]
      rw [List.map_congr_left (fun child hchild => by
        apply apply_eq_self_of_lookup_none binding child
        intro name hname
        apply hfree name
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩)]
      simp
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_unification atoms hchild)

/-- The instantiated witness is acyclic because every resolved target avoids
    every fresh-copy key. -/
def freshResolvedWitness_topological (fresh : String → String)
    (resolve : String → Atom) (allowed : List String)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars) :
    SubstTopological (freshResolvedWitness fresh resolve allowed) := by
  let unique := allowed.eraseDups
  let order := unique.map fresh
  have hgenerated := freshResolvedWitness_generated fresh resolve allowed
  refine
    { order := order
      nodup := ?_
      domain := ?_
      decreases := ?_ }
  · apply nodup_map_string_of_injective fresh unique
      (eraseDups_nodup_string allowed)
    intro left hleft right hright hnames
    exact hinjective left (by simpa [unique] using hleft) right
      (by simpa [unique] using hright) hnames
  · intro name
    constructor
    · intro hname hnone
      obtain ⟨source, hsource, hequal⟩ := List.mem_map.mp hname
      subst name
      have hlookup := freshResolvedWitness_lookup_fresh fresh resolve allowed
        hinjective source (by simpa [unique] using hsource)
      simp [hlookup] at hnone
    · intro hlookup
      have hkey : name ∈
          (freshResolvedWitness fresh resolve allowed).map Prod.fst :=
        lookup_ne_none_key_mem _ name hlookup
      simpa [freshResolvedWitness, order, unique, List.map_map,
        Function.comp_def] using hkey
  · intro bound value dependency hbound hdependency hdependencyLookup
    obtain ⟨source, hsource, hboundName, hvalue⟩ :=
      hgenerated.lookup_shape fresh resolve allowed
        (freshResolvedWitness fresh resolve allowed) bound value hbound
    subst bound
    subst value
    exact False.elim (hdependencyLookup
      (hgenerated.lookup_none_of_forbidden fresh resolve allowed
        (freshResolvedWitness fresh resolve allowed) dependency (by
          intro copied hcopied hequal
          apply havoids copied hcopied source hsource
          simpa [hequal] using hdependency)))

mutual

/-- One-pass application of the canonical instantiated witness identifies
    the copied and resolved sides exactly. -/
theorem FreshInstance.apply_witness {fresh : String → String}
    {resolve : String → Atom} {allowed : List String}
    {copied source : Atom}
    (related : FreshInstance fresh resolve allowed copied source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars) :
    Metta.Subst.apply (freshResolvedWitness fresh resolve allowed) copied =
      Metta.Subst.apply (freshResolvedWitness fresh resolve allowed) source := by
  cases related with
  | same => rfl
  | var source hsource hnotmem =>
      have hright : Metta.Subst.apply
          (freshResolvedWitness fresh resolve allowed) (resolve source) =
            resolve source := by
        apply apply_eq_self_of_lookup_none
        intro name hname
        apply (freshResolvedWitness_generated fresh resolve allowed).lookup_none_of_forbidden
        intro copied hcopied hequal
        apply havoids copied hcopied source hsource
        simpa [hequal] using hname
      simp [Metta.Subst.apply,
        freshResolvedWitness_lookup_fresh fresh resolve allowed hinjective
          source hsource, hright]
  | expr children =>
      simp only [Metta.Subst.apply, Atom.expr.injEq]
      exact children.apply_witness hinjective havoids

/-- List companion to `FreshInstance.apply_witness`. -/
theorem FreshInstanceList.apply_witness {fresh : String → String}
    {resolve : String → Atom} {allowed : List String}
    {copied source : List Atom}
    (related : FreshInstanceList fresh resolve allowed copied source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars) :
    copied.map
        (Metta.Subst.apply (freshResolvedWitness fresh resolve allowed)) =
      source.map
        (Metta.Subst.apply (freshResolvedWitness fresh resolve allowed)) := by
  cases related with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨head.apply_witness hinjective havoids,
        tail.apply_witness hinjective havoids⟩

end

/-- Every instantiated structural variant supplies a concrete exact unifier
    witness for the guard-step soundness theorem. -/
theorem FreshInstance.exact_witness {fresh : String → String}
    {resolve : String → Atom} {allowed : List String}
    {copied source : Atom}
    (related : FreshInstance fresh resolve allowed copied source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars) :
    ∃ witness, subst witness copied = subst witness source := by
  let witness := freshResolvedWitness fresh resolve allowed
  have happly : Metta.Subst.apply witness copied =
      Metta.Subst.apply witness source :=
    related.apply_witness hinjective havoids
  have htopological : SubstTopological witness :=
    freshResolvedWitness_topological fresh resolve allowed hinjective havoids
  have hdenotes : SubstLookupDenotes witness witness := by
    intro name value hlookup
    exact htopological.subst_var_of_lookup witness name value hlookup
  have hcopiedInvisible :=
    subst_apply_of_lookupDenotes witness witness hdenotes copied
  have hsourceInvisible :=
    subst_apply_of_lookupDenotes witness witness hdenotes source
  refine ⟨witness, ?_⟩
  calc
    subst witness copied =
        subst witness (Metta.Subst.apply witness copied) :=
      hcopiedInvisible.symm
    _ = subst witness (Metta.Subst.apply witness source) :=
      congrArg (subst witness) happly
    _ = subst witness source := hsourceInvisible

end PLeaTTa
