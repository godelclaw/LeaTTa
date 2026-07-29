import PLeaTTa.Proofs.Specialize
import PLeaTTa.PersistentSubstCore
import Std.Data.HashMap.Lemmas
import Std.Data.TreeMap.Lemmas

namespace PLeaTTa.PersistentSubst

open Metta (Atom Subst)

private theorem foldl_insert_contains (items : List String)
    (target : VarSet) (query : String) :
    (items.foldl (fun names name => names.insert name) target).contains query =
      (target.contains query || items.contains query) := by
  induction items generalizing target with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      rw [Std.HashSet.contains_insert]
      by_cases hhead : head = query
      · subst query
        simp
      · have hbeq : (head == query) = false :=
          beq_eq_false_iff_ne.mpr hhead
        have hreverse : (query == head) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm hhead)
        simp only [List.contains_cons, hbeq, hreverse, Bool.false_or]

def FreshSummary.Equivalent (left right : FreshSummary) : Prop :=
  left.maxLength = right.maxLength ∧
    (∀ suffix, left.containsSuffix suffix = right.containsSuffix suffix) ∧
    ∀ name, name ∈ left.names ↔ name ∈ right.names

theorem FreshSummary.Equivalent.refl (summary : FreshSummary) :
    summary.Equivalent summary :=
  ⟨rfl, fun _ => rfl, fun _ => Iff.rfl⟩

theorem FreshSummary.Equivalent.symm {left right : FreshSummary}
    (equivalent : left.Equivalent right) : right.Equivalent left :=
  ⟨equivalent.1.symm,
    fun suffix => (equivalent.2.1 suffix).symm,
    fun name => (equivalent.2.2 name).symm⟩

theorem FreshSummary.Equivalent.trans {left middle right : FreshSummary}
    (first : left.Equivalent middle) (second : middle.Equivalent right) :
    left.Equivalent right :=
  ⟨first.1.trans second.1,
    fun suffix => (first.2.1 suffix).trans (second.2.1 suffix),
    fun name => (first.2.2 name).trans (second.2.2 name)⟩

theorem FreshSummary.addName_contains (summary : FreshSummary)
    (name suffix : String) :
    (summary.addName name).containsSuffix suffix =
      (summary.containsSuffix suffix ||
        suffix.toList.isSuffixOf name.toList) := by
  simp [FreshSummary.addName, FreshSummary.containsSuffix, Bool.or_comm]

private theorem foldl_addName_contains (names : List String)
    (summary : FreshSummary) (suffix : String) :
    (names.foldl FreshSummary.addName summary).containsSuffix suffix =
      (summary.containsSuffix suffix ||
        names.any fun name => suffix.toList.isSuffixOf name.toList) := by
  induction names generalizing summary with
  | nil => simp
  | cons name rest ih =>
      rw [List.foldl_cons, ih, FreshSummary.addName_contains]
      simp [Bool.or_assoc]

private theorem foldl_addName_names (names : List String)
    (summary : FreshSummary) :
    (names.foldl FreshSummary.addName summary).names =
      names.reverse ++ summary.names := by
  induction names generalizing summary with
  | nil => rfl
  | cons name rest ih =>
      rw [List.foldl_cons, ih]
      simp [FreshSummary.addName, List.reverse_cons, List.append_assoc]

private def maxNameLengthFrom (initial : Nat) (names : List String) : Nat :=
  names.foldl (fun current name => max current name.length) initial

private theorem foldl_addName_maxLength (names : List String)
    (summary : FreshSummary) :
    (names.foldl FreshSummary.addName summary).maxLength =
      maxNameLengthFrom summary.maxLength names := by
  induction names generalizing summary with
  | nil => rfl
  | cons name rest ih =>
      simp only [List.foldl_cons]
      rw [ih (summary.addName name)]
      rfl

theorem FreshSummary.ofNames_maxLength (names : List String) :
    (FreshSummary.ofNames names).maxLength =
      names.foldl (fun current name => max current name.length) 0 := by
  simp only [FreshSummary.ofNames, foldl_addName_maxLength,
    FreshSummary.empty]
  rfl

theorem FreshSummary.ofNames_containsSuffix (names : List String)
    (suffix : String) :
    (FreshSummary.ofNames names).containsSuffix suffix =
      names.any fun name => suffix.toList.isSuffixOf name.toList := by
  unfold FreshSummary.ofNames
  rw [foldl_addName_contains]
  simp [FreshSummary.empty, FreshSummary.containsSuffix]

theorem FreshSummary.ofNames_names (names : List String) :
    (FreshSummary.ofNames names).names = names.reverse := by
  unfold FreshSummary.ofNames
  rw [foldl_addName_names]
  simp [FreshSummary.empty]

private theorem maxNameLengthFrom_le_iff (initial bound : Nat)
    (names : List String) :
    maxNameLengthFrom initial names ≤ bound ↔
      initial ≤ bound ∧ ∀ name ∈ names, name.length ≤ bound := by
  induction names generalizing initial with
  | nil => simp [maxNameLengthFrom]
  | cons name rest ih =>
      change maxNameLengthFrom (max initial name.length) rest ≤ bound ↔ _
      rw [ih]
      constructor
      · intro h
        rcases h with ⟨hmax, hrest⟩
        have hinitial : initial ≤ bound :=
          Nat.le_trans (Nat.le_max_left _ _) hmax
        have hname : name.length ≤ bound :=
          Nat.le_trans (Nat.le_max_right _ _) hmax
        exact ⟨hinitial, by
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact hname
          · exact hrest candidate member⟩
      · rintro ⟨hinitial, hall⟩
        constructor
        · exact Nat.max_le.mpr ⟨hinitial, hall name (by simp)⟩
        · intro candidate member
          exact hall candidate (List.mem_cons_of_mem name member)

private theorem maxNameLengthFrom_zero_eq_of_mem_iff
    (left right : List String)
    (same : ∀ name, name ∈ left ↔ name ∈ right) :
    maxNameLengthFrom 0 left = maxNameLengthFrom 0 right := by
  apply Nat.le_antisymm
  · apply (maxNameLengthFrom_le_iff 0 _ left).2
    have rightBounds :=
      (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 right) right).1
        (Nat.le_refl _)
    exact ⟨Nat.zero_le _, fun name member =>
      rightBounds.2 name ((same name).1 member)⟩
  · apply (maxNameLengthFrom_le_iff 0 _ right).2
    have leftBounds :=
      (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 left) left).1
        (Nat.le_refl _)
    exact ⟨Nat.zero_le _, fun name member =>
      leftBounds.2 name ((same name).2 member)⟩

private theorem any_eq_of_mem_iff (left right : List String)
    (predicate : String → Bool)
    (same : ∀ name, name ∈ left ↔ name ∈ right) :
    left.any predicate = right.any predicate := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    rcases List.any_eq_true.mp h with ⟨name, member, accepted⟩
    exact List.any_eq_true.mpr ⟨name, (same name).1 member, accepted⟩
  · intro h
    rcases List.any_eq_true.mp h with ⟨name, member, accepted⟩
    exact List.any_eq_true.mpr ⟨name, (same name).2 member, accepted⟩

theorem resolutionSeedHighWaterNames_le_iff (names : List String)
    (bound : Nat) :
    resolutionSeedHighWaterNames names ≤ bound ↔
      ∀ name ∈ names, resolutionSeedHighWaterName name ≤ bound := by
  induction names with
  | nil => simp [resolutionSeedHighWaterNames]
  | cons head rest ih =>
      simp only [resolutionSeedHighWaterNames, Nat.max_le, ih,
        List.mem_cons]
      constructor
      · rintro ⟨hhead, hrest⟩ name (rfl | member)
        · exact hhead
        · exact hrest name member
      · intro hall
        exact ⟨hall head (Or.inl rfl), fun name member =>
          hall name (Or.inr member)⟩

theorem resolutionSeedHighWaterNames_eq_of_mem_iff
    (left right : List String)
    (same : ∀ name, name ∈ left ↔ name ∈ right) :
    resolutionSeedHighWaterNames left =
      resolutionSeedHighWaterNames right := by
  apply Nat.le_antisymm
  · rw [resolutionSeedHighWaterNames_le_iff]
    intro name member
    have bounds := (resolutionSeedHighWaterNames_le_iff right
      (resolutionSeedHighWaterNames right)).mp (Nat.le_refl _)
    exact bounds name ((same name).mp member)
  · rw [resolutionSeedHighWaterNames_le_iff]
    intro name member
    have bounds := (resolutionSeedHighWaterNames_le_iff left
      (resolutionSeedHighWaterNames left)).mp (Nat.le_refl _)
    exact bounds name ((same name).mpr member)

theorem FreshSummary.ofNames_equivalent_of_mem_iff
    (left right : List String)
    (same : ∀ name, name ∈ left ↔ name ∈ right) :
    (FreshSummary.ofNames left).Equivalent (FreshSummary.ofNames right) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [FreshSummary.ofNames, foldl_addName_maxLength,
      FreshSummary.empty]
    exact maxNameLengthFrom_zero_eq_of_mem_iff left right same
  · intro suffix
    rw [FreshSummary.ofNames_containsSuffix,
      FreshSummary.ofNames_containsSuffix]
    exact any_eq_of_mem_iff left right
      (fun name => suffix.toList.isSuffixOf name.toList) same
  · intro name
    rw [FreshSummary.ofNames_names, FreshSummary.ofNames_names]
    simpa using same name

theorem FreshSummary.merge_contains (summary added : FreshSummary)
    (suffix : String) :
    (summary.merge added).containsSuffix suffix =
      (summary.containsSuffix suffix || added.containsSuffix suffix) := by
  simp [FreshSummary.merge, FreshSummary.containsSuffix, List.any_append,
    Bool.or_comm]

private theorem maxNameLengthFrom_zero_append (left right : List String) :
    maxNameLengthFrom 0 (left ++ right) =
      max (maxNameLengthFrom 0 left) (maxNameLengthFrom 0 right) := by
  apply Nat.le_antisymm
  · apply (maxNameLengthFrom_le_iff 0 _ (left ++ right)).2
    have leftBounds :=
      (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 left) left).1
        (Nat.le_refl _)
    have rightBounds :=
      (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 right) right).1
        (Nat.le_refl _)
    refine ⟨Nat.zero_le _, ?_⟩
    intro name member
    rcases List.mem_append.mp member with member | member
    · exact Nat.le_trans (leftBounds.2 name member) (Nat.le_max_left _ _)
    · exact Nat.le_trans (rightBounds.2 name member) (Nat.le_max_right _ _)
  · apply Nat.max_le.mpr
    constructor
    · apply (maxNameLengthFrom_le_iff 0 _ left).2
      have appendBounds :=
        (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 (left ++ right))
          (left ++ right)).1 (Nat.le_refl _)
      exact ⟨Nat.zero_le _, fun name member =>
        appendBounds.2 name (List.mem_append_left right member)⟩
    · apply (maxNameLengthFrom_le_iff 0 _ right).2
      have appendBounds :=
        (maxNameLengthFrom_le_iff 0 (maxNameLengthFrom 0 (left ++ right))
          (left ++ right)).1 (Nat.le_refl _)
      exact ⟨Nat.zero_le _, fun name member =>
        appendBounds.2 name (List.mem_append_right left member)⟩

theorem FreshSummary.merge_ofNames_equivalent_append
    (left right : List String) :
    ((FreshSummary.ofNames left).merge (FreshSummary.ofNames right)).Equivalent
      (FreshSummary.ofNames (left ++ right)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [FreshSummary.merge, FreshSummary.ofNames,
      foldl_addName_maxLength, FreshSummary.empty]
    exact (maxNameLengthFrom_zero_append left right).symm
  · intro suffix
    rw [FreshSummary.merge_contains]
    rw [FreshSummary.ofNames_containsSuffix,
      FreshSummary.ofNames_containsSuffix,
      FreshSummary.ofNames_containsSuffix]
    simp [List.any_append]
  · intro name
    simp [FreshSummary.merge, FreshSummary.ofNames_names,
      List.reverse_append]

theorem FreshSummary.merge_equivalent {summary summary' added added' :
    FreshSummary} (summaryEq : summary.Equivalent summary')
    (addedEq : added.Equivalent added') :
    (summary.merge added).Equivalent (summary'.merge added') := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FreshSummary.merge, summaryEq.1, addedEq.1]
  · intro suffix
    rw [FreshSummary.merge_contains, FreshSummary.merge_contains,
      summaryEq.2.1 suffix, addedEq.2.1 suffix]
  · intro name
    simp only [FreshSummary.merge, List.mem_append]
    exact or_congr (addedEq.2.2 name) (summaryEq.2.2 name)

private theorem lookup_pair_mem (entries : Subst) (name : String)
    (value : Atom) (lookup : Metta.Subst.lookup entries name = some value) :
    (name, value) ∈ entries := by
  induction entries with
  | nil => simp [Metta.Subst.lookup] at lookup
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      by_cases hkey : name = key
      · subst key
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at lookup
        subst target
        simp
      · have hbeq : (name == key) = false := by simp [hkey]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at lookup
        exact List.mem_cons_of_mem (key, target) (ih lookup)

private theorem freshAtomSize_le_sum_of_mem {atom : Atom} :
    (atoms : List Atom) → atom ∈ atoms →
      atom.size ≤ (atoms.map Atom.size).sum
  | [], member => by simp at member
  | head :: tail, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (freshAtomSize_le_sum_of_mem tail member)
          (Nat.le_add_left _ _)

@[elab_as_elim, induction_eliminator]
private def freshAtomRecAux {motive : Atom → Prop}
    (sym : ∀ name, motive (Atom.sym name))
    (var : ∀ name, motive (Atom.var name))
    (gnd : ∀ ground, motive (Atom.gnd ground))
    (expr : ∀ atoms, (∀ atom ∈ atoms, motive atom) →
      motive (Atom.expr atoms)) :
    (atom : Atom) → motive atom
  | .sym name => sym name
  | .var name => var name
  | .gnd ground => gnd ground
  | .expr atoms =>
      expr atoms (fun atom _ => freshAtomRecAux sym var gnd expr atom)
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  have hle := freshAtomSize_le_sum_of_mem atoms (by assumption)
  omega

private theorem atomsClosed_eq_true_iff_vars_nil
    (atoms : List Atom)
    (correct : ∀ atom ∈ atoms,
      atomClosed atom = true ↔ atom.vars = []) :
    atomsClosed atoms = true ↔ (atoms.map Atom.vars).flatten = [] := by
  induction atoms with
  | nil => simp [atomsClosed]
  | cons atom rest ih =>
      have hhead := correct atom (by simp)
      have htail := ih (fun child member =>
        correct child (by simp [member]))
      simp [atomsClosed, hhead, htail]

theorem atomClosed_eq_true_iff_vars_nil (atom : Atom) :
    atomClosed atom = true ↔ atom.vars = [] := by
  induction atom using freshAtomRecAux with
  | sym name => simp [atomClosed, Atom.vars]
  | var name => simp [atomClosed, Atom.vars]
  | gnd ground => simp [atomClosed, Atom.vars]
  | expr atoms ih =>
      simpa [atomClosed, Atom.vars] using
        atomsClosed_eq_true_iff_vars_nil atoms ih

@[simp] theorem atomDependencies_eq_vars (atom : Atom) :
    atomDependencies atom = atom.vars := by
  by_cases hclosed : atomClosed atom = true
  · have hvars := (atomClosed_eq_true_iff_vars_nil atom).mp hclosed
    simp [atomDependencies, hclosed, hvars]
  · simp [atomDependencies, hclosed]

namespace PreparedAtom

@[simp] theorem atom_ofAtom (atom : Atom) :
    (ofAtom atom).atom = atom := rfl

@[simp] theorem variables_ofAtom (atom : Atom) :
    (ofAtom atom).variables = atom.vars := rfl

@[simp] theorem atom_ofClosed (atom : Atom) :
    (ofClosed atom).atom = atom := rfl

@[simp] theorem variables_ofClosed (atom : Atom) :
    (ofClosed atom).variables = [] := rfl

@[simp] theorem atom_mkExpr (children : List PreparedAtom) :
    (mkExpr children).atom = Atom.expr (children.map PreparedAtom.atom) := rfl

@[simp] theorem variables_mkExpr (children : List PreparedAtom) :
    (mkExpr children).variables = children.flatMap PreparedAtom.variables :=
  rfl

theorem ofAtom_valid (atom : Atom) : (ofAtom atom).Valid := by
  exact Valid.summary atom

theorem ofClosed_valid (atom : Atom) (closed : atom.vars = []) :
    (ofClosed atom).Valid := by
  simpa [ofClosed, closed] using Valid.summary atom

theorem Valid.variables_eq : ∀ {prepared : PreparedAtom},
    prepared.Valid → prepared.variables = prepared.atom.vars
  | _, .summary atom => rfl
  | _, .cached atom cachedVariables exact exactSound variablesSound =>
      variablesSound
  | _, .expr children childrenValid => by
      simp only [mkExpr, PreparedAtom.variables, atom, Atom.vars, List.flatMap_def,
        List.map_map]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro child member
      simpa [Function.comp_def] using
        Valid.variables_eq (childrenValid child member)

theorem Valid.exact_eq {prepared : PreparedAtom}
    (_valid : prepared.Valid) {result : Option AtomExactKey}
    (found : prepared.exact = some result) :
    result = atomExactKey prepared.atom :=
  prepared.exact_sound result found

/-- Every successful recent-root lookup returns a closed cached atom equal
to the requested raw root. -/
theorem findRecentClosed_some {target : Atom} {recent : List PreparedAtom}
    {prepared : PreparedAtom}
    (found : findRecentClosed target recent = some prepared) :
    prepared ∈ recent ∧ prepared.variables = [] ∧
      prepared.atom = target := by
  induction recent with
  | nil => simp [findRecentClosed] at found
  | cons candidate rest ih =>
      cases hmatch :
          (candidate.variables.isEmpty && candidate.sameAtom target) with
      | false =>
          have tail := ih (by simpa [findRecentClosed, hmatch] using found)
          exact ⟨by simp [tail.1], tail.2⟩
      | true =>
          have selected : candidate = prepared := by
            simpa [findRecentClosed, hmatch] using found
          subst candidate
          have parts := Bool.and_eq_true_iff.mp hmatch
          have closed : prepared.variables = [] := by
            cases hvariables : prepared.variables with
            | nil => rfl
            | cons head tail => simp [hvariables] at parts
          exact ⟨by simp, closed, sameAtom_eq_true parts.2⟩

theorem refreshRecent_valid {fresh previous : List PreparedAtom}
    (freshValid : ∀ prepared ∈ fresh, prepared.Valid)
    (_previousValid : ∀ prepared ∈ previous, prepared.Valid) :
    ∀ prepared ∈ refreshRecent fresh previous, prepared.Valid := by
  intro prepared member
  exact freshValid prepared member

theorem mkExpr_valid (children : List PreparedAtom)
    (valid : ∀ child ∈ children, child.Valid) :
    (mkExpr children).Valid :=
  Valid.expr children valid

theorem mkExprFrom_valid (root : Atom) (children : List PreparedAtom)
    (valid : ∀ child ∈ children, child.Valid) :
    (mkExprFrom root children).Valid := by
  cases root with
  | sym name => exact ofAtom_valid (.sym name)
  | var name => exact ofAtom_valid (.var name)
  | gnd ground => exact ofAtom_valid (.gnd ground)
  | expr atoms =>
      rw [mkExprFrom_eq_mkExpr]
      exact mkExpr_valid children valid

theorem lookup_eraseSubst (entries : PreparedSubst) (source : String) :
    Metta.Subst.lookup (eraseSubst entries) source =
      (lookup entries source).map PreparedAtom.atom := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, target⟩
      change
        (if source == name then some target.atom
          else Metta.Subst.lookup (eraseSubst rest) source) =
        (if source == name then some target
          else PreparedAtom.lookup rest source).map PreparedAtom.atom
      by_cases equal : source = name
      · simp [equal]
      · simp [equal]
        exact ih

theorem PreparedSubst.Valid.lookup {entries : PreparedSubst}
    (valid : entries.Valid) (source : String) (target : PreparedAtom)
    (found : lookup entries source = some target) : target.Valid := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      change
        (if source == name then some value
          else PreparedAtom.lookup rest source) = some target at found
      by_cases equal : source = name
      · simp [equal] at found
        subst target
        exact valid (name, value) (by simp)
      · simp [equal] at found
        exact ih (fun entry member => valid entry (by simp [member])) found

end PreparedAtom

/-- A successful transient space-root lookup returns the indexed root whose
raw atom is exactly the requested atom. -/
theorem findClosedRoot_some {target : Atom} {roots : List ClosedRoot}
    {root : ClosedRoot} (found : findClosedRoot target roots = some root) :
    root ∈ roots ∧ root.atom = target := by
  induction roots with
  | nil => simp [findClosedRoot] at found
  | cons candidate rest ih =>
      cases equal : candidate.sameAtom target with
      | false =>
          have tail := ih (by simpa [findClosedRoot, equal] using found)
          exact ⟨by simp [tail.1], tail.2⟩
      | true =>
          have selected : candidate = root := by
            simpa [findClosedRoot, equal] using found
          subst candidate
          exact ⟨by simp, ClosedRoot.sameAtom_eq_true equal⟩

theorem transformDependenciesPrepared_eq (generated :
    PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (dependencies : List String) :
    transformDependenciesPrepared generated dependencies =
      transformDependencies (PreparedAtom.eraseSubst generated)
        dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      cases found : PreparedAtom.lookup generated dependency with
      | none =>
          have erasedNone : Metta.Subst.lookup
              (PreparedAtom.eraseSubst generated) dependency = none := by
            rw [PreparedAtom.lookup_eraseSubst, found]
            rfl
          simp only [transformDependenciesPrepared, transformDependencies,
            List.flatMap_cons, found, erasedNone, List.singleton_append]
          apply congrArg (dependency :: ·)
          simpa only [transformDependenciesPrepared, transformDependencies]
            using ih
      | some target =>
          have targetValid := valid.lookup dependency target found
          have erasedSome : Metta.Subst.lookup
              (PreparedAtom.eraseSubst generated) dependency =
                some target.atom := by
            rw [PreparedAtom.lookup_eraseSubst, found]
            rfl
          simp only [transformDependenciesPrepared, transformDependencies,
            List.flatMap_cons, found, erasedSome]
          rw [PersistentSubst.atomDependencies_eq_vars,
            ← targetValid.variables_eq]
          apply congrArg (target.variables ++ ·)
          simpa only [transformDependenciesPrepared, transformDependencies]
            using ih

theorem DependencyGraph.transformSourcesPrepared_eq
    (graph : DependencyGraph) (generated : PreparedAtom.PreparedSubst)
    (valid : generated.Valid) (sources : List String) :
    graph.transformSourcesPrepared generated sources =
      graph.transformSources (PreparedAtom.eraseSubst generated) sources := by
  induction sources generalizing graph with
  | nil => rfl
  | cons source rest ih =>
      cases found : graph.forward[source]? with
      | none =>
          simp [DependencyGraph.transformSourcesPrepared,
            DependencyGraph.transformSources, found, ih]
      | some dependencies =>
          simp only [DependencyGraph.transformSourcesPrepared,
            DependencyGraph.transformSources, found]
          rw [transformDependenciesPrepared_eq generated valid dependencies]
          exact ih _

theorem DependencyGraph.addGeneratedPrepared_eq
    (graph : DependencyGraph) (generated : PreparedAtom.PreparedSubst)
    (valid : generated.Valid) :
    graph.addGeneratedPrepared generated =
      graph.addGenerated (PreparedAtom.eraseSubst generated) := by
  induction generated generalizing graph with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨source, target⟩
      have targetValid : target.Valid := valid (source, target) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun entry member => valid entry (by simp [member])
      have dependencies : PersistentSubst.atomDependencies target.atom =
          target.variables := by
        rw [PersistentSubst.atomDependencies_eq_vars,
          ← targetValid.variables_eq]
      simp only [DependencyGraph.addGeneratedPrepared,
        PreparedAtom.eraseSubst, List.map_cons,
        DependencyGraph.addGenerated, dependencies]
      split <;> exact ih _ restValid

theorem DependencyGraph.composePrepared_eq (graph : DependencyGraph)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    graph.composePrepared generated =
      graph.compose (PreparedAtom.eraseSubst generated) := by
  unfold DependencyGraph.composePrepared DependencyGraph.compose
  let affected := graph.affectedSources
    (PreparedAtom.eraseSubst generated)
  change
    DependencyGraph.addGeneratedPrepared
        (graph.transformSourcesPrepared generated affected.toList) generated =
      DependencyGraph.addGenerated
        (graph.transformSources (PreparedAtom.eraseSubst generated)
          affected.toList) (PreparedAtom.eraseSubst generated)
  rw [graph.transformSourcesPrepared_eq generated valid]
  exact DependencyGraph.addGeneratedPrepared_eq _ generated valid

private theorem apply_vars_origin (entries : Subst) :
    ∀ atom name, name ∈ (Metta.Subst.apply entries atom).vars →
      name ∈ atom.vars ∨ name ∈ bindingNames entries := by
  intro atom
  induction atom using freshAtomRecAux with
  | sym symbol => simp [Metta.Subst.apply, Atom.vars]
  | gnd ground => simp [Metta.Subst.apply, Atom.vars]
  | var source =>
      intro name member
      cases lookup : Metta.Subst.lookup entries source with
      | none =>
          simp only [Metta.Subst.apply, lookup, Option.getD_none,
            Atom.vars, List.mem_singleton] at member
          subst name
          exact Or.inl (by simp [Atom.vars])
      | some value =>
          simp only [Metta.Subst.apply, lookup, Option.getD_some] at member
          apply Or.inr
          simp only [bindingNames, List.mem_flatMap]
          exact ⟨(source, value), lookup_pair_mem entries source value lookup,
            by simp [member]⟩
  | expr atoms ih =>
      intro name member
      simp only [Metta.Subst.apply, Atom.vars] at member
      rw [List.mem_flatten] at member
      obtain ⟨variableList, variableListMem, nameMem⟩ := member
      rcases List.mem_map.mp variableListMem with ⟨applied, appliedMem, rfl⟩
      rcases List.mem_map.mp appliedMem with ⟨child, childMem, rfl⟩
      rcases ih child childMem name nameMem with source | generated
      · exact Or.inl (by
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, childMem, rfl⟩, source⟩)
      · exact Or.inr generated

private theorem vars_covered_by_apply (entries : Subst) :
    ∀ atom name, name ∈ atom.vars →
      name ∈ bindingNames entries ∨
        name ∈ (Metta.Subst.apply entries atom).vars := by
  intro atom
  induction atom using freshAtomRecAux with
  | sym symbol => simp [Atom.vars]
  | gnd ground => simp [Atom.vars]
  | var source =>
      intro name member
      simp only [Atom.vars, List.mem_singleton] at member
      subst name
      cases lookup : Metta.Subst.lookup entries source with
      | none =>
          exact Or.inr (by
            simp [Metta.Subst.apply, lookup, Atom.vars])
      | some value =>
          apply Or.inl
          simp only [bindingNames, List.mem_flatMap]
          exact ⟨(source, value), lookup_pair_mem entries source value lookup,
            by simp⟩
  | expr atoms ih =>
      intro name member
      simp only [Atom.vars] at member
      rw [List.mem_flatten] at member
      obtain ⟨variableList, variableListMem, nameMem⟩ := member
      rcases List.mem_map.mp variableListMem with ⟨child, childMem, rfl⟩
      rcases ih child childMem name nameMem with generated | applied
      · exact Or.inl generated
      · exact Or.inr (by
          simp only [Metta.Subst.apply, Atom.vars, List.mem_flatten,
            List.mem_map]
          exact ⟨(Metta.Subst.apply entries child).vars,
            ⟨Metta.Subst.apply entries child,
              ⟨child, childMem, rfl⟩, rfl⟩, applied⟩)

private theorem mem_bindingNames_iff (entries : Subst) (name : String) :
    name ∈ bindingNames entries ↔
      ∃ key value, (key, value) ∈ entries ∧
        (name = key ∨ name ∈ value.vars) := by
  simp [bindingNames, List.mem_flatMap]

theorem bindingNames_compose_mem_iff (base generated : Subst)
    (name : String) :
    name ∈ bindingNames (Metta.Subst.compose generated base) ↔
      name ∈ bindingNames base ∨ name ∈ bindingNames generated := by
  constructor
  · rw [mem_bindingNames_iff]
    rintro ⟨key, value, bindingMem, nameMem⟩
    simp only [Metta.Subst.compose, List.mem_append, List.mem_map] at bindingMem
    rcases bindingMem with mapped | generatedMem
    · rcases mapped with ⟨⟨baseKey, baseValue⟩, baseMem, equality⟩
      simp only at equality
      cases equality
      rcases nameMem with rfl | nameMem
      · exact Or.inl ((mem_bindingNames_iff base name).2
          ⟨name, baseValue, baseMem, Or.inl rfl⟩)
      · rcases apply_vars_origin generated baseValue name nameMem with
          old | new
        · exact Or.inl ((mem_bindingNames_iff base name).2
            ⟨key, baseValue, baseMem, Or.inr old⟩)
        · exact Or.inr new
    · exact Or.inr ((mem_bindingNames_iff generated name).2
        ⟨key, value, generatedMem, nameMem⟩)
  · intro member
    rcases member with old | new
    · rcases (mem_bindingNames_iff base name).1 old with
        ⟨key, value, baseMem, nameMem⟩
      rw [mem_bindingNames_iff]
      rcases nameMem with rfl | nameMem
      · have composedMem :
            (name, Metta.Subst.apply generated value) ∈
              Metta.Subst.compose generated base := by
          unfold Metta.Subst.compose
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨(name, value), baseMem, rfl⟩
        exact ⟨name, Metta.Subst.apply generated value,
          composedMem, Or.inl rfl⟩
      · rcases vars_covered_by_apply generated value name nameMem with
          generatedName | appliedName
        · rcases (mem_bindingNames_iff generated name).1 generatedName with
            ⟨generatedKey, generatedValue, generatedMem, generatedNameMem⟩
          have composedMem : (generatedKey, generatedValue) ∈
              Metta.Subst.compose generated base := by
            unfold Metta.Subst.compose
            exact List.mem_append_right _ generatedMem
          exact ⟨generatedKey, generatedValue,
            composedMem, generatedNameMem⟩
        · have composedMem :
              (key, Metta.Subst.apply generated value) ∈
                Metta.Subst.compose generated base := by
            unfold Metta.Subst.compose
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨(key, value), baseMem, rfl⟩
          exact ⟨key, Metta.Subst.apply generated value,
            composedMem, Or.inr appliedName⟩
    · rcases (mem_bindingNames_iff generated name).1 new with
        ⟨key, value, generatedMem, nameMem⟩
      rw [mem_bindingNames_iff]
      have composedMem : (key, value) ∈
          Metta.Subst.compose generated base := by
        unfold Metta.Subst.compose
        exact List.mem_append_right _ generatedMem
      exact ⟨key, value, composedMem, nameMem⟩

theorem FreshSummary.ofSubst_compose_equivalent (base generated : Subst) :
    ((FreshSummary.ofSubst base).merge (FreshSummary.ofSubst generated)).Equivalent
      (FreshSummary.ofSubst (Metta.Subst.compose generated base)) := by
  unfold FreshSummary.ofSubst
  apply (FreshSummary.merge_ofNames_equivalent_append
    (bindingNames base) (bindingNames generated)).trans
  apply FreshSummary.ofNames_equivalent_of_mem_iff
  intro name
  rw [List.mem_append, bindingNames_compose_mem_iff]

theorem transformDependencies_eq_apply_vars (generated : Subst) :
    ∀ atom : Atom,
      transformDependencies generated atom.vars =
        (Metta.Subst.apply generated atom).vars := by
  intro atom
  induction atom with
  | sym name => simp [transformDependencies, Atom.vars, Metta.Subst.apply]
  | var name =>
      cases hlookup : Metta.Subst.lookup generated name <;>
        simp [transformDependencies, Atom.vars, Metta.Subst.apply, hlookup]
  | gnd ground => simp [transformDependencies, Atom.vars, Metta.Subst.apply]
  | expr atoms ih =>
      simp only [Atom.vars, Metta.Subst.apply]
      induction atoms with
      | nil => rfl
      | cons head tail tailIH =>
          simp only [List.map_cons, List.flatten_cons]
          rw [show transformDependencies generated
                (head.vars ++ (tail.map Atom.vars).flatten) =
              transformDependencies generated head.vars ++
                transformDependencies generated (tail.map Atom.vars).flatten by
            simp [transformDependencies]]
          rw [ih head (by simp)]
          rw [tailIH (fun child member => ih child (by simp [member]))]

theorem insertAll_contains (target source : VarSet) (query : String) :
    (insertAll target source).contains query =
      (target.contains query || source.contains query) := by
  unfold insertAll
  rw [foldl_insert_contains]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, Std.HashSet.mem_toList,
    Std.HashSet.mem_iff_contains]

theorem DependencyGraph.affectedSources_contains (graph : DependencyGraph)
    (generated : Subst) (source : String) :
    (graph.affectedSources generated).contains source =
      generated.any fun binding =>
        graph.reverseContains binding.1 source := by
  induction generated with
  | nil => simp [DependencyGraph.affectedSources]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [DependencyGraph.affectedSources, List.any_cons]
      cases husers : graph.reverse[key]? with
      | none =>
          simp [DependencyGraph.reverseContains, husers, ih]
      | some users =>
          rw [insertAll_contains, ih]
          simp [DependencyGraph.reverseContains, husers, Bool.or_comm]

theorem subst_lookup_isSome_iff_mem_keys (entries : Subst) (name : String) :
    (Metta.Subst.lookup entries name).isSome = true ↔
      name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases hkey : name = key
      · subst key
        simp [Metta.Subst.lookup]
      · have hreverse : key ≠ name := Ne.symm hkey
        simp [Metta.Subst.lookup, hkey, ih]

theorem lookup_eq_none_of_dependenciesTouched_false (generated : Subst)
    (dependencies : List String)
    (untouched : dependenciesTouched generated dependencies = false)
    (dependency : String) (member : dependency ∈ dependencies) :
    Metta.Subst.lookup generated dependency = none := by
  induction generated with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      have parts : dependencies.contains key = false ∧
          dependenciesTouched rest dependencies = false := by
        simpa [dependenciesTouched, Bool.or_eq_false_iff] using untouched
      have hkey : dependency ≠ key := by
        intro equality
        subst key
        have contains : dependencies.contains dependency = true :=
          List.contains_iff_mem.mpr member
        exact False.elim (Bool.noConfusion (contains.symm.trans parts.1))
      have hbeq : (dependency == key) = false :=
        beq_eq_false_iff_ne.mpr hkey
      simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
      exact ih parts.2

theorem transformDependencies_eq_self_of_lookup_none (generated : Subst)
    (dependencies : List String)
    (lookupNone : ∀ dependency ∈ dependencies,
      Metta.Subst.lookup generated dependency = none) :
    transformDependencies generated dependencies = dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      simp only [transformDependencies, List.flatMap_cons]
      rw [lookupNone dependency (by simp)]
      simp only [List.singleton_append]
      change dependency :: transformDependencies generated rest =
        dependency :: rest
      rw [ih]
      intro item member
      exact lookupNone item (by simp [member])

theorem transformDependencies_eq_self_of_untouched (generated : Subst)
    (dependencies : List String)
    (untouched : dependenciesTouched generated dependencies = false) :
    transformDependencies generated dependencies = dependencies := by
  apply transformDependencies_eq_self_of_lookup_none
  intro dependency member
  exact lookup_eq_none_of_dependenciesTouched_false generated dependencies
    untouched dependency member

theorem DependencyGraph.reverseContains_addReverse
    (graph : DependencyGraph) (dependency source queryDependency querySource : String) :
    ({ graph with reverse := (DependencyGraph.addReverse graph.reverse
        dependency source) } :
        DependencyGraph).reverseContains queryDependency querySource =
      (((dependency == queryDependency) && (source == querySource)) ||
        graph.reverseContains queryDependency querySource) := by
  unfold DependencyGraph.addReverse DependencyGraph.reverseContains
  rw [Std.HashMap.getElem?_insert]
  by_cases hdependency : dependency = queryDependency
  · subst queryDependency
    simp only [beq_self_eq_true, Bool.true_and, if_true]
    cases husers : graph.reverse[dependency]? with
    | none => simp [Std.HashSet.contains_insert]
    | some users => simp [Std.HashSet.contains_insert]
  · have hbeq : (dependency == queryDependency) = false := by
      simp [hdependency]
    simp only [hbeq, Bool.false_eq_true, Bool.false_and, Bool.false_or,
      if_false]

theorem DependencyGraph.reverseContains_removeReverse
    (graph : DependencyGraph) (dependency source queryDependency querySource : String) :
    ({ graph with reverse := (DependencyGraph.removeReverse graph.reverse
        dependency source) } :
        DependencyGraph).reverseContains queryDependency querySource =
      ((!((dependency == queryDependency) && (source == querySource))) &&
        graph.reverseContains queryDependency querySource) := by
  unfold DependencyGraph.removeReverse DependencyGraph.reverseContains
  cases husers : graph.reverse[dependency]? with
  | none =>
      by_cases hdependency : dependency = queryDependency
      · subst queryDependency
        simp [husers]
      · have hbeq : (dependency == queryDependency) = false := by
          simp [hdependency]
        simp [hbeq]
  | some users =>
      let remaining := users.erase source
      by_cases hempty : (remaining.size == 0) = true
      · have hisEmpty : remaining.isEmpty = true := by
          rw [Std.HashSet.isEmpty_eq_size_eq_zero]
          exact hempty
        have hremaining : remaining.contains querySource = false :=
          (Std.HashSet.isEmpty_iff_forall_contains.mp hisEmpty) querySource
        simp only [remaining, hempty, if_true]
        rw [Std.HashMap.getElem?_erase]
        by_cases hdependency : dependency = queryDependency
        · subst queryDependency
          simp only [beq_self_eq_true, if_true, Bool.true_and]
          have removed :
              (!(source == querySource) && users.contains querySource) =
                false := by
            simpa [remaining, Std.HashSet.contains_erase] using hremaining
          rw [husers]
          exact removed.symm
        · have hbeq : (dependency == queryDependency) = false := by
            simp [hdependency]
          simp [hbeq]
      · have hemptyFalse : (remaining.size == 0) = false := by
          cases hvalue : remaining.size == 0
          · rfl
          · exact False.elim (hempty hvalue)
        simp only [remaining, hemptyFalse, Bool.false_eq_true,
          if_false]
        rw [Std.HashMap.getElem?_insert]
        by_cases hdependency : dependency = queryDependency
        · subst queryDependency
          simp only [beq_self_eq_true, if_true, Bool.true_and]
          rw [Std.HashSet.contains_erase]
          simp [husers]
        · have hbeq : (dependency == queryDependency) = false := by
            simp [hdependency]
          simp [hbeq]

theorem DependencyGraph.reverseContains_fold_add
    (graph : DependencyGraph) (dependencies : List String)
    (source queryDependency querySource : String) :
    ({ graph with reverse := (dependencies.foldl
        (fun reverse dependency =>
          DependencyGraph.addReverse reverse dependency source)
        graph.reverse) } : DependencyGraph).reverseContains
          queryDependency querySource =
      (((dependencies.contains queryDependency) && (source == querySource)) ||
        graph.reverseContains queryDependency querySource) := by
  induction dependencies generalizing graph with
  | nil => simp
  | cons dependency rest ih =>
      simp only [List.foldl_cons, List.contains_cons]
      let next : DependencyGraph :=
        { graph with reverse := (DependencyGraph.addReverse graph.reverse
            dependency source) }
      change ({ next with reverse := (rest.foldl
          (fun reverse item =>
            DependencyGraph.addReverse reverse item source)
          next.reverse) } : DependencyGraph).reverseContains
            queryDependency querySource = _
      rw [ih next]
      rw [DependencyGraph.reverseContains_addReverse]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
        beq_iff_eq]
      constructor
      · intro hypothesis
        rcases hypothesis with direct | addedOrOld
        · exact Or.inl ⟨Or.inr direct.1, direct.2⟩
        · rcases addedOrOld with added | old
          · exact Or.inl ⟨Or.inl added.1.symm, added.2⟩
          · exact Or.inr old
      · intro hypothesis
        rcases hypothesis with combined | old
        · rcases combined.1 with added | direct
          · exact Or.inr (Or.inl ⟨added.symm, combined.2⟩)
          · exact Or.inl ⟨direct, combined.2⟩
        · exact Or.inr (Or.inr old)

theorem DependencyGraph.reverseContains_fold_remove
    (graph : DependencyGraph) (dependencies : List String)
    (source queryDependency querySource : String) :
    ({ graph with reverse := (dependencies.foldl
        (fun reverse dependency =>
          DependencyGraph.removeReverse reverse dependency source)
        graph.reverse) } : DependencyGraph).reverseContains
          queryDependency querySource =
      ((!((dependencies.contains queryDependency) &&
          (source == querySource))) &&
        graph.reverseContains queryDependency querySource) := by
  induction dependencies generalizing graph with
  | nil => simp
  | cons dependency rest ih =>
      simp only [List.foldl_cons, List.contains_cons]
      let next : DependencyGraph :=
        { graph with reverse := (DependencyGraph.removeReverse graph.reverse
            dependency source) }
      change ({ next with reverse := (rest.foldl
          (fun reverse item =>
            DependencyGraph.removeReverse reverse item source)
          next.reverse) } : DependencyGraph).reverseContains
            queryDependency querySource = _
      rw [ih next]
      rw [DependencyGraph.reverseContains_removeReverse]
      by_cases hdependency : dependency = queryDependency
      · subst queryDependency
        by_cases hsource : source = querySource
        · subst querySource
          simp
        · simp [hsource]
      · have hforward : (dependency == queryDependency) = false := by
          simp [hdependency]
        have hreverse : (queryDependency == dependency) = false := by
          exact beq_eq_false_iff_ne.mpr (Ne.symm hdependency)
        simp [hforward, hreverse]

theorem DependencyGraph.forward_bindSource (graph : DependencyGraph)
    (source : String) (dependencies : List String) (query : String) :
    (graph.bindSource source dependencies).forward[query]? =
      if (source == query) = true then some dependencies
      else graph.forward[query]? := by
  unfold DependencyGraph.bindSource
  exact Std.HashMap.getElem?_insert

theorem DependencyGraph.reverseContains_bindSource
    (graph : DependencyGraph) (source : String)
    (dependencies : List String) (queryDependency querySource : String) :
    (graph.bindSource source dependencies).reverseContains
        queryDependency querySource =
      (((dependencies.contains queryDependency) && (source == querySource)) ||
        graph.reverseContains queryDependency querySource) := by
  unfold DependencyGraph.bindSource
  exact graph.reverseContains_fold_add dependencies source
    queryDependency querySource

theorem DependencyGraph.forward_unbindSource (graph : DependencyGraph)
    (source query : String) :
    (graph.unbindSource source).forward[query]? =
      match graph.forward[source]? with
      | none => graph.forward[query]?
      | some _ => if (source == query) = true then none
          else graph.forward[query]? := by
  unfold DependencyGraph.unbindSource
  cases graph.forward[source]? <;> simp [Std.HashMap.getElem?_erase]

theorem DependencyGraph.reverseContains_unbindSource
    (graph : DependencyGraph) (source queryDependency querySource : String) :
    (graph.unbindSource source).reverseContains queryDependency querySource =
      match graph.forward[source]? with
      | none => graph.reverseContains queryDependency querySource
      | some dependencies =>
          (!((dependencies.contains queryDependency) &&
              (source == querySource))) &&
            graph.reverseContains queryDependency querySource := by
  unfold DependencyGraph.unbindSource
  cases hforward : graph.forward[source]? with
  | none => rfl
  | some dependencies =>
      exact graph.reverseContains_fold_remove dependencies source
        queryDependency querySource

theorem DependencyGraph.forward_replaceSource (graph : DependencyGraph)
    (source : String) (dependencies : List String) (query : String) :
    (graph.replaceSource source dependencies).forward[query]? =
      if (source == query) = true then some dependencies
      else graph.forward[query]? := by
  unfold DependencyGraph.replaceSource
  rw [DependencyGraph.forward_bindSource,
    DependencyGraph.forward_unbindSource]
  split <;> rename_i hsource
  · rfl
  · split <;> rfl

theorem DependencyGraph.reverseContains_replaceSource
    (graph : DependencyGraph) (source : String)
    (dependencies : List String) (queryDependency querySource : String) :
    (graph.replaceSource source dependencies).reverseContains
        queryDependency querySource =
      (((dependencies.contains queryDependency) && (source == querySource)) ||
        match graph.forward[source]? with
        | none => graph.reverseContains queryDependency querySource
        | some oldDependencies =>
            (!((oldDependencies.contains queryDependency) &&
                (source == querySource))) &&
              graph.reverseContains queryDependency querySource) := by
  unfold DependencyGraph.replaceSource
  rw [DependencyGraph.reverseContains_bindSource,
    DependencyGraph.reverseContains_unbindSource]

structure DependencyGraph.Models (graph : DependencyGraph)
    (values : String → Option (List String)) : Prop where
  forward_eq : ∀ source,
    graph.forward[source]? = values source
  reverse_eq : ∀ dependency source,
    graph.reverseContains dependency source =
      match values source with
      | none => false
      | some dependencies => dependencies.contains dependency

abbrev DependencyGraph.Coherent (graph : DependencyGraph)
    (entries : Subst) : Prop :=
  graph.Models fun source =>
    (Metta.Subst.lookup entries source).map Atom.vars

theorem DependencyGraph.affectedSources_contains_of_models
    (graph : DependencyGraph) (generated : Subst)
    (values : String → Option (List String)) (coherent : graph.Models values)
    (source : String) :
    (graph.affectedSources generated).contains source =
      match values source with
      | none => false
      | some dependencies => dependenciesTouched generated dependencies := by
  rw [DependencyGraph.affectedSources_contains]
  cases hvalue : values source with
  | none =>
      calc
        generated.any (fun binding =>
            graph.reverseContains binding.1 source) =
            generated.any (fun _ => false) := by
          apply List.any_congr rfl
          intro binding
          rw [coherent.reverse_eq, hvalue]
        _ = false := by simp
  | some dependencies =>
      unfold dependenciesTouched
      apply List.any_congr rfl
      intro binding
      rw [coherent.reverse_eq, hvalue]

theorem DependencyGraph.replaceSource_models (graph : DependencyGraph)
    (values : String → Option (List String)) (source : String)
    (dependencies : List String) (coherent : graph.Models values) :
    (graph.replaceSource source dependencies).Models fun query =>
      if (source == query) = true then some dependencies else values query := by
  constructor
  · intro query
    rw [DependencyGraph.forward_replaceSource]
    split
    · rfl
    · exact coherent.forward_eq query
  · intro dependency query
    rw [DependencyGraph.reverseContains_replaceSource]
    by_cases hsource : source = query
    · subst query
      have hforwardOld := coherent.forward_eq source
      have hreverseOld := coherent.reverse_eq dependency source
      cases hvalue : values source with
      | none =>
          rw [hvalue] at hforwardOld hreverseOld
          simp [hforwardOld, hreverseOld]
      | some oldDependencies =>
          rw [hvalue] at hforwardOld hreverseOld
          simp [hforwardOld, hreverseOld]
    · have hforward : (source == query) = false := by simp [hsource]
      cases hold : graph.forward[source]? <;>
        simpa [hforward, hold] using coherent.reverse_eq dependency query

theorem DependencyGraph.bindSource_models_of_none (graph : DependencyGraph)
    (values : String → Option (List String)) (source : String)
    (dependencies : List String) (coherent : graph.Models values)
    (absent : values source = none) :
    (graph.bindSource source dependencies).Models fun query =>
      if (source == query) = true then some dependencies else values query := by
  constructor
  · intro query
    rw [DependencyGraph.forward_bindSource]
    split
    · rfl
    · exact coherent.forward_eq query
  · intro dependency query
    rw [DependencyGraph.reverseContains_bindSource]
    by_cases hsource : source = query
    · subst query
      have old := coherent.reverse_eq dependency source
      rw [absent] at old
      simp [old]
    · have hbeq : (source == query) = false :=
        beq_eq_false_iff_ne.mpr hsource
      simpa [hbeq] using coherent.reverse_eq dependency query

theorem DependencyGraph.unbindSource_models (graph : DependencyGraph)
    (values : String → Option (List String)) (source : String)
    (coherent : graph.Models values) :
    (graph.unbindSource source).Models fun query =>
      if (source == query) = true then none else values query := by
  constructor
  · intro query
    rw [DependencyGraph.forward_unbindSource]
    have hforward := coherent.forward_eq source
    cases hvalue : values source with
    | none =>
        rw [hvalue] at hforward
        by_cases hsource : source = query
        · subst query
          simp [hforward]
        · simp [hforward, hsource, coherent.forward_eq]
    | some dependencies =>
        rw [hvalue] at hforward
        simp [hforward, coherent.forward_eq]
  · intro dependency query
    rw [DependencyGraph.reverseContains_unbindSource]
    have hforward := coherent.forward_eq source
    cases hvalue : values source with
    | none =>
        rw [hvalue] at hforward
        by_cases hsource : source = query
        · subst query
          have old := coherent.reverse_eq dependency source
          rw [hvalue] at old
          simp [hforward, old]
        · have hbeq : (source == query) = false :=
            beq_eq_false_iff_ne.mpr hsource
          simpa [hforward, hbeq] using coherent.reverse_eq dependency query
    | some dependencies =>
        rw [hvalue] at hforward
        by_cases hsource : source = query
        · subst query
          have old := coherent.reverse_eq dependency source
          rw [hvalue] at old
          simp [hforward, old]
        · have hbeq : (source == query) = false :=
            beq_eq_false_iff_ne.mpr hsource
          simpa [hforward, hbeq] using coherent.reverse_eq dependency query

theorem DependencyGraph.Models.congr {graph : DependencyGraph}
    {left right : String → Option (List String)} (coherent : graph.Models left)
    (equality : ∀ source, left source = right source) : graph.Models right := by
  constructor
  · intro source
    rw [← equality source]
    exact coherent.forward_eq source
  · intro dependency source
    rw [← equality source]
    exact coherent.reverse_eq dependency source

theorem DependencyGraph.retainList_models (graph : DependencyGraph)
    (retained : VarSet) (sources : List String)
    (values : String → Option (List String)) (coherent : graph.Models values) :
    (graph.retainList retained sources).Models fun query =>
      if sources.contains query && !(retained.contains query) then none
      else values query := by
  induction sources generalizing graph values with
  | nil => simpa [DependencyGraph.retainList] using coherent
  | cons source rest ih =>
      cases hretained : retained.contains source with
      | true =>
          simp only [DependencyGraph.retainList, hretained, if_true]
          have tail := ih graph values coherent
          apply tail.congr
          intro query
          by_cases hsource : source = query
          · subst query
            simp [hretained]
          · simp [Ne.symm hsource]
      | false =>
          simp only [DependencyGraph.retainList, hretained,
            Bool.false_eq_true, if_false]
          let nextValues := fun query =>
            if (source == query) = true then none else values query
          have nextCoherent : (graph.unbindSource source).Models nextValues :=
            graph.unbindSource_models values source coherent
          have tail := ih (graph.unbindSource source) nextValues nextCoherent
          apply tail.congr
          intro query
          by_cases hsource : source = query
          · subst query
            simp [nextValues, hretained]
          · simp [nextValues, hsource, Ne.symm hsource]

theorem DependencyGraph.retainSources_models (graph : DependencyGraph)
    (active retained : VarSet) (values : String → Option (List String))
    (coherent : graph.Models values) :
    (graph.retainSources active retained).Models fun query =>
      if active.contains query && !(retained.contains query) then none
      else values query := by
  unfold DependencyGraph.retainSources
  have result := graph.retainList_models retained active.toList values coherent
  apply result.congr
  intro query
  rw [Std.HashSet.contains_toList]

theorem DependencyGraph.transformSources_models (graph : DependencyGraph)
    (generated : Subst) (sources : List String)
    (values : String → Option (List String)) (coherent : graph.Models values)
    (nodup : sources.Nodup) :
    (graph.transformSources generated sources).Models fun query =>
      if sources.contains query then
        (values query).map (transformDependencies generated)
      else values query := by
  induction sources generalizing graph values with
  | nil => simpa [DependencyGraph.transformSources] using coherent
  | cons source rest ih =>
      simp only [List.nodup_cons] at nodup
      rcases nodup with ⟨sourceNotRest, restNodup⟩
      have hforward := coherent.forward_eq source
      cases hvalue : values source with
      | none =>
          rw [hvalue] at hforward
          simp only [DependencyGraph.transformSources, hforward]
          change (graph.transformSources generated rest).Models _
          have tail := ih graph values coherent restNodup
          apply tail.congr
          intro query
          by_cases hsource : source = query
          · subst query
            simp [hvalue, sourceNotRest]
          · simp [Ne.symm hsource]
      | some dependencies =>
          rw [hvalue] at hforward
          let nextValues := fun query =>
            if (source == query) = true then
              some (transformDependencies generated dependencies)
            else values query
          have nextCoherent :
              (graph.replaceSource source
                (transformDependencies generated dependencies)).Models
                nextValues :=
            graph.replaceSource_models values source
              (transformDependencies generated dependencies) coherent
          simp only [DependencyGraph.transformSources, hforward]
          change ((graph.replaceSource source
            (transformDependencies generated dependencies)).transformSources
              generated rest).Models _
          have tail := ih (graph.replaceSource source
            (transformDependencies generated dependencies)) nextValues
              nextCoherent restNodup
          apply tail.congr
          intro query
          by_cases hsource : source = query
          · subst query
            simp [nextValues, hvalue, sourceNotRest]
          · simp [nextValues, hsource, Ne.symm hsource]

theorem DependencyGraph.transformAffected_models (graph : DependencyGraph)
    (generated : Subst) (values : String → Option (List String))
    (coherent : graph.Models values) :
    (graph.transformSources generated
      (graph.affectedSources generated).toList).Models fun source =>
        (values source).map (transformDependencies generated) := by
  let affected := graph.affectedSources generated
  have affectedNodup : affected.toList.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    simpa [beq_eq_false_iff_ne] using
      (Std.HashSet.distinct_toList (m := affected))
  have transformed := graph.transformSources_models generated affected.toList
    values coherent affectedNodup
  apply transformed.congr
  intro source
  rw [Std.HashSet.contains_toList]
  rw [graph.affectedSources_contains_of_models generated values coherent]
  cases hvalue : values source with
  | none => simp
  | some dependencies =>
      cases htouched : dependenciesTouched generated dependencies with
      | true => simp [htouched]
      | false =>
          have unchanged := transformDependencies_eq_self_of_untouched
            generated dependencies htouched
          simp [htouched, unchanged]

theorem DependencyGraph.addGenerated_models (graph : DependencyGraph)
    (generated : Subst) (values : String → Option (List String))
    (coherent : graph.Models values) :
    (graph.addGenerated generated).Models fun source =>
      (values source).orElse fun _ =>
        (Metta.Subst.lookup generated source).map Atom.vars := by
  induction generated generalizing graph values with
  | nil => simpa [DependencyGraph.addGenerated, Metta.Subst.lookup] using
      coherent
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      have hforward := coherent.forward_eq key
      cases hvalue : values key with
      | some oldDependencies =>
          rw [hvalue] at hforward
          have hcontains : graph.forward.contains key = true := by
            rw [Std.HashMap.contains_eq_isSome_getElem?, hforward]
            rfl
          simp only [DependencyGraph.addGenerated, hcontains, if_true]
          have tail := ih graph values coherent
          apply tail.congr
          intro query
          by_cases hkey : query = key
          · subst query
            simp [Metta.Subst.lookup, hvalue]
          · have hbeq : (query == key) = false :=
              beq_eq_false_iff_ne.mpr hkey
            simp [Metta.Subst.lookup, hbeq]
      | none =>
          rw [hvalue] at hforward
          have hcontains : graph.forward.contains key = false := by
            rw [Std.HashMap.contains_eq_isSome_getElem?, hforward]
            rfl
          let nextValues := fun query =>
            if (key == query) = true then some value.vars else values query
          have nextCoherent :
              (graph.bindSource key value.vars).Models nextValues :=
            graph.bindSource_models_of_none values key value.vars coherent
              hvalue
          simp only [DependencyGraph.addGenerated, hcontains,
            Bool.false_eq_true, if_false]
          rw [atomDependencies_eq_vars]
          have tail := ih (graph.bindSource key value.vars) nextValues
            nextCoherent
          apply tail.congr
          intro query
          by_cases hkey : query = key
          · subst query
            simp [nextValues, Metta.Subst.lookup, hvalue]
          · have hreverseBeq : (query == key) = false :=
              beq_eq_false_iff_ne.mpr hkey
            simp [nextValues, Metta.Subst.lookup, Ne.symm hkey,
              hreverseBeq]

theorem DependencyGraph.compose_coherent (graph : DependencyGraph)
    (base generated : Subst) (coherent : graph.Coherent base) :
    (graph.compose generated).Coherent
      (Metta.Subst.compose generated base) := by
  let values := fun source =>
    (Metta.Subst.lookup base source).map Atom.vars
  let transformedValues := fun source =>
    (values source).map (transformDependencies generated)
  let affected := graph.affectedSources generated
  let transformed := graph.transformSources generated affected.toList
  have transformedCoherent : transformed.Models transformedValues := by
    exact graph.transformAffected_models generated values coherent
  have addedCoherent := transformed.addGenerated_models generated
    transformedValues transformedCoherent
  unfold DependencyGraph.compose
  change (transformed.addGenerated generated).Coherent
    (Metta.Subst.compose generated base)
  apply addedCoherent.congr
  intro source
  unfold transformedValues values
  rw [PLeaTTa.lookup_compose]
  cases hbase : Metta.Subst.lookup base source with
  | none => simp
  | some value =>
      simp only [Option.map_some, Option.orElse_some]
      rw [transformDependencies_eq_apply_vars]

theorem DependencyGraph.empty_coherent :
    DependencyGraph.empty.Coherent [] := by
  constructor
  · intro source
    simp [DependencyGraph.empty, Metta.Subst.lookup]
  · intro dependency source
    simp [DependencyGraph.empty, DependencyGraph.reverseContains,
      Metta.Subst.lookup]

theorem DependencyGraph.ofList_coherent (entries : Subst) :
    (DependencyGraph.ofList entries).Coherent entries := by
  induction entries with
  | nil => exact DependencyGraph.empty_coherent
  | cons binding rest ih =>
      rcases binding with ⟨source, value⟩
      simp only [DependencyGraph.ofList, atomDependencies_eq_vars]
      constructor
      · intro query
        rw [DependencyGraph.forward_replaceSource]
        by_cases hsource : source = query
        · subst query
          simp [Metta.Subst.lookup]
        · have hforward : (source == query) = false := by simp [hsource]
          have hreverse : (query == source) = false := by
            exact beq_eq_false_iff_ne.mpr (Ne.symm hsource)
          simp only [hforward, Bool.false_eq_true, if_false,
            Metta.Subst.lookup, hreverse]
          exact ih.forward_eq query
      · intro dependency query
        rw [DependencyGraph.reverseContains_replaceSource]
        by_cases hsource : source = query
        · subst query
          have hforwardOld := ih.forward_eq source
          have hreverseOld := ih.reverse_eq dependency source
          cases hlookup : Metta.Subst.lookup rest source with
          | none =>
              rw [hlookup] at hforwardOld hreverseOld
              simp only [Option.map_none] at hforwardOld
              simp [Metta.Subst.lookup, hforwardOld, hreverseOld]
          | some oldValue =>
              rw [hlookup] at hforwardOld hreverseOld
              simp only [Option.map_some] at hforwardOld
              simp [Metta.Subst.lookup, hforwardOld, hreverseOld]
        · have hforward : (source == query) = false := by simp [hsource]
          have hreverse : (query == source) = false := by
            exact beq_eq_false_iff_ne.mpr (Ne.symm hsource)
          cases hold : (DependencyGraph.ofList rest).forward[source]? <;>
            simpa [hforward, hreverse, Metta.Subst.lookup, hold] using
              ih.reverse_eq dependency query

theorem resolutionSuffixFresh_eq_not_ofNames_contains
    (occupied : List String) (suffix : String) :
    resolutionSuffixFresh occupied suffix =
      !(FreshSummary.ofNames occupied).containsSuffix suffix := by
  rw [FreshSummary.ofNames_containsSuffix]
  unfold resolutionSuffixFresh
  induction occupied with
  | nil => rfl
  | cons caller rest ih =>
      simp only [List.all_cons, List.any_cons]
      rw [ih]
      cases suffix.toList.isSuffixOf caller.toList <;>
        cases rest.any (fun name => suffix.toList.isSuffixOf name.toList) <;>
        rfl

theorem resolutionFreshSuffixSummary_equivalent
    {left right : FreshSummary} (_equivalent : left.Equivalent right)
    (seed : Nat) :
    resolutionFreshSuffixSummary left seed =
      resolutionFreshSuffixSummary right seed := by
  rfl

theorem resolutionFreshSuffixCached_eq_merge_ofNames
    (summary : FreshSummary) (dynamic : List String) (seed : Nat) :
    resolutionFreshSuffixCached summary dynamic seed =
      resolutionFreshSuffixSummary
        (summary.merge (FreshSummary.ofNames dynamic)) seed := by
  rfl

theorem resolutionFreshSuffixSummary_ofOccupied
    (argsv : List Atom) (res : Atom) (rest : List Goal)
    (entries : Subst) (qterm : Atom) (seed : Nat) :
    resolutionFreshSuffixSummary
        (FreshSummary.ofNames
          (resolutionOccupiedVars argsv res rest entries qterm)) seed =
      resolutionFreshSuffix argsv res rest entries qterm seed := by
  rfl

theorem resolutionOccupiedSummary_equivalent
    (summary : FreshSummary) (argsv : List Atom) (res : Atom)
    (rest : List Goal) (entries : Subst) (qterm : Atom)
    (equivalent : summary.Equivalent (FreshSummary.ofSubst entries)) :
    (resolutionOccupiedSummary summary argsv res rest qterm).Equivalent
      (FreshSummary.ofNames
        (resolutionOccupiedVars argsv res rest entries qterm)) := by
  apply (FreshSummary.merge_equivalent equivalent
    (FreshSummary.Equivalent.refl _)).trans
  apply (FreshSummary.merge_ofNames_equivalent_append
    (bindingNames entries)
    (resolutionDynamicVars argsv res rest qterm)).trans
  apply FreshSummary.ofNames_equivalent_of_mem_iff
  intro name
  simp [resolutionDynamicVars, resolutionOccupiedVars, bindingNames,
    List.mem_append, or_assoc, or_left_comm, or_comm]

theorem resolutionFreshSuffixCached_ofOccupied
    (summary : FreshSummary) (argsv : List Atom) (res : Atom)
    (rest : List Goal) (entries : Subst) (qterm : Atom) (seed : Nat)
    (equivalent : summary.Equivalent (FreshSummary.ofSubst entries)) :
    resolutionFreshSuffixCached summary
        (resolutionDynamicVars argsv res rest qterm) seed =
      resolutionFreshSuffix argsv res rest entries qterm seed := by
  rw [resolutionFreshSuffixCached_eq_merge_ofNames]
  change resolutionFreshSuffixSummary
      (resolutionOccupiedSummary summary argsv res rest qterm) seed = _
  rw [resolutionFreshSuffixSummary_equivalent
    (resolutionOccupiedSummary_equivalent summary argsv res rest entries
      qterm equivalent)]
  exact resolutionFreshSuffixSummary_ofOccupied argsv res rest entries qterm
    seed

abbrev Index := Std.HashMap String Atom

def buildIndex (entries : Subst) : Index :=
  entries.foldl
    (fun index entry => index.insertIfNew entry.1 entry.2)
    (Std.HashMap.emptyWithCapacity entries.length)

theorem foldl_buildIndex_getElem? (entries : Subst) (index : Index)
    (name : String) :
    (entries.foldl
      (fun current entry => current.insertIfNew entry.1 entry.2)
      index)[name]? =
      match index[name]? with
      | some value => some value
      | none => Metta.Subst.lookup entries name := by
  induction entries generalizing index with
  | nil =>
      cases hget : index[name]? <;> simp [hget, Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hkey : key = name
      · subst key
        cases hget : index[name]? with
        | none =>
            have hnotmem : name ∉ index := by
              intro hmem
              have hisSome :=
                (Std.HashMap.mem_iff_isSome_getElem?).mp hmem
              simp [hget] at hisSome
            rw [Std.HashMap.getElem?_insertIfNew]
            simp [hnotmem, Metta.Subst.lookup]
        | some existing =>
            rcases (Std.HashMap.getElem?_eq_some_iff.mp hget) with
              ⟨hmem, hvalue⟩
            rw [Std.HashMap.getElem?_insertIfNew]
            simp only [beq_self_eq_true, true_and, hmem, not_true_eq_false,
              if_false, hget]
      · have hbeq : (key == name) = false := by simp [hkey]
        have hbeqReverse : (name == key) = false := by simp [Ne.symm hkey]
        rw [Std.HashMap.getElem?_insertIfNew]
        simp only [hbeq, Bool.false_eq_true, false_and, if_false,
          Metta.Subst.lookup, hbeqReverse]

theorem buildIndex_getElem? (entries : Subst) (name : String) :
    (buildIndex entries)[name]? = Metta.Subst.lookup entries name := by
  unfold buildIndex
  rw [foldl_buildIndex_getElem?]
  simp

/-- A proof-carrying, persistent lookup cache for the existing list
substitution. The list remains the semantic denotation; the proof field is
erased from executable code. -/
structure State where
  denotation : Subst
  index : Index
  coherent : ∀ name, index[name]? = Metta.Subst.lookup denotation name

def ofList (entries : Subst) : State :=
  { denotation := entries
    index := buildIndex entries
    coherent := buildIndex_getElem? entries }

def empty : State := ofList []

instance : Inhabited State := ⟨empty⟩

def State.lookup (state : State) (name : String) : Option Atom :=
  state.index[name]?

@[simp] theorem State.lookup_eq_reference (state : State) (name : String) :
    state.lookup name = Metta.Subst.lookup state.denotation name :=
  state.coherent name

private def substNWithLookup (lookup : String → Option Atom) : Nat → Atom → Atom
  | 0, atom => atom
  | fuel + 1, Atom.var name =>
      match lookup name with
      | some value => substNWithLookup lookup fuel value
      | none => Atom.var name
  | fuel + 1, Atom.expr atoms =>
      Atom.expr (atoms.map (substNWithLookup lookup (fuel + 1)))
  | _ + 1, atom => atom

private def substNWithIndex (fuel : Nat) (index : Index) (atom : Atom) : Atom :=
  substNWithLookup (fun name => index[name]?) fuel atom

def State.subst (state : State) (atom : Atom) : Atom :=
  substNWithIndex (state.denotation.length + 1) state.index atom

private theorem substNWithLookup_eq_reference
    (fuel : Nat) (entries : Subst) (atom : Atom) :
    ∀ (lookup : String → Option Atom),
      (∀ name, lookup name = Metta.Subst.lookup entries name) →
      substNWithLookup lookup fuel atom = PLeaTTa.substN fuel entries atom := by
  induction fuel, entries, atom using PLeaTTa.substN.induct with
  | case1 entries atom =>
      intro lookup hlookup
      simp [substNWithLookup, PLeaTTa.substN]
  | case2 fuel entries name value hlookup ih =>
      intro lookup hcoherent
      simp only [substNWithLookup, PLeaTTa.substN, hcoherent, hlookup]
      exact ih lookup hcoherent
  | case3 fuel entries name hlookup =>
      intro lookup hcoherent
      simp [substNWithLookup, hcoherent, hlookup, PLeaTTa.substN]
  | case4 fuel entries atoms ih =>
      intro lookup hcoherent
      simp only [substNWithLookup, PLeaTTa.substN, Atom.expr.injEq]
      apply List.map_congr_left
      intro child hchild
      exact ih child hchild lookup hcoherent
  | case5 fuel entries atom hvar hexpr =>
      intro lookup hcoherent
      cases atom with
      | sym name => simp [substNWithLookup, PLeaTTa.substN]
      | var name => exact False.elim (hvar name rfl)
      | gnd ground => simp [substNWithLookup, PLeaTTa.substN]
      | expr atoms => exact False.elim (hexpr atoms rfl)

private theorem substNWithIndex_eq_reference
    (fuel : Nat) (entries : Subst) (atom : Atom) (index : Index)
    (coherent : ∀ name, index[name]? = Metta.Subst.lookup entries name) :
    substNWithIndex fuel index atom = PLeaTTa.substN fuel entries atom := by
  unfold substNWithIndex
  exact substNWithLookup_eq_reference fuel entries atom
    (fun name => index[name]?) coherent

/-- Base representation theorem: cached lookup and deep substitution are
extensionally identical to the current list implementation. This theorem is
independent of the executable machine/spec correspondence proof. -/
theorem State.subst_eq_reference (state : State) (atom : Atom) :
    state.subst atom = PLeaTTa.subst state.denotation atom := by
  unfold State.subst PLeaTTa.subst
  exact substNWithIndex_eq_reference
    (state.denotation.length + 1) state.denotation atom state.index
      state.coherent

/-- Executable representation without a retained denotation list. `depth`
is the deep-substitution fuel bound; `index` is persistent across branches. -/
structure Graph where
  index : Index
  depth : Nat

def Graph.ofList (entries : Subst) : Graph :=
  { index := buildIndex entries, depth := entries.length }

def Graph.empty : Graph := Graph.ofList []

instance : Inhabited Graph := ⟨Graph.empty⟩

def Graph.lookup (graph : Graph) (name : String) : Option Atom :=
  graph.index[name]?

def Graph.subst (graph : Graph) (atom : Atom) : Atom :=
  substNWithIndex (graph.depth + 1) graph.index atom

/-- The proof-facing relation between the persistent graph and the original
association-list substitution. -/
def Graph.Coherent (graph : Graph) (entries : Subst) : Prop :=
  graph.depth = entries.length ∧
    ∀ name, graph.lookup name = Metta.Subst.lookup entries name

theorem Graph.ofList_coherent (entries : Subst) :
    (Graph.ofList entries).Coherent entries := by
  constructor
  · rfl
  · exact buildIndex_getElem? entries

theorem Graph.subst_eq_reference (graph : Graph) (entries : Subst)
    (coherent : graph.Coherent entries) (atom : Atom) :
    graph.subst atom = PLeaTTa.subst entries atom := by
  rcases coherent with ⟨hdepth, hlookup⟩
  unfold Graph.subst PLeaTTa.subst
  unfold Graph.lookup at hlookup
  rw [hdepth]
  exact substNWithIndex_eq_reference (entries.length + 1) entries atom
    graph.index hlookup

/-- Constant-update persistent extension. This is the base mutation used by
the later composition/dependency engine; unlike rebuilding an index, it
shares the previous graph. -/
def Graph.cons (graph : Graph) (name : String) (value : Atom) : Graph :=
  { index := graph.index.insert name value
    depth := graph.depth + 1 }

theorem Graph.cons_coherent (graph : Graph) (entries : Subst)
    (coherent : graph.Coherent entries) (name : String) (value : Atom) :
    (graph.cons name value).Coherent ((name, value) :: entries) := by
  rcases coherent with ⟨hdepth, hlookup⟩
  constructor
  · simp [Graph.cons, hdepth]
  · intro query
    unfold Graph.cons Graph.lookup
    rw [Std.HashMap.getElem?_insert]
    by_cases hname : name = query
    · subst query
      simp [Metta.Subst.lookup]
    · have hforward : (name == query) = false := by simp [hname]
      have hreverse : (query == name) = false := by simp [Ne.symm hname]
      simp only [hforward, Bool.false_eq_true, if_false,
        Metta.Subst.lookup, hreverse]
      simpa [Graph.lookup] using hlookup query

theorem Graph.cons_subst_eq_reference (graph : Graph) (entries : Subst)
    (coherent : graph.Coherent entries) (name : String) (value atom : Atom) :
    (graph.cons name value).subst atom =
      PLeaTTa.subst ((name, value) :: entries) atom :=
  Graph.subst_eq_reference _ _
    (Graph.cons_coherent graph entries coherent name value) atom

theorem lookup_append (left right : Subst) (name : String) :
    Metta.Subst.lookup (left ++ right) name =
      (Metta.Subst.lookup left name).orElse
        (fun _ => Metta.Subst.lookup right name) := by
  induction left with
  | nil => simp [Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.cons_append, Metta.Subst.lookup]
      by_cases hkey : (name == key) = true
      · rw [if_pos hkey, if_pos hkey]
        simp
      · rw [if_neg hkey, if_neg hkey]
        exact ih

/-- The non-eager composition graph (`generated ++ base`) has the same
elimination order as eager composition. Generated bindings precede the base;
base targets may point into that new prefix, which is exactly the dependency
shape that eager whole-list rebuilding used to erase. -/
def SubstTopological.append_of_avoids (base generated : Subst)
    (baseTopological : SubstTopological base)
    (generatedTopological : SubstTopological generated)
    (havoid : SubstEntriesAvoid base generated) :
    SubstTopological (generated ++ base) := by
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
      baseTopological.domain name, lookup_append]
    cases Metta.Subst.lookup generated name <;>
      cases Metta.Subst.lookup base name <;> simp
  · intro source value dependency hsource hdependency hdependencyBound
    rw [lookup_append generated base source] at hsource
    rw [lookup_append generated base dependency] at hdependencyBound
    cases hgeneratedSource : Metta.Subst.lookup generated source with
    | some generatedValue =>
        rw [hgeneratedSource] at hsource
        have hvalue : generatedValue = value := Option.some.inj hsource
        subst generatedValue
        have hsourceAvoid :=
          SubstEntriesAvoid.lookup base generated havoid source value
            hgeneratedSource
        have hdependencyBase : Metta.Subst.lookup base dependency = none :=
          hsourceAvoid.2 dependency hdependency
        rw [hdependencyBase] at hdependencyBound
        have hdependencyGenerated :
            Metta.Subst.lookup generated dependency ≠ none := by
          simpa using hdependencyBound
        have hdecreases := generatedTopological.decreases source value
          dependency hgeneratedSource hdependency hdependencyGenerated
        have hsourceMem : source ∈ generatedTopological.order :=
          (generatedTopological.domain source).2 (by simp [hgeneratedSource])
        have hdependencyMem : dependency ∈ generatedTopological.order :=
          (generatedTopological.domain dependency).2 hdependencyGenerated
        simpa [List.idxOf_append, hsourceMem, hdependencyMem] using hdecreases
    | none =>
        rw [hgeneratedSource] at hsource
        cases hbaseSource : Metta.Subst.lookup base source with
        | none => simp [hbaseSource] at hsource
        | some baseValue =>
            rw [hbaseSource] at hsource
            have hvalue : baseValue = value := Option.some.inj hsource
            subst baseValue
            have hsourceMem : source ∈ baseTopological.order :=
              (baseTopological.domain source).2 (by simp [hbaseSource])
            have hsourceNotGenerated : source ∉ generatedTopological.order :=
              generatedNotMemOfBaseLookup source value hbaseSource
            cases hbaseDependency : Metta.Subst.lookup base dependency with
            | some dependencyValue =>
                have hdependencyNotGenerated :
                    dependency ∉ generatedTopological.order :=
                  generatedNotMemOfBaseLookup dependency dependencyValue
                    hbaseDependency
                have hdecreases := baseTopological.decreases source value
                  dependency hbaseSource hdependency (by simp [hbaseDependency])
                simpa [List.idxOf_append, hsourceNotGenerated,
                  hdependencyNotGenerated] using
                    Nat.add_lt_add_right hdecreases
                      generatedTopological.order.length
            | none =>
                rw [hbaseDependency] at hdependencyBound
                have hdependencyGenerated :
                    Metta.Subst.lookup generated dependency ≠ none := by
                  simpa using hdependencyBound
                have hdependencyMem : dependency ∈ generatedTopological.order :=
                  (generatedTopological.domain dependency).2
                    hdependencyGenerated
                have hdependencyRank :
                    generatedTopological.order.idxOf dependency <
                      generatedTopological.order.length :=
                  List.idxOf_lt_length_of_mem hdependencyMem
                simp only [List.idxOf_append, hdependencyMem,
                  hsourceNotGenerated, if_true, if_false]
                omega

theorem lookup_append_eq_none_iff_lookup_compose_eq_none
    (generated base : Subst) (name : String) :
    Metta.Subst.lookup (generated ++ base) name = none ↔
      Metta.Subst.lookup (Metta.Subst.compose generated base) name = none := by
  rw [lookup_append, PLeaTTa.lookup_compose]
  cases Metta.Subst.lookup generated name <;>
    cases Metta.Subst.lookup base name <;> simp

theorem compose_denotes_append (base generated : Subst)
    (baseTopological : SubstTopological base)
    (generatedTopological : SubstTopological generated)
    (havoid : SubstEntriesAvoid base generated) :
    SubstLookupDenotes (Metta.Subst.compose generated base)
      (generated ++ base) := by
  let eager := Metta.Subst.compose generated base
  have eagerTopological : SubstTopological eager :=
    SubstTopological.compose_of_avoids base generated baseTopological
      generatedTopological havoid
  have eagerDenotesGenerated : SubstLookupDenotes eager generated := by
    intro name value hlookup
    have hbaseNone :=
      (SubstEntriesAvoid.lookup base generated havoid name value hlookup).1
    have heagerLookup : Metta.Subst.lookup eager name = some value := by
      simp [eager, PLeaTTa.lookup_compose, hbaseNone, hlookup]
    exact eagerTopological.subst_var_of_lookup eager name value heagerLookup
  intro name value hlookup
  rw [lookup_append] at hlookup
  cases hgenerated : Metta.Subst.lookup generated name with
  | some generatedValue =>
      rw [hgenerated] at hlookup
      have hvalue : generatedValue = value := Option.some.inj hlookup
      subst generatedValue
      have hbaseNone :=
        (SubstEntriesAvoid.lookup base generated havoid name value
          hgenerated).1
      have heagerLookup : Metta.Subst.lookup eager name = some value := by
        simp [eager, PLeaTTa.lookup_compose, hbaseNone, hgenerated]
      exact eagerTopological.subst_var_of_lookup eager name value heagerLookup
  | none =>
      rw [hgenerated] at hlookup
      cases hbase : Metta.Subst.lookup base name with
      | none => simp [hbase] at hlookup
      | some baseValue =>
          rw [hbase] at hlookup
          have hvalue : baseValue = value := Option.some.inj hlookup
          subst baseValue
          have heagerLookup : Metta.Subst.lookup eager name =
              some (Metta.Subst.apply generated value) := by
            simp [eager, PLeaTTa.lookup_compose, hbase]
          exact (eagerTopological.subst_var_of_lookup eager name
            (Metta.Subst.apply generated value) heagerLookup).trans
              (subst_apply_of_lookupDenotes eager generated
                eagerDenotesGenerated value)

/-- The central lazy-composition equivalence. Keeping old targets as graph
edges and prepending the generated unifier produces the same normal form as
eagerly rebuilding every old target with `Subst.compose`. -/
theorem subst_append_eq_compose (base generated : Subst)
    (baseTopological : SubstTopological base)
    (generatedTopological : SubstTopological generated)
    (havoid : SubstEntriesAvoid base generated) (atom : Atom) :
    subst (generated ++ base) atom =
      subst (Metta.Subst.compose generated base) atom := by
  let raw := generated ++ base
  let eager := Metta.Subst.compose generated base
  have rawTopological : SubstTopological raw :=
    SubstTopological.append_of_avoids base generated baseTopological
      generatedTopological havoid
  have eagerDenotesRaw : SubstLookupDenotes eager raw := by
    exact compose_denotes_append base generated baseTopological
      generatedTopological havoid
  have habsorb : subst eager (subst raw atom) = subst eager atom :=
    subst_subst_of_lookupDenotes eager raw eagerDenotesRaw atom
  have hfixed : subst eager (subst raw atom) = subst raw atom := by
    apply subst_eq_self_of_domain_free eager (subst raw atom)
    intro name hname
    have hrawNone : Metta.Subst.lookup raw name = none :=
      rawTopological.subst_resolvesDomain raw atom name hname
    exact (lookup_append_eq_none_iff_lookup_compose_eq_none
      generated base name).mp hrawNone
  exact hfixed.symm.trans habsorb

/-- Eager composition is observationally just the generated layer on an
atom outside the carried base domain.

The `SubstEntriesAvoid` premise is load-bearing: it says every generated
target is outside the base domain as well, so following a generated lookup
cannot re-enter the carried state.  This is the reusable carried-binding
lemma needed by local Prolog activation, where a standardized-apart clause
body is fixed by the incoming substitution. -/
theorem subst_compose_eq_generated_of_avoids
    (base generated : Subst)
    (baseTopological : SubstTopological base)
    (generatedTopological : SubstTopological generated)
    (havoid : SubstEntriesAvoid base generated)
    {atom : Atom} (atomAvoids : AtomAvoids base atom) :
    subst (Metta.Subst.compose generated base) atom =
      subst generated atom := by
  let composed := Metta.Subst.compose generated base
  have composedTopological : SubstTopological composed :=
    SubstTopological.compose_of_avoids base generated
      baseTopological generatedTopological havoid
  have composedDenotesGenerated :
      SubstLookupDenotes composed generated := by
    intro name value lookup
    have avoided :=
      SubstEntriesAvoid.lookup base generated havoid name value lookup
    have composedLookup :
        Metta.Subst.lookup composed name = some value := by
      simp [composed, PLeaTTa.lookup_compose, avoided.1, lookup]
    exact composedTopological.subst_var_of_lookup
      composed name value composedLookup
  have generatedResultAvoidsBase :
      AtomAvoids base (subst generated atom) := by
    intro name member
    rcases subst_vars_origin generated atom name member with
      original | generatedRange
    · exact atomAvoids name original
    · simp only [List.mem_flatMap] at generatedRange
      obtain ⟨entry, entryMember, nameMember⟩ := generatedRange
      exact (havoid entry entryMember).2 name nameMember
  have generatedResultOutsideComposed :
      ∀ name, name ∈ (subst generated atom).vars →
        Metta.Subst.lookup composed name = none := by
    intro name member
    have baseNone := generatedResultAvoidsBase name member
    have generatedNone :=
      generatedTopological.subst_resolvesDomain generated atom name member
    simp [composed, PLeaTTa.lookup_compose, baseNone, generatedNone]
  have fixed :
      subst composed (subst generated atom) = subst generated atom :=
    subst_eq_self_of_domain_free composed (subst generated atom)
      generatedResultOutsideComposed
  have absorbed :
      subst composed (subst generated atom) = subst composed atom :=
    subst_subst_of_lookupDenotes composed generated
      composedDenotesGenerated atom
  exact absorbed.symm.trans fixed

/-- A persistent composition spine. Adding a generated unifier is O(1): the
old state is shared, while `denote` remains exactly the existing eager list
composition used by the semantic reference. -/
inductive History where
  | base (entries : Subst)
  | compose (generated : Subst) (prior : History)

def History.denote : History → Subst
  | .base entries => entries
  | .compose generated prior =>
      Metta.Subst.compose generated prior.denote

def History.lookup : History → String → Option Atom
  | .base entries, name => Metta.Subst.lookup entries name
  | .compose generated prior, name =>
      match prior.lookup name with
      | some value => some (Metta.Subst.apply generated value)
      | none => Metta.Subst.lookup generated name

theorem History.lookup_eq_denote (history : History) (name : String) :
    history.lookup name = Metta.Subst.lookup history.denote name := by
  induction history with
  | base entries => rfl
  | compose generated prior ih =>
      rw [History.lookup, History.denote, PLeaTTa.lookup_compose, ih]
      rfl

structure Layered where
  history : History
  depth : Nat

def Layered.ofList (entries : Subst) : Layered :=
  { history := .base entries, depth := entries.length }

def Layered.empty : Layered := Layered.ofList []

instance : Inhabited Layered := ⟨Layered.empty⟩

def Layered.compose (state : Layered) (generated : Subst) : Layered :=
  { history := .compose generated state.history
    depth := state.depth + generated.length }

def Layered.Coherent (state : Layered) : Prop :=
  state.depth = state.history.denote.length

theorem Layered.ofList_coherent (entries : Subst) :
    (Layered.ofList entries).Coherent := rfl

theorem Layered.compose_coherent (state : Layered) (generated : Subst)
    (coherent : state.Coherent) :
    (state.compose generated).Coherent := by
  unfold Layered.Coherent at coherent ⊢
  simp [Layered.compose, History.denote, Metta.Subst.compose, coherent,
    Nat.add_comm]

def Layered.subst (state : Layered) (atom : Atom) : Atom :=
  substNWithLookup state.history.lookup (state.depth + 1) atom

/-- Load-bearing lazy-composition theorem: the O(1) persistent spine has the
same deep-substitution denotation as materializing every eager list compose. -/
theorem Layered.subst_eq_reference (state : Layered)
    (coherent : state.Coherent) (atom : Atom) :
    state.subst atom = PLeaTTa.subst state.history.denote atom := by
  unfold Layered.subst PLeaTTa.subst
  unfold Layered.Coherent at coherent
  rw [coherent]
  exact substNWithLookup_eq_reference
    (state.history.denote.length + 1) state.history.denote atom
      state.history.lookup state.history.lookup_eq_denote

theorem Layered.compose_subst_eq_reference (state : Layered)
    (generated : Subst) (coherent : state.Coherent) (atom : Atom) :
    (state.compose generated).subst atom =
      PLeaTTa.subst
        (Metta.Subst.compose generated state.history.denote) atom := by
  exact Layered.subst_eq_reference (state.compose generated)
    (state.compose_coherent generated coherent) atom

theorem foldl_buildMemoIndex_getElem? (entries : Subst)
    (index : MemoIndex) (version : Nat) (name : String) :
    (entries.foldl
      (fun current entry => current.insertIfNew entry.1
        { value := entry.2, version })
      index)[name]? =
      match index[name]? with
      | some entry => some entry
      | none => (Metta.Subst.lookup entries name).map
          (fun value => { value, version }) := by
  induction entries generalizing index with
  | nil =>
      cases hget : index[name]? <;> simp [hget, Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hkey : key = name
      · subst key
        cases hget : index[name]? with
        | none =>
            have hnotmem : name ∉ index := by
              intro hmem
              have hisSome :=
                (Std.TreeMap.mem_iff_isSome_getElem?).mp hmem
              simp [hget] at hisSome
            rw [Std.TreeMap.getElem?_insertIfNew]
            simp [hnotmem, Metta.Subst.lookup]
        | some existing =>
            rcases (Std.TreeMap.getElem?_eq_some_iff.mp hget) with
              ⟨hmem, hvalue⟩
            rw [Std.TreeMap.getElem?_insertIfNew]
            simpa [hmem] using hvalue
      · have hbeq : (key == name) = false := by simp [hkey]
        have hbeqReverse : (name == key) = false := by simp [Ne.symm hkey]
        rw [Std.TreeMap.getElem?_insertIfNew]
        simp [hkey, Metta.Subst.lookup, Ne.symm hkey]

theorem buildMemoIndex_getElem? (entries : Subst) (version : Nat)
    (name : String) :
    (buildMemoIndex entries version)[name]? =
      (Metta.Subst.lookup entries name).map
        (fun value => { value, version }) := by
  unfold buildMemoIndex
  rw [foldl_buildMemoIndex_getElem?]
  simp

theorem eraseInactiveEntries_getElem?_of_retained
    (entries : MemoIndex) (retained : VarSet) (names : List String)
    (query : String) (hretained : retained.contains query = true) :
    (eraseInactiveEntries entries retained names)[query]? = entries[query]? := by
  induction names generalizing entries with
  | nil => rfl
  | cons name rest ih =>
      by_cases hname : retained.contains name = true
      · simp [eraseInactiveEntries, hname, ih]
      · have hne : name ≠ query := by
          intro equality
          subst name
          exact hname hretained
        have hnameFalse : retained.contains name = false := by
          cases hvalue : retained.contains name
          · rfl
          · exact False.elim (hname hvalue)
        simp only [eraseInactiveEntries, hnameFalse, Bool.false_eq_true,
          if_false]
        rw [ih, Std.TreeMap.getElem?_erase]
        simp [hne]

theorem eraseInactiveEntries_getElem?_some
    (entries : MemoIndex) (retained : VarSet) (names : List String)
    (query : String) (entry : MemoEntry)
    (hentry :
      (eraseInactiveEntries entries retained names)[query]? = some entry) :
    entries[query]? = some entry := by
  induction names generalizing entries with
  | nil => simpa [eraseInactiveEntries] using hentry
  | cons name rest ih =>
      by_cases hname : retained.contains name = true
      · exact ih entries (by
          simpa [eraseInactiveEntries, hname] using hentry)
      · have erased : (entries.erase name)[query]? = some entry :=
          ih (entries.erase name) (by
            simpa [eraseInactiveEntries, hname] using hentry)
        by_cases hne : name = query
        · subst name
          simp at erased
        · rw [Std.TreeMap.getElem?_erase] at erased
          simpa [hne] using erased

theorem retainMemoEntries_getElem?_of_retained
    (entries : MemoIndex) (active retained : VarSet) (query : String)
    (hretained : retained.contains query = true) :
    (retainMemoEntries entries active retained)[query]? = entries[query]? := by
  exact eraseInactiveEntries_getElem?_of_retained entries retained
    active.toList query hretained

theorem retainMemoEntries_getElem?_some
    (entries : MemoIndex) (active retained : VarSet) (query : String)
    (entry : MemoEntry)
    (hentry :
      (retainMemoEntries entries active retained)[query]? = some entry) :
    entries[query]? = some entry := by
  exact eraseInactiveEntries_getElem?_some entries retained active.toList
    query entry hentry

@[simp] theorem Memo.advance_zero (layers : List Subst) (value : Atom) :
    Memo.advance layers 0 value = value := rfl

@[simp] theorem Memo.advance_cons_succ (generated : Subst)
    (layers : List Subst) (count : Nat) (value : Atom) :
    Memo.advance (generated :: layers) (count + 1) value =
      Metta.Subst.apply generated (Memo.advance layers count value) := by
  simp [Memo.advance]

theorem Memo.currentPrepared_some (state : Memo) (name : String)
    (prepared : PreparedAtom)
    (found : state.currentPrepared name = some prepared) :
    prepared.Valid ∧ state.peek name = some prepared.atom := by
  unfold Memo.currentPrepared at found
  cases hentry : state.entries[name]? with
  | none => simp [hentry] at found
  | some entry =>
      simp only [hentry] at found
      by_cases hversion : entry.version = state.version
      · have hversionBool : (entry.version == state.version) = true := by
          simp [hversion]
        rw [hversionBool] at found
        cases hprepared : entry.prepared with
        | none => simp [hprepared] at found
        | some certified =>
            simp only [hprepared, Option.map_some] at found
            have heq : certified.val = prepared := by
              simpa using found
            subst prepared
            refine ⟨certified.property.1, ?_⟩
            unfold Memo.peek
            rw [hentry]
            simp [hversion, certified.property.2]
      · have hversionBool : (entry.version == state.version) = false := by
          simp [hversion]
        rw [hversionBool] at found
        contradiction

theorem Memo.cachedPrepared_some (state : Memo) (name : String)
    (prepared : PreparedAtom)
    (found : state.cachedPrepared name = some prepared) :
    prepared.Valid ∧ ∃ entry : MemoEntry,
      state.entries[name]? = some entry ∧ prepared.atom = entry.value := by
  unfold Memo.cachedPrepared at found
  cases hentry : state.entries[name]? with
  | none => simp [hentry] at found
  | some entry =>
      simp only [hentry] at found
      cases hprepared : entry.prepared with
      | none => simp [hprepared] at found
      | some certified =>
          simp only [hprepared, Option.map_some] at found
          have heq : certified.val = prepared := by
            simpa using found
          subst prepared
          exact ⟨certified.property.1, entry, rfl, certified.property.2⟩

theorem Memo.advance_of_closed (layers : List Subst) (count : Nat)
    (atom : Atom) (closed : atom.vars = []) :
    Memo.advance layers count atom = atom := by
  have applyClosed (subst : Subst) : ∀ value : Atom,
      value.vars = [] → Metta.Subst.apply subst value = value := by
    intro value
    induction value with
    | var name => intro hvars; simp [Atom.vars] at hvars
    | expr children ih =>
        intro hvars
        simp only [Atom.vars] at hvars
        rw [List.flatten_eq_nil_iff] at hvars
        simp only [Metta.Subst.apply]
        have childrenFixed : ∀ child ∈ children,
            Metta.Subst.apply subst child = child := by
          intro child member
          exact ih child member
            (hvars (Atom.vars child) (List.mem_map_of_mem member))
        rw [List.map_congr_left childrenFixed]
        simp
    | _ => intro _; simp [Metta.Subst.apply]
  unfold Memo.advance
  generalize layers.take count = selected
  induction selected with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.foldr_cons]
      rw [ih, applyClosed layer atom closed]

@[simp] theorem Memo.denote_ofList (entries : Subst) :
    (Memo.ofList entries).denote = entries := rfl

@[simp] theorem Memo.denote_compose (state : Memo) (generated : Subst) :
    (state.compose generated).denote =
      Metta.Subst.compose generated state.denote := rfl

@[simp] theorem Memo.peek_ofList (entries : Subst) (name : String) :
    (Memo.ofList entries).peek name = Metta.Subst.lookup entries name := by
  unfold Memo.ofList Memo.peek
  rw [buildMemoIndex_getElem?]
  cases Metta.Subst.lookup entries name <;> rfl

/-- First composition checkpoint for the executable memo: every old key is
advanced through exactly the new generated unifier, while every genuinely
new key starts at the new version. -/
theorem Memo.peek_compose_ofList (base generated : Subst) (name : String) :
    ((Memo.ofList base).compose generated).peek name =
      Metta.Subst.lookup (Metta.Subst.compose generated base) name := by
  unfold Memo.compose Memo.ofList Memo.peek
  rw [foldl_buildMemoIndex_getElem?, buildMemoIndex_getElem?,
    PLeaTTa.lookup_compose]
  cases hbase : Metta.Subst.lookup base name with
  | some baseValue =>
      simp [Memo.advance]
  | none =>
      cases hgenerated : Metta.Subst.lookup generated name with
      | none => simp
      | some generatedValue => simp [Memo.advance]

/-- Executable cache invariant. The semantic substitution is `denote`; the
versioned map is merely an incremental implementation of its lookup. -/
structure Memo.Coherent (state : Memo) : Prop where
  version_eq : state.version = state.layers.length
  depth_eq : state.depth = state.denote.length
  stamped : ∀ (name : String) (entry : MemoEntry),
    state.entries[name]? = some entry →
    entry.version ≤ state.version
  peek_eq : ∀ name, state.peek name = Metta.Subst.lookup state.denote name

theorem Memo.ofList_coherent (entries : Subst) :
    (Memo.ofList entries).Coherent := by
  constructor
  · rfl
  · rfl
  · intro name entry hentry
    change (buildMemoIndex entries 0)[name]? = some entry at hentry
    change entry.version ≤ 0
    rw [buildMemoIndex_getElem?] at hentry
    rcases Option.map_eq_some_iff.mp hentry with ⟨value, hvalue, rfl⟩
    exact Nat.le_refl 0
  · exact Memo.peek_ofList entries

theorem Memo.peek_compose (state : Memo) (generated : Subst)
    (stamped : ∀ (name : String) (entry : MemoEntry),
      state.entries[name]? = some entry → entry.version ≤ state.version)
    (name : String) :
    (state.compose generated).peek name =
      match state.peek name with
      | some value => some (Metta.Subst.apply generated value)
      | none => Metta.Subst.lookup generated name := by
  cases hold : state.entries[name]? with
  | some oldEntry =>
      have hstamp := stamped name oldEntry hold
      have hsubtract :
          state.version + 1 - oldEntry.version =
            (state.version - oldEntry.version) + 1 := by
        omega
      simp [Memo.compose, Memo.peek, foldl_buildMemoIndex_getElem?, hold,
        hsubtract, Memo.advance_cons_succ]
  | none =>
      cases hgenerated : Metta.Subst.lookup generated name <;>
        simp [Memo.compose, Memo.peek, foldl_buildMemoIndex_getElem?, hold,
          hgenerated, Memo.advance]

theorem Memo.compose_coherent (state : Memo) (generated : Subst)
    (coherent : state.Coherent) :
    (state.compose generated).Coherent := by
  constructor
  · simp [Memo.compose, coherent.version_eq]
  · simp [Memo.compose, Memo.denote, Thunk.get, Metta.Subst.compose,
      coherent.depth_eq, Nat.add_comm]
  · intro name entry hentry
    unfold Memo.compose at hentry ⊢
    rw [foldl_buildMemoIndex_getElem?] at hentry
    cases hold : state.entries[name]? with
    | some oldEntry =>
        rw [hold] at hentry
        have heq : oldEntry = entry := Option.some.inj hentry
        subst entry
        exact Nat.le_trans (coherent.stamped name oldEntry hold)
          (Nat.le_add_right state.version 1)
    | none =>
        rw [hold] at hentry
        cases hgenerated : Metta.Subst.lookup generated name with
        | none => simp [hgenerated] at hentry
        | some value =>
            simp only [hgenerated, Option.map_some, Option.some.injEq] at hentry
            subst entry
            exact Nat.le_refl _
  · intro name
    rw [Memo.peek_compose state generated coherent.stamped name,
      coherent.peek_eq, Memo.denote_compose, PLeaTTa.lookup_compose]
    rfl

theorem Memo.refresh_coherent (state : Memo) (name : String) (value : Atom)
    (coherent : state.Coherent) (hvalue : state.peek name = some value) :
    (state.refresh name value).Coherent := by
  constructor
  · exact coherent.version_eq
  · exact coherent.depth_eq
  · intro query entry hentry
    change (state.entries.insert name
      { value := value, version := state.version })[query]? = some entry at hentry
    rw [Std.TreeMap.getElem?_insert] at hentry
    by_cases hname : name = query
    · subst query
      simp at hentry
      subst entry
      exact Nat.le_refl _
    · simp [hname] at hentry
      exact coherent.stamped query entry hentry
  · intro query
    unfold Memo.refresh Memo.peek
    rw [Std.TreeMap.getElem?_insert]
    by_cases hname : name = query
    · subst query
      have hreference := coherent.peek_eq name
      rw [hvalue] at hreference
      simp
      change some value = Metta.Subst.lookup state.denote name
      exact hreference
    · simp [hname]
      exact coherent.peek_eq query

theorem Memo.lookup_fst_eq_reference (state : Memo) (name : String)
    (coherent : state.Coherent) :
    (state.lookup name).1 = Metta.Subst.lookup state.denote name := by
  unfold Memo.lookup
  split <;> simp_all [coherent.peek_eq name]

theorem Memo.lookup_snd_coherent (state : Memo) (name : String)
    (coherent : state.Coherent) :
    (state.lookup name).2.Coherent := by
  unfold Memo.lookup
  split
  · exact coherent
  · next value hvalue =>
      exact Memo.refresh_coherent state name value coherent hvalue

theorem Memo.lookup_snd_denote (state : Memo) (name : String) :
    (state.lookup name).2.denote = state.denote := by
  unfold Memo.lookup
  split <;> rfl

private theorem run_mapM_eq_reference {α β : Type}
    (action : α → StateM Memo β) (reference : Subst → α → β)
    (items : List α)
    (correct : ∀ item ∈ items, ∀ state : Memo, state.Coherent →
      let result := Id.run ((action item).run state)
      result.1 = reference state.denote item ∧
        result.2.Coherent ∧ result.2.denote = state.denote) :
    ∀ state : Memo, state.Coherent →
      let result := Id.run ((items.mapM action).run state)
      result.1 = items.map (reference state.denote) ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  induction items with
  | nil =>
      intro state coherent
      simp [coherent]
  | cons item rest ih =>
      intro state coherent
      have hhead := correct item (by simp) state coherent
      cases hrunHead : Id.run ((action item).run state) with
      | mk head next =>
          simp only [hrunHead] at hhead
          have htail := ih
            (fun child hchild => correct child (by simp [hchild]))
            next hhead.2.1
          cases hrunTail : Id.run ((rest.mapM action).run next) with
          | mk tail final =>
              simp only [hrunTail] at htail
              simp [List.mapM_cons, hrunHead, hrunTail, hhead.1, hhead.2.2,
                htail.1, htail.2.1, htail.2.2]

theorem Memo.substN_run_eq_reference (fuel : Nat) (atom : Atom) :
    ∀ state : Memo, state.Coherent →
      let result := Id.run ((Memo.substN fuel atom).run state)
      result.1 = PLeaTTa.substN fuel state.denote atom ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  induction fuel, atom using Memo.substN.induct
  case case1 atom =>
    intro state coherent
    simp [Memo.substN, PLeaTTa.substN, coherent]
  case case2 fuel name ih =>
    intro state coherent
    have hfst := Memo.lookup_fst_eq_reference state name coherent
    have hsnd := Memo.lookup_snd_coherent state name coherent
    have hden := Memo.lookup_snd_denote state name
    cases hlookup : state.lookup name with
    | mk value next =>
        simp only [hlookup] at hfst hsnd hden
        cases value with
        | none =>
            have href : Metta.Subst.lookup state.denote name = none := hfst.symm
            simp [Memo.substN, hlookup, PLeaTTa.substN, href, hsnd, hden]
        | some target =>
            have hih := ih target next hsnd
            have href : Metta.Subst.lookup state.denote name = some target :=
              hfst.symm
            simp [Memo.substN, hlookup, PLeaTTa.substN, href, hden] at hih ⊢
            exact hih
  case case3 fuel atoms ih =>
    intro state coherent
    have hmap := run_mapM_eq_reference
      (Memo.substN (fuel + 1))
      (fun denotation atom => PLeaTTa.substN (fuel + 1) denotation atom)
      atoms ih state coherent
    simp [Memo.substN, PLeaTTa.substN] at hmap ⊢
    exact hmap
  case case4 fuel atom hvar hexpr =>
    intro state coherent
    cases atom with
    | sym name => simp [Memo.substN, PLeaTTa.substN, coherent]
    | var name => exact False.elim (hvar name rfl)
    | gnd ground => simp [Memo.substN, PLeaTTa.substN, coherent]
    | expr atoms => exact False.elim (hexpr atoms rfl)

/-- Load-bearing executable theorem: the state-threaded memo returns exactly
the existing deep-substitution result and preserves its invariant. -/
theorem Memo.subst_eq_reference (state : Memo) (atom : Atom)
    (coherent : state.Coherent) :
    let result := state.subst atom
    result.1 = PLeaTTa.subst state.denote atom ∧
      result.2.Coherent ∧ result.2.denote = state.denote := by
  have href := Memo.substN_run_eq_reference
    (state.depth + 1) atom state coherent
  simpa [Memo.subst, PLeaTTa.subst, coherent.depth_eq] using href

theorem Memo.compose_subst_eq_reference (state : Memo) (generated : Subst)
    (atom : Atom) (coherent : state.Coherent) :
    let result := (state.compose generated).subst atom
    result.1 = PLeaTTa.subst
        (Metta.Subst.compose generated state.denote) atom ∧
      result.2.Coherent ∧
        result.2.denote = Metta.Subst.compose generated state.denote := by
  simpa using Memo.subst_eq_reference (state.compose generated) atom
    (state.compose_coherent generated coherent)

theorem Memo.unifyB_map_denote (state : Memo) (left right : Atom)
    (coherent : state.Coherent) :
    (state.unifyB left right).map Memo.denote =
      PLeaTTa.unifyB state.denote left right := by
  have hleft := state.subst_eq_reference left coherent
  cases hleftResult : state.subst left with
  | mk leftValue leftState =>
      simp only [hleftResult] at hleft
      have hright := leftState.subst_eq_reference right hleft.2.1
      cases hrightResult : leftState.subst right with
      | mk rightValue rightState =>
          simp only [hrightResult] at hright
          unfold Memo.unifyB PLeaTTa.unifyB
          rw [hleftResult]
          dsimp only
          rw [hrightResult]
          dsimp only
          rw [hleft.1, hright.1, hleft.2.2]
          cases hunify : PLeaTTa.unifyTopExact
              (PLeaTTa.subst state.denote left)
              (PLeaTTa.subst state.denote right) with
          | none => rfl
          | some generated =>
              cases generated with
              | nil => simp [hright.2.2, hleft.2.2]
              | cons binding rest =>
                  simp [hright.2.2, hleft.2.2]

theorem Memo.unifyB_coherent (state : Memo) (left right : Atom)
    (coherent : state.Coherent) :
    ∀ next, state.unifyB left right = some next → next.Coherent := by
  intro next hnext
  have hleft := state.subst_eq_reference left coherent
  cases hleftResult : state.subst left with
  | mk leftValue leftState =>
      simp only [hleftResult] at hleft
      have hright := leftState.subst_eq_reference right hleft.2.1
      cases hrightResult : leftState.subst right with
      | mk rightValue rightState =>
          simp only [hrightResult] at hright
          unfold Memo.unifyB at hnext
          rw [hleftResult] at hnext
          dsimp only at hnext
          rw [hrightResult] at hnext
          dsimp only at hnext
          cases hunify : PLeaTTa.unifyTopExact leftValue rightValue with
          | none => simp [hunify] at hnext
          | some generated =>
              cases generated with
              | nil =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact hright.2.1
              | cons binding rest =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact rightState.compose_coherent (binding :: rest)
                    hright.2.1

theorem foldl_activeOfList_contains (entries : Subst) (active : VarSet)
    (name : String) :
    (entries.foldl (fun current entry => current.insert entry.1)
      active).contains name =
      (active.contains name ||
        (Metta.Subst.lookup entries name).isSome) := by
  induction entries generalizing active with
  | nil => simp [Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hkey : key = name
      · subst key
        simp [Std.HashSet.contains_insert, Metta.Subst.lookup]
      · have hforward : key ≠ name := hkey
        have hreverse : name ≠ key := Ne.symm hkey
        simp [Std.HashSet.contains_insert, hforward, hreverse,
          Metta.Subst.lookup, Bool.or_assoc]

theorem activeOfList_contains (entries : Subst) (name : String) :
    (activeOfList entries).contains name =
      (Metta.Subst.lookup entries name).isSome := by
  unfold activeOfList
  rw [foldl_activeOfList_contains]
  simp

theorem varSet_contains_filter (set : VarSet) (keep : String → Bool)
    (name : String) :
    (set.filter keep).contains name =
      (set.contains name && keep name) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hcontains
    have hfiltered : name ∈ set.filter keep :=
      Std.HashSet.mem_iff_contains.mpr hcontains
    rcases Std.HashSet.mem_filter.mp hfiltered with ⟨hmember, hkeep⟩
    have hcontainsSet : set.contains name = true :=
      Std.HashSet.mem_iff_contains.mp hmember
    simpa [hcontainsSet] using hkeep
  · intro hboth
    have hparts : set.contains name = true ∧ keep name = true := by
      simpa [Bool.and_eq_true] using hboth
    have hmember : name ∈ set :=
      Std.HashSet.mem_iff_contains.mpr hparts.1
    apply Std.HashSet.mem_iff_contains.mp
    apply Std.HashSet.mem_filter.mpr
    exact ⟨hmember, by simpa using hparts.2⟩

/-- Retaining exactly the active bindings selected by `live` produces the
same dependency relation as the duplicate-free reference substitution
filter. This is the representation-preservation obligation used by both
runtime trimming implementations. -/
theorem DependencyGraph.retainSources_coherent_filter
    (graph : DependencyGraph) (entries : Subst) (active live : VarSet)
    (coherent : graph.Coherent entries)
    (domain : ∀ source,
      active.contains source =
        (Metta.Subst.lookup entries source).isSome) :
    (graph.retainSources active (active.filter live.contains)).Coherent
      (PLeaTTa.filterLiveSubst live
        (Std.HashSet.emptyWithCapacity entries.length) entries) := by
  have retained := graph.retainSources_models active
    (active.filter live.contains)
    (fun source => (Metta.Subst.lookup entries source).map Atom.vars)
    coherent
  apply retained.congr
  intro source
  rw [PLeaTTa.filterLiveSubst_lookup_empty,
    varSet_contains_filter, domain]
  cases live.contains source <;>
    cases Metta.Subst.lookup entries source <;> rfl

theorem activeOfList_equiv_ofList_keys (entries : Subst) :
    Std.HashSet.Equiv (activeOfList entries)
      (Std.HashSet.ofList (entries.map Prod.fst)) := by
  rw [Std.HashSet.equiv_iff_forall_mem_iff]
  intro name
  rw [Std.HashSet.mem_iff_contains, activeOfList_contains,
    Std.HashSet.mem_iff_contains, Std.HashSet.contains_ofList]
  exact (subst_lookup_isSome_iff_mem_keys entries name).trans
    List.contains_iff_mem.symm

theorem activeOfList_size_eq_length_of_nodup (entries : Subst)
    (hnodup : (entries.map Prod.fst).Nodup) :
    (activeOfList entries).size = entries.length := by
  calc
    (activeOfList entries).size =
        (Std.HashSet.ofList (entries.map Prod.fst)).size :=
      Std.HashSet.Equiv.size_eq (activeOfList_equiv_ofList_keys entries)
    _ = (entries.map Prod.fst).length := by
      apply Std.HashSet.size_ofList
      simpa [beq_eq_false_iff_ne] using
        (List.nodup_iff_pairwise_ne.mp hnodup)
    _ = entries.length := by simp

/-- Exact semantic invariant for the logically-scoped persistent engine. -/
structure Scoped.Coherent (state : Scoped) : Prop where
  version_eq : state.memo.version = state.memo.layers.length
  depth_eq : state.memo.depth = state.denote.length
  stamped : ∀ (name : String) (entry : MemoEntry),
    state.memo.entries[name]? = some entry →
      entry.version ≤ state.memo.version
  domain_eq : ∀ name,
    state.active.contains name =
      (Metta.Subst.lookup state.denote name).isSome
  peek_eq : ∀ name,
    state.peek name = Metta.Subst.lookup state.denote name
  dependencies_eq : state.dependencies.Coherent state.denote
  recent_valid : ∀ prepared ∈ state.recent, prepared.Valid

theorem Scoped.ofList_coherent (entries : Subst) :
    (Scoped.ofList entries).Coherent := by
  constructor
  · rfl
  · rfl
  · intro name entry hentry
    change (buildMemoIndex entries 0)[name]? = some entry at hentry
    change entry.version ≤ 0
    rw [buildMemoIndex_getElem?] at hentry
    rcases Option.map_eq_some_iff.mp hentry with ⟨value, hvalue, rfl⟩
    exact Nat.le_refl 0
  · exact activeOfList_contains entries
  · intro name
    change (if (activeOfList entries).contains name then
        (Memo.ofList entries).peek name else none) =
      Metta.Subst.lookup entries name
    rw [activeOfList_contains, Memo.peek_ofList]
    cases Metta.Subst.lookup entries name <;> rfl
  · exact DependencyGraph.ofList_coherent entries
  · simp [Scoped.ofList]

/-- Replacing only the transient prepared-root cache preserves every
semantic invariant when all new cache entries are valid. -/
theorem Scoped.withRecent_coherent (state : Scoped)
    (recent : List PreparedAtom) (coherent : state.Coherent)
    (valid : ∀ prepared ∈ recent, prepared.Valid) :
    ({ state with recent := recent } : Scoped).Coherent := by
  constructor
  · exact coherent.version_eq
  · exact coherent.depth_eq
  · exact coherent.stamped
  · exact coherent.domain_eq
  · exact coherent.peek_eq
  · exact coherent.dependencies_eq
  · exact valid

/-- Installing an intrinsically certified closed root changes only transient
lookup metadata, so every semantic invariant is preserved. -/
theorem Scoped.withClosedRoot_coherent (state : Scoped) (root : ClosedRoot)
    (coherent : state.Coherent) :
    ({ state with closedRoots := [root] } : Scoped).Coherent := by
  constructor
  · exact coherent.version_eq
  · exact coherent.depth_eq
  · exact coherent.stamped
  · exact coherent.domain_eq
  · exact coherent.peek_eq
  · exact coherent.dependencies_eq
  · exact coherent.recent_valid

/-- The persistent prepared-value cache is operational metadata only. -/
theorem Scoped.withClosedPrepared_coherent (state : Scoped)
    (cache : ClosedPreparedCache) (coherent : state.Coherent) :
    ({ state with closedPrepared := cache } : Scoped).Coherent := by
  constructor
  · exact coherent.version_eq
  · exact coherent.depth_eq
  · exact coherent.stamped
  · exact coherent.domain_eq
  · exact coherent.peek_eq
  · exact coherent.dependencies_eq
  · exact coherent.recent_valid

@[simp] theorem Scoped.denote_rememberRecent (state : Scoped)
    (prepared : PreparedAtom) (valid : prepared.Valid) :
    (state.rememberRecent prepared valid).denote = state.denote := rfl

theorem Scoped.rememberRecent_coherent (state : Scoped)
    (prepared : PreparedAtom) (preparedValid : prepared.Valid)
    (coherent : state.Coherent) :
    (state.rememberRecent prepared preparedValid).Coherent := by
  apply state.withRecent_coherent [prepared] coherent
  intro candidate member
  simp only [List.mem_singleton] at member
  subst candidate
  exact preparedValid

@[simp] theorem Scoped.denote_rememberPrepared (state : Scoped)
    (prepared : PreparedAtom) (valid : prepared.Valid) :
    (state.rememberPrepared prepared valid).denote = state.denote := by
  unfold Scoped.rememberPrepared
  split <;> rfl

theorem Scoped.rememberPrepared_coherent (state : Scoped)
    (prepared : PreparedAtom) (preparedValid : prepared.Valid)
    (coherent : state.Coherent) :
    (state.rememberPrepared prepared preparedValid).Coherent := by
  have recentCoherent :=
    state.rememberRecent_coherent prepared preparedValid coherent
  unfold Scoped.rememberPrepared
  split
  · exact recentCoherent
  · exact Scoped.withClosedPrepared_coherent
      ({ state with recent := [prepared] } : Scoped) _ recentCoherent

@[simp] theorem Scoped.denote_selectClosedRoot (state : Scoped)
    (root : ClosedRoot) :
    (state.selectClosedRoot root).denote = state.denote := rfl

theorem Scoped.selectClosedRoot_coherent (state : Scoped)
    (root : ClosedRoot) (coherent : state.Coherent) :
    (state.selectClosedRoot root).Coherent := by
  unfold Scoped.selectClosedRoot
  let selected :=
    match state.closedPrepared[root.key]? with
    | some cached => if cached.sameAtom root.atom then cached else root
    | none => root
  exact state.withClosedRoot_coherent selected coherent

theorem Scoped.cachedClosedPrepared_some (state : Scoped) (name : String)
    (prepared : PreparedAtom) (coherent : state.Coherent)
    (found : state.cachedClosedPrepared name = some prepared) :
    prepared.Valid ∧
      Metta.Subst.lookup state.denote name = some prepared.atom ∧
      prepared.atom.vars = [] := by
  unfold Scoped.cachedClosedPrepared at found
  by_cases hactive : state.active.contains name = true
  · simp only [hactive, if_true] at found
    cases hcached : state.memo.cachedPrepared name with
    | none => simp [hcached] at found
    | some candidate =>
        simp only [hcached] at found
        cases hempty : candidate.variables.isEmpty with
        | false => simp [hempty] at found
        | true =>
            simp only [hempty, if_true, Option.some.injEq] at found
            subst candidate
            have cached := Memo.cachedPrepared_some state.memo name prepared
              hcached
            rcases cached with ⟨valid, entry, hentry, hatom⟩
            have hvariables : prepared.variables = [] := by
              cases hvars : prepared.variables with
              | nil => rfl
              | cons head tail => simp [hvars] at hempty
            have hatomVars : prepared.atom.vars = [] := by
              rw [← valid.variables_eq]
              exact hvariables
            have hmemoPeek : state.memo.peek name = some prepared.atom := by
              unfold Memo.peek
              rw [hentry]
              simp only [Option.map_some, Option.some.injEq]
              rw [← hatom]
              exact Memo.advance_of_closed state.memo.layers
                (state.memo.version - entry.version) prepared.atom hatomVars
            have hpeek := coherent.peek_eq name
            unfold Scoped.peek at hpeek
            rw [hactive, hmemoPeek] at hpeek
            exact ⟨valid, hpeek.symm, hatomVars⟩
  · have hfalse : state.active.contains name = false := by
      cases hcontains : state.active.contains name
      · rfl
      · exact False.elim (hactive hcontains)
    simp [hfalse] at found

theorem extendGenerated_active_contains (entries : MemoIndex)
    (active : VarSet) (version : Nat) (generated : Subst) (name : String) :
    (extendGenerated entries active version generated).2.contains name =
      (active.contains name ||
        (Metta.Subst.lookup generated name).isSome) := by
  induction generated generalizing entries active with
  | nil => simp [extendGenerated, Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      unfold extendGenerated
      simp only [List.foldl_cons]
      let nextEntries :=
        if active.contains key then
          entries.insertIfNew key { value := value, version := version }
        else entries.insert key { value := value, version := version }
      change (extendGenerated nextEntries (active.insert key) version rest).2.contains
          name = _
      rw [ih nextEntries (active.insert key)]
      by_cases hkey : key = name
      · subst key
        simp [Std.HashSet.contains_insert, Metta.Subst.lookup]
      · have hforward : key ≠ name := hkey
        have hreverse : name ≠ key := Ne.symm hkey
        simp [Std.HashSet.contains_insert, hforward, hreverse,
          Metta.Subst.lookup, Bool.or_assoc]

theorem extendGenerated_preserves_active_get (entries : MemoIndex)
    (active : VarSet) (version : Nat) (generated : Subst) (name : String)
    (entry : MemoEntry) (hactive : active.contains name = true)
    (hentry : entries[name]? = some entry) :
    (extendGenerated entries active version generated).1[name]? = some entry := by
  induction generated generalizing entries active with
  | nil => exact hentry
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      let cached : MemoEntry := { value := value, version := version }
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      have hactiveNext : (active.insert key).contains name = true := by
        simp [Std.HashSet.contains_insert, hactive]
      have hentryNext : nextEntries[name]? = some entry := by
        by_cases hkey : key = name
        · subst key
          simp only [nextEntries, hactive, if_true]
          rcases (Std.TreeMap.getElem?_eq_some_iff.mp hentry) with
            ⟨hmem, hvalue⟩
          rw [Std.TreeMap.getElem?_insertIfNew]
          simp [hmem, hvalue]
        · have hforward : key ≠ name := hkey
          simp only [nextEntries]
          split
          · rw [Std.TreeMap.getElem?_insertIfNew]
            simp [hforward, hentry]
          · rw [Std.TreeMap.getElem?_insert]
            simp [hforward, hentry]
      change (extendGenerated nextEntries (active.insert key) version rest).1[name]? =
        some entry
      exact ih nextEntries (active.insert key) hactiveNext hentryNext

theorem extendGenerated_inactive_get_of_lookup_some (entries : MemoIndex)
    (active : VarSet) (version : Nat) (generated : Subst) (name : String)
    (value : Atom) (hinactive : active.contains name = false)
    (hlookup : Metta.Subst.lookup generated name = some value) :
    (extendGenerated entries active version generated).1[name]? =
      some { value := value, version := version } := by
  induction generated generalizing entries active with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      let cached : MemoEntry := { value := target, version := version }
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      by_cases hkey : key = name
      · subst key
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst target
        have hentryNext : nextEntries[name]? =
            some { value := value, version := version } := by
          simp [nextEntries, hinactive]
          rfl
        change (extendGenerated nextEntries (active.insert name) version rest).1[name]? = _
        apply extendGenerated_preserves_active_get
        · simp [Std.HashSet.contains_insert]
        · exact hentryNext
      · have hforward : key ≠ name := hkey
        have hreverse : name ≠ key := Ne.symm hkey
        have hlookupRest : Metta.Subst.lookup rest name = some value := by
          simpa [Metta.Subst.lookup, hreverse] using hlookup
        have hinactiveNext : (active.insert key).contains name = false := by
          simp [Std.HashSet.contains_insert, hforward, hinactive]
        change (extendGenerated nextEntries (active.insert key) version rest).1[name]? = _
        exact ih nextEntries (active.insert key) hinactiveNext hlookupRest

theorem extendGenerated_inactive_get_of_lookup_none (entries : MemoIndex)
    (active : VarSet) (version : Nat) (generated : Subst) (name : String)
    (hinactive : active.contains name = false)
    (hlookup : Metta.Subst.lookup generated name = none) :
    (extendGenerated entries active version generated).1[name]? =
      entries[name]? := by
  induction generated generalizing entries active with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      have hkey : key ≠ name := by
        intro heq
        subst key
        simp [Metta.Subst.lookup] at hlookup
      have hforward : key ≠ name := hkey
      have hreverse : name ≠ key := Ne.symm hkey
      have hlookupRest : Metta.Subst.lookup rest name = none := by
        simpa [Metta.Subst.lookup, hreverse] using hlookup
      let cached : MemoEntry := { value := target, version := version }
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      have hinactiveNext : (active.insert key).contains name = false := by
        simp [Std.HashSet.contains_insert, hforward, hinactive]
      have hnextGet : nextEntries[name]? = entries[name]? := by
        simp only [nextEntries]
        split
        · rw [Std.TreeMap.getElem?_insertIfNew]
          simp [hforward]
        · rw [Std.TreeMap.getElem?_insert]
          simp [hforward]
      change (extendGenerated nextEntries (active.insert key) version rest).1[name]? = _
      rw [ih nextEntries (active.insert key) hinactiveNext hlookupRest,
        hnextGet]

theorem extendGeneratedPrepared_active_contains (entries : MemoIndex)
    (active : VarSet) (version : Nat)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (name : String) :
    (extendGeneratedPrepared entries active version generated valid).2.contains name =
      (active.contains name ||
        (PreparedAtom.lookup generated name).isSome) := by
  induction generated generalizing entries active with
  | nil => simp [extendGeneratedPrepared, PreparedAtom.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      have targetValid : target.Valid := valid (key, target) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun entry member => valid entry (by simp [member])
      unfold extendGeneratedPrepared
      dsimp only
      let cached := MemoEntry.ofPrepared target targetValid version
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      change
        (extendGeneratedPrepared nextEntries (active.insert key) version
          rest restValid).2.contains name = _
      rw [ih nextEntries (active.insert key)]
      by_cases hkey : key = name
      · subst key
        simp [Std.HashSet.contains_insert, PreparedAtom.lookup]
      · have hreverse : name ≠ key := Ne.symm hkey
        simp [Std.HashSet.contains_insert, hkey, hreverse,
          PreparedAtom.lookup, Bool.or_assoc]

theorem extendGeneratedPrepared_preserves_active_get (entries : MemoIndex)
    (active : VarSet) (version : Nat)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (name : String) (entry : MemoEntry)
    (hactive : active.contains name = true)
    (hentry : entries[name]? = some entry) :
    (extendGeneratedPrepared entries active version generated valid).1[name]? =
      some entry := by
  induction generated generalizing entries active with
  | nil => exact hentry
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      have targetValid : target.Valid := valid (key, target) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun restEntry member => valid restEntry (by simp [member])
      let cached := MemoEntry.ofPrepared target targetValid version
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      have hactiveNext : (active.insert key).contains name = true := by
        simp [Std.HashSet.contains_insert, hactive]
      have hentryNext : nextEntries[name]? = some entry := by
        by_cases hkey : key = name
        · subst key
          simp only [nextEntries, hactive, if_true]
          rcases (Std.TreeMap.getElem?_eq_some_iff.mp hentry) with
            ⟨hmem, hvalue⟩
          rw [Std.TreeMap.getElem?_insertIfNew]
          simp [hmem, hvalue]
        · simp only [nextEntries]
          split
          · rw [Std.TreeMap.getElem?_insertIfNew]
            simp [hkey, hentry]
          · rw [Std.TreeMap.getElem?_insert]
            simp [hkey, hentry]
      change
        (extendGeneratedPrepared nextEntries (active.insert key) version
          rest restValid).1[name]? = some entry
      exact ih nextEntries (active.insert key) restValid
        hactiveNext hentryNext

theorem extendGeneratedPrepared_inactive_get_of_lookup_some
    (entries : MemoIndex) (active : VarSet) (version : Nat)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (name : String) (target : PreparedAtom)
    (hinactive : active.contains name = false)
    (hlookup : PreparedAtom.lookup generated name = some target) :
    (extendGeneratedPrepared entries active version generated valid).1[name]? =
      some (MemoEntry.ofPrepared target
        (valid.lookup name target hlookup) version) := by
  induction generated generalizing entries active with
  | nil => simp [PreparedAtom.lookup] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      have valueValid : value.Valid := valid (key, value) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun restEntry member => valid restEntry (by simp [member])
      let cached := MemoEntry.ofPrepared value valueValid version
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      by_cases hkey : key = name
      · subst key
        simp only [PreparedAtom.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst value
        have hentryNext : nextEntries[name]? =
            some (MemoEntry.ofPrepared target valueValid version) := by
          simp [nextEntries, hinactive, cached]
        change
          (extendGeneratedPrepared nextEntries (active.insert name) version
            rest restValid).1[name]? = _
        have preserved := extendGeneratedPrepared_preserves_active_get
          nextEntries (active.insert name) version rest restValid name
          (MemoEntry.ofPrepared target valueValid version)
          (by simp [Std.HashSet.contains_insert]) hentryNext
        simpa using preserved
      · have hreverse : name ≠ key := Ne.symm hkey
        have hlookupRest : PreparedAtom.lookup rest name = some target := by
          simpa [PreparedAtom.lookup, hreverse] using hlookup
        have hinactiveNext : (active.insert key).contains name = false := by
          simp [Std.HashSet.contains_insert, hkey, hinactive]
        change
          (extendGeneratedPrepared nextEntries (active.insert key) version
            rest restValid).1[name]? = _
        have result := ih nextEntries (active.insert key) restValid
          hinactiveNext hlookupRest
        simpa [PreparedAtom.PreparedSubst.Valid.lookup, hlookup,
          hlookupRest] using result

theorem extendGeneratedPrepared_inactive_get_of_lookup_none
    (entries : MemoIndex) (active : VarSet) (version : Nat)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (name : String) (hinactive : active.contains name = false)
    (hlookup : PreparedAtom.lookup generated name = none) :
    (extendGeneratedPrepared entries active version generated valid).1[name]? =
      entries[name]? := by
  induction generated generalizing entries active with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      have targetValid : target.Valid := valid (key, target) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun restEntry member => valid restEntry (by simp [member])
      have hkey : key ≠ name := by
        intro equal
        subst key
        simp [PreparedAtom.lookup] at hlookup
      have hreverse : name ≠ key := Ne.symm hkey
      have hlookupRest : PreparedAtom.lookup rest name = none := by
        simpa [PreparedAtom.lookup, hreverse] using hlookup
      let cached := MemoEntry.ofPrepared target targetValid version
      let nextEntries :=
        if active.contains key then entries.insertIfNew key cached
        else entries.insert key cached
      have hinactiveNext : (active.insert key).contains name = false := by
        simp [Std.HashSet.contains_insert, hkey, hinactive]
      have hnextGet : nextEntries[name]? = entries[name]? := by
        simp only [nextEntries]
        split
        · rw [Std.TreeMap.getElem?_insertIfNew]
          simp [hkey]
        · rw [Std.TreeMap.getElem?_insert]
          simp [hkey]
      change
        (extendGeneratedPrepared nextEntries (active.insert key) version
          rest restValid).1[name]? = _
      rw [ih nextEntries (active.insert key) restValid hinactiveNext
        hlookupRest, hnextGet]

@[simp] theorem Scoped.denote_compose (state : Scoped) (generated : Subst) :
    (state.compose generated).denote =
      Metta.Subst.compose generated state.denote := rfl

@[simp] theorem Scoped.compose_version (state : Scoped) (generated : Subst) :
    (state.compose generated).memo.version = state.memo.version + 1 := rfl

@[simp] theorem Scoped.compose_layers (state : Scoped) (generated : Subst) :
    (state.compose generated).memo.layers = generated :: state.memo.layers := rfl

@[simp] theorem Scoped.compose_depth (state : Scoped) (generated : Subst) :
    (state.compose generated).memo.depth =
      state.memo.depth + generated.length := rfl

@[simp] theorem Scoped.compose_entries (state : Scoped) (generated : Subst) :
    (state.compose generated).memo.entries =
      (extendGenerated state.memo.entries state.active
        (state.memo.version + 1) generated).1 := rfl

@[simp] theorem Scoped.compose_active (state : Scoped) (generated : Subst) :
    (state.compose generated).active =
      (extendGenerated state.memo.entries state.active
        (state.memo.version + 1) generated).2 := rfl

theorem Scoped.active_of_lookup_some (state : Scoped) (name : String)
    (value : Atom) (coherent : state.Coherent)
    (hlookup : Metta.Subst.lookup state.denote name = some value) :
    state.active.contains name = true := by
  rw [coherent.domain_eq name, hlookup]
  rfl

theorem Scoped.inactive_of_lookup_none (state : Scoped) (name : String)
    (coherent : state.Coherent)
    (hlookup : Metta.Subst.lookup state.denote name = none) :
    state.active.contains name = false := by
  rw [coherent.domain_eq name, hlookup]
  rfl

theorem Scoped.entry_of_lookup_some (state : Scoped) (name : String)
    (value : Atom) (coherent : state.Coherent)
    (hlookup : Metta.Subst.lookup state.denote name = some value) :
    ∃ entry : MemoEntry,
      state.memo.entries[name]? = some entry ∧
        Memo.advance state.memo.layers
          (state.memo.version - entry.version) entry.value = value := by
  have hactive := state.active_of_lookup_some name value coherent hlookup
  have hpeek := coherent.peek_eq name
  unfold Scoped.peek at hpeek
  rw [hactive] at hpeek
  simp only [if_true] at hpeek
  rw [hlookup] at hpeek
  unfold Memo.peek at hpeek
  cases hentry : state.memo.entries[name]? with
  | none => simp [hentry] at hpeek
  | some entry =>
      simp only [hentry, Option.map_some, Option.some.injEq] at hpeek
      exact ⟨entry, rfl, hpeek⟩

theorem Scoped.peek_compose (state : Scoped) (generated : Subst)
    (coherent : state.Coherent) (name : String) :
    (state.compose generated).peek name =
      match state.peek name with
      | some value => some (Metta.Subst.apply generated value)
      | none => Metta.Subst.lookup generated name := by
  rw [coherent.peek_eq]
  cases hold : Metta.Subst.lookup state.denote name with
  | some oldValue =>
      have hactive := state.active_of_lookup_some name oldValue coherent hold
      rcases state.entry_of_lookup_some name oldValue coherent hold with
        ⟨entry, hentry, hvalue⟩
      have hfinalEntry := extendGenerated_preserves_active_get
        state.memo.entries state.active (state.memo.version + 1)
          generated name entry hactive hentry
      have hfinalActive := extendGenerated_active_contains
        state.memo.entries state.active (state.memo.version + 1)
          generated name
      have hstamp := coherent.stamped name entry hentry
      have hsubtract :
          state.memo.version + 1 - entry.version =
            (state.memo.version - entry.version) + 1 := by
        omega
      unfold Scoped.peek Memo.peek
      simp only [Scoped.compose_active, Scoped.compose_entries,
        Scoped.compose_layers, Scoped.compose_version]
      rw [hfinalActive, hactive, hfinalEntry]
      simp only [Bool.true_or, if_true, Option.map_some]
      rw [hsubtract, Memo.advance_cons_succ, hvalue]
  | none =>
      have hinactive := state.inactive_of_lookup_none name coherent hold
      have hfinalActive := extendGenerated_active_contains
        state.memo.entries state.active (state.memo.version + 1)
          generated name
      cases hgenerated : Metta.Subst.lookup generated name with
      | none =>
          unfold Scoped.peek Memo.peek
          simp only [Scoped.compose_active, Scoped.compose_entries,
            Scoped.compose_layers, Scoped.compose_version]
          rw [hfinalActive, hinactive, hgenerated]
          rfl
      | some generatedValue =>
          have hfinalEntry := extendGenerated_inactive_get_of_lookup_some
            state.memo.entries state.active (state.memo.version + 1)
              generated name generatedValue hinactive hgenerated
          unfold Scoped.peek Memo.peek
          simp only [Scoped.compose_active, Scoped.compose_entries,
            Scoped.compose_layers, Scoped.compose_version]
          rw [hfinalActive, hinactive, hgenerated, hfinalEntry]
          simp [Memo.advance]

theorem Scoped.compose_coherent (state : Scoped) (generated : Subst)
    (coherent : state.Coherent) :
    (state.compose generated).Coherent := by
  constructor
  · simp [coherent.version_eq]
  · simp [Metta.Subst.compose, coherent.depth_eq, Nat.add_comm]
  · intro name entry hentry
    simp only [Scoped.compose_entries] at hentry
    cases hold : Metta.Subst.lookup state.denote name with
    | some oldValue =>
        have hactive := state.active_of_lookup_some name oldValue coherent hold
        rcases state.entry_of_lookup_some name oldValue coherent hold with
          ⟨oldEntry, holdEntry, hvalue⟩
        have hfinal := extendGenerated_preserves_active_get
          state.memo.entries state.active (state.memo.version + 1)
            generated name oldEntry hactive holdEntry
        rw [hfinal] at hentry
        have heq : oldEntry = entry := Option.some.inj hentry
        subst entry
        exact Nat.le_trans (coherent.stamped name oldEntry holdEntry)
          (Nat.le_add_right state.memo.version 1)
    | none =>
        have hinactive := state.inactive_of_lookup_none name coherent hold
        cases hgenerated : Metta.Subst.lookup generated name with
        | some value =>
            have hfinal := extendGenerated_inactive_get_of_lookup_some
              state.memo.entries state.active (state.memo.version + 1)
                generated name value hinactive hgenerated
            rw [hfinal] at hentry
            have heq :
                ({ value := value, version := state.memo.version + 1 } : MemoEntry) = entry :=
                Option.some.inj hentry
            subst entry
            exact Nat.le_refl _
        | none =>
            have hfinal := extendGenerated_inactive_get_of_lookup_none
              state.memo.entries state.active (state.memo.version + 1)
                generated name hinactive hgenerated
            rw [hfinal] at hentry
            exact Nat.le_trans (coherent.stamped name entry hentry)
              (Nat.le_add_right state.memo.version 1)
  · intro name
    rw [Scoped.compose_active, extendGenerated_active_contains,
      Scoped.denote_compose, PLeaTTa.lookup_compose,
      coherent.domain_eq]
    cases Metta.Subst.lookup state.denote name <;>
      cases Metta.Subst.lookup generated name <;> rfl
  · intro name
    rw [Scoped.peek_compose state generated coherent name,
      coherent.peek_eq, Scoped.denote_compose, PLeaTTa.lookup_compose]
    rfl
  · exact state.dependencies.compose_coherent state.denote generated
      coherent.dependencies_eq
  · exact coherent.recent_valid

theorem Scoped.refresh_coherent (state : Scoped) (name : String)
    (value : Atom) (coherent : state.Coherent)
    (hvalue : state.peek name = some value) :
    ({ state with memo := state.memo.refresh name value } : Scoped).Coherent := by
  have hactive : state.active.contains name = true := by
    unfold Scoped.peek at hvalue
    split at hvalue
    · assumption
    · contradiction
  constructor
  · exact coherent.version_eq
  · exact coherent.depth_eq
  · intro query entry hentry
    change (state.memo.entries.insert name
      { value := value, version := state.memo.version })[query]? = some entry at hentry
    rw [Std.TreeMap.getElem?_insert] at hentry
    by_cases hname : name = query
    · subst query
      simp at hentry
      subst entry
      exact Nat.le_refl _
    · simp [hname] at hentry
      exact coherent.stamped query entry hentry
  · exact coherent.domain_eq
  · intro query
    unfold Scoped.peek
    by_cases hqueryActive : state.active.contains query = true
    · simp only [hqueryActive, if_true]
      unfold Memo.peek Memo.refresh
      rw [Std.TreeMap.getElem?_insert]
      by_cases hname : name = query
      · subst query
        have hreference := coherent.peek_eq name
        rw [hvalue] at hreference
        simp
        exact hreference
      · simp [hname]
        have hreference := coherent.peek_eq query
        unfold Scoped.peek at hreference
        simp only [hqueryActive, if_true] at hreference
        change state.memo.peek query = Metta.Subst.lookup state.denote query
        exact hreference
    · have hqueryFalse : state.active.contains query = false := by
        cases hcontains : state.active.contains query
        · rfl
        · exact False.elim (hqueryActive hcontains)
      simp only [hqueryFalse, Bool.false_eq_true, if_false]
      have hdomain := coherent.domain_eq query
      rw [hqueryFalse] at hdomain
      have hlookup : Metta.Subst.lookup state.denote query = none := by
        cases hresult : Metta.Subst.lookup state.denote query with
        | none => rfl
        | some result => simp [hresult] at hdomain
      change none = Metta.Subst.lookup state.denote query
      exact hlookup.symm
  · exact coherent.dependencies_eq
  · exact coherent.recent_valid

theorem Scoped.lookup_fst_eq_reference (state : Scoped) (name : String)
    (coherent : state.Coherent) :
    (state.lookup name).1 = Metta.Subst.lookup state.denote name := by
  by_cases hactive : state.active.contains name = true
  · have hpeek := coherent.peek_eq name
    unfold Scoped.peek at hpeek
    simp only [hactive, if_true] at hpeek
    simp only [Scoped.lookup, hactive, if_true]
    unfold Memo.lookup
    cases hvalue : state.memo.peek name <;> simp_all
  · have hdomain := coherent.domain_eq name
    have hinactive : state.active.contains name = false := by
      cases hcontains : state.active.contains name
      · rfl
      · exact False.elim (hactive hcontains)
    rw [hinactive] at hdomain
    have hlookup : Metta.Subst.lookup state.denote name = none := by
      cases hvalue : Metta.Subst.lookup state.denote name with
      | none => rfl
      | some value => simp [hvalue] at hdomain
    simp only [Scoped.lookup, hinactive, Bool.false_eq_true, if_false]
    exact hlookup.symm

theorem Scoped.lookup_snd_coherent (state : Scoped) (name : String)
    (coherent : state.Coherent) :
    (state.lookup name).2.Coherent := by
  by_cases hactive : state.active.contains name = true
  · simp only [Scoped.lookup, hactive, if_true]
    unfold Memo.lookup
    split
    · exact coherent
    · next value hvalue =>
        apply Scoped.refresh_coherent state name value coherent
        unfold Scoped.peek
        simp only [hactive, if_true]
        exact hvalue
  · have hinactive : state.active.contains name = false := by
      cases hcontains : state.active.contains name
      · rfl
      · exact False.elim (hactive hcontains)
    simp [Scoped.lookup, hinactive, coherent]

theorem Scoped.lookup_snd_denote (state : Scoped) (name : String) :
    (state.lookup name).2.denote = state.denote := by
  unfold Scoped.lookup
  split
  · unfold Memo.lookup
    split <;> rfl
  · rfl

private theorem runScoped_mapM_eq_reference {α β : Type}
    (action : α → StateM Scoped β) (reference : Subst → α → β)
    (items : List α)
    (correct : ∀ item ∈ items, ∀ state : Scoped, state.Coherent →
      let result := Id.run ((action item).run state)
      result.1 = reference state.denote item ∧
        result.2.Coherent ∧ result.2.denote = state.denote) :
    ∀ state : Scoped, state.Coherent →
      let result := Id.run ((items.mapM action).run state)
      result.1 = items.map (reference state.denote) ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  induction items with
  | nil =>
      intro state coherent
      simp [coherent]
  | cons item rest ih =>
      intro state coherent
      have hhead := correct item (by simp) state coherent
      cases hrunHead : Id.run ((action item).run state) with
      | mk head next =>
          simp only [hrunHead] at hhead
          have htail := ih
            (fun child hchild => correct child (by simp [hchild]))
            next hhead.2.1
          cases hrunTail : Id.run ((rest.mapM action).run next) with
          | mk tail final =>
              simp only [hrunTail] at htail
              simp [List.mapM_cons, hrunHead, hrunTail, hhead.1, hhead.2.2,
                htail.1, htail.2.1, htail.2.2]

private theorem runScoped_mapM_prepared_eq_reference {α : Type}
    (action : α → StateM Scoped PreparedAtom)
    (reference : Subst → α → Atom) (items : List α)
    (correct : ∀ item ∈ items, ∀ state : Scoped, state.Coherent →
      let result := Id.run ((action item).run state)
      result.1.atom = reference state.denote item ∧
        result.1.Valid ∧ result.2.Coherent ∧
        result.2.denote = state.denote) :
    ∀ state : Scoped, state.Coherent →
      let result := Id.run ((items.mapM action).run state)
      result.1.map PreparedAtom.atom =
          items.map (reference state.denote) ∧
        (∀ prepared ∈ result.1, prepared.Valid) ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  induction items with
  | nil =>
      intro state coherent
      simp [coherent]
  | cons item rest ih =>
      intro state coherent
      have hhead := correct item (by simp) state coherent
      cases hrunHead : Id.run ((action item).run state) with
      | mk head next =>
          simp only [hrunHead] at hhead
          have htail := ih
            (fun child hchild => correct child (by simp [hchild]))
            next hhead.2.2.1
          cases hrunTail : Id.run ((rest.mapM action).run next) with
          | mk tail final =>
              simp only [hrunTail] at htail
              simp [List.mapM_cons, hrunHead, hrunTail, hhead.1,
                hhead.2.1, hhead.2.2.2, htail.1,
                htail.2.2.1, htail.2.2.2]
              exact htail.2.1

theorem Scoped.substPreparedN_run_eq_reference (fuel : Nat) (atom : Atom) :
    ∀ state : Scoped, state.Coherent →
      let result := Id.run ((Scoped.substPreparedN fuel atom).run state)
      result.1.atom = PLeaTTa.substN fuel state.denote atom ∧
        result.1.Valid ∧ result.2.Coherent ∧
        result.2.denote = state.denote := by
  induction fuel, atom using Scoped.substPreparedN.induct
  case case1 atom =>
    intro state coherent
    simp [Scoped.substPreparedN, PLeaTTa.substN,
      PreparedAtom.ofAtom_valid, coherent]
  case case2 fuel name ih =>
    intro state coherent
    cases hfast : state.cachedClosedPrepared name with
    | some prepared =>
        have fastFacts := state.cachedClosedPrepared_some name prepared
          coherent hfast
        have hfixed := PLeaTTa.substN_of_closed fuel state.denote
          prepared.atom fastFacts.2.2
        simp [Scoped.substPreparedN, hfast, PLeaTTa.substN,
          fastFacts.2.1, hfixed, fastFacts.1, coherent]
    | none =>
        have hfst := Scoped.lookup_fst_eq_reference state name coherent
        have hsnd := Scoped.lookup_snd_coherent state name coherent
        have hden := Scoped.lookup_snd_denote state name
        cases hlookup : state.lookup name with
        | mk value next =>
            simp only [hlookup] at hfst hsnd hden
            cases value with
            | none =>
                have href :
                    Metta.Subst.lookup state.denote name = none := hfst.symm
                simp [Scoped.substPreparedN, hfast, hlookup,
                  PLeaTTa.substN, href, PreparedAtom.ofAtom_valid, hsnd,
                  hden]
            | some target =>
                have href :
                    Metta.Subst.lookup state.denote name = some target :=
                  hfst.symm
                have hforward := hsnd.dependencies_eq.forward_eq name
                rw [hden, href] at hforward
                cases hcached : next.dependencies.targetClosed name with
                | true =>
                    have hvars : target.vars = [] := by
                      unfold DependencyGraph.targetClosed at hcached
                      rw [hforward] at hcached
                      cases htargetVars : target.vars with
                      | nil => rfl
                      | cons head tail => simp [htargetVars] at hcached
                    have hfixed := PLeaTTa.substN_of_closed fuel
                      state.denote target hvars
                    simp [Scoped.substPreparedN, hfast, hlookup,
                      PLeaTTa.substN, href, hcached, hfixed,
                      PreparedAtom.ofClosed_valid target hvars, hsnd,
                      hden]
                | false =>
                    have hih := ih target next hsnd
                    simp [Scoped.substPreparedN, hfast, hlookup,
                      PLeaTTa.substN, href, hcached, hden] at hih ⊢
                    exact hih
  case case3 fuel atoms ih =>
    intro state coherent
    have hmap := runScoped_mapM_prepared_eq_reference
      (Scoped.substPreparedN (fuel + 1))
      (fun denotation atom => PLeaTTa.substN (fuel + 1) denotation atom)
      atoms ih state coherent
    simp [Scoped.substPreparedN, PLeaTTa.substN,
      PreparedAtom.mkExprFrom_eq_mkExpr] at hmap ⊢
    exact ⟨hmap.1,
      PreparedAtom.mkExpr_valid _ hmap.2.1,
      hmap.2.2.1, hmap.2.2.2⟩
  case case4 fuel atom hvar hexpr =>
    intro state coherent
    cases atom with
    | sym name =>
        simp [Scoped.substPreparedN, PLeaTTa.substN,
          PreparedAtom.ofAtom_valid, coherent]
    | var name => exact False.elim (hvar name rfl)
    | gnd ground =>
        simp [Scoped.substPreparedN, PLeaTTa.substN,
          PreparedAtom.ofAtom_valid, coherent]
    | expr atoms => exact False.elim (hexpr atoms rfl)

theorem Scoped.substN_run_eq_reference (fuel : Nat) (atom : Atom) :
    ∀ state : Scoped, state.Coherent →
      let result := Id.run ((Scoped.substN fuel atom).run state)
      result.1 = PLeaTTa.substN fuel state.denote atom ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  induction fuel, atom using Scoped.substN.induct
  case case1 atom =>
    intro state coherent
    simp [Scoped.substN, PLeaTTa.substN, coherent]
  case case2 fuel name ih =>
    intro state coherent
    cases hfast : state.cachedClosedPrepared name with
    | some prepared =>
        have fastFacts := state.cachedClosedPrepared_some name prepared
          coherent hfast
        have hfixed := PLeaTTa.substN_of_closed fuel state.denote
          prepared.atom fastFacts.2.2
        simp [Scoped.substN, hfast, PLeaTTa.substN,
          fastFacts.2.1, hfixed, coherent]
    | none =>
        have hfst := Scoped.lookup_fst_eq_reference state name coherent
        have hsnd := Scoped.lookup_snd_coherent state name coherent
        have hden := Scoped.lookup_snd_denote state name
        cases hlookup : state.lookup name with
        | mk value next =>
            simp only [hlookup] at hfst hsnd hden
            cases value with
            | none =>
                have href : Metta.Subst.lookup state.denote name = none :=
                  hfst.symm
                simp [Scoped.substN, hfast, hlookup, PLeaTTa.substN, href,
                  hsnd, hden]
            | some target =>
                have href : Metta.Subst.lookup state.denote name = some target :=
                  hfst.symm
                have hforward := hsnd.dependencies_eq.forward_eq name
                rw [hden, href] at hforward
                cases hcached : next.dependencies.targetClosed name with
                | true =>
                    have hvars : target.vars = [] :=
                      by
                        unfold DependencyGraph.targetClosed at hcached
                        rw [hforward] at hcached
                        cases hvars : target.vars with
                        | nil => rfl
                        | cons head tail => simp [hvars] at hcached
                    have hfixed := PLeaTTa.substN_of_closed fuel
                      state.denote target hvars
                    simp [Scoped.substN, hfast, hlookup, PLeaTTa.substN, href,
                      hcached, hfixed, hsnd, hden]
                | false =>
                    cases hclosed : atomClosed target with
                    | false =>
                        have hih := ih target next hsnd
                        simp [Scoped.substN, hfast, hlookup, PLeaTTa.substN,
                          href, hcached, hclosed, hden] at hih ⊢
                        exact hih
                    | true =>
                        have hvars : target.vars = [] :=
                          (atomClosed_eq_true_iff_vars_nil target).mp hclosed
                        have hfixed := PLeaTTa.substN_of_closed fuel
                          state.denote target hvars
                        simp [Scoped.substN, hfast, hlookup, PLeaTTa.substN,
                          href, hcached, hclosed, hfixed, hsnd, hden]
  case case3 fuel atoms ih =>
    intro state coherent
    have hmap := runScoped_mapM_eq_reference
      (Scoped.substN (fuel + 1))
      (fun denotation atom => PLeaTTa.substN (fuel + 1) denotation atom)
      atoms ih state coherent
    simp [Scoped.substN, PLeaTTa.substN] at hmap ⊢
    exact hmap
  case case4 fuel atom hvar hexpr =>
    intro state coherent
    cases atom with
    | sym name => simp [Scoped.substN, PLeaTTa.substN, coherent]
    | var name => exact False.elim (hvar name rfl)
    | gnd ground => simp [Scoped.substN, PLeaTTa.substN, coherent]
    | expr atoms => exact False.elim (hexpr atoms rfl)

theorem Scoped.substRootN_run_eq_reference (fuel : Nat) (atom : Atom) :
    ∀ state : Scoped, state.Coherent →
      let result := Id.run ((Scoped.substRootN fuel atom).run state)
      result.1 = PLeaTTa.substN fuel state.denote atom ∧
        result.2.Coherent ∧ result.2.denote = state.denote := by
  intro state coherent
  cases hclosed : atomClosed atom with
  | false =>
      simpa [Scoped.substRootN, hclosed] using
        Scoped.substN_run_eq_reference fuel atom state coherent
  | true =>
      have hvars : atom.vars = [] :=
        (atomClosed_eq_true_iff_vars_nil atom).mp hclosed
      simp [Scoped.substRootN, hclosed,
        PLeaTTa.substN_of_closed fuel state.denote atom hvars, coherent]

theorem Scoped.subst_eq_reference (state : Scoped) (atom : Atom)
    (coherent : state.Coherent) :
    let result := state.subst atom
    result.1 = PLeaTTa.subst state.denote atom ∧
      result.2.Coherent ∧ result.2.denote = state.denote := by
  cases hdepth : state.memo.depth with
  | zero =>
      have hlength : state.denote.length = 0 := by
        rw [← coherent.depth_eq, hdepth]
      have hdenote : state.denote = [] :=
        List.eq_nil_of_length_eq_zero hlength
      simp [Scoped.subst, hdepth, hdenote, coherent]
  | succ depth =>
      have hnonzero : (state.memo.depth == 0) = false := by
        simp [hdepth]
      have href := Scoped.substRootN_run_eq_reference
        (state.memo.depth + 1) atom state coherent
      unfold Scoped.subst
      rw [hnonzero]
      simp only [Bool.false_eq_true, if_false]
      unfold PLeaTTa.subst
      rw [← coherent.depth_eq]
      exact href

theorem Scoped.substPrepared_eq_reference (state : Scoped) (atom : Atom)
    (coherent : state.Coherent) :
    let result := state.substPrepared atom
    result.1.atom = PLeaTTa.subst state.denote atom ∧
      result.1.Valid ∧ result.2.Coherent ∧
      result.2.denote = state.denote := by
  unfold Scoped.substPrepared
  cases indexed : findClosedRoot atom state.closedRoots with
  | some root =>
      have facts := findClosedRoot_some indexed
      have fixed := PLeaTTa.subst_of_closed state.denote root.atom root.closed
      change root.prepared.atom = PLeaTTa.subst state.denote atom ∧
        root.prepared.Valid ∧ state.Coherent ∧
          state.denote = state.denote
      refine ⟨?_, root.prepared_valid, coherent, rfl⟩
      rw [root.prepared_atom, ← facts.2]
      exact fixed.symm
  | none =>
      cases recent : PreparedAtom.findRecentClosed atom state.recent with
      | some prepared =>
          have facts := PreparedAtom.findRecentClosed_some recent
          have valid := coherent.recent_valid prepared facts.1
          have closed : prepared.atom.vars = [] := by
            rw [← valid.variables_eq, facts.2.1]
          have fixed := PLeaTTa.subst_of_closed state.denote prepared.atom closed
          change prepared.atom = PLeaTTa.subst state.denote atom ∧
            prepared.Valid ∧ state.Coherent ∧ state.denote = state.denote
          refine ⟨?_, valid, coherent, rfl⟩
          rw [← facts.2.2]
          exact fixed.symm
      | none =>
          by_cases hdepth : state.memo.depth = 0
          · have hlength : state.denote.length = 0 := by
              rw [← coherent.depth_eq, hdepth]
            have hdenote : state.denote = [] :=
              List.eq_nil_of_length_eq_zero hlength
            have hzero : (state.memo.depth == 0) = true := by
              simp [hdepth]
            rw [hzero]
            simp only [if_true]
            refine ⟨?_, PreparedAtom.ofAtom_valid atom, coherent, True.intro⟩
            exact (PLeaTTa.subst_nil atom).symm.trans (by rw [← hdenote])
          · have hnonzero : (state.memo.depth == 0) = false := by
              simp [hdepth]
            have href := Scoped.substPreparedN_run_eq_reference
              (state.memo.depth + 1) atom state coherent
            rw [hnonzero]
            simp only [Bool.false_eq_true, if_false]
            unfold PLeaTTa.subst
            rw [← coherent.depth_eq]
            exact href

/-- The transient closed-root shortcut computes exactly the prepared value's
    ordinary structural key. -/
theorem Scoped.preparedExactKey_eq (state : Scoped)
    (prepared : PreparedAtom) :
    state.preparedExactKey prepared = atomExactKey prepared.atom := by
  unfold Scoped.preparedExactKey
  cases cached : prepared.exact with
  | some result => exact prepared.exact_sound result cached
  | none =>
      cases found : findClosedRoot prepared.atom state.closedRoots with
      | none => simp [PreparedAtom.exactValue, cached]
      | some root =>
          have facts := findClosedRoot_some found
          change some root.key = atomExactKey prepared.atom
          rw [← facts.2]
          exact root.exact.symm

theorem Scoped.substManyPrepared_eq_reference (state : Scoped)
    (atoms : List Atom) (coherent : state.Coherent) :
    let result := state.substManyPrepared atoms
    result.1.map PreparedAtom.atom =
        atoms.map (PLeaTTa.subst state.denote) ∧
      (∀ prepared ∈ result.1, prepared.Valid) ∧
      result.2.Coherent ∧ result.2.denote = state.denote := by
  cases hdepth : state.memo.depth with
  | zero =>
      have hlength : state.denote.length = 0 := by
        rw [← coherent.depth_eq, hdepth]
      have hdenote : state.denote = [] :=
        List.eq_nil_of_length_eq_zero hlength
      have hzero : (state.memo.depth == 0) = true := by
        simp [hdepth]
      have valid : ∀ prepared ∈ atoms.map PreparedAtom.ofAtom,
          prepared.Valid := by
        intro prepared member
        rw [List.mem_map] at member
        rcases member with ⟨source, _, rfl⟩
        exact PreparedAtom.ofAtom_valid source
      have recentValid := PreparedAtom.refreshRecent_valid valid
        coherent.recent_valid
      unfold Scoped.substManyPrepared
      rw [hzero]
      simp only [if_true]
      refine ⟨?_, valid, ?_, ?_⟩
      · rw [hdenote]
        symm
        rw [List.map_map]
        apply List.map_congr_left
        intro atom _
        exact PLeaTTa.subst_nil atom
      · exact Scoped.withRecent_coherent state
          (PreparedAtom.refreshRecent (atoms.map PreparedAtom.ofAtom)
            state.recent) coherent recentValid
      · rfl
  | succ depth =>
      have hnonzero : (state.memo.depth == 0) = false := by
        simp [hdepth]
      have href := runScoped_mapM_prepared_eq_reference
        Scoped.substPreparedRoot
        (fun denotation atom => PLeaTTa.subst denotation atom)
        atoms
        (fun atom _ next nextCoherent =>
          Scoped.substPrepared_eq_reference next atom nextCoherent)
        state coherent
      unfold Scoped.substManyPrepared
      rw [hnonzero]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨?_, href.2.1, ?_, href.2.2.2⟩
      · exact href.1
      · exact Scoped.withRecent_coherent _ _ href.2.2.1
          (PreparedAtom.refreshRecent_valid href.2.1
            href.2.2.1.recent_valid)

theorem Scoped.substMany_eq_reference (state : Scoped) (atoms : List Atom)
    (coherent : state.Coherent) :
    let result := state.substMany atoms
    result.1 = atoms.map (PLeaTTa.subst state.denote) ∧
      result.2.Coherent ∧ result.2.denote = state.denote := by
  have prepared := state.substManyPrepared_eq_reference atoms coherent
  unfold Scoped.substMany
  exact ⟨prepared.1, prepared.2.2⟩

theorem Scoped.unifyB_map_denote (state : Scoped) (left right : Atom)
    (coherent : state.Coherent) :
    (state.unifyB left right).map Scoped.denote =
      PLeaTTa.unifyB state.denote left right := by
  have hleft := state.subst_eq_reference left coherent
  cases hleftResult : state.subst left with
  | mk leftValue leftState =>
      simp only [hleftResult] at hleft
      have hright := leftState.subst_eq_reference right hleft.2.1
      cases hrightResult : leftState.subst right with
      | mk rightValue rightState =>
          simp only [hrightResult] at hright
          unfold Scoped.unifyB PLeaTTa.unifyB
          rw [hleftResult]
          dsimp only
          rw [hrightResult]
          dsimp only
          rw [hleft.1, hright.1, hleft.2.2]
          cases hunify : PLeaTTa.unifyTopExact
              (PLeaTTa.subst state.denote left)
              (PLeaTTa.subst state.denote right) with
          | none => rfl
          | some generated =>
              cases generated with
              | nil => simp [hright.2.2, hleft.2.2]
              | cons binding rest =>
                  simp [hright.2.2, hleft.2.2]

theorem Scoped.unifyB_coherent (state : Scoped) (left right : Atom)
    (coherent : state.Coherent) :
    ∀ next, state.unifyB left right = some next → next.Coherent := by
  intro next hnext
  have hleft := state.subst_eq_reference left coherent
  cases hleftResult : state.subst left with
  | mk leftValue leftState =>
      simp only [hleftResult] at hleft
      have hright := leftState.subst_eq_reference right hleft.2.1
      cases hrightResult : leftState.subst right with
      | mk rightValue rightState =>
          simp only [hrightResult] at hright
          unfold Scoped.unifyB at hnext
          rw [hleftResult] at hnext
          dsimp only at hnext
          rw [hrightResult] at hnext
          dsimp only at hnext
          cases hunify : PLeaTTa.unifyTopExact leftValue rightValue with
          | none => simp [hunify] at hnext
          | some generated =>
              cases generated with
              | nil =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact hright.2.1
              | cons binding rest =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact rightState.compose_coherent (binding :: rest)
                    hright.2.1

theorem addFreshAtomVars_eq_reference (state : VarSet × VarSet)
    (atom : Atom) :
    PersistentSubst.addFreshAtomVars state atom =
      PLeaTTa.addFreshAtomVars state atom := by
  induction atom generalizing state with
  | sym name => simp [PLeaTTa.PersistentSubst.addFreshAtomVars,
      PLeaTTa.addFreshAtomVars]
  | var name => simp [PLeaTTa.PersistentSubst.addFreshAtomVars,
      PLeaTTa.addFreshAtomVars]
  | gnd ground => simp [PLeaTTa.PersistentSubst.addFreshAtomVars,
      PLeaTTa.addFreshAtomVars]
  | expr atoms ih =>
      simp only [PersistentSubst.addFreshAtomVars,
        PLeaTTa.addFreshAtomVars]
      induction atoms generalizing state with
      | nil => rfl
      | cons head tail tailIH =>
          simp only [List.foldl_cons]
          rw [ih head (by simp)]
          apply tailIH
          intro child hchild childState
          exact ih child (by simp [hchild]) childState

theorem addFreshNames_atom_vars (state : VarSet × VarSet)
    (atom : Atom) :
    addFreshNames state atom.vars = addFreshAtomVars state atom := by
  induction atom generalizing state with
  | sym name => simp [addFreshNames, addFreshAtomVars, Atom.vars]
  | var name =>
      simp [addFreshNames, addFreshAtomVars, addFreshName, Atom.vars]
  | gnd ground => simp [addFreshNames, addFreshAtomVars, Atom.vars]
  | expr atoms ih =>
      simp only [Atom.vars, addFreshAtomVars]
      induction atoms generalizing state with
      | nil => rfl
      | cons head tail tailIH =>
          simp only [List.map_cons, List.flatten_cons, List.foldl_cons]
          unfold addFreshNames
          rw [List.foldl_append]
          change addFreshNames (addFreshNames state head.vars)
              (tail.map Atom.vars).flatten = _
          rw [ih head (by simp)]
          exact tailIH (fun child member => ih child (by simp [member]))
            (addFreshAtomVars state head)

theorem addVisiblePreparedBinding_eq (visible : VarSet)
    (source : String) (target : PreparedAtom) (valid : target.Valid) :
    addVisiblePreparedBinding visible (source, target) =
      addVisibleBinding visible (source, target.atom) := by
  unfold addVisiblePreparedBinding addVisibleBinding addVisibleAtom
  rw [valid.variables_eq]
  cases closed : atomClosed target.atom with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact congrArg Prod.fst
        (addFreshNames_atom_vars
          (visible.insert source,
            Std.HashSet.emptyWithCapacity target.atom.vars.length)
          target.atom)
  | true =>
      have variablesNil : target.atom.vars = [] :=
        (atomClosed_eq_true_iff_vars_nil target.atom).mp closed
      simp [variablesNil, addFreshNames]

theorem foldl_addVisiblePreparedBinding_eq
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (visible : VarSet) :
    generated.foldl addVisiblePreparedBinding visible =
      (PreparedAtom.eraseSubst generated).foldl addVisibleBinding visible := by
  induction generated generalizing visible with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨source, target⟩
      have targetValid : target.Valid := valid (source, target) (by simp)
      have restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun entry member => valid entry (by simp [member])
      simp only [List.foldl_cons, PreparedAtom.eraseSubst, List.map_cons]
      rw [addVisiblePreparedBinding_eq visible source target targetValid]
      exact ih restValid _

@[simp] theorem Scoped.composePrepared_version (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).memo.version =
      state.memo.version + 1 := rfl

@[simp] theorem Scoped.composePrepared_layers (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).memo.layers =
      PreparedAtom.eraseSubst generated :: state.memo.layers := rfl

@[simp] theorem Scoped.composePrepared_depth (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).memo.depth =
      state.memo.depth + (PreparedAtom.eraseSubst generated).length := rfl

@[simp] theorem Scoped.composePrepared_entries (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).memo.entries =
      (extendGeneratedPrepared state.memo.entries state.active
        (state.memo.version + 1) generated valid).1 := rfl

@[simp] theorem Scoped.composePrepared_active (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).active =
      (extendGeneratedPrepared state.memo.entries state.active
        (state.memo.version + 1) generated valid).2 := rfl

@[simp] theorem Scoped.denote_composePrepared (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    (state.composePrepared generated valid).denote =
      Metta.Subst.compose (PreparedAtom.eraseSubst generated) state.denote :=
  rfl

theorem Scoped.peek_composePrepared (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (coherent : state.Coherent) (name : String) :
    (state.composePrepared generated valid).peek name =
      match state.peek name with
      | some value =>
          some (Metta.Subst.apply (PreparedAtom.eraseSubst generated) value)
      | none => Metta.Subst.lookup (PreparedAtom.eraseSubst generated) name := by
  rw [coherent.peek_eq]
  cases hold : Metta.Subst.lookup state.denote name with
  | some oldValue =>
      have hactive := state.active_of_lookup_some name oldValue coherent hold
      rcases state.entry_of_lookup_some name oldValue coherent hold with
        ⟨entry, hentry, hvalue⟩
      have hfinalEntry := extendGeneratedPrepared_preserves_active_get
        state.memo.entries state.active (state.memo.version + 1)
          generated valid name entry hactive hentry
      have hfinalActive := extendGeneratedPrepared_active_contains
        state.memo.entries state.active (state.memo.version + 1)
          generated valid name
      have hstamp := coherent.stamped name entry hentry
      have hsubtract :
          state.memo.version + 1 - entry.version =
            (state.memo.version - entry.version) + 1 := by
        omega
      unfold Scoped.peek Memo.peek
      simp only [Scoped.composePrepared_active,
        Scoped.composePrepared_entries, Scoped.composePrepared_layers,
        Scoped.composePrepared_version]
      rw [hfinalActive, hactive, hfinalEntry]
      simp only [Bool.true_or, if_true, Option.map_some]
      rw [hsubtract, Memo.advance_cons_succ, hvalue]
  | none =>
      have hinactive := state.inactive_of_lookup_none name coherent hold
      have hfinalActive := extendGeneratedPrepared_active_contains
        state.memo.entries state.active (state.memo.version + 1)
          generated valid name
      cases hgenerated : PreparedAtom.lookup generated name with
      | none =>
          have hraw :
              Metta.Subst.lookup (PreparedAtom.eraseSubst generated) name =
                none := by
            rw [PreparedAtom.lookup_eraseSubst, hgenerated]
            rfl
          have hfinalEntry :=
            extendGeneratedPrepared_inactive_get_of_lookup_none
              state.memo.entries state.active (state.memo.version + 1)
                generated valid name hinactive hgenerated
          unfold Scoped.peek Memo.peek
          simp only [Scoped.composePrepared_active,
            Scoped.composePrepared_entries, Scoped.composePrepared_layers,
            Scoped.composePrepared_version]
          rw [hfinalActive, hinactive, hgenerated, hfinalEntry, hraw]
          rfl
      | some target =>
          have hraw :
              Metta.Subst.lookup (PreparedAtom.eraseSubst generated) name =
                some target.atom := by
            rw [PreparedAtom.lookup_eraseSubst, hgenerated]
            rfl
          have hfinalEntry :=
            extendGeneratedPrepared_inactive_get_of_lookup_some
              state.memo.entries state.active (state.memo.version + 1)
                generated valid name target hinactive hgenerated
          unfold Scoped.peek Memo.peek
          simp only [Scoped.composePrepared_active,
            Scoped.composePrepared_entries, Scoped.composePrepared_layers,
            Scoped.composePrepared_version]
          rw [hfinalActive, hinactive, hgenerated, hfinalEntry, hraw]
          simp [MemoEntry.ofPrepared, Memo.advance]

theorem Scoped.composePrepared_coherent (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid)
    (coherent : state.Coherent) :
    (state.composePrepared generated valid).Coherent := by
  constructor
  · simp [coherent.version_eq]
  · simp [Metta.Subst.compose, coherent.depth_eq, Nat.add_comm]
  · intro name entry hentry
    simp only [Scoped.composePrepared_entries] at hentry
    cases hold : Metta.Subst.lookup state.denote name with
    | some oldValue =>
        have hactive := state.active_of_lookup_some name oldValue coherent hold
        rcases state.entry_of_lookup_some name oldValue coherent hold with
          ⟨oldEntry, holdEntry, hvalue⟩
        have hfinal := extendGeneratedPrepared_preserves_active_get
          state.memo.entries state.active (state.memo.version + 1)
            generated valid name oldEntry hactive holdEntry
        rw [hfinal] at hentry
        have equal : oldEntry = entry := Option.some.inj hentry
        subst entry
        exact Nat.le_trans (coherent.stamped name oldEntry holdEntry)
          (Nat.le_add_right state.memo.version 1)
    | none =>
        have hinactive := state.inactive_of_lookup_none name coherent hold
        cases hgenerated : PreparedAtom.lookup generated name with
        | some target =>
            have hfinal :=
              extendGeneratedPrepared_inactive_get_of_lookup_some
                state.memo.entries state.active (state.memo.version + 1)
                  generated valid name target hinactive hgenerated
            rw [hfinal] at hentry
            have equal :
                MemoEntry.ofPrepared target
                  (valid.lookup name target hgenerated)
                    (state.memo.version + 1) = entry :=
              Option.some.inj hentry
            subst entry
            exact Nat.le_refl _
        | none =>
            have hfinal :=
              extendGeneratedPrepared_inactive_get_of_lookup_none
                state.memo.entries state.active (state.memo.version + 1)
                  generated valid name hinactive hgenerated
            rw [hfinal] at hentry
            exact Nat.le_trans (coherent.stamped name entry hentry)
              (Nat.le_add_right state.memo.version 1)
  · intro name
    rw [Scoped.composePrepared_active,
      extendGeneratedPrepared_active_contains,
      Scoped.denote_composePrepared, PLeaTTa.lookup_compose,
      coherent.domain_eq, PreparedAtom.lookup_eraseSubst]
    cases Metta.Subst.lookup state.denote name <;>
      cases PreparedAtom.lookup generated name <;> rfl
  · intro name
    rw [Scoped.peek_composePrepared state generated valid coherent name,
      coherent.peek_eq, Scoped.denote_composePrepared,
      PLeaTTa.lookup_compose]
    rfl
  · change (state.dependencies.composePrepared generated).Coherent
      (Metta.Subst.compose (PreparedAtom.eraseSubst generated) state.denote)
    rw [state.dependencies.composePrepared_eq generated valid]
    exact state.dependencies.compose_coherent state.denote
      (PreparedAtom.eraseSubst generated) coherent.dependencies_eq
  · exact coherent.recent_valid

theorem foldl_dependencyClosureStep_refines (names : List String)
    (graph : DependencyGraph) (denotation : Subst)
    (coherent : graph.Coherent denotation) (state : DependencyClosure) :
    let runtime := names.foldl graph.closureStep state
    let reference := names.foldl
      (fun current name =>
        match (PLeaTTa.substIndex denotation)[name]? with
        | some value => PLeaTTa.addFreshAtomVars current value
        | none => current)
      (state.live, state.frontier)
    runtime.live = reference.1 ∧ runtime.frontier = reference.2 := by
  induction names generalizing state with
  | nil => simp
  | cons name rest ih =>
      have hforward := coherent.forward_eq name
      cases hlookup : Metta.Subst.lookup denotation name with
      | none =>
          rw [hlookup] at hforward
          simp only [Option.map_none] at hforward
          simpa [DependencyGraph.closureStep, hforward,
            PLeaTTa.substIndex_getElem?, hlookup] using ih state
      | some value =>
          rw [hlookup] at hforward
          simp only [Option.map_some] at hforward
          let next := addFreshNames (state.live, state.frontier) value.vars
          have tail := ih
            ({ live := next.1, frontier := next.2 } : DependencyClosure)
          have hnext : addFreshNames (state.live, state.frontier) value.vars =
              PLeaTTa.addFreshAtomVars (state.live, state.frontier) value :=
            (addFreshNames_atom_vars
              (state.live, state.frontier) value).trans
              (addFreshAtomVars_eq_reference
                (state.live, state.frontier) value)
          simpa [DependencyGraph.closureStep, hforward,
            PLeaTTa.substIndex_getElem?, hlookup, next, hnext, Prod.eta]
            using tail

theorem DependencyGraph.close_refines (graph : DependencyGraph)
    (denotation : Subst) (coherent : graph.Coherent denotation)
    (fuel : Nat) (state : DependencyClosure) :
    let runtime := graph.close fuel state
    runtime.live = PLeaTTa.closeSubstVars (PLeaTTa.substIndex denotation)
      fuel state.live state.frontier := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [DependencyGraph.close, PLeaTTa.closeSubstVars]
      by_cases hempty : (state.frontier.size == 0) = true
      · simp [hempty]
      · simp only [hempty]
        let empty : VarSet :=
          Std.HashSet.emptyWithCapacity state.frontier.size
        let runtimeSeed : DependencyClosure :=
          { state with frontier := empty }
        let runtimeNext := state.frontier.toList.foldl graph.closureStep
          runtimeSeed
        let referenceNext := state.frontier.toList.foldl
          (fun current name =>
            match (PLeaTTa.substIndex denotation)[name]? with
            | some value => PLeaTTa.addFreshAtomVars current value
            | none => current)
          (state.live, empty)
        have hfold := foldl_dependencyClosureStep_refines
          state.frontier.toList graph denotation coherent runtimeSeed
        change runtimeNext.live = referenceNext.1 ∧
          runtimeNext.frontier = referenceNext.2 at hfold
        have tail := ih runtimeNext
        change (graph.close fuel runtimeNext).live =
          PLeaTTa.closeSubstVars (PLeaTTa.substIndex denotation) fuel
            referenceNext.1 referenceNext.2
        simpa [hfold.1, hfold.2] using tail

theorem foldl_closureStep_refines (names : List String)
    (state : ClosureState) (denotation : Subst)
    (coherent : state.subst.Coherent)
    (hdenote : state.subst.denote = denotation) :
    let runtime := names.foldl closureStep state
    let reference := names.foldl
      (fun current name =>
        match (PLeaTTa.substIndex denotation)[name]? with
        | some value => PLeaTTa.addFreshAtomVars current value
        | none => current)
      (state.live, state.frontier)
    runtime.subst.Coherent ∧ runtime.subst.denote = denotation ∧
      runtime.live = reference.1 ∧ runtime.frontier = reference.2 := by
  induction names generalizing state with
  | nil => simp [coherent, hdenote]
  | cons name rest ih =>
      have hfst := Scoped.lookup_fst_eq_reference state.subst name coherent
      have hsnd := Scoped.lookup_snd_coherent state.subst name coherent
      have hlookupDenote := Scoped.lookup_snd_denote state.subst name
      cases hlookup : state.subst.lookup name with
      | mk result next =>
          simp only [hlookup] at hfst hsnd hlookupDenote
          cases result with
          | none =>
              have href : Metta.Subst.lookup denotation name = none := by
                rw [← hdenote]
                exact hfst.symm
              have htail := ih
                ({ state with subst := next } : ClosureState)
                hsnd (hlookupDenote.trans hdenote)
              simpa [closureStep, hlookup, PLeaTTa.substIndex_getElem?,
                href] using htail
          | some value =>
              have href : Metta.Subst.lookup denotation name = some value := by
                rw [← hdenote]
                exact hfst.symm
              have htail := ih
                { subst := next
                  live := (addFreshAtomVars
                    (state.live, state.frontier) value).1
                  frontier := (addFreshAtomVars
                    (state.live, state.frontier) value).2 }
                hsnd (hlookupDenote.trans hdenote)
              simpa [closureStep, hlookup, PLeaTTa.substIndex_getElem?, href,
                addFreshAtomVars_eq_reference] using htail

theorem closeScoped_refines (fuel : Nat) (state : ClosureState)
    (denotation : Subst) (coherent : state.subst.Coherent)
    (hdenote : state.subst.denote = denotation) :
    let runtime := closeScoped fuel state
    runtime.subst.Coherent ∧ runtime.subst.denote = denotation ∧
      runtime.live = PLeaTTa.closeSubstVars
        (PLeaTTa.substIndex denotation) fuel state.live state.frontier := by
  induction fuel generalizing state with
  | zero => simp [closeScoped, PLeaTTa.closeSubstVars, coherent, hdenote]
  | succ fuel ih =>
      simp only [closeScoped, PLeaTTa.closeSubstVars]
      by_cases hempty : (state.frontier.size == 0) = true
      · simp only [hempty, if_true]
        exact ⟨coherent, hdenote, True.intro⟩
      · simp only [hempty]
        let empty : VarSet :=
          Std.HashSet.emptyWithCapacity state.frontier.size
        let runtimeSeed : ClosureState :=
          { state with frontier := empty }
        let runtimeNext := state.frontier.toList.foldl closureStep runtimeSeed
        let referenceNext := state.frontier.toList.foldl
          (fun current name =>
            match (PLeaTTa.substIndex denotation)[name]? with
            | some value => PLeaTTa.addFreshAtomVars current value
            | none => current)
          (state.live, empty)
        have hfold := foldl_closureStep_refines state.frontier.toList
          runtimeSeed denotation coherent hdenote
        change runtimeNext.subst.Coherent ∧
          runtimeNext.subst.denote = denotation ∧
          runtimeNext.live = referenceNext.1 ∧
          runtimeNext.frontier = referenceNext.2 at hfold
        have htail := ih runtimeNext hfold.1 hfold.2.1
        change
          (closeScoped fuel runtimeNext).subst.Coherent ∧
          (closeScoped fuel runtimeNext).subst.denote = denotation ∧
          (closeScoped fuel runtimeNext).live =
            PLeaTTa.closeSubstVars (PLeaTTa.substIndex denotation) fuel
              referenceNext.1 referenceNext.2
        simpa [hfold.2.2.1, hfold.2.2.2] using htail

theorem Scoped.filterActive_equiv_activeOfList (state : Scoped)
    (live : VarSet) (coherent : state.Coherent) :
    Std.HashSet.Equiv (state.active.filter live.contains)
      (activeOfList
        (PLeaTTa.filterLiveSubst live
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote)) := by
  rw [Std.HashSet.equiv_iff_forall_mem_iff]
  intro name
  rw [Std.HashSet.mem_iff_contains, varSet_contains_filter,
    coherent.domain_eq, Std.HashSet.mem_iff_contains,
    activeOfList_contains, PLeaTTa.filterLiveSubst_lookup_empty]
  cases live.contains name <;>
    cases Metta.Subst.lookup state.denote name <;> rfl

theorem Scoped.filterActive_size_eq_reference_length (state : Scoped)
    (live : VarSet) (coherent : state.Coherent) :
    (state.active.filter live.contains).size =
      (PLeaTTa.filterLiveSubst live
        (Std.HashSet.emptyWithCapacity state.denote.length)
        state.denote).length := by
  let filtered := PLeaTTa.filterLiveSubst live
    (Std.HashSet.emptyWithCapacity state.denote.length) state.denote
  calc
    (state.active.filter live.contains).size =
        (activeOfList filtered).size :=
      Std.HashSet.Equiv.size_eq
        (state.filterActive_equiv_activeOfList live coherent)
    _ = filtered.length := activeOfList_size_eq_length_of_nodup filtered
      (PLeaTTa.filterLiveSubst_keys_nodup live
        (Std.HashSet.emptyWithCapacity state.denote.length) state.denote)

theorem Scoped.mem_bindingsFor_iff (state : Scoped) (active : VarSet)
    (name : String) (value : Atom) :
    (name, value) ∈ state.bindingsFor active ↔
      name ∈ active ∧ state.peek name = some value := by
  simp [Scoped.bindingsFor, List.mem_filterMap]

private theorem subst_mem_iff_lookup_of_keys_nodup (entries : Subst)
    (name : String) (value : Atom)
    (hnodup : (entries.map Prod.fst).Nodup) :
    (name, value) ∈ entries ↔
      Metta.Subst.lookup entries name = some value := by
  induction entries with
  | nil => simp [Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, target⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnotmem, hrest⟩
      by_cases hkey : name = key
      · subst key
        simp only [List.mem_cons, Prod.mk.injEq, true_and,
          Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq]
        constructor
        · intro member
          rcases member with equality | member
          · exact equality.symm
          · exact False.elim (hnotmem (List.mem_map_of_mem member))
        · intro equality
          exact Or.inl equality.symm
      · simp [Metta.Subst.lookup, hkey, ih hrest]

theorem DependencyGraph.mem_namesForList_iff (graph : DependencyGraph)
    (sources : List String) (name : String) :
    name ∈ graph.namesForList sources ↔
      ∃ source ∈ sources,
        name = source ∨ name ∈ graph.forward[source]?.getD [] := by
  induction sources with
  | nil => simp [DependencyGraph.namesForList]
  | cons source rest ih =>
      simp [DependencyGraph.namesForList, ih, List.mem_append, or_assoc]

theorem DependencyGraph.mem_namesFor_iff (graph : DependencyGraph)
    (retained : VarSet) (name : String) :
    name ∈ graph.namesFor retained ↔
      ∃ source, source ∈ retained ∧
        (name = source ∨ name ∈ graph.forward[source]?.getD []) := by
  unfold DependencyGraph.namesFor
  rw [graph.mem_namesForList_iff retained.toList name]
  constructor
  · rintro ⟨source, member, occurrence⟩
    exact ⟨source, Std.HashSet.mem_of_mem_toList member, occurrence⟩
  · rintro ⟨source, member, occurrence⟩
    exact ⟨source, Std.HashSet.mem_toList.mpr member, occurrence⟩

theorem DependencyGraph.freshFor_equivalent (graph : DependencyGraph)
    (retained : VarSet) (entries : Subst)
    (domain : ∀ source,
      retained.contains source =
        (Metta.Subst.lookup entries source).isSome)
    (forward : ∀ source, retained.contains source = true →
      graph.forward[source]? =
        (Metta.Subst.lookup entries source).map Atom.vars)
    (nodup : (entries.map Prod.fst).Nodup) :
    (graph.freshFor retained).Equivalent (FreshSummary.ofSubst entries) := by
  unfold DependencyGraph.freshFor FreshSummary.ofSubst
  apply FreshSummary.ofNames_equivalent_of_mem_iff
  intro name
  rw [graph.mem_namesFor_iff retained name, mem_bindingNames_iff]
  constructor
  · rintro ⟨source, member, occurrence⟩
    have contains : retained.contains source = true :=
      Std.HashSet.mem_iff_contains.mp member
    cases hlookup : Metta.Subst.lookup entries source with
    | none =>
        rw [domain source, hlookup] at contains
        contradiction
    | some value =>
        have binding : (source, value) ∈ entries :=
          (subst_mem_iff_lookup_of_keys_nodup entries source value nodup).2
            hlookup
        rcases occurrence with occurrence | occurrence
        · exact ⟨source, value, binding, Or.inl occurrence⟩
        · have hforward := forward source contains
          rw [hlookup] at hforward
          simp only [Option.map_some] at hforward
          rw [hforward] at occurrence
          exact ⟨source, value, binding, Or.inr occurrence⟩
  · rintro ⟨source, value, binding, occurrence⟩
    have hlookup : Metta.Subst.lookup entries source = some value :=
      (subst_mem_iff_lookup_of_keys_nodup entries source value nodup).1
        binding
    have contains : retained.contains source = true := by
      rw [domain source, hlookup]
      rfl
    have member : source ∈ retained :=
      Std.HashSet.mem_iff_contains.mpr contains
    refine ⟨source, member, ?_⟩
    rcases occurrence with rfl | occurrence
    · exact Or.inl rfl
    · apply Or.inr
      have hforward := forward source contains
      rw [hlookup] at hforward
      simp only [Option.map_some] at hforward
      rw [hforward]
      exact occurrence

/-- Enumerating the active bindings from a coherent persistent map produces
the same freshness facts as an extensionally equal, duplicate-free list
substitution. This permits trimming to rebuild only the compact summary. -/
theorem Scoped.freshFor_equivalent (state : Scoped) (active : VarSet)
    (entries : Subst)
    (hdomain : ∀ name,
      active.contains name = (Metta.Subst.lookup entries name).isSome)
    (hpeek : ∀ name, active.contains name = true →
      state.peek name = Metta.Subst.lookup entries name)
    (hnodup : (entries.map Prod.fst).Nodup) :
    (state.freshFor active).Equivalent (FreshSummary.ofSubst entries) := by
  have hbindings : ∀ name value,
      (name, value) ∈ state.bindingsFor active ↔
        (name, value) ∈ entries := by
    intro name value
    rw [state.mem_bindingsFor_iff active name value,
      subst_mem_iff_lookup_of_keys_nodup entries name value hnodup]
    constructor
    · rintro ⟨member, stateLookup⟩
      have contains : active.contains name = true :=
        Std.HashSet.mem_iff_contains.mp member
      rw [hpeek name contains] at stateLookup
      exact stateLookup
    · intro referenceLookup
      have contains : active.contains name = true := by
        rw [hdomain name, referenceLookup]
        rfl
      exact ⟨Std.HashSet.mem_iff_contains.mpr contains, by
        rw [hpeek name contains]
        exact referenceLookup⟩
  unfold Scoped.freshFor FreshSummary.ofSubst
  apply FreshSummary.ofNames_equivalent_of_mem_iff
  intro name
  rw [mem_bindingNames_iff, mem_bindingNames_iff]
  constructor
  · rintro ⟨key, value, member, occurrence⟩
    exact ⟨key, value, (hbindings key value).1 member, occurrence⟩
  · rintro ⟨key, value, member, occurrence⟩
    exact ⟨key, value, (hbindings key value).2 member, occurrence⟩

/-- The executable identity guard is sufficient for the exact list trim to
be a no-op.  The proof uses the existing active-domain invariant and the
reference filter's length characterization; no observational weakening is
involved. -/
theorem Scoped.trimIsIdentity_sound (state : Scoped) (roots : VarSet)
    (coherent : state.Coherent)
    (identity : state.trimIsIdentity roots = true) :
    PLeaTTa.trimSubst state.denote roots = state.denote := by
  have parts : state.active.size = state.memo.depth ∧
      state.active.toList.all roots.contains = true := by
    simpa [Scoped.trimIsIdentity, Bool.and_eq_true] using identity
  let live := PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
    (state.denote.length + 1) roots roots
  have activeLive : ∀ name, state.active.contains name = true →
      live.contains name = true := by
    intro name active
    have member : name ∈ state.active :=
      Std.HashSet.mem_iff_contains.mpr active
    have listed : name ∈ state.active.toList :=
      Std.HashSet.mem_toList.mpr member
    have root : roots.contains name = true :=
      (List.all_eq_true.mp parts.2) name listed
    exact PLeaTTa.closeSubstVars_preserves_contains
      (PLeaTTa.substIndex state.denote) (state.denote.length + 1)
      roots roots name root
  have filteredEquiv : Std.HashSet.Equiv
      (state.active.filter live.contains) state.active := by
    rw [Std.HashSet.equiv_iff_forall_mem_iff]
    intro name
    rw [Std.HashSet.mem_iff_contains, varSet_contains_filter,
      Std.HashSet.mem_iff_contains]
    cases active : state.active.contains name with
    | false => simp
    | true => simp [activeLive name active]
  have referenceSize :=
    state.filterActive_size_eq_reference_length live coherent
  have filteredSize :
      (state.active.filter live.contains).size = state.active.size :=
    Std.HashSet.Equiv.size_eq filteredEquiv
  have referenceLength :
      (PLeaTTa.filterLiveSubst live
        (Std.HashSet.emptyWithCapacity state.denote.length)
        state.denote).length = state.denote.length := by
    calc
      _ = (state.active.filter live.contains).size := referenceSize.symm
      _ = state.active.size := filteredSize
      _ = state.memo.depth := parts.1
      _ = state.denote.length := coherent.depth_eq
  unfold PLeaTTa.trimSubst
  change PLeaTTa.filterLiveSubst live
      (Std.HashSet.emptyWithCapacity state.denote.length) state.denote =
    state.denote
  exact PLeaTTa.filterLiveSubst_eq_self_of_length_eq live
    (Std.HashSet.emptyWithCapacity state.denote.length) state.denote
    referenceLength

/-- Logical liveness trimming preserves the scoped persistent invariant when
the supplied denotation transformer is the list reference trim. -/
theorem Scoped.trimWithSlow_coherent (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) (coherent : state.Coherent)
    (hreference :
      referenceTrim state.denote =
        PLeaTTa.filterLiveSubst
          (PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
            (state.memo.depth + 1) roots roots)
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote) :
    (state.trimWithSlow roots referenceTrim).Coherent := by
  let seed : ClosureState :=
    { subst := state, live := roots, frontier := roots }
  let closed := closeScoped (state.memo.depth + 1) seed
  let retained := closed.subst.active.filter closed.live.contains
  have hclosed := closeScoped_refines (state.memo.depth + 1) seed
    state.denote coherent rfl
  have hclosedCoherent : closed.subst.Coherent := by
    simpa [closed] using hclosed.1
  have hclosedDenote : closed.subst.denote = state.denote := by
    simpa [closed] using hclosed.2.1
  have hclosedLive : closed.live =
      PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
        (state.memo.depth + 1) roots roots := by
    simpa [closed, seed] using hclosed.2.2
  have hreferenceClosed : referenceTrim state.denote =
      PLeaTTa.filterLiveSubst closed.live
        (Std.HashSet.emptyWithCapacity state.denote.length)
        state.denote := by
    rw [hclosedLive]
    exact hreference
  have hsize : retained.size =
      (referenceTrim state.denote).length := by
    have hrefSize := closed.subst.filterActive_size_eq_reference_length
      closed.live hclosedCoherent
    change retained.size = _ at hrefSize
    rw [hclosedDenote] at hrefSize
    rw [hreferenceClosed]
    exact hrefSize
  have hdomain : ∀ name,
      retained.contains name =
        (Metta.Subst.lookup (referenceTrim state.denote) name).isSome := by
    intro name
    rw [hreferenceClosed, varSet_contains_filter,
      hclosedCoherent.domain_eq, hclosedDenote,
      PLeaTTa.filterLiveSubst_lookup_empty]
    cases closed.live.contains name <;>
      cases Metta.Subst.lookup state.denote name <;> rfl
  have hretainedPeek : ∀ name, retained.contains name = true →
      closed.subst.peek name =
        Metta.Subst.lookup (referenceTrim state.denote) name := by
    intro name hretained
    have hfilter := varSet_contains_filter
      closed.subst.active closed.live.contains name
    have hparts : closed.subst.active.contains name = true ∧
        closed.live.contains name = true := by
      simpa [Bool.and_eq_true] using hfilter.symm.trans hretained
    have hpeek := hclosedCoherent.peek_eq name
    unfold Scoped.peek at hpeek
    rw [hparts.1] at hpeek
    simp only [if_true] at hpeek
    rw [hclosedDenote] at hpeek
    have hfiltered := PLeaTTa.filterLiveSubst_lookup_empty
      closed.live state.denote name
    rw [hparts.2] at hfiltered
    simp only [if_true] at hfiltered
    unfold Scoped.peek
    rw [hparts.1]
    simp only [if_true]
    rw [hreferenceClosed]
    exact hpeek.trans hfiltered.symm
  have hreferenceNodup :
      ((referenceTrim state.denote).map Prod.fst).Nodup := by
    rw [hreferenceClosed]
    exact PLeaTTa.filterLiveSubst_keys_nodup closed.live
      (Std.HashSet.emptyWithCapacity state.denote.length) state.denote
  have hreferenceEqState
      (unchanged : (retained.size == closed.subst.memo.depth) = true) :
      referenceTrim state.denote = state.denote := by
    have retainedEqDepth : retained.size = closed.subst.memo.depth := by
      simpa using unchanged
    rw [hreferenceClosed]
    apply PLeaTTa.filterLiveSubst_eq_self_of_length_eq
    calc
      (PLeaTTa.filterLiveSubst closed.live
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote).length =
          (referenceTrim state.denote).length := by
            rw [hreferenceClosed]
      _ = retained.size := hsize.symm
      _ = closed.subst.memo.depth := retainedEqDepth
      _ = closed.subst.denote.length := hclosedCoherent.depth_eq
      _ = state.denote.length := congrArg List.length hclosedDenote
  change
    ({ memo :=
        { closed.subst.memo with
          semantic := Thunk.mk fun _ => referenceTrim state.denote
          depth := retained.size
          entries := retainMemoEntries closed.subst.memo.entries
            closed.subst.active retained }
       active := retained
       visible := closed.live
       dependencies := closed.subst.dependencies.retainSources
         closed.subst.active retained
       recent := closed.subst.recent
       closedRoots := state.closedRoots
       closedPrepared := state.closedPrepared } : Scoped).Coherent
  constructor
  · exact hclosedCoherent.version_eq
  · exact hsize
  · intro name entry hentry
    apply hclosedCoherent.stamped name entry
    exact retainMemoEntries_getElem?_some closed.subst.memo.entries
      closed.subst.active retained name entry hentry
  · exact hdomain
  · intro name
    cases hretained : retained.contains name with
    | false =>
        have hdomainName := hdomain name
        rw [hretained] at hdomainName
        unfold Scoped.peek
        rw [hretained]
        cases hlookup : Metta.Subst.lookup
            (referenceTrim state.denote) name with
        | none =>
            simp only [Bool.false_eq_true, if_false]
            change none = Metta.Subst.lookup
              (referenceTrim state.denote) name
            exact hlookup.symm
        | some value => simp [hlookup] at hdomainName
    | true =>
        have hfilter := varSet_contains_filter
          closed.subst.active closed.live.contains name
        have hparts : closed.subst.active.contains name = true ∧
            closed.live.contains name = true := by
          simpa [Bool.and_eq_true] using hfilter.symm.trans hretained
        have hpeek := hclosedCoherent.peek_eq name
        unfold Scoped.peek at hpeek
        rw [hparts.1] at hpeek
        simp only [if_true] at hpeek
        rw [hclosedDenote] at hpeek
        have hfiltered := PLeaTTa.filterLiveSubst_lookup_empty
          closed.live state.denote name
        rw [hparts.2] at hfiltered
        simp only [if_true] at hfiltered
        unfold Scoped.peek
        rw [hretained]
        simp only [if_true]
        unfold Memo.peek
        rw [retainMemoEntries_getElem?_of_retained
          closed.subst.memo.entries closed.subst.active retained name
          hretained]
        change _ = Metta.Subst.lookup (referenceTrim state.denote) name
        have hretainedResult := hretainedPeek name hretained
        unfold Scoped.peek at hretainedResult
        rw [hparts.1] at hretainedResult
        unfold Memo.peek at hretainedResult
        simpa using hretainedResult
  · change (closed.subst.dependencies.retainSources
        closed.subst.active retained).Coherent
      (referenceTrim state.denote)
    have dependencies :=
      closed.subst.dependencies.retainSources_coherent_filter
        closed.subst.denote closed.subst.active closed.live
        hclosedCoherent.dependencies_eq hclosedCoherent.domain_eq
    rw [hclosedDenote] at dependencies
    simpa [retained, hreferenceClosed] using dependencies
  · exact hclosedCoherent.recent_valid

/-- The dependency graph computes the same liveness closure and retained
substitution as the list reference implementation. The executable path may
therefore avoid target reconstruction and cache refreshes without weakening
the scoped invariant. -/
theorem Scoped.trimWithGraph_coherent (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) (coherent : state.Coherent)
    (hreference :
      referenceTrim state.denote =
        PLeaTTa.filterLiveSubst
          (PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
            (state.memo.depth + 1) roots roots)
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote) :
    (state.trimWithGraph roots referenceTrim).Coherent := by
  let seed : DependencyClosure :=
    { live := roots, frontier := roots }
  let closed := state.dependencies.close (state.memo.depth + 1) seed
  let retained := state.active.filter closed.live.contains
  have hclosed := state.dependencies.close_refines state.denote
    coherent.dependencies_eq (state.memo.depth + 1) seed
  have hclosedLive : closed.live =
      PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
        (state.memo.depth + 1) roots roots := by
    simpa [closed, seed] using hclosed
  have hreferenceClosed : referenceTrim state.denote =
      PLeaTTa.filterLiveSubst closed.live
        (Std.HashSet.emptyWithCapacity state.denote.length)
        state.denote := by
    rw [hclosedLive]
    exact hreference
  have hsize : retained.size =
      (referenceTrim state.denote).length := by
    have hrefSize := state.filterActive_size_eq_reference_length
      closed.live coherent
    change retained.size = _ at hrefSize
    rw [hreferenceClosed]
    exact hrefSize
  have hdomain : ∀ name,
      retained.contains name =
        (Metta.Subst.lookup (referenceTrim state.denote) name).isSome := by
    intro name
    rw [hreferenceClosed, varSet_contains_filter,
      coherent.domain_eq, PLeaTTa.filterLiveSubst_lookup_empty]
    cases closed.live.contains name <;>
      cases Metta.Subst.lookup state.denote name <;> rfl
  have hretainedParts : ∀ name, retained.contains name = true →
      state.active.contains name = true ∧ closed.live.contains name = true := by
    intro name hretained
    have hfilter := varSet_contains_filter
      state.active closed.live.contains name
    simpa [Bool.and_eq_true] using hfilter.symm.trans hretained
  have hretainedPeek : ∀ name, retained.contains name = true →
      state.peek name =
        Metta.Subst.lookup (referenceTrim state.denote) name := by
    intro name hretained
    have hparts := hretainedParts name hretained
    rw [hreferenceClosed,
      PLeaTTa.filterLiveSubst_lookup_empty, hparts.2]
    simp only [if_true]
    exact coherent.peek_eq name
  have hretainedForward : ∀ name, retained.contains name = true →
      state.dependencies.forward[name]? =
        (Metta.Subst.lookup (referenceTrim state.denote) name).map Atom.vars := by
    intro name hretained
    have hparts := hretainedParts name hretained
    rw [hreferenceClosed,
      PLeaTTa.filterLiveSubst_lookup_empty, hparts.2]
    simp only [if_true]
    exact coherent.dependencies_eq.forward_eq name
  have hreferenceNodup :
      ((referenceTrim state.denote).map Prod.fst).Nodup := by
    rw [hreferenceClosed]
    exact PLeaTTa.filterLiveSubst_keys_nodup closed.live
      (Std.HashSet.emptyWithCapacity state.denote.length) state.denote
  have hreferenceEqState
      (unchanged : (retained.size == state.memo.depth) = true) :
      referenceTrim state.denote = state.denote := by
    have retainedEqDepth : retained.size = state.memo.depth := by
      simpa using unchanged
    rw [hreferenceClosed]
    apply PLeaTTa.filterLiveSubst_eq_self_of_length_eq
    calc
      (PLeaTTa.filterLiveSubst closed.live
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote).length =
          (referenceTrim state.denote).length := by
            rw [hreferenceClosed]
      _ = retained.size := hsize.symm
      _ = state.memo.depth := retainedEqDepth
      _ = state.denote.length := coherent.depth_eq
  change
    ({ memo :=
        { state.memo with
          semantic := Thunk.mk fun _ => referenceTrim state.denote
          depth := retained.size
          entries := retainMemoEntries state.memo.entries
            state.active retained }
       active := retained
       visible := closed.live
       dependencies := state.dependencies.retainSources
         state.active retained
       recent := state.recent
       closedRoots := state.closedRoots
       closedPrepared := state.closedPrepared } : Scoped).Coherent
  constructor
  · exact coherent.version_eq
  · exact hsize
  · intro name entry hentry
    apply coherent.stamped name entry
    exact retainMemoEntries_getElem?_some state.memo.entries state.active
      retained name entry hentry
  · exact hdomain
  · intro name
    cases hretained : retained.contains name with
    | false =>
        have hdomainName := hdomain name
        rw [hretained] at hdomainName
        unfold Scoped.peek
        rw [hretained]
        cases hlookup : Metta.Subst.lookup
            (referenceTrim state.denote) name with
        | none =>
            simp only [Bool.false_eq_true, if_false]
            change none = Metta.Subst.lookup
              (referenceTrim state.denote) name
            exact hlookup.symm
        | some value => simp [hlookup] at hdomainName
    | true =>
        have hparts := hretainedParts name hretained
        unfold Scoped.peek
        rw [hretained]
        simp only [if_true]
        unfold Memo.peek
        rw [retainMemoEntries_getElem?_of_retained state.memo.entries
          state.active retained name hretained]
        change _ = Metta.Subst.lookup (referenceTrim state.denote) name
        have hpeek := hretainedPeek name hretained
        unfold Scoped.peek at hpeek
        rw [hparts.1] at hpeek
        unfold Memo.peek at hpeek
        simpa using hpeek
  · change (state.dependencies.retainSources
        state.active retained).Coherent
      (referenceTrim state.denote)
    have dependencies :=
      state.dependencies.retainSources_coherent_filter
        state.denote state.active closed.live coherent.dependencies_eq
        coherent.domain_eq
    simpa [retained, hreferenceClosed] using dependencies
  · exact coherent.recent_valid

theorem Scoped.trimWith_coherent (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) (coherent : state.Coherent)
    (hreference :
      referenceTrim state.denote =
        PLeaTTa.filterLiveSubst
          (PLeaTTa.closeSubstVars (PLeaTTa.substIndex state.denote)
            (state.memo.depth + 1) roots roots)
          (Std.HashSet.emptyWithCapacity state.denote.length)
          state.denote) :
    (state.trimWith roots referenceTrim).Coherent := by
  unfold Scoped.trimWith
  split
  next identity =>
    have trimEq := state.trimIsIdentity_sound roots coherent identity
    have referenceEq : referenceTrim state.denote = state.denote := by
      calc
        referenceTrim state.denote =
            PLeaTTa.trimSubst state.denote roots := by
          simpa [PLeaTTa.trimSubst, coherent.depth_eq] using hreference
        _ = state.denote := trimEq
    change
      ({ state with
        memo :=
          { state.memo with
            semantic := Thunk.mk fun _ => referenceTrim state.denote } } :
        Scoped).Coherent
    constructor
    · exact coherent.version_eq
    · change state.memo.depth = (referenceTrim state.denote).length
      simpa [referenceEq] using coherent.depth_eq
    · exact coherent.stamped
    · intro name
      change state.active.contains name =
        (Metta.Subst.lookup (referenceTrim state.denote) name).isSome
      rw [referenceEq]
      exact coherent.domain_eq name
    · intro name
      change state.peek name =
        Metta.Subst.lookup (referenceTrim state.denote) name
      rw [referenceEq]
      exact coherent.peek_eq name
    · change state.dependencies.Coherent (referenceTrim state.denote)
      rw [referenceEq]
      exact coherent.dependencies_eq
    · exact coherent.recent_valid
  next notIdentity =>
    exact state.trimWithGraph_coherent roots referenceTrim coherent hreference

@[simp] theorem Scoped.denote_trimFor (state : Scoped)
    (goals : List PLeaTTa.Goal) (qterm : Atom) :
    (state.trimFor goals qterm).denote =
      PLeaTTa.trimFor goals qterm state.denote := by
  unfold Scoped.trimFor Scoped.trimWith
  split <;> rfl

theorem Scoped.trimFor_coherent (state : Scoped)
    (goals : List PLeaTTa.Goal) (qterm : Atom)
    (coherent : state.Coherent) :
    (state.trimFor goals qterm).Coherent := by
  unfold Scoped.trimFor
  apply state.trimWith_coherent (PLeaTTa.trimRoots goals qterm)
    (PLeaTTa.trimFor goals qterm) coherent
  simp [PLeaTTa.trimFor, PLeaTTa.trimSubst, PLeaTTa.trimRoots,
    coherent.depth_eq]

end PLeaTTa.PersistentSubst
