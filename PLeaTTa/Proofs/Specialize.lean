-- SPDX-License-Identifier: Apache-2.0

/-
Proofs for the compiler-profile specialization pass.  The base theorem is
developed before the stateful specialization lifecycle: it relates the
generic `callDyn` execution to the direct call emitted by the real IR rewrite.
-/
import PLeaTTa.Specialize
import PLeaTTa.Semantics
import PLeaTTa.Proofs.Unification
import PLeaTTa.Proofs.Reachability

namespace PLeaTTa

open Metta (Atom Subst GroundingTable)

@[simp] theorem residualFreshName_length (length : Nat) :
    (residualFreshName length).length = length := by
  induction length with
  | zero => rfl
  | succ length ih =>
      simp only [residualFreshName, String.length_append, ih]
      change 1 + length = length + 1
      omega

private theorem foldl_max_ge_initial (lengths : List String)
    (initial : Nat) :
    initial ≤ lengths.foldl (fun current name => max current name.length)
      initial := by
  induction lengths generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left initial head.length)
        (ih (max initial head.length))

private theorem member_length_le_foldl_max (names : List String)
    (initial : Nat) (name : String) (hmem : name ∈ names) :
    name.length ≤
      names.foldl (fun current item => max current item.length) initial := by
  induction names generalizing initial with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst name
        exact Nat.le_trans (Nat.le_max_right initial head.length)
          (foldl_max_ge_initial tail (max initial head.length))
      · exact ih (max initial head.length) htail

/-- Appending the common resolution suffix preserves distinct clause-variable
    identities. -/
theorem resolution_suffix_injective (suffix : String) :
    Function.Injective (fun name : String => name ++ suffix) := by
  intro left right hequal
  exact (String.append_left_inj suffix).mp hequal

/-- The unconditional length-based fallback makes every copied variable longer
    than every occupied caller variable. -/
theorem resolutionLongSuffix_target_long (occupied : List String)
    (source caller : String) (hcaller : caller ∈ occupied) :
    caller.length < (source ++ resolutionLongSuffix occupied).length := by
  let maxLength := occupied.foldl
    (fun current name => max current name.length) 0
  have hle : caller.length ≤ maxLength :=
    member_length_le_foldl_max occupied 0 caller hcaller
  have htarget : maxLength <
      (source ++ resolutionLongSuffix occupied).length := by
    simp only [resolutionLongSuffix, String.length_append,
      residualFreshName_length]
    change maxLength < source.length + (1 + (maxLength + 1))
    omega
  exact Nat.lt_of_le_of_lt hle htarget

private theorem resolution_repr_digits (seed : Nat) :
    ∀ char ∈ (Nat.repr seed).toList, Char.isDigit char = true := by
  intro char member
  rw [Nat.toList_repr] at member
  exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) member

private theorem resolution_repr_reverse_digits (seed : Nat) :
    ∀ char ∈ (Nat.repr seed).toList.reverse,
      Char.isDigit char = true := by
  intro char member
  exact resolution_repr_digits seed char (by simpa using member)

/-- Consuming a reversed decimal prefix places its digits back in source
    order in the scanner accumulator. -/
private theorem terminalResolutionSeedRev_digits
    (digitsRev tail accumulator : List Char)
    (allDigits : ∀ char ∈ digitsRev, Char.isDigit char = true) :
    terminalResolutionSeedRev (digitsRev ++ tail) accumulator =
      terminalResolutionSeedRev tail (digitsRev.reverse ++ accumulator) := by
  induction digitsRev generalizing accumulator with
  | nil => rfl
  | cons char rest ih =>
      have hchar : Char.isDigit char = true := allDigits char (by simp)
      have hrest : ∀ next ∈ rest, Char.isDigit next = true := by
        intro next member
        exact allDigits next (List.mem_cons_of_mem char member)
      simp only [List.cons_append, terminalResolutionSeedRev, hchar, if_true]
      rw [ih (char :: accumulator) hrest]
      simp [List.reverse_cons, List.append_assoc]

/-- The terminal-token scanner is a left inverse of the actual compact name
    constructor, for every source-name prefix. -/
theorem terminalResolutionSeed?_append (stem : String) (seed : Nat) :
    terminalResolutionSeed? (stem ++ resolutionCompactSuffix seed) =
      some seed := by
  unfold terminalResolutionSeed? resolutionCompactSuffix
  simp only [String.toList_append, List.reverse_append]
  rw [show toString seed = Nat.repr seed from rfl]
  simp only [String.reduceToList, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [List.append_assoc]
  rw [terminalResolutionSeedRev_digits (Nat.repr seed).toList.reverse
    (['r', '#'] ++ stem.toList.reverse) []
    (resolution_repr_reverse_digits seed)]
  simp [terminalResolutionSeedRev]
  exact Nat.toNat?_repr seed

/-- If the compact token is a suffix of a name, the terminal scanner recovers
    exactly that token's seed. -/
theorem terminalResolutionSeed?_of_suffix (caller : String) (seed : Nat)
    (suffix : (resolutionCompactSuffix seed).toList.isSuffixOf
      caller.toList = true) :
    terminalResolutionSeed? caller = some seed := by
  rw [List.isSuffixOf_iff_suffix] at suffix
  rcases suffix with ⟨stem, hstem⟩
  have hcaller : caller =
      String.ofList stem ++ resolutionCompactSuffix seed := by
    apply String.toList_injective
    simp only [String.toList_append, String.toList_ofList]
    exact hstem.symm
  rw [hcaller]
  exact terminalResolutionSeed?_append (String.ofList stem) seed

/-- A counter at or above one name's high-water mark cannot be its terminal
    compact suffix. -/
theorem resolutionCompactSuffix_not_suffix_of_highWater (caller : String)
    (seed : Nat) (highWater : resolutionSeedHighWaterName caller ≤ seed) :
    (resolutionCompactSuffix seed).toList.isSuffixOf caller.toList = false := by
  apply Bool.eq_false_iff.mpr
  intro suffix
  have parsed := terminalResolutionSeed?_of_suffix caller seed suffix
  simp [resolutionSeedHighWaterName, parsed] at highWater

private theorem resolutionSeedHighWaterName_le_of_mem (names : List String)
    (name : String) (member : name ∈ names) :
    resolutionSeedHighWaterName name ≤ resolutionSeedHighWaterNames names := by
  induction names with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih tailMember) (Nat.le_max_right _ _)

/-- The load-bearing allocator lemma: once the global counter is at the
    source/host high-water mark, its compact suffix is fresh from every name
    in that surface without inspecting the surface again. -/
theorem resolutionCompactSuffix_fresh_of_highWater (names : List String)
    (seed : Nat) (highWater : resolutionSeedHighWaterNames names ≤ seed) :
    resolutionSuffixFresh names (resolutionCompactSuffix seed) = true := by
  unfold resolutionSuffixFresh
  rw [List.all_eq_true]
  intro caller member
  rw [Bool.not_eq_true']
  apply resolutionCompactSuffix_not_suffix_of_highWater caller seed
  exact Nat.le_trans
    (resolutionSeedHighWaterName_le_of_mem names caller member) highWater

/-- A counter seeded above the occupied terminal-token high-water mark
    produces a clause-copy suffix that cannot capture a live caller variable. -/
theorem resolutionFreshSuffix_target_ne (argsv : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest b qterm) ≤ seed)
    (source caller : String)
    (hcaller : caller ∈ resolutionOccupiedVars argsv res rest b qterm) :
    source ++ resolutionFreshSuffix argsv res rest b qterm seed ≠ caller := by
  let occupied := resolutionOccupiedVars argsv res rest b qterm
  have hcaller' : caller ∈ occupied := hcaller
  have hcallerFresh := (List.all_eq_true.mp
    (resolutionCompactSuffix_fresh_of_highWater occupied seed hhighWater))
    caller hcaller'
  intro hequal
  have hsuffix : (resolutionCompactSuffix seed).toList.isSuffixOf
      caller.toList = true := by
    rw [List.isSuffixOf_iff_suffix]
    rw [← hequal, resolutionFreshSuffix, String.toList_append]
    exact List.suffix_append source.toList
      (resolutionCompactSuffix seed).toList
  simp [hsuffix] at hcallerFresh

/-- Suffix renaming maps variable occurrences pointwise.  This is the
    structural bridge from the executable clause copier to its freshness
    argument; duplicates and sharing are preserved rather than quotiented. -/
theorem mem_renameAtomSuffix_vars (suffix : String) (atom : Atom)
    (target : String) :
    target ∈ (renameAtomSuffix suffix atom).vars ↔
      ∃ source, source ∈ atom.vars ∧ target = source ++ suffix := by
  induction atom with
  | sym name => simp [renameAtomSuffix, Atom.vars]
  | var name => simp [renameAtomSuffix, Atom.vars]
  | gnd ground => simp [renameAtomSuffix, Atom.vars]
  | expr atoms ih =>
      constructor
      · intro htarget
        simp only [renameAtomSuffix, Atom.vars, List.mem_flatten,
          List.mem_map] at htarget
        obtain ⟨variableList, ⟨renamedChild, hrenamedChild, rfl⟩,
          htarget⟩ := htarget
        obtain ⟨attachedChild, hattached, rfl⟩ := hrenamedChild
        rcases attachedChild with ⟨child, hchild⟩
        obtain ⟨source, hsource, rfl⟩ :=
          (ih child hchild).mp htarget
        refine ⟨source, ?_, rfl⟩
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hsource⟩
      · rintro ⟨source, hsource, rfl⟩
        simp only [Atom.vars, List.mem_flatten, List.mem_map] at hsource
        obtain ⟨variableList, ⟨child, hchild, rfl⟩, hsource⟩ := hsource
        simp only [renameAtomSuffix, Atom.vars, List.mem_flatten,
          List.mem_map]
        refine ⟨(renameAtomSuffix suffix child).vars, ?_, ?_⟩
        · refine ⟨renameAtomSuffix suffix child, ?_, rfl⟩
          exact ⟨⟨child, hchild⟩, by simp, rfl⟩
        · exact (ih child hchild).mpr
            ⟨source, hsource, rfl⟩

/-- Every query variable is part of the live set used to allocate a
    resolution suffix. -/
theorem qterm_var_mem_resolutionOccupiedVars (argsv : List Atom)
    (res : Atom) (rest : List Goal) (b : Subst) (qterm : Atom)
    (name : String) (hname : name ∈ qterm.vars) :
    name ∈ resolutionOccupiedVars argsv res rest b qterm := by
  simp [resolutionOccupiedVars, hname]

/-- Every variable still visible after deep caller substitution is included
    in the live set used to allocate the resolution suffix. -/
theorem subst_qterm_var_mem_resolutionOccupiedVars (argsv : List Atom)
    (res : Atom) (rest : List Goal) (b : Subst) (qterm : Atom)
    (name : String) (hname : name ∈ (subst b qterm).vars) :
    name ∈ resolutionOccupiedVars argsv res rest b qterm := by
  rcases subst_vars_origin b qterm name hname with hquery | hrange
  · exact qterm_var_mem_resolutionOccupiedVars argsv res rest b qterm
      name hquery
  · simp only [List.mem_flatMap] at hrange
    obtain ⟨entry, hentry, hvalue⟩ := hrange
    have hbinding : name ∈
        b.flatMap (fun item => item.1 :: item.2.vars) := by
      simp only [List.mem_flatMap]
      exact ⟨entry, hentry, by simp [hvalue]⟩
    simp [resolutionOccupiedVars, hbinding]

/-- No variable introduced by the actual clause freshener can be a caller
    query variable. -/
theorem resolutionFreshSuffix_target_not_mem_qterm (argsv : List Atom)
    (res : Atom) (rest : List Goal) (b : Subst) (qterm : Atom)
    (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest b qterm) ≤ seed)
    (source : String) :
    source ++ resolutionFreshSuffix argsv res rest b qterm seed ∉ qterm.vars := by
  intro hmem
  exact resolutionFreshSuffix_target_ne argsv res rest b qterm seed hhighWater
    source _
    (qterm_var_mem_resolutionOccupiedVars argsv res rest b qterm _ hmem) rfl

/-- Total name function induced by a finite residual-copy substitution and
    the actual per-resolution suffix.  On covered residuals the fallback is
    unreachable; keeping it total lets `FreshVariant` share one function
    across every occurrence. -/
def copiedResidualNameSuffix (copy : Subst) (suffix source : String) : String :=
  match Metta.Subst.lookup copy source with
  | some (Atom.var target) => target ++ suffix
  | _ => source ++ suffix

/-- Sequential guard invariant.  Caller/source residuals stay outside the
    runtime domain; each copied residual is either still unbound or is bound
    exactly to its source by an earlier guard. -/
def FreshResidualLookupState (fresh : String → String)
    (allowed : List String) (runtime : Subst) : Prop :=
  ∀ source, source ∈ allowed →
    Metta.Subst.lookup runtime source = none ∧
      (Metta.Subst.lookup runtime (fresh source) = none ∨
        Metta.Subst.lookup runtime (fresh source) = some (Atom.var source))

/-- General sequential invariant for nested/cross-argument residuals.  A
    copied residual is either not bound yet or already has exactly the
    current denotation of its source; the source itself may be bound. -/
def FreshResidualDenotationState (fresh : String → String)
    (allowed : List String) (runtime : Subst) : Prop :=
  ∀ source, source ∈ allowed →
    Metta.Subst.lookup runtime (fresh source) = none ∨
      subst runtime (Atom.var (fresh source)) =
        subst runtime (Atom.var source)

/-- Guard-run state relative to the immutable denotation established by the
    clause-head unifier.  Liveness may discard the original source variable;
    copied residuals therefore track the saved head-time value, not a later
    lookup of that source name. -/
def FreshResidualSnapshotState (fresh : String → String)
    (resolve : String → Atom) (allowed : List String)
    (runtime : Subst) : Prop :=
  ∀ source, source ∈ allowed →
    Metta.Subst.lookup runtime (fresh source) = none ∨
      subst runtime (Atom.var (fresh source)) = resolve source

theorem FreshResidualSnapshotState.mono
    {fresh : String → String} {resolve : String → Atom}
    {before after : List String} {runtime : Subst}
    (state : FreshResidualSnapshotState fresh resolve before runtime)
    (subset : ∀ source, source ∈ after → source ∈ before) :
    FreshResidualSnapshotState fresh resolve after runtime := by
  intro source hsource
  exact state source (subset source hsource)

/-- Liveness trimming can drop an unused copied residual or retain its exact
    denotation; either outcome preserves the head-time snapshot invariant. -/
theorem FreshResidualSnapshotState.trimFor
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String) (runtime : Subst) (goals : List Goal)
    (qterm : Atom) (topological : SubstTopological runtime)
    (state : FreshResidualSnapshotState fresh resolve allowed runtime) :
    FreshResidualSnapshotState fresh resolve allowed
      (PLeaTTa.trimFor goals qterm runtime) := by
  intro source hsourceAllowed
  cases htrimmed : Metta.Subst.lookup
      (PLeaTTa.trimFor goals qterm runtime) (fresh source) with
  | none => exact Or.inl rfl
  | some value =>
      right
      have hfreshPreserved := subst_trimFor_var_eq_of_lookup_some goals qterm
        runtime topological (fresh source) value htrimmed
      have hsemantic : subst runtime (Atom.var (fresh source)) =
          resolve source := by
        rcases state source hsourceAllowed with horiginalNone | hsemantic
        · exfalso
          have horiginal := trimFor_lookup_eq_original_of_some goals qterm
            runtime (fresh source) value htrimmed
          rw [horiginalNone] at horiginal
          contradiction
        · exact hsemantic
      exact hfreshPreserved.trans hsemantic

theorem FreshResidualDenotationState.mono
    {fresh : String → String} {before after : List String}
    {runtime : Subst}
    (state : FreshResidualDenotationState fresh before runtime)
    (subset : ∀ source, source ∈ after → source ∈ before) :
    FreshResidualDenotationState fresh after runtime := by
  intro source hsource
  exact state source (subset source hsource)

/-- Trimming preserves the semantic residual invariant whenever the active
    source denotations are preserved by the remaining guard continuation. -/
theorem FreshResidualDenotationState.trimFor
    (fresh : String → String) (allowed : List String)
    (runtime : Subst) (goals : List Goal) (qterm : Atom)
    (topological : SubstTopological runtime)
    (state : FreshResidualDenotationState fresh allowed runtime)
    (hsource : ∀ source, source ∈ allowed →
      subst (PLeaTTa.trimFor goals qterm runtime) (Atom.var source) =
        subst runtime (Atom.var source)) :
    FreshResidualDenotationState fresh allowed
      (PLeaTTa.trimFor goals qterm runtime) := by
  intro source hsourceAllowed
  cases htrimmed : Metta.Subst.lookup
      (PLeaTTa.trimFor goals qterm runtime) (fresh source) with
  | none => exact Or.inl rfl
  | some value =>
      right
      have hfreshPreserved := subst_trimFor_var_eq_of_lookup_some goals qterm
        runtime topological (fresh source) value htrimmed
      have hsemantic : subst runtime (Atom.var (fresh source)) =
          subst runtime (Atom.var source) := by
        rcases state source hsourceAllowed with horiginalNone | hsemantic
        · exfalso
          have horiginal := trimFor_lookup_eq_original_of_some goals qterm
            runtime (fresh source) value htrimmed
          rw [horiginalNone] at horiginal
          contradiction
        · exact hsemantic
      exact hfreshPreserved.trans
        (hsemantic.trans (hsource source hsourceAllowed).symm)

theorem FreshResidualLookupState.source_fixed {fresh : String → String}
    {allowed : List String} {runtime : Subst}
    (state : FreshResidualLookupState fresh allowed runtime)
    (source : String) (hsource : source ∈ allowed) :
    subst runtime (Atom.var source) = Atom.var source := by
  exact subst_var_of_lookup_none runtime source (state source hsource).1

theorem FreshResidualLookupState.fresh_state {fresh : String → String}
    {allowed : List String} {runtime : Subst}
    (state : FreshResidualLookupState fresh allowed runtime)
    (topological : SubstTopological runtime)
    (source : String) (hsource : source ∈ allowed) :
    subst runtime (Atom.var (fresh source)) = Atom.var (fresh source) ∨
      subst runtime (Atom.var (fresh source)) = Atom.var source := by
  rcases (state source hsource).2 with hnone | hbound
  · exact Or.inl (subst_var_of_lookup_none runtime (fresh source) hnone)
  · exact Or.inr ((topological.subst_var_of_lookup runtime (fresh source)
      (Atom.var source) hbound).trans (state.source_fixed source hsource))

/-- Composing one generated fresh-variant unifier preserves the sequential
    lookup invariant over the complete residual family. -/
theorem FreshResidualLookupState.compose_generated
    (fresh : String → String) (allowed current : List String)
    (base generated : Subst)
    (state : FreshResidualLookupState fresh allowed base)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ copied, copied ∈ allowed →
      ∀ source, source ∈ allowed → fresh copied ≠ source)
    (hcurrent : ∀ source, source ∈ current → source ∈ allowed)
    (hgenerated : FreshGenerated fresh current generated) :
    FreshResidualLookupState fresh allowed
      (Metta.Subst.compose generated base) := by
  intro source hsource
  have hbaseSource := (state source hsource).1
  have hgeneratedSource : Metta.Subst.lookup generated source = none := by
    apply hgenerated.lookup_none_of_forbidden
    intro copied hcopied
    exact hdisjoint copied (hcurrent copied hcopied) source hsource
  constructor
  · simp [lookup_compose, hbaseSource, hgeneratedSource]
  · rcases (state source hsource).2 with hbaseFresh | hbaseBound
    · rw [lookup_compose, hbaseFresh]
      cases hlookup : Metta.Subst.lookup generated (fresh source) with
      | none => exact Or.inl (by simp)
      | some value =>
          obtain ⟨origin, horigin, hname, hvalue⟩ :=
            FreshGenerated.lookup_shape fresh current generated hgenerated
              (fresh source) value hlookup
          have horiginAllowed := hcurrent origin horigin
          have hequal : source = origin :=
            hinjective source hsource origin horiginAllowed hname
          subst origin
          subst value
          exact Or.inr (by simp)
    · rw [lookup_compose, hbaseBound]
      have hgeneratedSourceNone :
          Metta.Subst.lookup generated source = none := hgeneratedSource
      simp [Metta.Subst.apply, hgeneratedSourceNone]

/-- Liveness trimming preserves the sequential residual invariant.  A live
    copied residual keeps its original source binding; a dead one simply
    returns to the invariant's unbound branch. -/
theorem FreshResidualLookupState.trimFor
    (fresh : String → String) (allowed : List String)
    (runtime : Subst) (goals : List Goal) (qterm : Atom)
    (state : FreshResidualLookupState fresh allowed runtime) :
    FreshResidualLookupState fresh allowed
      (PLeaTTa.trimFor goals qterm runtime) := by
  intro source hsource
  have hsourceNone := (state source hsource).1
  constructor
  · cases htrimmed : Metta.Subst.lookup
      (PLeaTTa.trimFor goals qterm runtime) source with
    | none => rfl
    | some value =>
        have horiginal := trimFor_lookup_eq_original_of_some goals qterm
          runtime source value htrimmed
        rw [hsourceNone] at horiginal
        contradiction
  · cases htrimmed : Metta.Subst.lookup
        (PLeaTTa.trimFor goals qterm runtime) (fresh source) with
    | none => exact Or.inl rfl
    | some value =>
        have horiginal := trimFor_lookup_eq_original_of_some goals qterm
          runtime (fresh source) value htrimmed
        rcases (state source hsource).2 with hfreshNone | hfreshBound
        · rw [hfreshNone] at horiginal
          contradiction
        · have hvalue : value = Atom.var source := by
            exact Option.some.inj (horiginal.symm.trans hfreshBound)
          subst value
          exact Or.inr rfl

/-- Fixed-copy view of any remaining suffix-renamed guard tail.  The copy
    map is computed once from `allBinding`, exactly as in the generated
    clause, while recursion consumes `remaining` in source order. -/
def specializationGuardBindingSuffix (clause : Clause)
    (allBinding : Subst) (suffix : String) (remaining : Subst) : Subst :=
  remaining.map (fun entry =>
    (entry.1 ++ suffix,
      renameAtomSuffix suffix
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) entry.2)))

@[simp] theorem specializationGuardBindingSuffix_nil (clause : Clause)
    (allBinding : Subst) (suffix : String) :
    specializationGuardBindingSuffix clause allBinding suffix [] = [] := rfl

@[simp] theorem specializationGuardBindingSuffix_cons (clause : Clause)
    (allBinding : Subst) (suffix name : String) (value : Atom)
    (tail : Subst) :
    specializationGuardBindingSuffix clause allBinding suffix
        ((name, value) :: tail) =
      (name ++ suffix,
        renameAtomSuffix suffix
          (Metta.Subst.apply
            (specializationCopySubst clause allBinding) value)) ::
        specializationGuardBindingSuffix clause allBinding suffix tail := rfl

/-- Literal post-head-narrowing interface for the selected source formals.
    This is deliberately propositional equality, not `Ground.equiv`. -/
def SourceBindingHeadState (suffix : String) (binding : Subst)
    (runtime : Subst) : Prop :=
  ∀ name value, (name, value) ∈ binding →
    subst runtime (Atom.var (name ++ suffix)) = value

/-- Raw head-unifier lookups retained for the selected source formals.  This
    stronger operational interface survives later guard composition and
    liveness trimming, and yields the dynamic denotation equation on demand. -/
def SourceBindingHeadLookupState (suffix : String) (binding : Subst)
    (runtime : Subst) : Prop :=
  ∀ name value, (name, value) ∈ binding →
    Metta.Subst.lookup runtime (name ++ suffix) = some value

/-- Raw head bindings after caller substitution.  The stored target is the
    immutable head-time denotation of the discovery value, not necessarily
    its original open syntax. -/
def SourceBindingHeadSnapshotLookupState (suffix : String) (origin : Subst)
    (binding : Subst) (runtime : Subst) : Prop :=
  ∀ name value, (name, value) ∈ binding →
    Metta.Subst.lookup runtime (name ++ suffix) =
      some (subst origin value)

private theorem map_eq_at_mem {f g : Atom → Atom} (atoms : List Atom)
    (hequal : atoms.map f = atoms.map g) (atom : Atom)
    (hmem : atom ∈ atoms) : f atom = g atom := by
  induction atoms with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at hequal
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hequal.1
      · exact ih hequal.2 hmem

/-- Equality of two deep substitutions on an atom projects to every variable
    occurrence in that atom. -/
theorem subst_var_eq_of_mem (left right : Subst) (atom : Atom)
    (name : String) (hmem : name ∈ atom.vars)
    (hequal : subst left atom = subst right atom) :
    subst left (Atom.var name) = subst right (Atom.var name) := by
  induction atom with
  | sym symbol => simp [Atom.vars] at hmem
  | var source =>
      simp only [Atom.vars, List.mem_singleton] at hmem
      subst source
      exact hequal
  | gnd ground => simp [Atom.vars] at hmem
  | expr atoms ih =>
      simp only [Atom.vars, List.mem_flatten, List.mem_map] at hmem
      obtain ⟨variableList, ⟨child, hchild, rfl⟩, hname⟩ := hmem
      simp only [subst_expr, Atom.expr.injEq] at hequal
      have hchildEqual : subst left child = subst right child :=
        map_eq_at_mem atoms hequal child hchild
      exact ih child hchild hname hchildEqual

private theorem atomEquiv_self_of_mem
    (atoms : List Atom) (atom : Atom) (hmem : atom ∈ atoms)
    (hreflexive : Metta.Atom.equivList atoms atoms = true) :
    Metta.Atom.equiv atom atom = true := by
  induction atoms with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [Metta.Atom.equivList, Bool.and_eq_true] at hreflexive
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hreflexive.1
      · exact ih hmem hreflexive.2

private theorem freshVariantList_map (fresh : String → String)
    (transform : Atom → Atom) (atoms : List Atom)
    (hvariants : ∀ atom, atom ∈ atoms →
      FreshVariant fresh (transform atom) atom) :
    FreshVariantList fresh (atoms.map transform) atoms := by
  induction atoms with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (hvariants head (by simp))
        (ih (fun atom hmem => hvariants atom (by simp [hmem])))

private theorem freshInstanceList_map
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String)
    (left right : Atom → Atom) (atoms : List Atom)
    (hinstances : ∀ atom, atom ∈ atoms →
      FreshInstance fresh resolve allowed (left atom) (right atom)) :
    FreshInstanceList fresh resolve allowed
      (atoms.map left) (atoms.map right) := by
  induction atoms with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (hinstances head (by simp))
        (ih (fun atom hmem => hinstances atom (by simp [hmem])))

/-- Applying a variable-only copy and then the runtime suffix constructs a
    genuine fresh structural variant whenever the copy covers every source
    variable and runtime equality is reflexive on the copied value. -/
theorem rename_apply_freshVariant (copy : Subst) (suffix : String)
    (atom : Atom)
    (hlookup : ∀ name, name ∈ atom.vars →
      ∃ target, Metta.Subst.lookup copy name = some (Atom.var target))
    (hfresh : ∀ name, name ∈ atom.vars →
      copiedResidualNameSuffix copy suffix name ≠ name)
    (hreflexive : Metta.Atom.equiv (Metta.Subst.apply copy atom)
      (Metta.Subst.apply copy atom) = true) :
    FreshVariant (copiedResidualNameSuffix copy suffix)
      (renameAtomSuffix suffix (Metta.Subst.apply copy atom)) atom := by
  induction atom with
  | sym name =>
      simpa [Metta.Subst.apply, renameAtomSuffix] using
        (FreshVariant.sym (fresh := copiedResidualNameSuffix copy suffix) name)
  | var name =>
      obtain ⟨target, htarget⟩ := hlookup name (by simp [Atom.vars])
      have hnameFresh := hfresh name (by simp [Atom.vars])
      have hcopiedName : copiedResidualNameSuffix copy suffix name =
          target ++ suffix := by
        simp [copiedResidualNameSuffix, htarget]
      simpa [Metta.Subst.apply, htarget, renameAtomSuffix,
        hcopiedName] using
        (FreshVariant.var (fresh := fun source =>
          copiedResidualNameSuffix copy suffix source) name hnameFresh)
  | gnd ground =>
      simpa [Metta.Subst.apply, renameAtomSuffix] using
        (FreshVariant.gnd
          (fresh := copiedResidualNameSuffix copy suffix) ground)
  | expr atoms ih =>
      have hchildVariants : ∀ child, child ∈ atoms →
          FreshVariant (copiedResidualNameSuffix copy suffix)
            (renameAtomSuffix suffix (Metta.Subst.apply copy child)) child := by
        intro child hchild
        apply ih child hchild
        · intro name hname
          apply hlookup name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩
        · intro name hname
          apply hfresh name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩
        · have hlist : Metta.Atom.equivList
              (atoms.map (Metta.Subst.apply copy))
              (atoms.map (Metta.Subst.apply copy)) = true := by
            simpa [Metta.Subst.apply, Metta.Atom.equiv] using hreflexive
          exact atomEquiv_self_of_mem
            (atoms.map (Metta.Subst.apply copy))
            (Metta.Subst.apply copy child)
            (List.mem_map_of_mem hchild) hlist
      have hchildren : FreshVariantList
          (copiedResidualNameSuffix copy suffix)
          (atoms.map fun child =>
            renameAtomSuffix suffix (Metta.Subst.apply copy child)) atoms := by
        exact freshVariantList_map _ _ atoms hchildVariants
      simpa [Metta.Subst.apply, renameAtomSuffix, Function.comp_def] using
        (FreshVariant.expr hchildren)

/-- The concrete discovery copy under a later guard state is an instance of
    the immutable denotation produced by the original head unifier.  This is
    the construction theorem needed when caller variables have already been
    resolved and may subsequently be removed by liveness trimming. -/
theorem rename_apply_current_freshSnapshotInstance
    (copy : Subst) (suffix : String) (atom : Atom)
    (origin runtime : Subst) (allowed : List String)
    (hlookup : ∀ name, name ∈ atom.vars →
      ∃ target, Metta.Subst.lookup copy name = some (Atom.var target))
    (hallowed : ∀ name, name ∈ atom.vars → name ∈ allowed)
    (state : FreshResidualSnapshotState
      (copiedResidualNameSuffix copy suffix)
      (fun name => subst origin (Atom.var name)) allowed runtime)
    (hresolvedFixed : ∀ name, name ∈ allowed →
      subst runtime (subst origin (Atom.var name)) =
        subst origin (Atom.var name))
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        copiedResidualNameSuffix copy suffix left ∉
          (subst origin (Atom.var right)).vars)
    (hreflexive : Metta.Atom.equiv (Metta.Subst.apply copy atom)
      (Metta.Subst.apply copy atom) = true) :
    FreshInstance (copiedResidualNameSuffix copy suffix)
        (fun name => subst origin (Atom.var name)) allowed
        (subst runtime
          (renameAtomSuffix suffix (Metta.Subst.apply copy atom)))
        (subst origin atom) ∧
      subst runtime (subst origin atom) = subst origin atom := by
  induction atom with
  | sym name =>
      constructor
      · simpa [Metta.Subst.apply, renameAtomSuffix] using
          (FreshInstance.same
            (fresh := copiedResidualNameSuffix copy suffix)
            (resolve := fun source => subst origin (Atom.var source))
            (allowed := allowed) (Atom.sym name))
      · simp
  | var name =>
      have hname : name ∈ allowed := hallowed name (by simp [Atom.vars])
      obtain ⟨target, htarget⟩ := hlookup name (by simp [Atom.vars])
      have hcopiedName : copiedResidualNameSuffix copy suffix name =
          target ++ suffix := by
        simp [copiedResidualNameSuffix, htarget]
      have htargetFixed := hresolvedFixed name hname
      constructor
      · rcases state name hname with hnone | hsemantic
        · have hleft := subst_var_of_lookup_none runtime
            (copiedResidualNameSuffix copy suffix name) hnone
          have hcopied : subst runtime
              (renameAtomSuffix suffix
                (Metta.Subst.apply copy (Atom.var name))) =
              Atom.var (copiedResidualNameSuffix copy suffix name) := by
            simp [Metta.Subst.apply, htarget, renameAtomSuffix,
              ← hcopiedName, hleft]
          rw [hcopied]
          exact FreshInstance.var name hname
            (havoids name hname name hname)
        · have hcopied : subst runtime
              (renameAtomSuffix suffix
                (Metta.Subst.apply copy (Atom.var name))) =
              subst origin (Atom.var name) := by
            simp [Metta.Subst.apply, htarget, renameAtomSuffix,
              ← hcopiedName, hsemantic]
          rw [hcopied]
          exact FreshInstance.same (subst origin (Atom.var name))
      · exact htargetFixed
  | gnd ground =>
      constructor
      · simpa [Metta.Subst.apply, renameAtomSuffix] using
          (FreshInstance.same
            (fresh := copiedResidualNameSuffix copy suffix)
            (resolve := fun source => subst origin (Atom.var source))
            (allowed := allowed) (Atom.gnd ground))
      · simp
  | expr atoms ih =>
      have hchildren : ∀ child, child ∈ atoms →
          FreshInstance (copiedResidualNameSuffix copy suffix)
              (fun name => subst origin (Atom.var name)) allowed
              (subst runtime
                (renameAtomSuffix suffix (Metta.Subst.apply copy child)))
              (subst origin child) ∧
            subst runtime (subst origin child) = subst origin child := by
        intro child hchild
        apply ih child hchild
        · intro name hname
          apply hlookup name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩
        · intro name hname
          apply hallowed name
          simp only [Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, hchild, rfl⟩, hname⟩
        · have hlist : Metta.Atom.equivList
              (atoms.map (Metta.Subst.apply copy))
              (atoms.map (Metta.Subst.apply copy)) = true := by
            simpa [Metta.Subst.apply, Metta.Atom.equiv] using hreflexive
          exact atomEquiv_self_of_mem
            (atoms.map (Metta.Subst.apply copy))
            (Metta.Subst.apply copy child)
            (List.mem_map_of_mem hchild) hlist
      constructor
      · have children := freshInstanceList_map
          (copiedResidualNameSuffix copy suffix)
          (fun name => subst origin (Atom.var name)) allowed
          (fun child => subst runtime
            (renameAtomSuffix suffix (Metta.Subst.apply copy child)))
          (fun child => subst origin child) atoms
          (fun child hchild => (hchildren child hchild).1)
        simpa [Metta.Subst.apply, renameAtomSuffix, subst_expr,
          Function.comp_def] using FreshInstance.expr children
      · simp only [subst_expr, Atom.expr.injEq, List.map_map]
        apply List.map_congr_left
        intro child hchild
        exact (hchildren child hchild).2

/-- Every name allocated by the residual copier is strictly longer than the
    maximum occupied length supplied to it. -/
theorem residualFreshNames_lookup_long (maxLength index : Nat)
    (sources : List String) (source : String) (hmem : source ∈ sources) :
    ∃ target,
      Metta.Subst.lookup (residualFreshNames maxLength index sources) source =
        some (Atom.var target) ∧
      maxLength < target.length := by
  induction sources generalizing index with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      by_cases hsource : source = head
      · subst head
        refine ⟨residualFreshName (maxLength + index + 1), ?_, ?_⟩
        · simp [residualFreshNames, Metta.Subst.lookup]
        · simp only [residualFreshName_length]
          omega
      · have htail : source ∈ tail := hmem.resolve_left hsource
        obtain ⟨target, hlookup, hlong⟩ := ih (index + 1) htail
        refine ⟨target, ?_, hlong⟩
        simp [residualFreshNames, Metta.Subst.lookup, hsource, hlookup]

/-- The target allocated at or after `index` has at least the corresponding
    deterministic length. -/
theorem residualFreshNames_lookup_length_ge (maxLength index : Nat)
    (sources : List String) (source target : String)
    (hlookup : Metta.Subst.lookup
      (residualFreshNames maxLength index sources) source =
        some (Atom.var target)) :
    maxLength + index + 1 ≤ target.length := by
  induction sources generalizing index with
  | nil => simp [residualFreshNames, Metta.Subst.lookup] at hlookup
  | cons head tail ih =>
      by_cases hsource : source = head
      · subst head
        simp [residualFreshNames, Metta.Subst.lookup] at hlookup
        subst target
        simp only [residualFreshName_length]
        exact Nat.le_refl _
      · have hbeq : (source == head) = false := by simp [hsource]
        simp only [residualFreshNames, Metta.Subst.lookup, hbeq,
          Bool.false_eq_true, if_false] at hlookup
        have htail := ih (index + 1) hlookup
        omega

/-- With unique source keys, the residual allocator is injective on lookup
    targets.  This is the sharing boundary needed by fresh-variant
    unification: equal generated variables came from the same residual. -/
theorem residualFreshNames_lookup_injective (maxLength index : Nat)
    (sources : List String) (left right target : String)
    (hleft : Metta.Subst.lookup
      (residualFreshNames maxLength index sources) left =
        some (Atom.var target))
    (hright : Metta.Subst.lookup
      (residualFreshNames maxLength index sources) right =
        some (Atom.var target)) :
    left = right := by
  induction sources generalizing index left right target with
  | nil => simp [residualFreshNames, Metta.Subst.lookup] at hleft
  | cons head tail ih =>
      by_cases hleftHead : left = head
      · subst left
        simp [residualFreshNames, Metta.Subst.lookup] at hleft
        subst target
        by_cases hrightHead : right = head
        · exact hrightHead.symm
        · have hbeq : (right == head) = false := by simp [hrightHead]
          simp only [residualFreshNames, Metta.Subst.lookup, hbeq,
            Bool.false_eq_true, if_false] at hright
          have hlong := residualFreshNames_lookup_length_ge maxLength
            (index + 1) tail right
            (residualFreshName (maxLength + index + 1)) hright
          simp only [residualFreshName_length] at hlong
          omega
      · have hleftBeq : (left == head) = false := by simp [hleftHead]
        simp only [residualFreshNames, Metta.Subst.lookup, hleftBeq,
          Bool.false_eq_true, if_false] at hleft
        by_cases hrightHead : right = head
        · subst right
          simp [residualFreshNames, Metta.Subst.lookup] at hright
          subst target
          have hlong := residualFreshNames_lookup_length_ge maxLength
            (index + 1) tail left
            (residualFreshName (maxLength + index + 1)) hleft
          simp only [residualFreshName_length] at hlong
          omega
        · have hrightBeq : (right == head) = false := by simp [hrightHead]
          simp only [residualFreshNames, Metta.Subst.lookup, hrightBeq,
            Bool.false_eq_true, if_false] at hright
          exact ih (index + 1) left right target hleft hright

/-- Every variable in a retained source-binding value belongs to the one
    shared residual set copied for the generated clause. -/
theorem sourceBinding_value_var_mem_residuals (binding : Subst)
    (name : String) (value : Atom) (hentry : (name, value) ∈ binding)
    (source : String) (hsource : source ∈ value.vars) :
    source ∈ specializationResiduals binding := by
  simp only [specializationResiduals, List.mem_eraseDups,
    List.mem_flatMap]
  exact ⟨(name, value), hentry, hsource⟩

/-- Every residual name comes from a concrete source-binding entry and a
    variable occurrence in that entry's value. -/
theorem specializationResiduals_mem_origin (binding : Subst) (source : String)
    (hsource : source ∈ specializationResiduals binding) :
    ∃ name value, (name, value) ∈ binding ∧ source ∈ value.vars := by
  simp only [specializationResiduals, List.mem_eraseDups,
    List.mem_flatMap] at hsource
  obtain ⟨entry, hentry, hvalue⟩ := hsource
  exact ⟨entry.1, entry.2, by simpa using hentry, hvalue⟩

/-- One source residual is covered by the actual deterministic copy map. -/
theorem specializationCopySubst_lookup_var (clause : Clause)
    (binding : Subst) (source : String)
    (hsource : source ∈ specializationResiduals binding) :
    ∃ target,
      Metta.Subst.lookup (specializationCopySubst clause binding) source =
        some (Atom.var target) := by
  unfold specializationCopySubst
  let residuals := specializationResiduals binding
  let occupied := specializationClauseVars clause ++ residuals
  let maxLength := occupied.foldl
    (fun current name => max current name.length) 0
  obtain ⟨target, hlookup, hlong⟩ :=
    residualFreshNames_lookup_long maxLength 0 residuals source hsource
  exact ⟨target, hlookup⟩

/-- The deterministic discovery copy remains a structural fresh variant
    after any ordered guard prefix satisfying `FreshResidualLookupState`.
    Earlier guards may already have identified a copied residual with its
    source; `FreshVariant.varSame` records precisely that shared-variable
    case. -/
theorem specializationCopy_current_freshVariant (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding) (suffix : String)
    (runtime : Subst) (topological : SubstTopological runtime)
    (state : FreshResidualLookupState
      (copiedResidualNameSuffix (specializationCopySubst clause binding)
        suffix)
      (specializationResiduals binding) runtime)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hdisjoint : ∀ copied, copied ∈ specializationResiduals binding →
      ∀ source, source ∈ specializationResiduals binding →
        copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix copied ≠ source) :
    FreshVariant
      (copiedResidualNameSuffix (specializationCopySubst clause binding)
        suffix)
      (subst runtime
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue)))
      sourceValue := by
  let copy := specializationCopySubst clause binding
  let fresh := copiedResidualNameSuffix copy suffix
  have hlookup : ∀ source, source ∈ sourceValue.vars →
      ∃ target, Metta.Subst.lookup copy source = some (Atom.var target) := by
    intro source hsource
    exact specializationCopySubst_lookup_var clause binding source
      (sourceBinding_value_var_mem_residuals binding name sourceValue hentry
        source hsource)
  have original : FreshVariant fresh
      (renameAtomSuffix suffix (Metta.Subst.apply copy sourceValue))
      sourceValue := by
    apply rename_apply_freshVariant copy suffix sourceValue hlookup
    · intro source hsource
      apply hdisjoint source
        (sourceBinding_value_var_mem_residuals binding name sourceValue hentry
          source hsource)
      exact sourceBinding_value_var_mem_residuals binding name sourceValue
        hentry source hsource
    · simpa [copy] using hreflexive
  apply original.subst_left runtime
  · intro source hsource
    apply state.source_fixed source
    exact sourceBinding_value_var_mem_residuals binding name sourceValue hentry
      source hsource
  · intro source hsource
    apply state.fresh_state topological source
    exact sourceBinding_value_var_mem_residuals binding name sourceValue hentry
      source hsource

/-- Generalized current-operand relation for a source residual that may
    already be instantiated by another call argument or an outer recursive
    specialization. -/
theorem specializationCopy_current_freshInstance (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding) (suffix : String)
    (runtime : Subst) (allowed : List String)
    (hsourceAllowed : ∀ source, source ∈ sourceValue.vars →
      source ∈ allowed)
    (state : FreshResidualDenotationState
      (copiedResidualNameSuffix (specializationCopySubst clause binding)
        suffix) allowed runtime)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hrawDisjoint : ∀ source, source ∈ allowed →
      copiedResidualNameSuffix
        (specializationCopySubst clause binding) suffix source ≠ source)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        copiedResidualNameSuffix
            (specializationCopySubst clause binding) suffix left ∉
          (subst runtime (Atom.var right)).vars) :
    FreshInstance
      (copiedResidualNameSuffix (specializationCopySubst clause binding)
        suffix)
      (fun source => subst runtime (Atom.var source))
      allowed
      (subst runtime
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue)))
      (subst runtime sourceValue) := by
  let copy := specializationCopySubst clause binding
  let fresh := copiedResidualNameSuffix copy suffix
  have hlookup : ∀ source, source ∈ sourceValue.vars →
      ∃ target, Metta.Subst.lookup copy source = some (Atom.var target) := by
    intro source hsource
    exact specializationCopySubst_lookup_var clause binding source
      (sourceBinding_value_var_mem_residuals binding name sourceValue hentry
        source hsource)
  have original : FreshVariant fresh
      (renameAtomSuffix suffix (Metta.Subst.apply copy sourceValue))
      sourceValue := by
    apply rename_apply_freshVariant copy suffix sourceValue hlookup
    · intro source hsource
      exact hrawDisjoint source (hsourceAllowed source hsource)
    · simpa [copy] using hreflexive
  apply original.instantiate runtime allowed
  · exact hsourceAllowed
  · exact state
  · exact havoids

/-- The real discovery copy, followed by the real resolution suffix, is an
    input on which the executable unifier succeeds.  The theorem permits
    arbitrary trees and repeated/shared residuals; its only semantic premise
    is runtime reflexivity of the copied value, already checked by provenance. -/
theorem specializationCopy_unifyTop_succeeds_with_domain (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding) (suffix : String)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hdisjoint : ∀ left, left ∈ sourceValue.vars →
      ∀ right, right ∈ sourceValue.vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix left ≠ right) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result ∧
      unifyTopExact
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result ∧
      FreshGenerated
        (copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix)
        sourceValue.vars result := by
  let copy := specializationCopySubst clause binding
  have hlookup : ∀ source, source ∈ sourceValue.vars →
      ∃ target, Metta.Subst.lookup copy source = some (Atom.var target) := by
    intro source hsource
    exact specializationCopySubst_lookup_var clause binding source
      (sourceBinding_value_var_mem_residuals binding name sourceValue hentry
        source hsource)
  have hinjective : ∀ left, left ∈ sourceValue.vars →
      ∀ right, right ∈ sourceValue.vars →
        copiedResidualNameSuffix copy suffix left =
          copiedResidualNameSuffix copy suffix right → left = right := by
    intro left hleft right hright hequal
    obtain ⟨leftTarget, hleftLookup⟩ := hlookup left hleft
    obtain ⟨rightTarget, hrightLookup⟩ := hlookup right hright
    have htargets : leftTarget = rightTarget := by
      apply resolution_suffix_injective suffix
      simpa [copiedResidualNameSuffix, hleftLookup, hrightLookup] using hequal
    subst rightTarget
    exact residualFreshNames_lookup_injective
      ((specializationClauseVars clause ++ specializationResiduals binding).foldl
        (fun current item => max current item.length) 0) 0
      (specializationResiduals binding) left right leftTarget
      (by simpa [copy, specializationCopySubst] using hleftLookup)
      (by simpa [copy, specializationCopySubst] using hrightLookup)
  have variant : FreshVariant (copiedResidualNameSuffix copy suffix)
      (renameAtomSuffix suffix (Metta.Subst.apply copy sourceValue))
      sourceValue := by
    apply rename_apply_freshVariant copy suffix sourceValue hlookup
    · intro source hsource
      exact hdisjoint source hsource source hsource
    · simpa [copy] using hreflexive
  obtain ⟨result, exactResult, generated⟩ :=
    variant.unifyTopExact_succeeds_with_domain hinjective hdisjoint
  exact ⟨result, unifyTopExact_some_underlying _ _ _ exactResult,
    exactResult, generated⟩

/-- Existence-only projection of the copied-residual unification theorem. -/
theorem specializationCopy_unifyTop_succeeds (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding) (suffix : String)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hdisjoint : ∀ left, left ∈ sourceValue.vars →
      ∀ right, right ∈ sourceValue.vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix left ≠ right) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result := by
  obtain ⟨result, hresult, hexact, hdomain⟩ :=
    specializationCopy_unifyTop_succeeds_with_domain clause binding name
      sourceValue hentry suffix hreflexive hdisjoint
  exact ⟨result, hresult⟩

/-- Resolution's occupied-variable set supplies the disjointness premise of
    `specializationCopy_unifyTop_succeeds_with_domain` for the actual suffix. -/
theorem specializationCopy_resolution_unifyTop_succeeds_with_domain
    (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding)
    (argsv : List Atom) (res : Atom) (rest : List Goal) (base : Subst)
    (qterm : Atom) (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest base qterm) ≤ seed)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hoccupied : ∀ source, source ∈ sourceValue.vars →
      source ∈ resolutionOccupiedVars argsv res rest base qterm) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical
        (renameAtomSuffix
          (resolutionFreshSuffix argsv res rest base qterm seed)
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result ∧
      unifyTopExact
        (renameAtomSuffix
          (resolutionFreshSuffix argsv res rest base qterm seed)
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result ∧
      FreshGenerated
        (copiedResidualNameSuffix
          (specializationCopySubst clause binding)
          (resolutionFreshSuffix argsv res rest base qterm seed))
        sourceValue.vars result := by
  apply specializationCopy_unifyTop_succeeds_with_domain clause binding name
    sourceValue hentry (resolutionFreshSuffix argsv res rest base qterm seed)
      hreflexive
  intro left hleft right hright
  obtain ⟨target, htarget⟩ := specializationCopySubst_lookup_var clause
    binding left (sourceBinding_value_var_mem_residuals binding name
      sourceValue hentry left hleft)
  have hfresh : copiedResidualNameSuffix
      (specializationCopySubst clause binding)
      (resolutionFreshSuffix argsv res rest base qterm seed) left =
        target ++ resolutionFreshSuffix argsv res rest base qterm seed := by
    simp [copiedResidualNameSuffix, htarget]
  rw [hfresh]
  exact resolutionFreshSuffix_target_ne argsv res rest base qterm seed
    hhighWater target right (hoccupied right hright)

/-- Existence-only projection for resolution callers that do not inspect the
    generated fresh-variable domain. -/
theorem specializationCopy_resolution_unifyTop_succeeds (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding)
    (argsv : List Atom) (res : Atom) (rest : List Goal) (base : Subst)
    (qterm : Atom) (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest base qterm) ≤ seed)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hoccupied : ∀ source, source ∈ sourceValue.vars →
      source ∈ resolutionOccupiedVars argsv res rest base qterm) :
    ∃ result,
      Metta.Unify.unifyTopWith prologGroundIdentical
        (renameAtomSuffix
          (resolutionFreshSuffix argsv res rest base qterm seed)
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        sourceValue = some result := by
  obtain ⟨result, hresult, hexact, hdomain⟩ :=
    specializationCopy_resolution_unifyTop_succeeds_with_domain clause binding
      name sourceValue hentry argsv res rest base qterm seed hhighWater
      hreflexive hoccupied
  exact ⟨result, hresult⟩

/-- Once generic head narrowing exposes the aligned source value and leaves
    the copied pattern fixed, the actual guard `unifyB` succeeds. -/
theorem specialization_guard_unifyB_succeeds (clause : Clause)
    (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding)
    (argsv : List Atom) (res : Atom) (rest : List Goal) (base : Subst)
    (qterm formalName : Atom) (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest base qterm) ≤ seed)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hoccupied : ∀ source, source ∈ sourceValue.vars →
      source ∈ resolutionOccupiedVars argsv res rest base qterm)
    (hcopiedFixed : subst base
      (renameAtomSuffix
        (resolutionFreshSuffix argsv res rest base qterm seed)
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue)) =
      renameAtomSuffix
        (resolutionFreshSuffix argsv res rest base qterm seed)
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue))
    (hformal : subst base formalName = sourceValue) :
    ∃ next,
      unifyB base
        (renameAtomSuffix
          (resolutionFreshSuffix argsv res rest base qterm seed)
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        formalName = some next := by
  obtain ⟨generated, hgeneratedUnderlying, hgenerated, hdomain⟩ :=
    specializationCopy_resolution_unifyTop_succeeds_with_domain clause binding
      name sourceValue hentry argsv res rest base qterm seed hhighWater
      hreflexive hoccupied
  unfold unifyB
  rw [hcopiedFixed, hformal, hgenerated]
  cases generated with
  | nil => exact ⟨base, rfl⟩
  | cons entry tail =>
      exact ⟨Metta.Subst.compose (entry :: tail) base, rfl⟩

@[simp] theorem metaClause_ofRule (parent : String) (params : List Atom)
    (body : Atom) (compiled : Clause) :
    MetaClause.ofRule?
        (Atom.expr [Atom.sym "=", Atom.expr (Atom.sym parent :: params), body])
        compiled =
      some { parent, sourceParams := params, sourceBody := body, compiled } := by
  rfl

@[simp] theorem captureMeta_rule (w : PWorld) (parent : String)
    (params : List Atom) (body : Atom) (compiled : Clause) :
    w.captureMeta
        (Atom.expr [Atom.sym "=", Atom.expr (Atom.sym parent :: params), body])
        compiled =
      { w with metaClauses :=
          { parent, sourceParams := params, sourceBody := body, compiled } ::
            w.metaClauses } := by
  rfl

@[simp] theorem captureMeta_nonrule (w : PWorld) (a : Atom) (compiled : Clause)
    (h : MetaClause.ofRule? a compiled = none) :
    w.captureMeta a compiled = w := by
  simp [PWorld.captureMeta, h]

@[simp] theorem discoverClause_captured (isDefined hasMeta : String → Bool)
    (actuals : List Atom) (captured : MetaClause) :
    (discoverClause isDefined hasMeta actuals captured).1.captured = captured := by
  unfold discoverClause
  split <;> simp only <;> split <;> rfl

@[simp] theorem discoverClause_discoveryActuals
    (isDefined hasMeta : String → Bool) (actuals : List Atom)
    (captured : MetaClause) :
    (discoverClause isDefined hasMeta actuals captured).1.discoveryActuals =
      actuals := by
  unfold discoverClause
  split <;> simp only <;> split <;> rfl

mutual

/-- One selected specialization binding is literally rooted at a matching
    variable occurrence in the static call tuple.  The value index is the
    actual call-site subterm itself, not the result of a Boolean equality
    inversion. -/
inductive SpecializationAlignedAt (name : String) (value : Atom) :
    Atom → Atom → Prop where
  | root : SpecializationAlignedAt name value (Atom.var name) value
  | expr {formals actuals : List Atom} :
      SpecializationAlignedList name value formals actuals →
      SpecializationAlignedAt name value (Atom.expr formals)
        (Atom.expr actuals)

/-- Pointwise context closure for an aligned occurrence in argument lists. -/
inductive SpecializationAlignedList (name : String) (value : Atom) :
    List Atom → List Atom → Prop where
  | head {formal actual formals actuals} :
      SpecializationAlignedAt name value formal actual →
      SpecializationAlignedList name value
        (formal :: formals) (actual :: actuals)
  | tail {formal actual formals actuals} :
      SpecializationAlignedList name value formals actuals →
      SpecializationAlignedList name value
        (formal :: formals) (actual :: actuals)

end

mutual

/-- Denotational equality at an aligned atom exposes equality for the selected
    source binding, independently of unrelated numeric-equivalent siblings. -/
theorem SpecializationAlignedAt.denotes {name : String} {value : Atom}
    {formal actual : Atom}
    (aligned : SpecializationAlignedAt name value formal actual)
    (runtime : Subst)
    (hdenotes : subst runtime formal = subst runtime actual) :
    subst runtime (Atom.var name) = subst runtime value := by
  cases aligned with
  | root => exact hdenotes
  | expr alignedList =>
      simp only [subst_expr, Atom.expr.injEq] at hdenotes
      exact alignedList.denotes runtime hdenotes

/-- List-context counterpart of `SpecializationAlignedAt.denotes`. -/
theorem SpecializationAlignedList.denotes {name : String} {value : Atom}
    {formals actuals : List Atom}
    (aligned : SpecializationAlignedList name value formals actuals)
    (runtime : Subst)
    (hdenotes : formals.map (subst runtime) = actuals.map (subst runtime)) :
    subst runtime (Atom.var name) = subst runtime value := by
  cases aligned with
  | head alignedHead =>
      simp only [List.map_cons, List.cons.injEq] at hdenotes
      exact alignedHead.denotes runtime hdenotes.1
  | tail alignedTail =>
      simp only [List.map_cons, List.cons.injEq] at hdenotes
      exact alignedTail.denotes runtime hdenotes.2

end

mutual

/-- Applying a unique discovered binding at an aligned occurrence exposes
    the selected executable value on the specialized side. -/
theorem SpecializationAlignedAt.appliedDenotes
    {name : String} {sourceValue formal actual : Atom}
    (aligned : SpecializationAlignedAt name sourceValue formal actual)
    (runtime binding : Subst) (boundValue : Atom)
    (hlookup : Metta.Subst.lookup binding name = some boundValue)
    (hdenotes :
      subst runtime (Metta.Subst.apply binding formal) =
        subst runtime actual) :
    subst runtime boundValue = subst runtime sourceValue := by
  cases aligned with
  | root =>
      simpa [Metta.Subst.apply, hlookup] using hdenotes
  | expr alignedList =>
      simp only [Metta.Subst.apply, subst_expr, Atom.expr.injEq,
        List.map_map] at hdenotes
      exact alignedList.appliedDenotes runtime binding boundValue hlookup
        hdenotes

/-- List-context companion to denotation through an applied discovered
    binding. -/
theorem SpecializationAlignedList.appliedDenotes
    {name : String} {sourceValue : Atom} {formals actuals : List Atom}
    (aligned : SpecializationAlignedList name sourceValue formals actuals)
    (runtime binding : Subst) (boundValue : Atom)
    (hlookup : Metta.Subst.lookup binding name = some boundValue)
    (hdenotes :
      formals.map (fun formal =>
        subst runtime (Metta.Subst.apply binding formal)) =
          actuals.map (subst runtime)) :
    subst runtime boundValue = subst runtime sourceValue := by
  cases aligned with
  | head alignedHead =>
      simp only [List.map_cons, List.cons.injEq] at hdenotes
      exact alignedHead.appliedDenotes runtime binding boundValue hlookup
        hdenotes.1
  | tail alignedTail =>
      simp only [List.map_cons, List.cons.injEq] at hdenotes
      exact alignedTail.appliedDenotes runtime binding boundValue hlookup
        hdenotes.2

end

/-- A pair selected from `List.zip` supplies an aligned list context at the
    same position. -/
theorem specializationAlignedList_of_zip_mem (name : String) (value : Atom)
    {formals actuals : List Atom} {formal actual : Atom}
    (hmem : (formal, actual) ∈ formals.zip actuals)
    (haligned : SpecializationAlignedAt name value formal actual) :
    SpecializationAlignedList name value formals actuals := by
  induction formals generalizing actuals with
  | nil => simp at hmem
  | cons formalHead formalTail ih =>
      cases actuals with
      | nil => simp at hmem
      | cons actualHead actualTail =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            exact .head haligned
          · exact .tail (ih htail)

/-- The executable structural aligner can only retain an old binding or add
    the literal actual subterm paired with a selected formal occurrence. -/
theorem alignSpecializable_binding_origin (isDefined relevant : String → Bool)
    (fuel : Nat) (formal actual : Atom) (st : Alignment)
    (name : String) (value : Atom)
    (hmem : (name, value) ∈
      (alignSpecializable isDefined relevant fuel formal actual st).binding) :
    (name, value) ∈ st.binding ∨
      SpecializationAlignedAt name value formal actual := by
  induction fuel generalizing formal actual st name value with
  | zero =>
      simpa [alignSpecializable] using Or.inl hmem
  | succ fuel ih =>
      cases formal with
      | sym formalName =>
          cases actual <;> simpa [alignSpecializable] using Or.inl hmem
      | gnd formalGround =>
          cases actual <;> simpa [alignSpecializable] using Or.inl hmem
      | var formalName =>
          simp only [alignSpecializable] at hmem
          split at hmem
          next hselected =>
            unfold Alignment.add at hmem
            split at hmem
            next prior hlookup =>
              exact Or.inl hmem
            next hlookup =>
              simp only at hmem
              have happend : (name, value) ∈ st.binding ∨
                  (name, value) = (formalName, actual) := by
                simpa [List.mem_append] using hmem
              rcases happend with hold | hnew
              · exact Or.inl hold
              · cases hnew
                exact Or.inr .root
          next hselected =>
            exact Or.inl hmem
      | expr formals =>
          cases actual with
          | sym actualName =>
              simpa [alignSpecializable] using Or.inl hmem
          | var actualName =>
              simpa [alignSpecializable] using Or.inl hmem
          | gnd actualGround =>
              simpa [alignSpecializable] using Or.inl hmem
          | expr actuals =>
              simp only [alignSpecializable] at hmem
              split at hmem
              next hlength =>
                let pairs := formals.zip actuals
                have hfold : ∀ (remaining : List (Atom × Atom))
                    (current : Alignment) (name : String) (value : Atom),
                    (name, value) ∈ (remaining.foldl
                      (fun acc (pair : Atom × Atom) =>
                        alignSpecializable isDefined relevant
                          fuel pair.1 pair.2 acc) current).binding →
                    (name, value) ∈ current.binding ∨
                      ∃ pair ∈ remaining,
                        SpecializationAlignedAt name value pair.1 pair.2 := by
                  intro remaining
                  induction remaining with
                  | nil =>
                      intro current name value hmember
                      exact Or.inl hmember
                  | cons pair rest restIH =>
                      intro current name value hmember
                      simp only [List.foldl_cons] at hmember
                      have hrest := restIH
                        (alignSpecializable isDefined relevant fuel
                          pair.1 pair.2 current) name value hmember
                      rcases hrest with hnext | ⟨origin, horiginMem,
                          horigin⟩
                      · have hstep := ih pair.1 pair.2 current name value hnext
                        rcases hstep with hold | hpair
                        · exact Or.inl hold
                        · exact Or.inr ⟨pair, by simp, hpair⟩
                      · exact Or.inr ⟨origin, by simp [horiginMem], horigin⟩
                have horigin := hfold pairs st name value hmem
                rcases horigin with hold | ⟨pair, hpair, hpairAligned⟩
                · exact Or.inl hold
                · exact Or.inr (.expr
                    (specializationAlignedList_of_zip_mem name value hpair
                      hpairAligned))
              next hlength =>
                exact Or.inl hmem

private theorem subst_lookup_none_iff_key_not_mem (binding : Subst)
    (name : String) :
    Metta.Subst.lookup binding name = none ↔
      name ∉ binding.map Prod.fst := by
  induction binding with
  | nil => simp [Metta.Subst.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases hname : name = key
      · subst key
        simp [Metta.Subst.lookup]
      · have hbeq : (name == key) = false := by simp [hname]
        simp [Metta.Subst.lookup, hbeq, hname, ih]

private theorem Alignment.add_keys_nodup (st : Alignment)
    (name : String) (actual : Atom)
    (hnodup : (st.binding.map Prod.fst).Nodup) :
    (((st.add name actual).binding).map Prod.fst).Nodup := by
  unfold Alignment.add
  cases hlookup : Metta.Subst.lookup st.binding name with
  | some prior => simpa using hnodup
  | none =>
      have hnotmem : name ∉ st.binding.map Prod.fst :=
        (subst_lookup_none_iff_key_not_mem st.binding name).mp hlookup
      simp only [List.map_append, List.map_singleton]
      apply List.nodup_append.mpr
      refine ⟨hnodup, by simp, ?_⟩
      intro oldName hold newName hnew hequal
      simp only [List.mem_singleton] at hnew
      subst newName
      subst oldName
      exact hnotmem hold

/-- Structural discovery never emits two entries for the same formal
    variable; repeated occurrences reuse the first alignment. -/
theorem alignSpecializable_binding_keys_nodup
    (isDefined relevant : String → Bool) (fuel : Nat)
    (formal actual : Atom) (st : Alignment)
    (hnodup : (st.binding.map Prod.fst).Nodup) :
    (((alignSpecializable isDefined relevant fuel formal actual st).binding
      ).map Prod.fst).Nodup := by
  induction fuel generalizing formal actual st with
  | zero => simpa [alignSpecializable] using hnodup
  | succ fuel ih =>
      cases formal with
      | sym formalName =>
          cases actual <;> simpa [alignSpecializable] using hnodup
      | gnd formalGround =>
          cases actual <;> simpa [alignSpecializable] using hnodup
      | var formalName =>
          simp only [alignSpecializable]
          split
          · exact Alignment.add_keys_nodup st formalName actual hnodup
          · exact hnodup
      | expr formals =>
          cases actual with
          | sym actualName => simpa [alignSpecializable] using hnodup
          | var actualName => simpa [alignSpecializable] using hnodup
          | gnd actualGround => simpa [alignSpecializable] using hnodup
          | expr actuals =>
              simp only [alignSpecializable]
              split
              · let pairs := formals.zip actuals
                have hfold : ∀ (remaining : List (Atom × Atom))
                    (current : Alignment),
                    (current.binding.map Prod.fst).Nodup →
                    (((remaining.foldl
                      (fun acc pair =>
                        alignSpecializable isDefined relevant fuel
                          pair.1 pair.2 acc) current).binding).map
                        Prod.fst).Nodup := by
                  intro remaining
                  induction remaining with
                  | nil =>
                      intro current hcurrent
                      exact hcurrent
                  | cons pair rest restIH =>
                      intro current hcurrent
                      simp only [List.foldl_cons]
                      exact restIH _
                        (ih pair.1 pair.2 current hcurrent)
                exact hfold pairs st hnodup
              · exact hnodup

/-- Every source binding emitted by one real discovery clause has a literal
    aligned origin in that clause's complete static call tuple. -/
theorem discoverClause_sourceBinding_aligned
    (isDefined hasMeta : String → Bool) (actuals : List Atom)
    (captured : MetaClause) (name : String) (value : Atom)
    (hmem : (name, value) ∈
      (discoverClause isDefined hasMeta actuals captured).1.sourceBinding) :
    SpecializationAlignedList name value captured.compiled.params actuals := by
  unfold discoverClause at hmem
  let relevant := relevantSpecializationVar hasMeta captured.compiled.body
  let aligned :=
    if captured.compiled.params.length == actuals.length then
      (captured.compiled.params.zip actuals).foldl
        (fun st pair =>
          alignSpecializable isDefined relevant (pair.1.size + 1)
            pair.1 pair.2 st) {}
    else { compatible := false : Alignment }
  change (name, value) ∈ ((if aligned.compatible then
      (({ captured := captured
          sourceBinding := aligned.binding
          discoveryActuals := actuals } : SpecClauseCandidate), aligned.values)
    else (({ captured := captured
             sourceBinding := []
             discoveryActuals := actuals } : SpecClauseCandidate), [])).1
      |>.sourceBinding) at hmem
  split at hmem
  next hcompatible =>
    simp only at hmem
    unfold aligned at hmem
    split at hmem
    next hlength =>
      let pairs := captured.compiled.params.zip actuals
      have hfold : ∀ (remaining : List (Atom × Atom))
          (current : Alignment) (name : String) (value : Atom),
          (name, value) ∈ (remaining.foldl
            (fun st (pair : Atom × Atom) =>
              alignSpecializable isDefined relevant
                (pair.1.size + 1) pair.1 pair.2 st) current).binding →
          (name, value) ∈ current.binding ∨
            ∃ pair ∈ remaining,
              SpecializationAlignedAt name value pair.1 pair.2 := by
        intro remaining
        induction remaining with
        | nil =>
            intro current name value hmember
            exact Or.inl hmember
        | cons pair rest ih =>
            intro current name value hmember
            simp only [List.foldl_cons] at hmember
            have hrest := ih
              (alignSpecializable isDefined relevant (pair.1.size + 1)
                pair.1 pair.2 current) name value hmember
            rcases hrest with hnext | ⟨origin, horiginMem, horigin⟩
            · have hstep := alignSpecializable_binding_origin isDefined
                relevant (pair.1.size + 1) pair.1 pair.2 current name value
                hnext
              rcases hstep with hold | hpair
              · exact Or.inl hold
              · exact Or.inr ⟨pair, by simp, hpair⟩
            · exact Or.inr ⟨origin, by simp [horiginMem], horigin⟩
      have horigin := hfold pairs {} name value hmem
      rcases horigin with hold | ⟨pair, hpair, hpairAligned⟩
      · simp at hold
      · exact specializationAlignedList_of_zip_mem name value hpair
          hpairAligned
    next hlength =>
      simp at hmem
  next hcompatible =>
    simp at hmem

/-- A real discovery clause retains the unique-key invariant established by
    `Alignment.add`. -/
theorem discoverClause_sourceBinding_keys_nodup
    (isDefined hasMeta : String → Bool) (actuals : List Atom)
    (captured : MetaClause) :
    (((discoverClause isDefined hasMeta actuals captured).1.sourceBinding
      ).map Prod.fst).Nodup := by
  unfold discoverClause
  let relevant := relevantSpecializationVar hasMeta captured.compiled.body
  let aligned :=
    if captured.compiled.params.length == actuals.length then
      (captured.compiled.params.zip actuals).foldl
        (fun st pair =>
          alignSpecializable isDefined relevant (pair.1.size + 1)
            pair.1 pair.2 st) {}
    else { compatible := false : Alignment }
  have haligned : (aligned.binding.map Prod.fst).Nodup := by
    unfold aligned
    split
    · let pairs := captured.compiled.params.zip actuals
      have hfold : ∀ (remaining : List (Atom × Atom))
          (current : Alignment),
          (current.binding.map Prod.fst).Nodup →
          (((remaining.foldl
            (fun st pair =>
              alignSpecializable isDefined relevant (pair.1.size + 1)
                pair.1 pair.2 st) current).binding).map Prod.fst).Nodup := by
        intro remaining
        induction remaining with
        | nil =>
            intro current hcurrent
            exact hcurrent
        | cons pair rest ih =>
            intro current hcurrent
            simp only [List.foldl_cons]
            exact ih _ (alignSpecializable_binding_keys_nodup isDefined
              relevant (pair.1.size + 1) pair.1 pair.2 current hcurrent)
      exact hfold pairs {} (by simp)
    · simp
  change (if aligned.compatible then
      (({ captured := captured
          sourceBinding := aligned.binding
          discoveryActuals := actuals } : SpecClauseCandidate), aligned.values)
    else (({ captured := captured
             sourceBinding := []
             discoveryActuals := actuals } : SpecClauseCandidate), [])).1
      |>.sourceBinding.map Prod.fst |>.Nodup
  split
  · exact haligned
  · simp

/-- Constructional source-origin invariant for a discovered clause candidate. -/
def SpecClauseCandidate.SourceAligned (candidate : SpecClauseCandidate) : Prop :=
  ∀ name value, (name, value) ∈ candidate.sourceBinding →
    SpecializationAlignedList name value candidate.captured.compiled.params
      candidate.discoveryActuals

/-- Whole-family discovery gives every emitted candidate the literal
    call-site origin relation established by `discoverClause`. -/
theorem discoverSpecialization_clauses_sourceAligned
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (captured : List MetaClause)
    (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      captured = some candidate) :
    ∀ clause, clause ∈ candidate.clauses → clause.SourceAligned := by
  let parentClauses := captured.filter (fun clause => clause.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  change (if values.isEmpty then none else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }) = some candidate at hdiscover
  by_cases hempty : values.isEmpty = true
  · simp [hempty] at hdiscover
  · simp [hempty] at hdiscover
    subst candidate
    intro clause hclause name value hbinding
    simp only [List.mem_map] at hclause
    obtain ⟨discovered, hfound, rfl⟩ := hclause
    simp only [found, List.mem_map] at hfound
    obtain ⟨source, hsource, rfl⟩ := hfound
    simpa using
      (discoverClause_sourceBinding_aligned isDefined hasMeta actuals
        source name value hbinding)

/-- Whole-family discovery also preserves unique source-binding keys for
    every emitted candidate. -/
theorem discoverSpecialization_clauses_sourceKeysNodup
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (captured : List MetaClause)
    (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      captured = some candidate) :
    ∀ clause, clause ∈ candidate.clauses →
      (clause.sourceBinding.map Prod.fst).Nodup := by
  let parentClauses := captured.filter (fun clause => clause.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  change (if values.isEmpty then none else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }) = some candidate at hdiscover
  by_cases hempty : values.isEmpty = true
  · simp [hempty] at hdiscover
  · simp [hempty] at hdiscover
    subst candidate
    intro clause hclause
    simp only [List.mem_map] at hclause
    obtain ⟨discovered, hfound, rfl⟩ := hclause
    simp only [found, List.mem_map] at hfound
    obtain ⟨source, hsource, rfl⟩ := hfound
    exact discoverClause_sourceBinding_keys_nodup isDefined hasMeta actuals
      source

/-- Exact source-alignment validation exposes the occurrence and literal
    call-site agreement for each selected binding entry. -/
theorem specializationSourceBindingExact_entry (binding : Subst)
    (formals actuals : List Atom) (name : String) (value : Atom)
    (hexact : specializationSourceBindingExact binding formals actuals = true)
    (hmem : (name, value) ∈ binding) :
    formals.any (specializationVarOccurs name) = true ∧
      specializationEntryExactlyAgreesList name value formals actuals = true := by
  cases binding with
  | nil => simp at hmem
  | cons head tail =>
      simp only [specializationSourceBindingExact, List.isEmpty,
        Bool.false_or, Bool.and_eq_true] at hexact
      exact Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hexact.2 (name, value) hmem)

/-- Successful discovery retains every captured parent clause exactly once
    and in native newest-first metadata order. -/
theorem discoverSpecialization_captured_order
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (captured : List MetaClause)
    (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      captured = some candidate) :
    candidate.clauses.map (·.captured) =
      captured.filter (fun clause => clause.parent == parent) := by
  let parentClauses := captured.filter (fun clause => clause.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  change (if values.isEmpty then none else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }) = some candidate at hdiscover
  by_cases hempty : values.isEmpty = true
  · simp [hempty] at hdiscover
  · simp [hempty] at hdiscover
    subst candidate
    simp [found, parentClauses, Function.comp_def]

theorem discoverSpecialization_clauses_nonempty
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (captured : List MetaClause)
    (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      captured = some candidate) :
    candidate.clauses ≠ [] := by
  let parentClauses := captured.filter (fun clause => clause.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  change (if values.isEmpty then none else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }) = some candidate at hdiscover
  by_cases hempty : values.isEmpty = true
  · simp [hempty] at hdiscover
  · simp [hempty] at hdiscover
    subst candidate
    intro hclauses
    have hfound : found = [] := by simpa using hclauses
    simp [values, hfound] at hempty

theorem discoverSpecialization_parent
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (captured : List MetaClause)
    (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      captured = some candidate) :
    candidate.key.parent = parent := by
  let parentClauses := captured.filter (fun clause => clause.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  change (if values.isEmpty then none else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }) = some candidate at hdiscover
  by_cases hempty : values.isEmpty = true
  · simp [hempty] at hdiscover
  · simp [hempty] at hdiscover
    subst candidate
    rfl

/-- Combining successful discovery with the live metadata invariant gives
    the exact source-order parent list consumed by specialization install. -/
theorem discovered_parent_clause_order (w : PWorld) (parent : String)
    (isDefined hasMeta : String → Bool) (actuals : List Atom)
    (candidate : SpecCandidate)
    (ordered : w.CapturedParentOrdered parent)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      w.metaClauses = some candidate) :
    w.clausesOf parent =
      candidate.clauses.reverse.map (fun clause => clause.captured.compiled) := by
  rw [ordered.clauses, PWorld.capturedMetaOf]
  rw [← discoverSpecialization_captured_order isDefined hasMeta parent
    actuals w.metaClauses candidate hdiscover]
  simp

/-- Clause construction preserves the complete candidate family and its
    newest-first order in the provenance ledger. -/
theorem buildSpecClauses_parent_provenance (fuel : Nat) (st : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate)
    (after : SpecBuildState) (built : List BuiltSpecClause)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built)) :
    built.map (fun item => item.provenance.parentClause) =
      candidates.map (fun candidate => candidate.captured.compiled) := by
  induction fuel generalizing st candidates after built with
  | zero =>
      cases candidates <;> simp [buildSpecClauses] at hbuild ⊢
      rcases hbuild with ⟨rfl, rfl⟩
      rfl
  | succ fuel ih =>
      cases candidates with
      | nil =>
          simp [buildSpecClauses] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          rfl
      | cons candidate rest =>
          simp only [buildSpecClauses] at hbuild
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          simp only [Option.some.injEq, Prod.mk.injEq] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          simp only [List.map_cons, List.cons.injEq, true_and]
          apply ih
          assumption

/-- Every clause produced by the actual builder carries the requested public
    name/parent and retains its generic resolution head definitionally. -/
theorem buildSpecClauses_provenance_shape (fuel : Nat) (st : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate)
    (after : SpecBuildState) (built : List BuiltSpecClause)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built)) :
    ∀ item, item ∈ built →
      item.provenance.name = specName ∧
        item.provenance.parent = key.parent ∧
        item.provenance.parentClause.params =
          item.provenance.executableClause.params ∧
        item.provenance.parentClause.result =
          item.provenance.executableClause.result := by
  induction fuel generalizing st candidates after built with
  | zero =>
      cases candidates <;> simp [buildSpecClauses] at hbuild ⊢
      rcases hbuild with ⟨rfl, rfl⟩
      simp
  | succ fuel ih =>
      cases candidates with
      | nil =>
          simp [buildSpecClauses] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          simp
      | cons candidate rest =>
          simp only [buildSpecClauses] at hbuild
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          simp only [Option.some.injEq, Prod.mk.injEq] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · apply ih <;> assumption

def SourceDefines (name : String) (source : Atom) : Prop :=
  ∃ params body,
    source = Atom.expr
      [Atom.sym "=", Atom.expr (Atom.sym name :: params), body]

theorem specializedSource_defines (specName : String)
    (candidate : SpecClauseCandidate) :
    SourceDefines specName (specializedSource specName candidate) := by
  exact ⟨candidate.captured.sourceParams.map
      (Metta.Subst.apply candidate.binding),
    Metta.Subst.apply candidate.binding candidate.captured.sourceBody, rfl⟩

theorem buildSpecClauses_source_defines (fuel : Nat) (st : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate)
    (after : SpecBuildState) (built : List BuiltSpecClause)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built)) :
    ∀ item, item ∈ built → SourceDefines specName item.source := by
  induction fuel generalizing st candidates after built with
  | zero =>
      cases candidates <;> simp [buildSpecClauses] at hbuild ⊢
      rcases hbuild with ⟨rfl, rfl⟩
      simp
  | succ fuel ih =>
      cases candidates with
      | nil =>
          simp [buildSpecClauses] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          simp
      | cons candidate rest =>
          simp only [buildSpecClauses] at hbuild
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          split at hbuild <;> try contradiction
          simp only [Option.some.injEq, Prod.mk.injEq] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact specializedSource_defines specName candidate
          · apply ih <;> assumption

theorem installBuiltClauses_exact_fields (w : PWorld) (specName : String)
    (built : List BuiltSpecClause) :
    (installBuiltClauses w specName built).progClauses =
        w.progClauses ++ built.reverse.map (fun item =>
          (specName, item.provenance.executableClause)) ∧
      (installBuiltClauses w specName built).specClauseProvenance =
        w.specClauseProvenance ++ built.reverse.map (·.provenance) := by
  simp [installBuiltClauses]

theorem installBuiltClauses_clauseIndexCoherent (w : PWorld)
    (specName : String) (built : List BuiltSpecClause) :
    (installBuiltClauses w specName built).ClauseIndexCoherent := by
  intro hready
  unfold installBuiltClauses at hready ⊢
  simp only at hready ⊢
  rw [if_pos hready]
  rfl

theorem installBuiltClauses_spaceIndexCoherent (w : PWorld)
    (specName : String) (built : List BuiltSpecClause)
    (coherent : w.SpaceIndexCoherent) :
    (installBuiltClauses w specName built).SpaceIndexCoherent := by
  let addVisible := fun (current : PWorld) (item : BuiltSpecClause) =>
    let withAtom := current.addAtom selfSpace (chainify item.source)
    withAtom.captureMetaWithSourceKey item.source
      item.provenance.executableClause (clauseAlphaKey item.sourceClause)
  have fold_coherent : ∀ (items : List BuiltSpecClause) (current : PWorld),
      current.SpaceIndexCoherent →
        (items.foldl addVisible current).SpaceIndexCoherent := by
    intro items
    induction items with
    | nil =>
        intro current hcurrent
        exact hcurrent
    | cons item rest ih =>
        intro current hcurrent
        simp only [List.foldl_cons]
        apply ih
        apply PWorld.captureMetaWithSourceKey_spaceCoherent
        exact PWorld.addAtom_spaceCoherent current selfSpace
          (chainify item.source) hcurrent
  have hvisible := fold_coherent built.reverse w coherent
  unfold installBuiltClauses
  dsimp only
  exact hvisible

theorem installCopiedTypes_spaceIndexCoherent (w : PWorld)
    (parent specName : String) (coherent : w.SpaceIndexCoherent) :
    (installCopiedTypes w parent specName).SpaceIndexCoherent := by
  let addType := fun (current : PWorld) (declaration : Atom × Atom) =>
    let visible := Atom.expr
      [Atom.sym ":", Atom.sym specName, declaration.2]
    let withAtom := current.addAtom selfSpace (chainify visible)
    { withAtom with typeDecls :=
        withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] }
  have fold_coherent : ∀ (declarations : List (Atom × Atom))
      (current : PWorld), current.SpaceIndexCoherent →
        (declarations.foldl addType current).SpaceIndexCoherent := by
    intro declarations
    induction declarations with
    | nil =>
        intro current hcurrent
        exact hcurrent
    | cons declaration rest ih =>
        intro current hcurrent
        simp only [List.foldl_cons]
        apply ih
        exact PWorld.addAtom_spaceCoherent current selfSpace
          (chainify (Atom.expr
            [Atom.sym ":", Atom.sym specName, declaration.2])) hcurrent
  unfold installCopiedTypes
  exact fold_coherent _ w coherent

@[simp] theorem addAtom_capturedMetaOf (w : PWorld) (space atom : Atom)
    (name : String) :
    (w.addAtom space atom).capturedMetaOf name = w.capturedMetaOf name := by
  unfold PWorld.addAtom PWorld.capturedMetaOf
  split <;> rfl

theorem captureMeta_sourceDefines_compiled (w : PWorld) (name : String)
    (source : Atom) (compiled : Clause)
    (hsource : SourceDefines name source) :
    ((w.captureMeta source compiled).capturedMetaOf name).map (·.compiled) =
      compiled :: (w.capturedMetaOf name).map (·.compiled) := by
  rcases hsource with ⟨params, body, rfl⟩
  simp [PWorld.captureMeta, PWorld.capturedMetaOf, MetaClause.ofRule?]

theorem captureMeta_sourceDefines_other (w : PWorld)
    (sourceName name : String) (source : Atom) (compiled : Clause)
    (hdifferent : name ≠ sourceName)
    (hsource : SourceDefines sourceName source) :
    (w.captureMeta source compiled).capturedMetaOf name =
      w.capturedMetaOf name := by
  rcases hsource with ⟨params, body, rfl⟩
  have hreverse : sourceName ≠ name := Ne.symm hdifferent
  simp [PWorld.captureMeta, PWorld.capturedMetaOf, MetaClause.ofRule?,
    hreverse]

theorem captureMetaWithSourceKey_sourceDefines_compiled (w : PWorld)
    (name : String) (source : Atom) (compiled : Clause) (sourceKey : String)
    (hsource : SourceDefines name source) :
    ((w.captureMetaWithSourceKey source compiled sourceKey).capturedMetaOf
      name).map (·.compiled) =
      compiled :: (w.capturedMetaOf name).map (·.compiled) := by
  rcases hsource with ⟨params, body, rfl⟩
  simp [PWorld.captureMetaWithSourceKey, PWorld.capturedMetaOf,
    MetaClause.ofRule?]

theorem captureMetaWithSourceKey_sourceDefines_other (w : PWorld)
    (sourceName name : String) (source : Atom) (compiled : Clause)
    (sourceKey : String) (hdifferent : name ≠ sourceName)
    (hsource : SourceDefines sourceName source) :
    (w.captureMetaWithSourceKey source compiled sourceKey).capturedMetaOf name =
      w.capturedMetaOf name := by
  rcases hsource with ⟨params, body, rfl⟩
  have hreverse : sourceName ≠ name := Ne.symm hdifferent
  simp [PWorld.captureMetaWithSourceKey, PWorld.capturedMetaOf,
    MetaClause.ofRule?, hreverse]

theorem installBuiltClauses_capturedCompiled (w : PWorld)
    (specName : String) (built : List BuiltSpecClause)
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source) :
    ((installBuiltClauses w specName built).capturedMetaOf specName).map
        (·.compiled) =
      built.map (fun item => item.provenance.executableClause) ++
        (w.capturedMetaOf specName).map (·.compiled) := by
  let step := fun (current : PWorld) (item : BuiltSpecClause) =>
    let withAtom := current.addAtom selfSpace (chainify item.source)
    withAtom.captureMetaWithSourceKey item.source
      item.provenance.executableClause (clauseAlphaKey item.sourceClause)
  have hfold : ∀ (items : List BuiltSpecClause) (current : PWorld),
      (∀ item, item ∈ items → SourceDefines specName item.source) →
      ((items.foldl step current).capturedMetaOf specName).map
          (·.compiled) =
        items.reverse.map (fun item => item.provenance.executableClause) ++
          (current.capturedMetaOf specName).map (·.compiled) := by
    intro items
    induction items with
    | nil => intro current hitems; simp
    | cons item rest ih =>
        intro current hitems
        simp only [List.foldl_cons]
        rw [ih]
        · rw [captureMetaWithSourceKey_sourceDefines_compiled]
          · simp [List.append_assoc]
          · exact hitems item (by simp)
        · intro next hnext
          exact hitems next (by simp [hnext])
  unfold installBuiltClauses
  change
    (((built.reverse.foldl step w).capturedMetaOf specName).map
      (·.compiled)) = _
  rw [hfold]
  · simp
  · intro item hitem
    exact hsource item (by simpa using hitem)

theorem installBuiltClauses_capturedMetaOf_other (w : PWorld)
    (specName name : String) (built : List BuiltSpecClause)
    (hdifferent : name ≠ specName)
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source) :
    (installBuiltClauses w specName built).capturedMetaOf name =
      w.capturedMetaOf name := by
  let step := fun (current : PWorld) (item : BuiltSpecClause) =>
    let withAtom := current.addAtom selfSpace (chainify item.source)
    withAtom.captureMetaWithSourceKey item.source
      item.provenance.executableClause (clauseAlphaKey item.sourceClause)
  have hfold : ∀ (items : List BuiltSpecClause) (current : PWorld),
      (∀ item, item ∈ items → SourceDefines specName item.source) →
      (items.foldl step current).capturedMetaOf name =
        current.capturedMetaOf name := by
    intro items
    induction items with
    | nil => intro current hitems; rfl
    | cons item rest ih =>
        intro current hitems
        simp only [List.foldl_cons]
        rw [ih]
        · have hitemSource := hitems item (by simp)
          rw [captureMetaWithSourceKey_sourceDefines_other
            (current.addAtom selfSpace (chainify item.source)) specName name
            item.source item.provenance.executableClause
            (clauseAlphaKey item.sourceClause) hdifferent hitemSource]
          exact addAtom_capturedMetaOf current selfSpace
            (chainify item.source) name
        · intro next hnext
          exact hitems next (by simp [hnext])
  unfold installBuiltClauses
  change (built.reverse.foldl step w).capturedMetaOf name = _
  apply hfold
  intro item hitem
  exact hsource item (by simpa using hitem)

theorem installBuiltClauses_clausesOf (w : PWorld) (specName : String)
    (built : List BuiltSpecClause) :
    (installBuiltClauses w specName built).clausesOf specName =
      w.clausesOf specName ++
        built.reverse.map (fun item => item.provenance.executableClause) := by
  rw [PWorld.clausesOf]
  rw [(installBuiltClauses_exact_fields w specName built).1]
  simp [PWorld.clausesOf, List.filterMap_append]

theorem installBuiltClauses_clausesOf_other (w : PWorld) (specName parent : String)
    (built : List BuiltSpecClause) (hdifferent : parent ≠ specName) :
    (installBuiltClauses w specName built).clausesOf parent =
      w.clausesOf parent := by
  rw [PWorld.clausesOf]
  rw [(installBuiltClauses_exact_fields w specName built).1]
  simp [PWorld.clausesOf, List.filterMap_append,
    Ne.symm hdifferent]

theorem installBuiltClauses_capturedParentOrdered (w : PWorld)
    (specName : String) (built : List BuiltSpecClause)
    (hspecEmpty : w.clausesOf specName = [])
    (hmetaEmpty : w.capturedMetaOf specName = [])
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source) :
    (installBuiltClauses w specName built).CapturedParentOrdered specName := by
  constructor
  rw [installBuiltClauses_clausesOf, hspecEmpty]
  rw [show
      ((installBuiltClauses w specName built).capturedMetaOf specName).reverse.map
          (·.compiled) =
        (((installBuiltClauses w specName built).capturedMetaOf specName).map
          (·.compiled)).reverse by simp]
  rw [installBuiltClauses_capturedCompiled w specName built hsource]
  simp [hmetaEmpty]

theorem installBuiltClauses_recordProvenance (w : PWorld) (key : SpecKey)
    (specName : String) (built : List BuiltSpecClause)
    (hprior : w.recordProvenance { key, name := specName } = [])
    (hshape : ∀ item, item ∈ built →
      item.provenance.name = specName ∧
        item.provenance.parent = key.parent) :
    (installBuiltClauses w specName built).recordProvenance
      { key, name := specName } = built.reverse.map (·.provenance) := by
  unfold PWorld.recordProvenance at hprior ⊢
  rw [(installBuiltClauses_exact_fields w specName built).2]
  rw [List.filter_append, hprior]
  simp only [List.nil_append]
  apply List.filter_eq_self.mpr
  intro provenance hprovenance
  rcases List.mem_map.mp hprovenance with ⟨item, hitem, rfl⟩
  have hitemBuilt : item ∈ built := by simpa using hitem
  have h := hshape item hitemBuilt
  simp [h.1, h.2]

/-- Once the installer's exact record slice is identified, the actual
    builder facts discharge the complete constructional ordered invariant. -/
theorem installBuiltClauses_recordOrdered (fuel : Nat) (st after : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate) (built : List BuiltSpecClause)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built))
    (hcandidates : candidates ≠ [])
    (hdifferent : key.parent ≠ specName)
    (hspecEmpty : after.world.clausesOf specName = [])
    (hparent : after.world.clausesOf key.parent =
      candidates.reverse.map (fun candidate => candidate.captured.compiled))
    (hrecord :
      (installBuiltClauses after.world specName built).recordProvenance
        { key, name := specName } = built.reverse.map (·.provenance)) :
    (installBuiltClauses after.world specName built).SpecializationRecordOrdered
      { key, name := specName } := by
  have hparentBuilt := buildSpecClauses_parent_provenance fuel st key
    specName candidates after built hbuild
  have hshape := buildSpecClauses_provenance_shape fuel st key specName
    candidates after built hbuild
  have hbuilt : built ≠ [] := by
    intro hempty
    subst built
    cases candidates with
    | nil => exact hcandidates rfl
    | cons candidate rest => simp at hparentBuilt
  constructor
  · rw [installBuiltClauses_clausesOf, hspecEmpty]
    simp [hbuilt]
  · rw [installBuiltClauses_clausesOf_other _ _ _ _ hdifferent]
    rw [hparent, hrecord]
    simpa [List.map_reverse, List.map_map, Function.comp_def] using
      (congrArg List.reverse hparentBuilt).symm
  · rw [installBuiltClauses_clausesOf, hspecEmpty, hrecord]
    simp [Function.comp_def]
  · intro provenance hprovenance
    rw [hrecord] at hprovenance
    rcases List.mem_map.mp hprovenance with ⟨item, hitem, rfl⟩
    have hitemBuilt : item ∈ built := by simpa using hitem
    exact (hshape item hitemBuilt).2.2

/-- Proof-facing install theorem with no assumed ledger equality: the actual
    builder shape theorem derives the exact record slice. -/
theorem installBuiltClauses_recordOrdered_of_build
    (fuel : Nat) (st after : SpecBuildState) (key : SpecKey)
    (specName : String) (candidates : List SpecClauseCandidate)
    (built : List BuiltSpecClause)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built))
    (hcandidates : candidates ≠ [])
    (hdifferent : key.parent ≠ specName)
    (hspecEmpty : after.world.clausesOf specName = [])
    (hparent : after.world.clausesOf key.parent =
      candidates.reverse.map (fun candidate => candidate.captured.compiled))
    (hprior : after.world.recordProvenance { key, name := specName } = []) :
    (installBuiltClauses after.world specName built).SpecializationRecordOrdered
      { key, name := specName } := by
  have hshape := buildSpecClauses_provenance_shape fuel st key specName
    candidates after built hbuild
  have hrecord := installBuiltClauses_recordProvenance after.world key
    specName built hprior (fun item hitem =>
      ⟨(hshape item hitem).1, (hshape item hitem).2.1⟩)
  exact installBuiltClauses_recordOrdered fuel st after key specName
    candidates built hbuild hcandidates hdifferent hspecEmpty hparent hrecord

/-! ## Transactional name frames -/

/-- A recursive builder leaves an already live or provisionally reserved
    public name completely alone.  In particular it cannot install clauses
    or provenance under the root name before the root transaction commits. -/
structure SpecNameFrame (before after : SpecBuildState)
    (name : String) : Prop where
  clauses : after.world.clausesOf name = before.world.clausesOf name
  provenance : after.world.provenanceNamed name =
    before.world.provenanceNamed name
  metadata : after.world.capturedMetaOf name =
    before.world.capturedMetaOf name
  reserved : after.isDefined name = true

theorem SpecNameFrame.refl (st : SpecBuildState) (name : String)
    (hreserved : st.isDefined name = true) :
    SpecNameFrame st st name :=
  ⟨rfl, rfl, rfl, hreserved⟩

theorem SpecNameFrame.trans {first second third : SpecBuildState}
    {name : String} (h₁ : SpecNameFrame first second name)
    (h₂ : SpecNameFrame second third name) :
    SpecNameFrame first third name :=
  ⟨h₂.clauses.trans h₁.clauses,
   h₂.provenance.trans h₁.provenance,
   h₂.metadata.trans h₁.metadata,
   h₂.reserved⟩

theorem SpecNameFrame.recordProvenance {before after : SpecBuildState}
    {name : String} (hframe : SpecNameFrame before after name)
    (record : SpecRecord) (hname : record.name = name) :
    after.world.recordProvenance record =
      before.world.recordProvenance record := by
  have hnamed := hframe.provenance
  unfold PWorld.provenanceNamed at hnamed
  unfold PWorld.recordProvenance
  rw [← hname] at hnamed
  have := congrArg
    (List.filter (fun provenance : SpecClauseProvenance =>
      provenance.parent == record.key.parent)) hnamed
  simpa [List.filter_filter, Bool.and_comm, Bool.and_left_comm,
    Bool.and_assoc] using this

/-- A constructionally ordered record necessarily has a live parent family.
    This rules out a previously ordered record depending on a freshly
    reserved, still-empty generated name. -/
theorem PWorld.SpecializationRecordOrdered.parent_nonempty {w : PWorld}
    {record : SpecRecord} (ordered : w.SpecializationRecordOrdered record) :
    w.clausesOf record.key.parent ≠ [] := by
  intro hparent
  have hprovenance : w.recordProvenance record = [] := by
    have h := ordered.parentClauses
    rw [hparent] at h
    simpa using h
  have hgenerated : w.clausesOf record.name = [] := by
    rw [ordered.executableClauses, hprovenance]
    rfl
  have hnonempty := ordered.nonempty
  rw [hgenerated] at hnonempty
  simp at hnonempty

/-- Name frames transport the exact ordered record proposition; no Boolean
    checker is inverted to recover Lean equality. -/
theorem SpecNameFrame.preserves_recordOrdered {before after : SpecBuildState}
    (record : SpecRecord)
    (hname : SpecNameFrame before after record.name)
    (hparent : SpecNameFrame before after record.key.parent)
    (ordered : before.world.SpecializationRecordOrdered record) :
    after.world.SpecializationRecordOrdered record := by
  have hprovenance := hname.recordProvenance record rfl
  constructor
  · rw [hname.clauses]
    exact ordered.nonempty
  · rw [hparent.clauses, hprovenance]
    exact ordered.parentClauses
  · rw [hname.clauses, hprovenance]
    exact ordered.executableClauses
  · intro provenance hmember
    rw [hprovenance] at hmember
    exact ordered.exactHeads provenance hmember

/-- Captured-family order is likewise transported exactly by a name frame. -/
theorem SpecNameFrame.preserves_capturedParentOrdered
    {before after : SpecBuildState} {parent : String}
    (hframe : SpecNameFrame before after parent)
    (ordered : before.world.CapturedParentOrdered parent) :
    after.world.CapturedParentOrdered parent := by
  constructor
  rw [hframe.clauses, hframe.metadata]
  exact ordered.clauses

/-- Every captured metadata family agrees, in source order, with its live
    executable clause family. -/
def PWorld.CapturedFamiliesOrdered (w : PWorld) : Prop :=
  ∀ parent, w.capturedMetaOf parent ≠ [] →
    w.CapturedParentOrdered parent

/-- Successful specialization discovery witnesses a nonempty captured
    family for its parent. -/
theorem discoverSpecialization_captured_nonempty
    (isDefined hasMeta : String → Bool) (parent : String)
    (actuals : List Atom) (w : PWorld) (candidate : SpecCandidate)
    (hdiscover : discoverSpecialization isDefined hasMeta parent actuals
      w.metaClauses = some candidate) :
    w.capturedMetaOf parent ≠ [] := by
  intro hempty
  have horder := discoverSpecialization_captured_order isDefined hasMeta
    parent actuals w.metaClauses candidate hdiscover
  have hcandidates := discoverSpecialization_clauses_nonempty isDefined
    hasMeta parent actuals w.metaClauses candidate hdiscover
  rw [← PWorld.capturedMetaOf] at horder
  rw [hempty] at horder
  have : candidate.clauses = [] := by simpa using horder
  exact hcandidates this

@[simp] theorem installCopiedTypes_clausesOf (w : PWorld)
    (parent specName name : String) :
    (installCopiedTypes w parent specName).clausesOf name =
      w.clausesOf name := by
  unfold installCopiedTypes
  generalize w.typeDecls.filter
      (fun declaration => declaration.fst == Atom.sym parent) = declarations
  have hfold : ∀ (items : List (Atom × Atom)) (current : PWorld),
      (items.foldl (fun current declaration =>
        let visible := Atom.expr
          [Atom.sym ":", Atom.sym specName, declaration.2]
        let withAtom := current.addAtom selfSpace (chainify visible)
        { withAtom with typeDecls :=
            withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] })
        current).progClauses = current.progClauses := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons declaration rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        have hself : (Atom.sym "&self" == Atom.sym "&self") = true := by
          decide
        simp [PWorld.addAtom, selfSpace, hself]
  simp only [PWorld.clausesOf]
  rw [hfold]

@[simp] theorem installCopiedTypes_provenanceNamed (w : PWorld)
    (parent specName name : String) :
    (installCopiedTypes w parent specName).provenanceNamed name =
      w.provenanceNamed name := by
  unfold installCopiedTypes PWorld.provenanceNamed
  generalize w.typeDecls.filter
      (fun declaration => declaration.fst == Atom.sym parent) = declarations
  have hfold : ∀ (items : List (Atom × Atom)) (current : PWorld),
      (items.foldl (fun current declaration =>
        let visible := Atom.expr
          [Atom.sym ":", Atom.sym specName, declaration.2]
        let withAtom := current.addAtom selfSpace (chainify visible)
        { withAtom with typeDecls :=
            withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] })
        current).specClauseProvenance = current.specClauseProvenance := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons declaration rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        have hself : (Atom.sym "&self" == Atom.sym "&self") = true := by
          decide
        simp [PWorld.addAtom, selfSpace, hself]
  rw [hfold]

@[simp] theorem installCopiedTypes_specClauseProvenance (w : PWorld)
    (parent specName : String) :
    (installCopiedTypes w parent specName).specClauseProvenance =
      w.specClauseProvenance := by
  unfold installCopiedTypes
  generalize w.typeDecls.filter
      (fun declaration => declaration.fst == Atom.sym parent) = declarations
  have hfold : ∀ (items : List (Atom × Atom)) (current : PWorld),
      (items.foldl (fun current declaration =>
        let visible := Atom.expr
          [Atom.sym ":", Atom.sym specName, declaration.2]
        let withAtom := current.addAtom selfSpace (chainify visible)
        { withAtom with typeDecls :=
            withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] })
        current).specClauseProvenance = current.specClauseProvenance := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons declaration rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        have hself : (Atom.sym "&self" == Atom.sym "&self") = true := by
          decide
        simp [PWorld.addAtom, selfSpace, hself]
  exact hfold _ w

@[simp] theorem installCopiedTypes_specializations (w : PWorld)
    (parent specName : String) :
    (installCopiedTypes w parent specName).specializations =
      w.specializations := by
  unfold installCopiedTypes
  generalize w.typeDecls.filter
      (fun declaration => declaration.fst == Atom.sym parent) = declarations
  have hfold : ∀ (items : List (Atom × Atom)) (current : PWorld),
      (items.foldl (fun current declaration =>
        let visible := Atom.expr
          [Atom.sym ":", Atom.sym specName, declaration.2]
        let withAtom := current.addAtom selfSpace (chainify visible)
        { withAtom with typeDecls :=
            withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] })
        current).specializations = current.specializations := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons declaration rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        have hself : (Atom.sym "&self" == Atom.sym "&self") = true := by
          decide
        simp [PWorld.addAtom, selfSpace, hself]
  rw [hfold]

@[simp] theorem installCopiedTypes_capturedMetaOf (w : PWorld)
    (parent specName name : String) :
    (installCopiedTypes w parent specName).capturedMetaOf name =
      w.capturedMetaOf name := by
  unfold installCopiedTypes
  generalize w.typeDecls.filter
      (fun declaration => declaration.fst == Atom.sym parent) = declarations
  have hfold : ∀ (items : List (Atom × Atom)) (current : PWorld),
      (items.foldl (fun current declaration =>
        let visible := Atom.expr
          [Atom.sym ":", Atom.sym specName, declaration.2]
        let withAtom := current.addAtom selfSpace (chainify visible)
        { withAtom with typeDecls :=
            withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] })
        current).capturedMetaOf name = current.capturedMetaOf name := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons declaration rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        exact addAtom_capturedMetaOf current selfSpace
          (chainify (Atom.expr
            [Atom.sym ":", Atom.sym specName, declaration.2])) name
  rw [hfold]

/-- Installation under a genuinely different generated name preserves the
    protected name's complete executable/provenance slice. -/
theorem installBuiltClauses_nameFrame (st : SpecBuildState)
    (name specName : String) (built : List BuiltSpecClause)
    (hdifferent : name ≠ specName)
    (hshape : ∀ item, item ∈ built → item.provenance.name = specName)
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source)
    (hreserved : st.isDefined name = true) :
    SpecNameFrame st
      { st with world := installBuiltClauses st.world specName built }
      name := by
  constructor
  · exact installBuiltClauses_clausesOf_other st.world specName name
      built hdifferent
  · unfold PWorld.provenanceNamed
    rw [(installBuiltClauses_exact_fields st.world specName built).2]
    rw [List.filter_append]
    have hfiltered :
        (built.reverse.map (fun item => item.provenance)).filter
            (fun provenance => provenance.name == name) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro provenance hprovenance
      rcases List.mem_map.mp hprovenance with ⟨item, hitem, rfl⟩
      have hitemBuilt : item ∈ built := by simpa using hitem
      have hname := hshape item hitemBuilt
      have hreverse : specName ≠ name := Ne.symm hdifferent
      simp [hname, hreverse]
    rw [hfiltered, List.append_nil]
  · exact installBuiltClauses_capturedMetaOf_other st.world specName name
      built hdifferent hsource
  · simp only [SpecBuildState.isDefined]
    rw [installBuiltClauses_clausesOf_other st.world specName name
      built hdifferent]
    exact hreserved

/-- Installing a different fresh family preserves an already ordered record
    whenever neither its public name nor its parent is the installed name. -/
theorem installBuiltClauses_preserves_recordOrdered_other
    (st : SpecBuildState) (specName : String)
    (built : List BuiltSpecClause) (record : SpecRecord)
    (hname : record.name ≠ specName)
    (hparent : record.key.parent ≠ specName)
    (hshape : ∀ item, item ∈ built → item.provenance.name = specName)
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source)
  (ordered : st.world.SpecializationRecordOrdered record) :
    (installBuiltClauses st.world specName built).SpecializationRecordOrdered
      record := by
  have hnameNonempty : st.world.clausesOf record.name ≠ [] := by
    intro hempty
    have hnonempty := ordered.nonempty
    rw [hempty] at hnonempty
    simp at hnonempty
  have hnameDefined : st.isDefined record.name = true := by
    cases hclauses : st.world.clausesOf record.name with
    | nil => exact False.elim (hnameNonempty hclauses)
    | cons clause rest => simp [SpecBuildState.isDefined, hclauses]
  have hparentDefined : st.isDefined record.key.parent = true := by
    cases hclauses : st.world.clausesOf record.key.parent with
    | nil => exact False.elim (ordered.parent_nonempty hclauses)
    | cons clause rest => simp [SpecBuildState.isDefined, hclauses]
  have hnameFrame := installBuiltClauses_nameFrame st record.name specName
    built hname hshape hsource hnameDefined
  have hparentFrame := installBuiltClauses_nameFrame st record.key.parent
    specName built hparent hshape hsource hparentDefined
  exact hnameFrame.preserves_recordOrdered record hparentFrame ordered

/-- A fresh family install extends, rather than invalidates, the global
    captured-family ordering invariant. -/
theorem installBuiltClauses_preserves_capturedFamiliesOrdered
    (w : PWorld) (specName : String) (built : List BuiltSpecClause)
    (hspecEmpty : w.clausesOf specName = [])
    (hmetaEmpty : w.capturedMetaOf specName = [])
    (hsource : ∀ item, item ∈ built → SourceDefines specName item.source)
    (ordered : w.CapturedFamiliesOrdered) :
    (installBuiltClauses w specName built).CapturedFamiliesOrdered := by
  intro parent hnonempty
  by_cases hequal : parent = specName
  · subst parent
    exact installBuiltClauses_capturedParentOrdered w specName built
      hspecEmpty hmetaEmpty hsource
  · have hmetadata := installBuiltClauses_capturedMetaOf_other w specName
      parent built hequal hsource
    have hbeforeNonempty : w.capturedMetaOf parent ≠ [] := by
      rw [hmetadata] at hnonempty
      exact hnonempty
    have hbefore := ordered parent hbeforeNonempty
    constructor
    rw [installBuiltClauses_clausesOf_other w specName parent built hequal]
    rw [hmetadata]
    exact hbefore.clauses

@[simp] theorem addAtom_specializations (w : PWorld) (space atom : Atom) :
    (w.addAtom space atom).specializations = w.specializations := by
  unfold PWorld.addAtom
  split <;> rfl

@[simp] theorem captureMetaWithSourceKey_specializations (w : PWorld)
    (source : Atom) (compiled : Clause) (sourceKey : String) :
    (w.captureMetaWithSourceKey source compiled sourceKey).specializations =
      w.specializations := by
  unfold PWorld.captureMetaWithSourceKey
  split <;> rfl

@[simp] theorem installBuiltClauses_specializations (w : PWorld)
    (specName : String) (built : List BuiltSpecClause) :
    (installBuiltClauses w specName built).specializations =
      w.specializations := by
  let step := fun (current : PWorld) (item : BuiltSpecClause) =>
    let withAtom := current.addAtom selfSpace (chainify item.source)
    withAtom.captureMetaWithSourceKey item.source
      item.provenance.executableClause (clauseAlphaKey item.sourceClause)
  have hfold : ∀ (items : List BuiltSpecClause) (current : PWorld),
      (items.foldl step current).specializations =
        current.specializations := by
    intro items
    induction items with
    | nil => intro current; rfl
    | cons item rest ih =>
        intro current
        simp only [List.foldl_cons]
        rw [ih]
        unfold step
        rw [captureMetaWithSourceKey_specializations,
          addAtom_specializations]
  unfold installBuiltClauses
  change (built.reverse.foldl step w).specializations = w.specializations
  exact hfold built.reverse w

theorem registerSpecialization_nameFrame (st : SpecBuildState)
    (name parent specName : String) (record : SpecRecord)
    (hreserved : st.isDefined name = true) :
    SpecNameFrame st
      { st with
          provisional := st.provisional ++ [record]
          pending := st.pending ++ [record.key]
          world := installCopiedTypes st.world parent specName }
      name := by
  constructor
  · exact installCopiedTypes_clausesOf st.world parent specName name
  · exact installCopiedTypes_provenanceNamed st.world parent specName name
  · exact installCopiedTypes_capturedMetaOf st.world parent specName name
  · simp only [SpecBuildState.isDefined]
    rw [installCopiedTypes_clausesOf]
    cases hclauses : (st.world.clausesOf name).isEmpty with
    | false => simp
    | true =>
        have hprovisional :
            st.provisional.any (fun record => record.name == name) = true := by
          simpa [SpecBuildState.isDefined, hclauses] using hreserved
        simp [hprovisional]

/-- Constructional invariant carried through the mutually recursive atomic
    builder.  A provisional row is either genuinely not installed yet or
    already has its exact ordered proof; public names are unique across the
    committed and provisional registry. -/
structure SpecBuildOrdered (st : SpecBuildState) : Prop where
  committed : ∀ record, record ∈ st.world.specializations →
    st.world.SpecializationRecordOrdered record
  provisional : ∀ record, record ∈ st.provisional →
    st.world.clausesOf record.name = [] ∨
      st.world.SpecializationRecordOrdered record
  captured : st.world.CapturedFamiliesOrdered
  uniqueNames : ((st.world.specializations ++ st.provisional).map
    (fun record => record.name)).Nodup

theorem SpecBuildState.isDefined_of_clauses_nonempty (st : SpecBuildState)
    (name : String) (hnonempty : st.world.clausesOf name ≠ []) :
    st.isDefined name = true := by
  cases hclauses : st.world.clausesOf name with
  | nil => exact False.elim (hnonempty hclauses)
  | cons clause rest => simp [SpecBuildState.isDefined, hclauses]

/-- A failed collision test makes the generated name fresh in the complete
    construction registry, using orderedness to rule out an empty committed
    row. -/
theorem SpecBuildOrdered.name_not_mem_of_not_occupied {st : SpecBuildState}
    (invariant : SpecBuildOrdered st) (name : String)
    (hcollision : st.isNameOccupied name = false) :
    name ∉ (st.world.specializations ++ st.provisional).map
      (fun record => record.name) := by
  have hnotDefined : st.isDefined name = false := by
    cases hdefined : st.isDefined name with
    | false => rfl
    | true => simp [SpecBuildState.isNameOccupied, hdefined] at hcollision
  intro hmember
  rcases List.mem_map.mp hmember with ⟨record, hrecord, hname⟩
  rcases List.mem_append.mp hrecord with hcommitted | hprovisional
  · have hordered := invariant.committed record hcommitted
    have hdefined := st.isDefined_of_clauses_nonempty record.name (by
      intro hempty
      have hnonempty := hordered.nonempty
      rw [hempty] at hnonempty
      simp at hnonempty)
    rw [hname, hnotDefined] at hdefined
    contradiction
  · have hany : st.provisional.any (fun item => item.name == name) = true := by
      apply List.any_eq_true.mpr
      exact ⟨record, hprovisional, by simp [hname]⟩
    have hdefined : st.isDefined name = true := by
      simp [SpecBuildState.isDefined, hany]
    rw [hnotDefined] at hdefined
    contradiction

/-- Reserving one collision-free record and copying its type declarations
    preserves the transaction invariant; the new row is represented by the
    honest not-yet-installed disjunct. -/
theorem SpecBuildOrdered.register (st : SpecBuildState) (parent : String)
    (record : SpecRecord) (invariant : SpecBuildOrdered st)
    (hspecEmpty : st.world.clausesOf record.name = [])
    (hnameFresh : record.name ∉
      (st.world.specializations ++ st.provisional).map
        (fun item => item.name)) :
    SpecBuildOrdered
      { st with
          provisional := st.provisional ++ [record]
          pending := st.pending ++ [record.key]
          world := installCopiedTypes st.world parent record.name } := by
  let registered : SpecBuildState :=
    { st with
        provisional := st.provisional ++ [record]
        pending := st.pending ++ [record.key]
        world := installCopiedTypes st.world parent record.name }
  have preserveOrdered : ∀ old : SpecRecord,
      st.world.SpecializationRecordOrdered old →
        registered.world.SpecializationRecordOrdered old := by
    intro old ordered
    have hnameDefined := st.isDefined_of_clauses_nonempty old.name (by
      intro hempty
      have hnonempty := ordered.nonempty
      rw [hempty] at hnonempty
      simp at hnonempty)
    have hparentDefined := st.isDefined_of_clauses_nonempty old.key.parent
      ordered.parent_nonempty
    have hnameFrame := registerSpecialization_nameFrame st old.name parent
      record.name record hnameDefined
    have hparentFrame := registerSpecialization_nameFrame st old.key.parent
      parent record.name record hparentDefined
    exact hnameFrame.preserves_recordOrdered old hparentFrame ordered
  constructor
  · intro old hmember
    rw [installCopiedTypes_specializations] at hmember
    exact preserveOrdered old (invariant.committed old hmember)
  · intro old hmember
    simp only [List.mem_append, List.mem_singleton] at hmember
    rcases hmember with hold | hnew
    · rcases invariant.provisional old hold with hempty | hordered
      · left
        exact installCopiedTypes_clausesOf st.world parent record.name old.name
          |>.trans hempty
      · exact Or.inr (preserveOrdered old hordered)
    · left
      subst old
      exact installCopiedTypes_clausesOf st.world parent record.name record.name
        |>.trans hspecEmpty
  · intro name hnonempty
    have hbeforeNonempty : st.world.capturedMetaOf name ≠ [] := by
      rw [installCopiedTypes_capturedMetaOf] at hnonempty
      exact hnonempty
    have hbefore := invariant.captured name hbeforeNonempty
    constructor
    rw [installCopiedTypes_clausesOf, installCopiedTypes_capturedMetaOf]
    exact hbefore.clauses
  · simp only [installCopiedTypes_specializations]
    simp only [List.map_append, List.map_singleton]
    rw [← List.append_assoc]
    have appendFresh : ∀ (names : List String), names.Nodup →
        record.name ∉ names → (names ++ [record.name]).Nodup := by
      intro names hnodup hfresh
      induction names with
      | nil => simp
      | cons name rest ih =>
          simp only [List.nodup_cons] at hnodup
          simp only [List.mem_cons, not_or] at hfresh
          simp only [List.cons_append, List.nodup_cons]
          constructor
          · simp [hnodup.1, Ne.symm hfresh.1]
          · exact ih hnodup.2 hfresh.2
    have hnames :
        (st.world.specializations.map (fun item => item.name) ++
          st.provisional.map (fun item => item.name)).Nodup := by
      simpa [List.map_append] using invariant.uniqueNames
    have hfresh : record.name ∉
        st.world.specializations.map (fun item => item.name) ++
          st.provisional.map (fun item => item.name) := by
      simpa [List.map_append] using hnameFresh
    exact appendFresh _ hnames hfresh

theorem SpecBuildOrdered.markGain (st : SpecBuildState) (key : SpecKey)
  (invariant : SpecBuildOrdered st) :
    SpecBuildOrdered (st.markGain key) := by
  unfold SpecBuildState.markGain
  split
  · exact invariant
  · exact ⟨invariant.committed, invariant.provisional,
      invariant.captured, invariant.uniqueNames⟩

/-- Registry-name uniqueness is injectivity on records that occur in the
    registry, even though `SpecRecord` itself is not globally keyed by name. -/
private theorem record_eq_of_nodup_names (records : List SpecRecord)
    (hnodup : (records.map (fun record => record.name)).Nodup)
    {left right : SpecRecord} (hleft : left ∈ records)
    (hright : right ∈ records) (hnames : left.name = right.name) :
    left = right := by
  induction records with
  | nil => simp at hleft
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exact False.elim (hnodup.1 (List.mem_map.mpr
            ⟨right, hright, hnames.symm⟩))
      · rcases hright with rfl | hright
        · exact False.elim (hnodup.1 (List.mem_map.mpr
            ⟨left, hleft, hnames⟩))
        · exact ih hnodup.2 hleft hright

/-- Atomically installing the freshly reserved root converts precisely that
    provisional row to its constructional proof and frames every older row. -/
theorem SpecBuildOrdered.install (st : SpecBuildState) (record : SpecRecord)
    (built : List BuiltSpecClause) (invariant : SpecBuildOrdered st)
    (hrecord : record ∈ st.provisional)
    (hspecEmpty : st.world.clausesOf record.name = [])
    (hmetaEmpty : st.world.capturedMetaOf record.name = [])
    (hshape : ∀ item, item ∈ built →
      item.provenance.name = record.name)
    (hsource : ∀ item, item ∈ built →
      SourceDefines record.name item.source)
    (hroot : PWorld.SpecializationRecordOrdered
      (installBuiltClauses st.world record.name built) record) :
    SpecBuildOrdered
      { st with world := installBuiltClauses st.world record.name built } := by
  let registry := st.world.specializations ++ st.provisional
  have hrecordRegistry : record ∈ registry := by
    exact List.mem_append.mpr (Or.inr hrecord)
  have nameDifferent : ∀ old, old ∈ registry → old ≠ record →
      old.name ≠ record.name := by
    intro old hold hdifferent hequal
    exact hdifferent (record_eq_of_nodup_names registry invariant.uniqueNames
      hold hrecordRegistry hequal)
  have preserveOrdered : ∀ old, old ∈ registry → old ≠ record →
      st.world.SpecializationRecordOrdered old →
        PWorld.SpecializationRecordOrdered
          (installBuiltClauses st.world record.name built) old := by
    intro old hold hdifferent ordered
    have hname := nameDifferent old hold hdifferent
    have hparent : old.key.parent ≠ record.name := by
      intro hequal
      have hnonempty := ordered.parent_nonempty
      rw [hequal, hspecEmpty] at hnonempty
      exact hnonempty rfl
    exact installBuiltClauses_preserves_recordOrdered_other st record.name
      built old hname hparent hshape hsource ordered
  constructor
  · intro old hold
    rw [installBuiltClauses_specializations] at hold
    have holdRegistry : old ∈ registry :=
      List.mem_append.mpr (Or.inl hold)
    have hdifferent : old ≠ record := by
      intro hequal
      subst old
      have hnames := invariant.uniqueNames
      have hcommitted : record ∈ st.world.specializations := hold
      have htwice : record.name ∈
          (st.world.specializations.map (fun item => item.name)) :=
        List.mem_map.mpr ⟨record, hcommitted, rfl⟩
      have hprovisional : record.name ∈
          st.provisional.map (fun item => item.name) :=
        List.mem_map.mpr ⟨record, hrecord, rfl⟩
      have happend :
          (st.world.specializations.map (fun item => item.name) ++
            st.provisional.map (fun item => item.name)).Nodup := by
        simpa [List.map_append] using hnames
      have hcross := (List.nodup_append.mp happend).2.2
      exact hcross record.name htwice record.name hprovisional rfl
    exact preserveOrdered old holdRegistry hdifferent
      (invariant.committed old hold)
  · intro old hold
    have holdRegistry : old ∈ registry :=
      List.mem_append.mpr (Or.inr hold)
    by_cases hequal : old = record
    · subst old
      exact Or.inr hroot
    · have hname := nameDifferent old holdRegistry hequal
      rcases invariant.provisional old hold with hempty | ordered
      · exact Or.inl ((installBuiltClauses_clausesOf_other st.world
          record.name old.name built hname).trans hempty)
      · exact Or.inr
          (preserveOrdered old holdRegistry hequal ordered)
  · exact installBuiltClauses_preserves_capturedFamiliesOrdered st.world
      record.name built hspecEmpty hmetaEmpty hsource invariant.captured
  · simpa [List.map_append] using invariant.uniqueNames

theorem markGain_nameFrame (st : SpecBuildState) (key : SpecKey)
    (name : String) (hreserved : st.isDefined name = true) :
    SpecNameFrame st (st.markGain key) name := by
  unfold SpecBuildState.markGain
  split
  · exact SpecNameFrame.refl st name hreserved
  · exact ⟨rfl, rfl, rfl, hreserved⟩

/-- All five mutually recursive builder entry points preserve any name that
    was live or provisionally reserved before the call. -/
structure BuildFrameAtFuel (fuel : Nat) : Prop where
  request : ∀ st parent actuals after result name,
    st.isDefined name = true →
    buildSpecRequest fuel st parent actuals = some (after, result) →
    SpecNameFrame st after name
  clauses : ∀ st key specName candidates after built name,
    st.isDefined name = true →
    buildSpecClauses fuel st key specName candidates = some (after, built) →
    SpecNameFrame st after name
  goals : ∀ st binding goals after rewritten name,
    st.isDefined name = true →
    buildProfileGoals fuel st binding goals = some (after, rewritten) →
    SpecNameFrame st after name
  goal : ∀ st binding goal after rewritten name,
    st.isDefined name = true →
    buildProfileGoal fuel st binding goal = some (after, rewritten) →
    SpecNameFrame st after name
  branches : ∀ st binding branches after rewritten name,
    st.isDefined name = true →
    buildProfileBranches fuel st binding branches = some (after, rewritten) →
    SpecNameFrame st after name

private theorem buildFrameAtFuel_zero : BuildFrameAtFuel 0 := by
  constructor
  · intro st parent actuals after result name hreserved hbuild
    simp [buildSpecRequest] at hbuild
  · intro st key specName candidates after built name hreserved hbuild
    cases candidates with
    | nil =>
        simp [buildSpecClauses] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecNameFrame.refl st name hreserved
    | cons candidate rest => simp [buildSpecClauses] at hbuild
  · intro st binding goals after rewritten name hreserved hbuild
    cases goals with
    | nil =>
        simp [buildProfileGoals] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecNameFrame.refl st name hreserved
    | cons goal rest => simp [buildProfileGoals] at hbuild
  · intro st binding goal after rewritten name hreserved hbuild
    simp [buildProfileGoal] at hbuild
  · intro st binding branches after rewritten name hreserved hbuild
    cases branches with
    | nil =>
        simp [buildProfileBranches] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecNameFrame.refl st name hreserved
    | cons branch rest => simp [buildProfileBranches] at hbuild

private theorem buildProfileGoals_nameFrame_succ (fuel : Nat)
    (ih : BuildFrameAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (goals : List Goal) (after : SpecBuildState) (rewritten : List Goal)
    (name : String) (hreserved : st.isDefined name = true)
    (hbuild : buildProfileGoals (fuel + 1) st binding goals =
      some (after, rewritten)) :
    SpecNameFrame st after name := by
  cases goals with
  | nil =>
      simp [buildProfileGoals] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecNameFrame.refl st name hreserved
  | cons goal rest =>
      simp only [buildProfileGoals] at hbuild
      cases hgoal : buildProfileGoal fuel st binding goal with
      | none => simp [hgoal] at hbuild
      | some goalResult =>
          rcases goalResult with ⟨afterGoal, rewrittenGoal⟩
          simp only [hgoal] at hbuild
          cases hrest : buildProfileGoals fuel afterGoal binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goal st binding goal afterGoal rewrittenGoal
                name hreserved hgoal
              have hsecond := ih.goals afterGoal binding rest afterRest
                rewrittenRest name hfirst.reserved hrest
              exact hfirst.trans hsecond

private theorem buildProfileBranches_nameFrame_succ (fuel : Nat)
    (ih : BuildFrameAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (branches : List (Atom × List Goal)) (after : SpecBuildState)
    (rewritten : List (Atom × List Goal)) (name : String)
    (hreserved : st.isDefined name = true)
    (hbuild : buildProfileBranches (fuel + 1) st binding branches =
      some (after, rewritten)) :
    SpecNameFrame st after name := by
  cases branches with
  | nil =>
      simp [buildProfileBranches] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecNameFrame.refl st name hreserved
  | cons branch rest =>
      rcases branch with ⟨tmpl, goals⟩
      simp only [buildProfileBranches] at hbuild
      cases hgoals : buildProfileGoals fuel st binding goals with
      | none => simp [hgoals] at hbuild
      | some goalsResult =>
          rcases goalsResult with ⟨afterGoals, rewrittenGoals⟩
          simp only [hgoals] at hbuild
          cases hrest : buildProfileBranches fuel afterGoals binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goals st binding goals afterGoals
                rewrittenGoals name hreserved hgoals
              have hsecond := ih.branches afterGoals binding rest afterRest
                rewrittenRest name hfirst.reserved hrest
              exact hfirst.trans hsecond

private theorem buildProfileGoal_nameFrame_succ (fuel : Nat)
    (ih : BuildFrameAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (goal : Goal) (after : SpecBuildState) (rewritten : Goal)
    (name : String) (hreserved : st.isDefined name = true)
    (hbuild : buildProfileGoal (fuel + 1) st binding goal =
      some (after, rewritten)) :
    SpecNameFrame st after name := by
  cases goal with
  | call f args res =>
      simp only [buildProfileGoal] at hbuild
      cases hrequest : buildSpecRequest fuel st f
          (args.map (Metta.Subst.apply binding)) with
      | none => simp [hrequest] at hbuild
      | some requestResult =>
          rcases requestResult with ⟨next, found⟩
          simp only [hrequest] at hbuild
          cases found with
          | none =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st f
                (args.map (Metta.Subst.apply binding)) next none name
                hreserved hrequest
          | some specName =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st f
                (args.map (Metta.Subst.apply binding)) next (some specName)
                name hreserved hrequest
  | catchg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals name hreserved hsub
  | softcut tmpl sub thn els =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨afterSub, sub'⟩
          simp only [hsub] at hbuild
          cases hthen : buildProfileGoals fuel afterSub binding thn with
          | none => simp [hthen] at hbuild
          | some thenResult =>
              rcases thenResult with ⟨afterThen, thn'⟩
              simp only [hthen] at hbuild
              cases helse : buildProfileGoals fuel afterThen binding els with
              | none => simp [helse] at hbuild
              | some elseResult =>
                  rcases elseResult with ⟨afterElse, els'⟩
                  simp [helse] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  have hfirst := ih.goals st binding sub afterSub sub' name
                    hreserved hsub
                  have hsecond := ih.goals afterSub binding thn afterThen thn'
                    name hfirst.reserved hthen
                  have hthird := ih.goals afterThen binding els afterElse els'
                    name hsecond.reserved helse
                  exact (hfirst.trans hsecond).trans hthird
  | findall tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals name hreserved hsub
  | onceg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals name hreserved hsub
  | transactiong tmpl sub =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals name hreserved hsub
  | amb branches res =>
      simp only [buildProfileGoal] at hbuild
      cases hbranches : buildProfileBranches fuel st binding branches with
      | none => simp [hbranches] at hbuild
      | some branchResult =>
          rcases branchResult with ⟨next, branches'⟩
          simp [hbranches] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.branches st binding branches next branches' name hreserved
            hbranches
  | ite cond thn els res =>
      simp only [buildProfileGoal] at hbuild
      cases hthen : buildProfileGoals fuel st binding thn.2 with
      | none => simp [hthen] at hbuild
      | some thenResult =>
          rcases thenResult with ⟨afterThen, thnGoals⟩
          simp only [hthen] at hbuild
          cases helse : buildProfileGoals fuel afterThen binding els.2 with
          | none => simp [helse] at hbuild
          | some elseResult =>
              rcases elseResult with ⟨afterElse, elsGoals⟩
              simp [helse] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goals st binding thn.2 afterThen thnGoals name
                hreserved hthen
              have hsecond := ih.goals afterThen binding els.2 afterElse
                elsGoals name hfirst.reserved helse
              exact hfirst.trans hsecond
  | _ =>
      simp [buildProfileGoal] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecNameFrame.refl st name hreserved

private theorem buildSpecClauses_nameFrame_succ (fuel : Nat)
    (ih : BuildFrameAtFuel fuel) (st : SpecBuildState) (key : SpecKey)
    (specName : String) (candidates : List SpecClauseCandidate)
    (after : SpecBuildState) (built : List BuiltSpecClause) (name : String)
    (hreserved : st.isDefined name = true)
    (hbuild : buildSpecClauses (fuel + 1) st key specName candidates =
      some (after, built)) :
    SpecNameFrame st after name := by
  cases candidates with
  | nil =>
      simp [buildSpecClauses] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecNameFrame.refl st name hreserved
  | cons candidate rest =>
      simp only [buildSpecClauses] at hbuild
      let instantiated := instantiateGoals candidate.binding
        candidate.captured.compiled.body
      let gained := profileDynamicUseGoals st.isDefined st.isBin instantiated
      let base := specializeClauseGuarded st.isDefined st.isBin
        candidate.binding candidate.captured.compiled
      let gainedState := if gained then st.markGain key else st
      have hgain : SpecNameFrame st gainedState name := by
        dsimp only [gainedState]
        split
        · exact markGain_nameFrame st key name hreserved
        · exact SpecNameFrame.refl st name hreserved
      cases hbody : buildProfileGoals fuel gainedState candidate.binding
          base.body with
      | none => simp [instantiated, gained, base, gainedState, hbody] at hbuild
      | some bodyResult =>
          rcases bodyResult with ⟨afterBody, body⟩
          simp only [instantiated, gained, base, gainedState, hbody] at hbuild
          split at hbuild
          · contradiction
          · cases hrest : buildSpecClauses fuel afterBody key specName rest with
            | none => simp [hrest] at hbuild
            | some restResult =>
                rcases restResult with ⟨afterRest, builtRest⟩
                simp [hrest] at hbuild
                rcases hbuild with ⟨rfl, rfl⟩
                have hbodyFrame := ih.goals gainedState candidate.binding
                  base.body afterBody body name hgain.reserved hbody
                have hrestFrame := ih.clauses afterBody key specName rest
                  afterRest builtRest name hbodyFrame.reserved hrest
                exact (hgain.trans hbodyFrame).trans hrestFrame

private theorem buildSpecRequest_nameFrame_succ (fuel : Nat)
    (ih : BuildFrameAtFuel fuel) (st : SpecBuildState) (parent : String)
    (actuals : List Atom) (after : SpecBuildState) (result : Option String)
    (name : String) (hreserved : st.isDefined name = true)
    (hbuild : buildSpecRequest (fuel + 1) st parent actuals =
      some (after, result)) :
    SpecNameFrame st after name := by
  cases hdiscover : discoverSpecialization st.isSpecializable st.hasMeta
      parent actuals st.world.metaClauses with
  | none =>
      simp [buildSpecRequest, hdiscover] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecNameFrame.refl st name hreserved
  | some candidate =>
      cases hsafe : candidate.clauses.all SpecClauseCandidate.safe with
      | false =>
          simp [buildSpecRequest, hdiscover, hsafe] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact SpecNameFrame.refl st name hreserved
      | true =>
          cases hrecord : st.findRecord? candidate.key with
          | some record =>
              simp [buildSpecRequest, hdiscover, hsafe, hrecord] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact SpecNameFrame.refl st name hreserved
          | none =>
              let record : SpecRecord :=
                { key := candidate.key
                  name := specializationName candidate.key }
              cases hcollision : st.isNameOccupied record.name with
              | true =>
                  simp [buildSpecRequest, hdiscover, hsafe, hrecord, record,
                    hcollision] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  exact SpecNameFrame.refl st name hreserved
              | false =>
                  let registered : SpecBuildState :=
                    { st with
                        provisional := st.provisional ++ [record]
                        pending := st.pending ++ [candidate.key]
                        world := installCopiedTypes st.world parent record.name }
                  cases hclauses : buildSpecClauses fuel registered candidate.key
                      record.name candidate.clauses with
                  | none =>
                      simp [buildSpecRequest, hdiscover, hsafe, hrecord, record,
                        registered, hcollision, hclauses] at hbuild
                  | some clausesResult =>
                      rcases clausesResult with ⟨expanded, built⟩
                      simp [buildSpecRequest, hdiscover, hsafe, hrecord, record,
                        registered, hcollision, hclauses] at hbuild
                      rcases hbuild with ⟨rfl, rfl⟩
                      have hregistered := registerSpecialization_nameFrame st
                        name parent record.name record hreserved
                      have hrecursive := ih.clauses registered candidate.key
                        record.name candidate.clauses expanded built name
                        hregistered.reserved hclauses
                      have hdifferent : name ≠ record.name := by
                        intro hequal
                        have hoccupied : st.isNameOccupied name = true := by
                          simp [SpecBuildState.isNameOccupied, hreserved]
                        rw [← hequal] at hcollision
                        rw [hoccupied] at hcollision
                        contradiction
                      have hshape := buildSpecClauses_provenance_shape fuel
                        registered candidate.key record.name candidate.clauses
                        expanded built hclauses
                      have hsource := buildSpecClauses_source_defines fuel
                        registered candidate.key record.name candidate.clauses
                        expanded built hclauses
                      have hinstalled := installBuiltClauses_nameFrame expanded
                        name record.name built hdifferent
                        (fun item hitem => (hshape item hitem).1)
                        hsource hrecursive.reserved
                      have hfinished : SpecNameFrame expanded
                          { expanded with
                              world := installBuiltClauses expanded.world
                                record.name built
                              pending := expanded.pending.filter
                                (· != candidate.key)
                              expanded := expanded.expanded ++ [candidate.key] }
                          name := by
                        exact ⟨hinstalled.clauses, hinstalled.provenance,
                          hinstalled.metadata, hinstalled.reserved⟩
                      exact (hregistered.trans hrecursive).trans hfinished

theorem buildFrameAtFuel (fuel : Nat) : BuildFrameAtFuel fuel := by
  induction fuel with
  | zero => exact buildFrameAtFuel_zero
  | succ fuel ih =>
      constructor
      · intro st parent actuals after result name hreserved hbuild
        exact buildSpecRequest_nameFrame_succ fuel ih st parent actuals after
          result name hreserved hbuild
      · intro st key specName candidates after built name hreserved hbuild
        exact buildSpecClauses_nameFrame_succ fuel ih st key specName candidates
          after built name hreserved hbuild
      · intro st binding goals after rewritten name hreserved hbuild
        exact buildProfileGoals_nameFrame_succ fuel ih st binding goals after
          rewritten name hreserved hbuild
      · intro st binding goal after rewritten name hreserved hbuild
        exact buildProfileGoal_nameFrame_succ fuel ih st binding goal after
          rewritten name hreserved hbuild
      · intro st binding branches after rewritten name hreserved hbuild
        exact buildProfileBranches_nameFrame_succ fuel ih st binding branches
          after rewritten name hreserved hbuild

/-- Recursive specialization construction cannot mutate any name already
    defined or reserved at transaction entry. -/
theorem buildSpecRequest_preserves_reserved_name (fuel : Nat)
    (st : SpecBuildState) (parent : String) (actuals : List Atom)
    (after : SpecBuildState) (result : Option String) (name : String)
    (hreserved : st.isDefined name = true)
    (hbuild : buildSpecRequest fuel st parent actuals = some (after, result)) :
    SpecNameFrame st after name :=
  (buildFrameAtFuel fuel).request st parent actuals after result name hreserved
    hbuild

theorem buildSpecClauses_preserves_reserved_name (fuel : Nat)
    (st : SpecBuildState) (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate) (after : SpecBuildState)
    (built : List BuiltSpecClause) (name : String)
    (hreserved : st.isDefined name = true)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built)) :
    SpecNameFrame st after name :=
  (buildFrameAtFuel fuel).clauses st key specName candidates after built name
    hreserved hbuild

/-- The real recursive builder, not an idealized constructor, supplies every
    constructional premise required by ordered resolution transport for a
    freshly installed root record. -/
theorem buildSpecClauses_install_recordOrdered
    (fuel : Nat) (st expanded : SpecBuildState) (parent : String)
    (actuals : List Atom) (candidate : SpecCandidate) (specName : String)
    (built : List BuiltSpecClause)
    (hdiscover : discoverSpecialization st.isSpecializable st.hasMeta parent
      actuals st.world.metaClauses = some candidate)
    (hcollision : st.isNameOccupied specName = false)
    (hcaptured : st.world.CapturedParentOrdered parent)
    (hbuild : buildSpecClauses fuel
      { st with
          provisional := st.provisional ++
            [{ key := candidate.key, name := specName }]
          pending := st.pending ++ [candidate.key]
          world := installCopiedTypes st.world parent specName }
      candidate.key specName candidate.clauses = some (expanded, built)) :
      PWorld.SpecializationRecordOrdered
        (installBuiltClauses expanded.world specName built)
        { key := candidate.key, name := specName } ∧
      PWorld.CapturedParentOrdered
        (installBuiltClauses expanded.world specName built) specName := by
  let record : SpecRecord := { key := candidate.key, name := specName }
  let registered : SpecBuildState :=
    { st with
        provisional := st.provisional ++ [record]
        pending := st.pending ++ [candidate.key]
        world := installCopiedTypes st.world parent specName }
  change buildSpecClauses fuel registered candidate.key specName
    candidate.clauses = some (expanded, built) at hbuild
  have hcandidates := discoverSpecialization_clauses_nonempty
    st.isSpecializable st.hasMeta parent actuals st.world.metaClauses
    candidate hdiscover
  have hparentInitial := discovered_parent_clause_order st.world parent
    st.isSpecializable st.hasMeta actuals candidate hcaptured hdiscover
  have hparentNonempty : st.world.clausesOf parent ≠ [] := by
    rw [hparentInitial]
    simpa using hcandidates
  have hparentReserved : st.isDefined parent = true := by
    simp [SpecBuildState.isDefined, hparentNonempty]
  have hspecEmptyInitial : st.world.clausesOf specName = [] := by
    cases hclauses : st.world.clausesOf specName with
    | nil => rfl
    | cons clause rest =>
        simp [SpecBuildState.isNameOccupied, SpecBuildState.isDefined,
          hclauses] at hcollision
  have hmetaEmptyInitial : st.world.capturedMetaOf specName = [] := by
    cases hmeta : st.world.capturedMetaOf specName with
    | nil => rfl
    | cons captured rest =>
        simp [SpecBuildState.isNameOccupied, hmeta] at hcollision
  have hprovenanceEmptyInitial : st.world.provenanceNamed specName = [] := by
    cases hprovenance : st.world.provenanceNamed specName with
    | nil => rfl
    | cons provenance rest =>
        simp [SpecBuildState.isNameOccupied, hprovenance] at hcollision
  have hdifferent : parent ≠ specName := by
    intro hequal
    subst specName
    exact hparentNonempty hspecEmptyInitial
  have hparentRegistered := registerSpecialization_nameFrame st parent parent
    specName record hparentReserved
  have hrootRegistered : SpecNameFrame st registered specName := by
    constructor
    · exact installCopiedTypes_clausesOf st.world parent specName specName
    · exact installCopiedTypes_provenanceNamed st.world parent specName
        specName
    · exact installCopiedTypes_capturedMetaOf st.world parent specName
        specName
    · simp [registered, SpecBuildState.isDefined, record]
  have hparentRecursive := buildSpecClauses_preserves_reserved_name fuel
    registered candidate.key specName candidate.clauses expanded built parent
    hparentRegistered.reserved hbuild
  have hrootRecursive := buildSpecClauses_preserves_reserved_name fuel
    registered candidate.key specName candidate.clauses expanded built specName
    hrootRegistered.reserved hbuild
  have hparentExpanded : expanded.world.clausesOf parent =
      candidate.clauses.reverse.map
        (fun clause => clause.captured.compiled) := by
    rw [hparentRecursive.clauses]
    rw [hparentRegistered.clauses]
    exact hparentInitial
  have hspecEmptyExpanded : expanded.world.clausesOf specName = [] := by
    rw [hrootRecursive.clauses]
    rw [hrootRegistered.clauses]
    exact hspecEmptyInitial
  have hmetaEmptyExpanded : expanded.world.capturedMetaOf specName = [] := by
    rw [hrootRecursive.metadata]
    rw [hrootRegistered.metadata]
    exact hmetaEmptyInitial
  have hpriorInitial : st.world.recordProvenance record = [] := by
    unfold PWorld.provenanceNamed at hprovenanceEmptyInitial
    unfold PWorld.recordProvenance
    have := congrArg
      (List.filter (fun provenance : SpecClauseProvenance =>
        provenance.parent == record.key.parent)) hprovenanceEmptyInitial
    simpa [List.filter_filter, Bool.and_comm, Bool.and_left_comm,
      Bool.and_assoc, record] using this
  have hpriorExpanded : expanded.world.recordProvenance record = [] := by
    rw [hrootRecursive.recordProvenance record rfl]
    rw [hrootRegistered.recordProvenance record rfl]
    exact hpriorInitial
  have hkeyParent := discoverSpecialization_parent st.isSpecializable
    st.hasMeta parent actuals st.world.metaClauses candidate hdiscover
  have hkeyDifferent : candidate.key.parent ≠ specName := by
    rw [hkeyParent]
    exact hdifferent
  have hparentExpandedKey : expanded.world.clausesOf candidate.key.parent =
      candidate.clauses.reverse.map
        (fun clause => clause.captured.compiled) := by
    rw [hkeyParent]
    exact hparentExpanded
  constructor
  · exact installBuiltClauses_recordOrdered_of_build fuel registered expanded
      candidate.key specName candidate.clauses built hbuild hcandidates
      hkeyDifferent hspecEmptyExpanded hparentExpandedKey hpriorExpanded
  · exact installBuiltClauses_capturedParentOrdered expanded.world specName
      built hspecEmptyExpanded hmetaEmptyExpanded
      (buildSpecClauses_source_defines fuel registered candidate.key specName
        candidate.clauses expanded built hbuild)

/-! ## Whole-transaction constructional preservation -/

structure SpecBuildOrderedFrame (before after : SpecBuildState) : Prop where
  valid : SpecBuildOrdered after
  worldRegistry : after.world.specializations = before.world.specializations
  provisional : List.Sublist before.provisional after.provisional

/-- The complete registry visible inside one atomic build: already committed
    rows followed by provisional rows. -/
def SpecBuildState.registry (st : SpecBuildState) : List SpecRecord :=
  st.world.specializations ++ st.provisional

/-- Recursive construction only grows the complete transaction registry.
    This is the transport fact needed to retain child-call witnesses while
    later siblings are built. -/
theorem SpecBuildOrderedFrame.registrySublist {before after : SpecBuildState}
    (frame : SpecBuildOrderedFrame before after) :
    before.registry.Sublist after.registry := by
  unfold SpecBuildState.registry
  rw [frame.worldRegistry]
  exact (List.Sublist.refl before.world.specializations).append
    frame.provisional

theorem SpecBuildOrderedFrame.refl (st : SpecBuildState)
    (invariant : SpecBuildOrdered st) : SpecBuildOrderedFrame st st :=
  ⟨invariant, rfl, List.Sublist.refl _⟩

theorem SpecBuildOrderedFrame.trans {first second third : SpecBuildState}
    (h₁ : SpecBuildOrderedFrame first second)
    (h₂ : SpecBuildOrderedFrame second third) :
    SpecBuildOrderedFrame first third :=
  ⟨h₂.valid, h₂.worldRegistry.trans h₁.worldRegistry,
    h₁.provisional.trans h₂.provisional⟩

/-- Mutual induction hypothesis for all five recursive builder entry points.
    Besides the construction invariant it carries the monotone provisional
    registry needed to identify an installed recursive root. -/
structure BuildOrderedAtFuel (fuel : Nat) : Prop where
  request : ∀ st parent actuals after result,
    SpecBuildOrdered st →
    buildSpecRequest fuel st parent actuals = some (after, result) →
    SpecBuildOrderedFrame st after
  clauses : ∀ st key specName candidates after built,
    SpecBuildOrdered st →
    buildSpecClauses fuel st key specName candidates = some (after, built) →
    SpecBuildOrderedFrame st after
  goals : ∀ st binding goals after rewritten,
    SpecBuildOrdered st →
    buildProfileGoals fuel st binding goals = some (after, rewritten) →
    SpecBuildOrderedFrame st after
  goal : ∀ st binding goal after rewritten,
    SpecBuildOrdered st →
    buildProfileGoal fuel st binding goal = some (after, rewritten) →
    SpecBuildOrderedFrame st after
  branches : ∀ st binding branches after rewritten,
    SpecBuildOrdered st →
    buildProfileBranches fuel st binding branches = some (after, rewritten) →
    SpecBuildOrderedFrame st after

private theorem buildOrderedAtFuel_zero : BuildOrderedAtFuel 0 := by
  constructor
  · intro st parent actuals after result invariant hbuild
    simp [buildSpecRequest] at hbuild
  · intro st key specName candidates after built invariant hbuild
    cases candidates with
    | nil =>
        simp [buildSpecClauses] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecBuildOrderedFrame.refl st invariant
    | cons candidate rest => simp [buildSpecClauses] at hbuild
  · intro st binding goals after rewritten invariant hbuild
    cases goals with
    | nil =>
        simp [buildProfileGoals] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecBuildOrderedFrame.refl st invariant
    | cons goal rest => simp [buildProfileGoals] at hbuild
  · intro st binding goal after rewritten invariant hbuild
    simp [buildProfileGoal] at hbuild
  · intro st binding branches after rewritten invariant hbuild
    cases branches with
    | nil =>
        simp [buildProfileBranches] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact SpecBuildOrderedFrame.refl st invariant
    | cons branch rest => simp [buildProfileBranches] at hbuild

private theorem buildProfileGoals_ordered_succ (fuel : Nat)
    (ih : BuildOrderedAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (goals : List Goal) (after : SpecBuildState) (rewritten : List Goal)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileGoals (fuel + 1) st binding goals =
      some (after, rewritten)) :
    SpecBuildOrderedFrame st after := by
  cases goals with
  | nil =>
      simp [buildProfileGoals] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecBuildOrderedFrame.refl st invariant
  | cons goal rest =>
      simp only [buildProfileGoals] at hbuild
      cases hgoal : buildProfileGoal fuel st binding goal with
      | none => simp [hgoal] at hbuild
      | some goalResult =>
          rcases goalResult with ⟨afterGoal, rewrittenGoal⟩
          simp only [hgoal] at hbuild
          cases hrest : buildProfileGoals fuel afterGoal binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goal st binding goal afterGoal rewrittenGoal
                invariant hgoal
              have hsecond := ih.goals afterGoal binding rest afterRest
                rewrittenRest hfirst.valid hrest
              exact hfirst.trans hsecond

private theorem buildProfileBranches_ordered_succ (fuel : Nat)
    (ih : BuildOrderedAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (branches : List (Atom × List Goal)) (after : SpecBuildState)
    (rewritten : List (Atom × List Goal))
    (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileBranches (fuel + 1) st binding branches =
      some (after, rewritten)) :
    SpecBuildOrderedFrame st after := by
  cases branches with
  | nil =>
      simp [buildProfileBranches] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecBuildOrderedFrame.refl st invariant
  | cons branch rest =>
      rcases branch with ⟨tmpl, goals⟩
      simp only [buildProfileBranches] at hbuild
      cases hgoals : buildProfileGoals fuel st binding goals with
      | none => simp [hgoals] at hbuild
      | some goalsResult =>
          rcases goalsResult with ⟨afterGoals, rewrittenGoals⟩
          simp only [hgoals] at hbuild
          cases hrest : buildProfileBranches fuel afterGoals binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goals st binding goals afterGoals
                rewrittenGoals invariant hgoals
              have hsecond := ih.branches afterGoals binding rest afterRest
                rewrittenRest hfirst.valid hrest
              exact hfirst.trans hsecond

private theorem buildProfileGoal_ordered_succ (fuel : Nat)
    (ih : BuildOrderedAtFuel fuel) (st : SpecBuildState) (binding : Subst)
    (goal : Goal) (after : SpecBuildState) (rewritten : Goal)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileGoal (fuel + 1) st binding goal =
      some (after, rewritten)) :
    SpecBuildOrderedFrame st after := by
  cases goal with
  | call f args res =>
      simp only [buildProfileGoal] at hbuild
      cases hrequest : buildSpecRequest fuel st f
          (args.map (Metta.Subst.apply binding)) with
      | none => simp [hrequest] at hbuild
      | some requestResult =>
          rcases requestResult with ⟨next, found⟩
          simp only [hrequest] at hbuild
          cases found with
          | none =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st f (args.map (Metta.Subst.apply binding))
                next none invariant hrequest
          | some specName =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st f (args.map (Metta.Subst.apply binding))
                next (some specName) invariant hrequest
  | catchg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals invariant hsub
  | softcut tmpl sub thn els =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨afterSub, sub'⟩
          simp only [hsub] at hbuild
          cases hthen : buildProfileGoals fuel afterSub binding thn with
          | none => simp [hthen] at hbuild
          | some thenResult =>
              rcases thenResult with ⟨afterThen, thn'⟩
              simp only [hthen] at hbuild
              cases helse : buildProfileGoals fuel afterThen binding els with
              | none => simp [helse] at hbuild
              | some elseResult =>
                  rcases elseResult with ⟨afterElse, els'⟩
                  simp [helse] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  have hfirst := ih.goals st binding sub afterSub sub'
                    invariant hsub
                  have hsecond := ih.goals afterSub binding thn afterThen thn'
                    hfirst.valid hthen
                  have hthird := ih.goals afterThen binding els afterElse els'
                    hsecond.valid helse
                  exact (hfirst.trans hsecond).trans hthird
  | findall tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals invariant hsub
  | onceg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals invariant hsub
  | transactiong tmpl sub =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, goals⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next goals invariant hsub
  | amb branches res =>
      simp only [buildProfileGoal] at hbuild
      cases hbranches : buildProfileBranches fuel st binding branches with
      | none => simp [hbranches] at hbuild
      | some branchResult =>
          rcases branchResult with ⟨next, branches'⟩
          simp [hbranches] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.branches st binding branches next branches' invariant
            hbranches
  | ite cond thn els res =>
      simp only [buildProfileGoal] at hbuild
      cases hthen : buildProfileGoals fuel st binding thn.2 with
      | none => simp [hthen] at hbuild
      | some thenResult =>
          rcases thenResult with ⟨afterThen, thnGoals⟩
          simp only [hthen] at hbuild
          cases helse : buildProfileGoals fuel afterThen binding els.2 with
          | none => simp [helse] at hbuild
          | some elseResult =>
              rcases elseResult with ⟨afterElse, elsGoals⟩
              simp [helse] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hfirst := ih.goals st binding thn.2 afterThen thnGoals
                invariant hthen
              have hsecond := ih.goals afterThen binding els.2 afterElse
                elsGoals hfirst.valid helse
              exact hfirst.trans hsecond
  | _ =>
      simp [buildProfileGoal] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecBuildOrderedFrame.refl st invariant

private theorem buildSpecClauses_ordered_succ (fuel : Nat)
    (ih : BuildOrderedAtFuel fuel) (st : SpecBuildState) (key : SpecKey)
    (specName : String) (candidates : List SpecClauseCandidate)
    (after : SpecBuildState) (built : List BuiltSpecClause)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildSpecClauses (fuel + 1) st key specName candidates =
      some (after, built)) :
    SpecBuildOrderedFrame st after := by
  cases candidates with
  | nil =>
      simp [buildSpecClauses] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecBuildOrderedFrame.refl st invariant
  | cons candidate rest =>
      simp only [buildSpecClauses] at hbuild
      let instantiated := instantiateGoals candidate.binding
        candidate.captured.compiled.body
      let gained := profileDynamicUseGoals st.isDefined st.isBin instantiated
      let base := specializeClauseGuarded st.isDefined st.isBin
        candidate.binding candidate.captured.compiled
      let gainedState := if gained then st.markGain key else st
      have hgain : SpecBuildOrderedFrame st gainedState := by
        dsimp only [gainedState]
        split
        · refine ⟨invariant.markGain st key, ?_, ?_⟩
          · unfold SpecBuildState.markGain
            split <;> rfl
          · unfold SpecBuildState.markGain
            split <;> exact List.Sublist.refl _
        · exact SpecBuildOrderedFrame.refl st invariant
      cases hbody : buildProfileGoals fuel gainedState candidate.binding
          base.body with
      | none => simp [instantiated, gained, base, gainedState, hbody] at hbuild
      | some bodyResult =>
          rcases bodyResult with ⟨afterBody, body⟩
          simp only [instantiated, gained, base, gainedState, hbody] at hbuild
          split at hbuild
          · contradiction
          · cases hrest : buildSpecClauses fuel afterBody key specName rest with
            | none => simp [hrest] at hbuild
            | some restResult =>
                rcases restResult with ⟨afterRest, builtRest⟩
                simp [hrest] at hbuild
                rcases hbuild with ⟨rfl, rfl⟩
                have hbodyFrame := ih.goals gainedState candidate.binding
                  base.body afterBody body hgain.valid hbody
                have hrestFrame := ih.clauses afterBody key specName rest
                  afterRest builtRest hbodyFrame.valid hrest
                exact (hgain.trans hbodyFrame).trans hrestFrame

private theorem buildSpecRequest_ordered_succ (fuel : Nat)
    (ih : BuildOrderedAtFuel fuel) (st : SpecBuildState) (parent : String)
    (actuals : List Atom) (after : SpecBuildState) (result : Option String)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildSpecRequest (fuel + 1) st parent actuals =
      some (after, result)) :
    SpecBuildOrderedFrame st after := by
  cases hdiscover : discoverSpecialization st.isSpecializable st.hasMeta
      parent actuals st.world.metaClauses with
  | none =>
      simp [buildSpecRequest, hdiscover] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact SpecBuildOrderedFrame.refl st invariant
  | some candidate =>
      cases hsafe : candidate.clauses.all SpecClauseCandidate.safe with
      | false =>
          simp [buildSpecRequest, hdiscover, hsafe] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact SpecBuildOrderedFrame.refl st invariant
      | true =>
          cases hfound : st.findRecord? candidate.key with
          | some found =>
              simp [buildSpecRequest, hdiscover, hsafe, hfound] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact SpecBuildOrderedFrame.refl st invariant
          | none =>
              let record : SpecRecord :=
                { key := candidate.key
                  name := specializationName candidate.key }
              cases hcollision : st.isNameOccupied record.name with
              | true =>
                  simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                    hcollision] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  exact SpecBuildOrderedFrame.refl st invariant
              | false =>
                  let registered : SpecBuildState :=
                    { st with
                        provisional := st.provisional ++ [record]
                        pending := st.pending ++ [candidate.key]
                        world := installCopiedTypes st.world parent record.name }
                  cases hclauses : buildSpecClauses fuel registered
                      candidate.key record.name candidate.clauses with
                  | none =>
                      simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                        registered, hcollision, hclauses] at hbuild
                  | some clausesResult =>
                      rcases clausesResult with ⟨expanded, built⟩
                      simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                        registered, hcollision, hclauses] at hbuild
                      rcases hbuild with ⟨rfl, rfl⟩
                      have hspecEmpty : st.world.clausesOf record.name = [] := by
                        cases hclauses : st.world.clausesOf record.name with
                        | nil => rfl
                        | cons clause rest =>
                            simp [SpecBuildState.isNameOccupied,
                              SpecBuildState.isDefined, hclauses] at hcollision
                      have hmetaEmpty : st.world.capturedMetaOf record.name =
                          [] := by
                        cases hmeta : st.world.capturedMetaOf record.name with
                        | nil => rfl
                        | cons captured rest =>
                            simp [SpecBuildState.isNameOccupied, hmeta] at hcollision
                      have hnameFresh :=
                        invariant.name_not_mem_of_not_occupied record.name
                          hcollision
                      have hregistered : SpecBuildOrdered registered := by
                        exact invariant.register st parent record hspecEmpty
                          hnameFresh
                      have hrecursive := ih.clauses registered candidate.key
                        record.name candidate.clauses expanded built hregistered
                        hclauses
                      have hrecordRegistered : record ∈ registered.provisional :=
                        by simp [registered]
                      have hrecordExpanded : record ∈ expanded.provisional :=
                        List.Sublist.mem hrecordRegistered
                          hrecursive.provisional
                      have hrootDefined : registered.isDefined record.name =
                          true := by
                        simp [registered, SpecBuildState.isDefined, record]
                      have hrootFrame :=
                        buildSpecClauses_preserves_reserved_name fuel registered
                          candidate.key record.name candidate.clauses expanded
                          built record.name hrootDefined hclauses
                      have hspecExpanded :
                          expanded.world.clausesOf record.name = [] := by
                        rw [hrootFrame.clauses]
                        rw [installCopiedTypes_clausesOf]
                        exact hspecEmpty
                      have hmetaExpanded :
                          expanded.world.capturedMetaOf record.name = [] := by
                        rw [hrootFrame.metadata]
                        rw [installCopiedTypes_capturedMetaOf]
                        exact hmetaEmpty
                      have hcaptured := invariant.captured parent
                        (discoverSpecialization_captured_nonempty
                          st.isSpecializable st.hasMeta parent actuals st.world
                          candidate hdiscover)
                      have hroot := buildSpecClauses_install_recordOrdered fuel
                        st expanded parent actuals candidate record.name built
                        hdiscover hcollision hcaptured hclauses
                      have hshape := buildSpecClauses_provenance_shape fuel
                        registered candidate.key record.name candidate.clauses
                        expanded built hclauses
                      have hsource := buildSpecClauses_source_defines fuel
                        registered candidate.key record.name candidate.clauses
                        expanded built hclauses
                      have hinstalled := hrecursive.valid.install expanded
                        record built hrecordExpanded hspecExpanded hmetaExpanded
                        (fun item hitem => (hshape item hitem).1) hsource hroot.1
                      have hfinished : SpecBuildOrdered
                          { expanded with
                            world := installBuiltClauses expanded.world
                              record.name built
                            pending := expanded.pending.filter
                              (· != candidate.key)
                            expanded := expanded.expanded ++ [candidate.key] } :=
                        ⟨hinstalled.committed, hinstalled.provisional,
                          hinstalled.captured, hinstalled.uniqueNames⟩
                      have hregisteredSub :
                          List.Sublist st.provisional registered.provisional := by
                        simp only [registered]
                        exact List.sublist_append_left _ _
                      have hworldRegistry :
                          (installBuiltClauses expanded.world record.name
                              built).specializations =
                            st.world.specializations := by
                        rw [installBuiltClauses_specializations,
                          hrecursive.worldRegistry]
                        exact installCopiedTypes_specializations st.world
                          parent record.name
                      exact ⟨hfinished, hworldRegistry,
                        hregisteredSub.trans hrecursive.provisional⟩

theorem buildOrderedAtFuel (fuel : Nat) : BuildOrderedAtFuel fuel := by
  induction fuel with
  | zero => exact buildOrderedAtFuel_zero
  | succ fuel ih =>
      constructor
      · intro st parent actuals after result invariant hbuild
        exact buildSpecRequest_ordered_succ fuel ih st parent actuals after
          result invariant hbuild
      · intro st key specName candidates after built invariant hbuild
        exact buildSpecClauses_ordered_succ fuel ih st key specName candidates
          after built invariant hbuild
      · intro st binding goals after rewritten invariant hbuild
        exact buildProfileGoals_ordered_succ fuel ih st binding goals after
          rewritten invariant hbuild
      · intro st binding goal after rewritten invariant hbuild
        exact buildProfileGoal_ordered_succ fuel ih st binding goal after
          rewritten invariant hbuild
      · intro st binding branches after rewritten invariant hbuild
        exact buildProfileBranches_ordered_succ fuel ih st binding branches
          after rewritten invariant hbuild

/-- The actual recursive request preserves all constructional registry and
    captured-family invariants, not merely the executable Boolean checker. -/
theorem buildSpecRequest_preserves_ordered (fuel : Nat)
    (st : SpecBuildState) (parent : String) (actuals : List Atom)
    (after : SpecBuildState) (result : Option String)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildSpecRequest fuel st parent actuals = some (after, result)) :
    SpecBuildOrderedFrame st after :=
  (buildOrderedAtFuel fuel).request st parent actuals after result invariant
    hbuild

/-- A successful retargeting request carries a concrete registry row in the
    returned transaction state.  The row names the rewritten call and points
    back to the requested parent; this is constructional evidence from the
    real recursive builder, not an inversion of the public name or integrity
    checker. -/
theorem buildSpecRequest_success_record (fuel : Nat)
    (st after : SpecBuildState) (parent : String) (actuals : List Atom)
    (specName : String) (invariant : SpecBuildOrdered st)
    (hbuild : buildSpecRequest fuel st parent actuals =
      some (after, some specName)) :
    ∃ record, record ∈ after.registry ∧ record.name = specName ∧
      record.key.parent = parent := by
  cases fuel with
  | zero => simp [buildSpecRequest] at hbuild
  | succ fuel =>
      cases hdiscover : discoverSpecialization st.isSpecializable st.hasMeta
          parent actuals st.world.metaClauses with
      | none => simp [buildSpecRequest, hdiscover] at hbuild
      | some candidate =>
          cases hsafe : candidate.clauses.all SpecClauseCandidate.safe with
          | false => simp [buildSpecRequest, hdiscover, hsafe] at hbuild
          | true =>
              cases hfound : st.findRecord? candidate.key with
              | some record =>
                  simp [buildSpecRequest, hdiscover, hsafe, hfound] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  have hfind : st.registry.find?
                      (fun item => item.key == candidate.key) = some record := by
                    simpa [SpecBuildState.registry,
                      SpecBuildState.findRecord?] using hfound
                  have hmember : record ∈ st.registry :=
                    List.mem_of_find?_eq_some hfind
                  have hparentKey : record.key.parent =
                      candidate.key.parent := by
                    have hselected := List.find?_some hfind
                    cases hrecordKey : record.key with
                    | mk recordParent recordBindings =>
                        cases hcandidateKey : candidate.key with
                        | mk candidateParent candidateBindings =>
                            rw [hrecordKey, hcandidateKey] at hselected
                            change ((recordParent == candidateParent) &&
                              (recordBindings == candidateBindings)) = true
                                at hselected
                            simpa [hrecordKey, hcandidateKey] using
                              (beq_iff_eq.mp
                                (Bool.and_eq_true_iff.mp hselected).1)
                  refine ⟨record, hmember, rfl, ?_⟩
                  rw [hparentKey]
                  exact discoverSpecialization_parent st.isSpecializable
                    st.hasMeta parent actuals st.world.metaClauses candidate
                    hdiscover
              | none =>
                  let record : SpecRecord :=
                    { key := candidate.key
                      name := specializationName candidate.key }
                  cases hcollision : st.isNameOccupied record.name with
                  | true =>
                      simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                        hcollision] at hbuild
                  | false =>
                      let registered : SpecBuildState :=
                        { st with
                            provisional := st.provisional ++ [record]
                            pending := st.pending ++ [candidate.key]
                            world := installCopiedTypes st.world parent
                              record.name }
                      cases hclauses : buildSpecClauses fuel registered
                          candidate.key record.name candidate.clauses with
                      | none =>
                          simp [buildSpecRequest, hdiscover, hsafe, hfound,
                            record, registered, hcollision, hclauses] at hbuild
                      | some clausesResult =>
                          rcases clausesResult with ⟨expanded, built⟩
                          simp [buildSpecRequest, hdiscover, hsafe, hfound,
                            record, registered, hcollision, hclauses] at hbuild
                          rcases hbuild with ⟨rfl, rfl⟩
                          have hspecEmpty :
                              st.world.clausesOf record.name = [] := by
                            cases hclausesAtName :
                                st.world.clausesOf record.name with
                            | nil => rfl
                            | cons clause rest =>
                                simp [SpecBuildState.isNameOccupied,
                                  SpecBuildState.isDefined, hclausesAtName]
                                  at hcollision
                          have hnameFresh :=
                            invariant.name_not_mem_of_not_occupied record.name
                              hcollision
                          have hregistered : SpecBuildOrdered registered := by
                            exact invariant.register st parent record hspecEmpty
                              hnameFresh
                          have hrecursive := (buildOrderedAtFuel fuel).clauses
                            registered candidate.key record.name
                            candidate.clauses expanded built hregistered
                            hclauses
                          have hregisteredMember :
                              record ∈ registered.registry := by
                            simp [SpecBuildState.registry, registered]
                          have hexpandedMember :
                              record ∈ expanded.registry :=
                            List.Sublist.mem hregisteredMember
                              hrecursive.registrySublist
                          have hfinishedMember : record ∈
                              ({ expanded with
                                world := installBuiltClauses expanded.world
                                  record.name built
                                pending := expanded.pending.filter
                                  (· != candidate.key)
                                expanded := expanded.expanded ++
                                  [candidate.key] } : SpecBuildState).registry := by
                            simpa [SpecBuildState.registry,
                              installBuiltClauses_specializations] using
                              hexpandedMember
                          refine ⟨record, hfinishedMember, rfl, ?_⟩
                          exact discoverSpecialization_parent
                            st.isSpecializable st.hasMeta parent actuals
                            st.world.metaClauses candidate hdiscover

/-- The executable global checker makes every committed registry row live.
    This lemma extracts only that structurally safe fact; exact clause equality
    continues to come from constructional proofs. -/
theorem PWorld.specializationProvenanceValid_record_nonempty (w : PWorld)
    (record : SpecRecord) (hchecked : w.specializationProvenanceValid = true)
    (hmember : record ∈ w.specializations) :
    w.clausesOf record.name ≠ [] := by
  simp only [PWorld.specializationProvenanceValid, Bool.and_eq_true] at hchecked
  have hrow := List.all_eq_true.mp hchecked.2 record hmember
  simp only [Bool.and_eq_true] at hrow
  intro hempty
  rw [hempty] at hrow
  simp at hrow

theorem SpecBuildOrdered.commit_preserves_recordOrdered
    (st : SpecBuildState) (record : SpecRecord)
    (ordered : st.world.SpecializationRecordOrdered record) :
    (st.commit).SpecializationRecordOrdered record := by
  constructor
  · simpa [SpecBuildState.commit, PWorld.clausesOf] using ordered.nonempty
  · simpa [SpecBuildState.commit, PWorld.clausesOf,
      PWorld.recordProvenance] using ordered.parentClauses
  · simpa [SpecBuildState.commit, PWorld.clausesOf,
      PWorld.recordProvenance] using ordered.executableClauses
  · intro provenance hmember
    have hmemberBefore :
        provenance ∈ st.world.recordProvenance record := by
      simpa [SpecBuildState.commit, PWorld.recordProvenance] using hmember
    exact ordered.exactHeads provenance hmemberBefore

theorem SpecBuildOrdered.world_well (st : SpecBuildState)
    (invariant : SpecBuildOrdered st)
    (hchecked : st.world.specializationProvenanceValid = true) :
    WellSpecializedWorld st.world := by
  exact ⟨hchecked, invariant.committed⟩

theorem SpecBuildOrdered.commit_well (st : SpecBuildState)
    (invariant : SpecBuildOrdered st)
    (hchecked : (st.commit).specializationProvenanceValid = true) :
    WellSpecializedWorld st.commit := by
  constructor
  · exact hchecked
  · intro record hmember
    change record ∈ st.world.specializations ++ st.provisional at hmember
    rcases List.mem_append.mp hmember with hold | hprovisional
    · exact SpecBuildOrdered.commit_preserves_recordOrdered st record
        (invariant.committed record hold)
    · rcases invariant.provisional record hprovisional with
        hempty | ordered
      · have hnonempty :=
          (st.commit).specializationProvenanceValid_record_nonempty record
            hchecked (by
              change record ∈ st.world.specializations ++ st.provisional
              exact List.mem_append.mpr (Or.inr hprovisional))
        have hcommitEmpty : (st.commit).clausesOf record.name = [] := by
          simpa [SpecBuildState.commit, PWorld.clausesOf] using hempty
        exact False.elim (hnonempty hcommitEmpty)
      · exact SpecBuildOrdered.commit_preserves_recordOrdered st record
          ordered

/-- Whichever branch the transaction boundary selects, a checked output has
    the full constructional `WellSpecializedWorld` postcondition. -/
theorem SpecBuildOrdered.committed_well (st : SpecBuildState)
    (invariant : SpecBuildOrdered st)
    (hchecked :
      PWorld.specializationProvenanceValid
        (if st.provisional.isEmpty then st.world else st.commit) = true) :
    WellSpecializedWorld
      (if st.provisional.isEmpty then st.world else st.commit) := by
  cases hempty : st.provisional.isEmpty with
  | true =>
      simp [hempty] at hchecked ⊢
      exact invariant.world_well st hchecked
  | false =>
      simp [hempty] at hchecked ⊢
      exact invariant.commit_well st hchecked

/-- Complete proof-facing invariant passed between successive specialization
    requests in a query tree. -/
structure SpecializationProfileInvariant (w : PWorld) : Prop where
  well : WellSpecializedWorld w
  captured : w.CapturedFamiliesOrdered
  uniqueNames : (w.specializations.map (fun record => record.name)).Nodup

theorem SpecBuildOrdered.commit_captured (st : SpecBuildState)
    (invariant : SpecBuildOrdered st) :
    (st.commit).CapturedFamiliesOrdered := by
  intro parent hnonempty
  have hbeforeNonempty : st.world.capturedMetaOf parent ≠ [] := by
    simpa [SpecBuildState.commit, PWorld.capturedMetaOf] using hnonempty
  have hbefore := invariant.captured parent hbeforeNonempty
  constructor
  simpa [SpecBuildState.commit, PWorld.clausesOf,
    PWorld.capturedMetaOf] using hbefore.clauses

theorem SpecBuildOrdered.committed_captured (st : SpecBuildState)
    (invariant : SpecBuildOrdered st) :
    PWorld.CapturedFamiliesOrdered
      (if st.provisional.isEmpty then st.world else st.commit) := by
  cases hempty : st.provisional.isEmpty with
  | true =>
      change st.world.CapturedFamiliesOrdered
      exact invariant.captured
  | false =>
      change (st.commit).CapturedFamiliesOrdered
      exact invariant.commit_captured st

theorem SpecBuildOrdered.committed_uniqueNames (st : SpecBuildState)
    (invariant : SpecBuildOrdered st) :
    ((PWorld.specializations
      (if st.provisional.isEmpty then st.world else st.commit)).map
        (fun record => record.name)).Nodup := by
  cases hempty : st.provisional.isEmpty with
  | true =>
      have hnil : st.provisional = [] := by simpa using hempty
      simpa [hempty, hnil, List.map_append] using invariant.uniqueNames
  | false =>
      simpa [hempty, SpecBuildState.commit, List.map_append] using
        invariant.uniqueNames

theorem SpecBuildOrdered.committed_profile (st : SpecBuildState)
    (invariant : SpecBuildOrdered st)
    (hchecked : PWorld.specializationProvenanceValid
      (if st.provisional.isEmpty then st.world else st.commit) = true) :
    SpecializationProfileInvariant
      (if st.provisional.isEmpty then st.world else st.commit) :=
  ⟨invariant.committed_well st hchecked,
   invariant.committed_captured st,
   invariant.committed_uniqueNames st⟩

theorem instantiateGoal_direct_binding (v f : String) (args : List Atom)
    (res : Atom) :
    instantiateGoal [(v, Atom.sym f)] (Goal.callDyn (Atom.var v) args res) =
      Goal.callDyn (Atom.sym f)
        (args.map (Metta.Subst.apply [(v, Atom.sym f)]))
        (Metta.Subst.apply [(v, Atom.sym f)] res) := by
  simp [instantiateGoal, Metta.Subst.apply, Metta.Subst.lookup]

theorem lowerConcreteGoal_defined (isDefined : String → Bool) (f : String)
    (args : List Atom) (res : Atom) (h : isDefined f = true) :
    lowerConcreteGoal isDefined (Goal.callDyn (Atom.sym f) args res) =
      Goal.call f args res := by
  simp [lowerConcreteGoal, h]

theorem lowerProfileGoal_defined (isDefined isBin : String → Bool)
    (f : String) (args : List Atom) (res : Atom)
    (h : isDefined f = true) :
    lowerProfileGoal isDefined isBin (Goal.callDyn (Atom.sym f) args res) =
      Goal.call f args res := by
  simp [lowerProfileGoal, h]

theorem lowerProfileGoal_builtin (isDefined isBin : String → Bool)
    (f : String) (args : List Atom) (res : Atom)
    (hdef : isDefined f = false) (hbin : isBin f = true) :
    lowerProfileGoal isDefined isBin (Goal.callDyn (Atom.sym f) args res) =
      Goal.bin f args res := by
  simp [lowerProfileGoal, hdef, hbin]

/-! ## Exact syntactic boundary of profile lowering -/

/- An independent specification of the only rewrites permitted in one
    profile-lowering pass.  In particular, arguments, results, templates,
    conditions, and world-effect operands are preserved verbatim; only a
    concrete dynamic-call head may change its goal constructor. -/
mutual
inductive ProfileGoalLowered (isDefined isBin : String → Bool) :
    Goal → Goal → Prop where
  | call (f : String) (args : List Atom) (res : Atom) :
      ProfileGoalLowered isDefined isBin (.call f args res) (.call f args res)
  | bin (op : String) (args : List Atom) (res : Atom) :
      ProfileGoalLowered isDefined isBin (.bin op args res) (.bin op args res)
  | dynDefined (f : String) (args : List Atom) (res : Atom)
      (hdef : isDefined f = true) :
      ProfileGoalLowered isDefined isBin (.callDyn (.sym f) args res)
        (.call f args res)
  | dynBuiltin (f : String) (args : List Atom) (res : Atom)
      (hdef : isDefined f = false) (hbin : isBin f = true) :
      ProfileGoalLowered isDefined isBin (.callDyn (.sym f) args res)
        (.bin f args res)
  | dynSymbolFallback (f : String) (args : List Atom) (res : Atom)
      (hdef : isDefined f = false) (hbin : isBin f = false) :
      ProfileGoalLowered isDefined isBin (.callDyn (.sym f) args res)
        (.callDyn (.sym f) args res)
  | dynPartialDefined (head : Atom) (base : String) (bound args : List Atom)
      (res : Atom) (hp : specPartialView? head = some (base, bound))
      (hdef : isDefined base = true) :
      ProfileGoalLowered isDefined isBin (.callDyn head args res)
        (.call base (bound ++ args) res)
  | dynPartialBuiltin (head : Atom) (base : String) (bound args : List Atom)
      (res : Atom) (hp : specPartialView? head = some (base, bound))
      (hdef : isDefined base = false) (hbin : isBin base = true) :
      ProfileGoalLowered isDefined isBin (.callDyn head args res)
        (.bin base (bound ++ args) res)
  | dynPartialFallback (head : Atom) (base : String) (bound args : List Atom)
      (res : Atom) (hp : specPartialView? head = some (base, bound))
      (hdef : isDefined base = false) (hbin : isBin base = false) :
      ProfileGoalLowered isDefined isBin (.callDyn head args res)
        (.callDyn head args res)
  | dynData (head : Atom) (args : List Atom) (res : Atom)
      (hns : ∀ f, head ≠ Atom.sym f)
      (hp : specPartialView? head = none) :
      ProfileGoalLowered isDefined isBin (.callDyn head args res)
        (.callDyn head args res)
  | evalg (val res : Atom) :
      ProfileGoalLowered isDefined isBin (.evalg val res) (.evalg val res)
  | catchg (tmpl res : Atom) (sub sub' : List Goal)
      (hsub : ProfileGoalsLowered isDefined isBin sub sub') :
      ProfileGoalLowered isDefined isBin (.catchg tmpl sub res)
        (.catchg tmpl sub' res)
  | softcut (tmpl : Atom) (sub sub' thn thn' els els' : List Goal)
      (hsub : ProfileGoalsLowered isDefined isBin sub sub')
      (hthn : ProfileGoalsLowered isDefined isBin thn thn')
      (hels : ProfileGoalsLowered isDefined isBin els els') :
      ProfileGoalLowered isDefined isBin (.softcut tmpl sub thn els)
        (.softcut tmpl sub' thn' els')
  | eq (a b : Atom) :
      ProfileGoalLowered isDefined isBin (.eq a b) (.eq a b)
  | compileAlias (a b : Atom) :
      ProfileGoalLowered isDefined isBin (.compileAlias a b)
        (.compileAlias a b)
  | cut : ProfileGoalLowered isDefined isBin .cut .cut
  | cutAt (n : Nat) : ProfileGoalLowered isDefined isBin (.cutAt n) (.cutAt n)
  | findall (tmpl res : Atom) (sub sub' : List Goal)
      (hsub : ProfileGoalsLowered isDefined isBin sub sub') :
      ProfileGoalLowered isDefined isBin (.findall tmpl sub res)
        (.findall tmpl sub' res)
  | onceg (tmpl res : Atom) (sub sub' : List Goal)
      (hsub : ProfileGoalsLowered isDefined isBin sub sub') :
      ProfileGoalLowered isDefined isBin (.onceg tmpl sub res)
        (.onceg tmpl sub' res)
  | transactiong (tmpl : Atom) (sub sub' : List Goal)
      (hsub : ProfileGoalsLowered isDefined isBin sub sub') :
      ProfileGoalLowered isDefined isBin (.transactiong tmpl sub)
        (.transactiong tmpl sub')
  | amb (branches branches' : List (Atom × List Goal)) (res : Atom)
      (hbranches : ProfileBranchesLowered isDefined isBin branches branches') :
      ProfileGoalLowered isDefined isBin (.amb branches res)
        (.amb branches' res)
  | spread (val res : Atom) :
      ProfileGoalLowered isDefined isBin (.spread val res) (.spread val res)
  | ite (cond thnValue elsValue res : Atom)
      (thn thn' els els' : List Goal)
      (hthn : ProfileGoalsLowered isDefined isBin thn thn')
      (hels : ProfileGoalsLowered isDefined isBin els els') :
      ProfileGoalLowered isDefined isBin
        (.ite cond (thnValue, thn) (elsValue, els) res)
        (.ite cond (thnValue, thn') (elsValue, els') res)
  | smatch (pat : Atom) :
      ProfileGoalLowered isDefined isBin (.smatch pat) (.smatch pat)
  | wact (op : String) (args : List Atom) (res : Atom) :
      ProfileGoalLowered isDefined isBin (.wact op args res) (.wact op args res)

inductive ProfileGoalsLowered (isDefined isBin : String → Bool) :
    List Goal → List Goal → Prop where
  | nil : ProfileGoalsLowered isDefined isBin [] []
  | cons (goal goal' : Goal) (rest rest' : List Goal)
      (hgoal : ProfileGoalLowered isDefined isBin goal goal')
      (hrest : ProfileGoalsLowered isDefined isBin rest rest') :
      ProfileGoalsLowered isDefined isBin (goal :: rest) (goal' :: rest')

inductive ProfileBranchesLowered (isDefined isBin : String → Bool) :
    List (Atom × List Goal) → List (Atom × List Goal) → Prop where
  | nil : ProfileBranchesLowered isDefined isBin [] []
  | cons (tmpl : Atom) (goals goals' : List Goal)
      (rest rest' : List (Atom × List Goal))
      (hgoals : ProfileGoalsLowered isDefined isBin goals goals')
      (hrest : ProfileBranchesLowered isDefined isBin rest rest') :
      ProfileBranchesLowered isDefined isBin
        ((tmpl, goals) :: rest) ((tmpl, goals') :: rest')
end

/- The executable lowering function satisfies the exact, head-only rewrite
    relation for every goal tree. -/
mutual
theorem lowerProfileGoal_exact (isDefined isBin : String → Bool)
    (goal : Goal) :
    ProfileGoalLowered isDefined isBin goal
      (lowerProfileGoal isDefined isBin goal) := by
  cases goal with
  | call f args res => exact .call f args res
  | bin op args res => exact .bin op args res
  | callDyn head args res =>
      exact lowerProfileGoal_exact_nonSymbol isDefined isBin head args res
  | evalg val res => exact .evalg val res
  | catchg tmpl sub res =>
      exact .catchg tmpl res sub _ (lowerProfileGoals_exact _ _ sub)
  | softcut tmpl sub thn els =>
      exact .softcut tmpl sub _ thn _ els _ (lowerProfileGoals_exact _ _ sub)
        (lowerProfileGoals_exact _ _ thn) (lowerProfileGoals_exact _ _ els)
  | eq a b => exact .eq a b
  | compileAlias a b => exact .compileAlias a b
  | cut => exact .cut
  | cutAt n => exact .cutAt n
  | findall tmpl sub res =>
      exact .findall tmpl res sub _ (lowerProfileGoals_exact _ _ sub)
  | onceg tmpl sub res =>
      exact .onceg tmpl res sub _ (lowerProfileGoals_exact _ _ sub)
  | transactiong tmpl sub =>
      exact .transactiong tmpl sub _ (lowerProfileGoals_exact _ _ sub)
  | amb branches res =>
      exact .amb branches _ res (lowerProfileBranches_exact _ _ branches)
  | spread val res => exact .spread val res
  | ite cond thn els res =>
      exact .ite cond thn.1 els.1 res thn.2 _ els.2 _
        (lowerProfileGoals_exact _ _ thn.2)
        (lowerProfileGoals_exact _ _ els.2)
  | smatch pat => exact .smatch pat
  | wact op args res => exact .wact op args res

theorem lowerProfileGoal_exact_nonSymbol (isDefined isBin : String → Bool)
    (head : Atom) (args : List Atom) (res : Atom) :
    ProfileGoalLowered isDefined isBin (.callDyn head args res)
      (lowerProfileGoal isDefined isBin (.callDyn head args res)) := by
  cases head with
  | sym f =>
      cases hdef : isDefined f with
      | false =>
          cases hbin : isBin f with
          | false =>
              simpa [lowerProfileGoal, hdef, hbin] using
                ProfileGoalLowered.dynSymbolFallback f args res hdef hbin
          | true =>
              simpa [lowerProfileGoal, hdef, hbin] using
                ProfileGoalLowered.dynBuiltin f args res hdef hbin
      | true =>
          simpa [lowerProfileGoal, hdef] using
            ProfileGoalLowered.dynDefined f args res hdef
  | var v =>
      have hpPublic : specPartialView? (.var v) = none := rfl
      have hp := hpPublic
      simp only [specPartialView?] at hp
      simpa [lowerProfileGoal, hp] using
        ProfileGoalLowered.dynData (isDefined := isDefined) (isBin := isBin)
          (.var v) args res (by simp) hpPublic
  | gnd g =>
      have hpPublic : specPartialView? (.gnd g) = none := rfl
      have hp := hpPublic
      simp only [specPartialView?] at hp
      simpa [lowerProfileGoal, hp] using
        ProfileGoalLowered.dynData (isDefined := isDefined) (isBin := isBin)
          (.gnd g) args res (by simp) hpPublic
  | expr xs =>
      cases hp : specPartialView? (.expr xs) with
      | none =>
          have hpPublic := hp
          simp only [specPartialView?] at hp
          simpa [lowerProfileGoal, hp] using
            ProfileGoalLowered.dynData (isDefined := isDefined) (isBin := isBin)
              (.expr xs) args res (by simp) hpPublic
      | some view =>
          have hpPublic := hp
          simp only [specPartialView?] at hp
          rcases view with ⟨base, bound⟩
          cases hdef : isDefined base with
          | false =>
              cases hbin : isBin base with
              | false =>
                  simpa [lowerProfileGoal, hp, hdef, hbin] using
                    ProfileGoalLowered.dynPartialFallback
                      (.expr xs) base bound args res hpPublic hdef hbin
              | true =>
                  simpa [lowerProfileGoal, hp, hdef, hbin] using
                    ProfileGoalLowered.dynPartialBuiltin
                      (.expr xs) base bound args res hpPublic hdef hbin
          | true =>
              simpa [lowerProfileGoal, hp, hdef] using
                ProfileGoalLowered.dynPartialDefined (isBin := isBin)
                  (.expr xs) base bound args res hpPublic hdef

theorem lowerProfileGoals_exact (isDefined isBin : String → Bool)
    (goals : List Goal) :
    ProfileGoalsLowered isDefined isBin goals
      (lowerProfileGoals isDefined isBin goals) := by
  cases goals with
  | nil => exact .nil
  | cons goal rest =>
      exact .cons goal _ rest _ (lowerProfileGoal_exact _ _ goal)
        (lowerProfileGoals_exact _ _ rest)

theorem lowerProfileBranches_exact (isDefined isBin : String → Bool)
    (branches : List (Atom × List Goal)) :
    ProfileBranchesLowered isDefined isBin branches
      (lowerProfileBranches isDefined isBin branches) := by
  cases branches with
  | nil => exact .nil
  | cons branch rest =>
      exact .cons branch.1 branch.2 _ rest _
        (lowerProfileGoals_exact _ _ branch.2)
        (lowerProfileBranches_exact _ _ rest)
end

/-- Static provenance of the pure clause rewrite: the head is precisely the
    specialization binding applied to the captured head, while the body is
    related to the bound generic body by the independently specified
    head-only lowering relation above. -/
theorem specializeClauseProfile_exact (isDefined isBin : String → Bool)
    (binding : Subst) (clause : Clause) :
    (specializeClauseProfile isDefined isBin binding clause).params =
        clause.params.map (Metta.Subst.apply binding) ∧
    (specializeClauseProfile isDefined isBin binding clause).result =
        Metta.Subst.apply binding clause.result ∧
    ProfileGoalsLowered isDefined isBin
      (instantiateGoals binding clause.body)
      (specializeClauseProfile isDefined isBin binding clause).body := by
  exact ⟨rfl, rfl, lowerProfileGoals_exact _ _ _⟩

/-! ## Guarded-normal-form invariants -/

mutual

/-- Every atom carried by a goal except the dynamic callable-head position.
    Equality of this projection rules out accidental specialization of data,
    results, templates, conditions, or world-effect operands. -/
def nonHeadAtomsGoal : Goal → List Atom
  | .call _ args res | .bin _ args res | .callDyn _ args res => args ++ [res]
  | .evalg val res => [val, res]
  | .catchg tmpl sub res => tmpl :: res :: nonHeadAtomsGoals sub
  | .softcut tmpl sub thn els =>
      tmpl :: (nonHeadAtomsGoals sub ++ nonHeadAtomsGoals thn ++
        nonHeadAtomsGoals els)
  | .eq a b | .compileAlias a b => [a, b]
  | .cut | .cutAt _ => []
  | .findall tmpl sub res | .onceg tmpl sub res =>
      tmpl :: res :: nonHeadAtomsGoals sub
  | .transactiong tmpl sub => tmpl :: nonHeadAtomsGoals sub
  | .amb branches res => res :: nonHeadAtomsBranches branches
  | .spread val res => [val, res]
  | .ite cond thn els res =>
      [cond, thn.1, els.1, res] ++ nonHeadAtomsGoals thn.2 ++
        nonHeadAtomsGoals els.2
  | .smatch pat => [pat]
  | .wact _ args res => args ++ [res]

def nonHeadAtomsGoals : List Goal → List Atom
  | [] => []
  | goal :: rest => nonHeadAtomsGoal goal ++ nonHeadAtomsGoals rest

def nonHeadAtomsBranches : List (Atom × List Goal) → List Atom
  | [] => []
  | (tmpl, goals) :: rest =>
      tmpl :: (nonHeadAtomsGoals goals ++ nonHeadAtomsBranches rest)

end

/-- The guard prefix is exactly a list of pure unification goals, one for
    each binding and in binding order. -/
inductive PureBindingGuards : Subst → List Goal → Prop where
  | nil : PureBindingGuards [] []
  | cons (v : String) (value : Atom) (binding : Subst) (guards : List Goal)
      (hrest : PureBindingGuards binding guards) :
      PureBindingGuards ((v, value) :: binding)
        (Goal.eq value (Atom.var v) :: guards)

theorem specializationGuards_pure (binding : Subst) :
    PureBindingGuards binding (specializationGuards binding) := by
  induction binding with
  | nil => exact .nil
  | cons entry rest ih =>
      rcases entry with ⟨v, value⟩
      exact .cons v value rest _ ih

private theorem nodup_map_of_injective {α β : Type}
    (f : α → β) (hinjective : Function.Injective f) :
    (items : List α) → items.Nodup → (items.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: rest, hnodup => by
      simp only [List.nodup_cons] at hnodup ⊢
      constructor
      · intro mapped hmapped hequal
        rw [List.mem_map] at hmapped
        obtain ⟨source, hsource, hsourceMapped⟩ := hmapped
        have : source = head :=
          hinjective (hsourceMapped.trans hequal.symm)
        subst source
        exact hnodup.1 hsource
      · exact nodup_map_of_injective f hinjective rest hnodup.2

/-- Clause freshening of a specialization binding by the actual
    convention-independent resolution suffix. -/
def renameSpecBindingSuffix (suffix : String) (binding : Subst) : Subst :=
  binding.map (fun entry =>
    (entry.1 ++ suffix, renameAtomSuffix suffix entry.2))

theorem renameSpecBindingSuffix_keys_nodup (suffix : String)
    (binding : Subst) (hnodup : (binding.map Prod.fst).Nodup) :
    ((renameSpecBindingSuffix suffix binding).map Prod.fst).Nodup := by
  have hkeys :
      (renameSpecBindingSuffix suffix binding).map Prod.fst =
        (binding.map Prod.fst).map (fun name => name ++ suffix) := by
    unfold renameSpecBindingSuffix
    simp only [List.map_map]
    apply List.map_congr_left
    intro entry hentry
    rfl
  rw [hkeys]
  exact nodup_map_of_injective _ (resolution_suffix_injective suffix) _ hnodup

/-- The actual resolution freshener commutes with the guard constructor. -/
theorem rename_specializationGuards_suffix (suffix : String) (barrier : Nat)
    (binding : Subst) :
    (specializationGuards binding).map (renameGoalSuffix suffix barrier) =
      specializationGuards (renameSpecBindingSuffix suffix binding) := by
  induction binding with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      simp [specializationGuards, renameSpecBindingSuffix,
        renameGoalSuffix, renameAtomSuffix]

/-- On the complete source binding, the fixed-copy view is definitionally
    the executable alpha-copy followed by resolution standardizing-apart. -/
theorem specializationGuardBindingSuffix_eq_executable (clause : Clause)
    (binding : Subst) (suffix : String) :
    specializationGuardBindingSuffix clause binding suffix binding =
      renameSpecBindingSuffix suffix
        (freshenSpecializationBinding clause binding) := by
  unfold specializationGuardBindingSuffix renameSpecBindingSuffix
    freshenSpecializationBinding
  simp only [List.map_map]
  apply List.map_congr_left
  intro entry hentry
  rfl

@[simp] theorem renameGoalsSuffix_eq_map (suffix : String) (barrier : Nat)
    (goals : List Goal) :
    renameGoalsSuffix suffix barrier goals =
      goals.map (renameGoalSuffix suffix barrier) := by
  induction goals with
  | nil => rfl
  | cons goal rest ih => simp [renameGoalsSuffix, ih]

@[simp] theorem renameBranchesSuffix_eq_map (suffix : String) (barrier : Nat)
    (branches : List (Atom × List Goal)) :
    renameBranchesSuffix suffix barrier branches =
      branches.map (fun branch =>
        (renameAtomSuffix suffix branch.1,
          branch.2.map (renameGoalSuffix suffix barrier))) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      rcases branch with ⟨tmpl, goals⟩
      simp [renameBranchesSuffix, ih]

/-! ### Execution of a satisfied specialization guard -/

mutual

/-- Runtime-equivalent atoms decompose reflexively to no unification
    constraints.  The `Atom.equiv` premise is essential for grounded NaN,
    whose runtime equality is deliberately non-reflexive. -/
theorem decomposeEq_self_of_equiv : (a : Atom) →
    Atom.equiv a a = true →
      Metta.Unify.decomposeEq a a = some []
  | .sym s, _ => by simp [Metta.Unify.decomposeEq]
  | .var x, _ => by simp [Metta.Unify.decomposeEq]
  | .gnd g, h => by
      have hg : Metta.Ground.equiv g g = true := by
        simpa only [Atom.equiv] using h
      simp [Metta.Unify.decomposeEq, hg]
  | .expr xs, h => decomposeList_self_of_equivList xs h

/-- List companion to `decomposeEq_self_of_equiv`. -/
theorem decomposeList_self_of_equivList : (xs : List Atom) →
    Atom.equivList xs xs = true →
      Metta.Unify.decomposeList xs xs = some []
  | [], _ => rfl
  | x :: xs, h => by
      simp only [Atom.equivList, Bool.and_eq_true] at h
      simp [Metta.Unify.decomposeList,
        decomposeEq_self_of_equiv x h.1,
        decomposeList_self_of_equivList xs h.2]

end

/-- Reflexive runtime-compatible unification produces the empty unifier. -/
theorem unifyTop_self_of_equiv (a : Atom) (h : Atom.equiv a a = true) :
    Metta.Unify.unifyTop a a = some [] := by
  have hdecompose : Metta.Unify.decomposeEq a a = some [] :=
    decomposeEq_self_of_equiv a h
  have hsize : 0 < Atom.size a + Atom.size a := by
    have hone : 0 < Atom.size a := by
      cases a <;> simp [Atom.size]
    omega
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsize)
  unfold Metta.Unify.unifyTop
  rw [hfuel]
  simp [Metta.Unify.unifyRounds, Metta.Unify.decomposeAll, hdecompose]

/-- Once both sides of an equality goal denote the same runtime-compatible
    atom, the guard contributes no binding: `unifyB` returns the incoming
    substitution verbatim. -/
theorem unifyB_redundant (b : Subst) (x y : Atom)
    (hsame : subst b x = subst b y) :
    unifyB b x y = some b := by
  have hexact : unifyTopExact (subst b y) (subst b y) = some [] :=
    unifyTopExact_self _
  rw [unifyB, hsame, hexact]

/-- A satisfied specialization equality is one genuine semantic stutter:
    it removes only the guard and performs the machine's ordinary liveness
    trim.  It changes neither the world, alternatives, counter, query term,
    nor ordered answers. -/
theorem redundant_eq_guard_step (prog : Prog) (gt : GroundingTable)
    (c : Conf) (x y : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.eq x y :: rest, b))
    (hsame : subst b x = subst b y) :
    Step prog gt c
      { c with cur := some (rest, trimFor rest c.qterm b) } := by
  exact Step.eq_ok c x y rest b b hcur
    (unifyB_redundant b x y hsame)

/-- One specialization guard is an actual unification step, not generally a
    redundant equality.  Given an exact unifier for the already-substituted
    guard operands, the concrete `unifyB` result propositionally realizes
    that guard before liveness trimming; the executable `Step` then installs
    precisely the ordinary trimmed result.  This is the operational seam for
    open alpha-copied residuals. -/
theorem exact_binding_guard_step (prog : Prog) (gt : GroundingTable)
    (c : Conf) (name : String) (value : Atom) (rest : List Goal)
    (b next witness : Subst)
    (hcur : c.cur = some (Goal.eq value (Atom.var name) :: rest, b))
    (topological : SubstTopological b)
    (hwitness :
      subst witness (subst b value) =
        subst witness (subst b (Atom.var name)))
    (hresult : unifyB b value (Atom.var name) = some next) :
    Step prog gt c
        { c with cur := some (rest, trimFor rest c.qterm next) } ∧
      Nonempty (SubstTopological next) ∧
        subst next value = subst next (Atom.var name) := by
  have hstep : Step prog gt c
      { c with cur := some (rest, trimFor rest c.qterm next) } :=
    Step.eq_ok c value (Atom.var name) rest b next hcur hresult
  have hnextTopological : SubstTopological next :=
    unifyB_topological b value (Atom.var name) next topological hresult
  have hexact : subst next value = subst next (Atom.var name) :=
    unifyB_exact_sound_of_exact_unifier b value (Atom.var name) next witness
      topological hwitness hresult
  exact ⟨hstep, ⟨hnextTopological⟩, hexact⟩

/-- A later successful guard unification preserves every exact equation
    established before it.  This is the induction principle needed for an
    ordered guard prefix; no pre-guard realization assumption is involved. -/
theorem exact_binding_guard_preserves_prior (b next : Subst)
    (name : String) (value priorLeft priorRight : Atom)
    (topological : SubstTopological b)
    (hresult : unifyB b value (Atom.var name) = some next)
    (hprior : subst b priorLeft = subst b priorRight) :
    subst next priorLeft = subst next priorRight := by
  exact unifyB_preserves_denotation b value (Atom.var name) next topological
    hresult priorLeft priorRight hprior

/-- Closed captured values give the common specialization-guard case
    directly from the head-unifier lookup. -/
theorem closed_binding_guard_step (prog : Prog) (gt : GroundingTable)
    (c : Conf) (v : String) (value : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.eq (Atom.var v) value :: rest, b))
    (hlookup : Metta.Subst.lookup b v = some value)
    (hclosed : value.vars = []) :
    Step prog gt c
      { c with cur := some (rest, trimFor rest c.qterm b) } := by
  apply redundant_eq_guard_step prog gt c (Atom.var v) value rest b hcur
  rw [subst_var_of_lookup_closed b v value hlookup hclosed,
    subst_of_closed b value hclosed]

/-- Exact runtime denotation of every (possibly open) captured binding.  This
    is the semantic fact consumed by callable-head rewriting. -/
def SubstDenotesBinding (runtime : Subst) (binding : Subst) : Prop :=
  ∀ name value, (name, value) ∈ binding →
    subst runtime (Atom.var name) = subst runtime value

/-- A binding realized by the current runtime substitution.  Exact Prolog
    identity is reflexive even for NaN, so denotation equality alone is now
    sufficient for redundant equality guards. -/
def SubstRealizesBinding (runtime : Subst) (binding : Subst) : Prop :=
  SubstDenotesBinding runtime binding

theorem SubstRealizesBinding.denotes {runtime binding : Subst}
    (realized : SubstRealizesBinding runtime binding) :
    SubstDenotesBinding runtime binding :=
  realized

private theorem subst_lookup_mem (binding : Subst) (name : String)
    (value : Atom) (hlookup : Metta.Subst.lookup binding name = some value) :
    (name, value) ∈ binding := by
  induction binding with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨headName, headValue⟩
      by_cases hname : name = headName
      · subst headName
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst headValue
        simp
      · have hbeq : (name == headName) = false := by simp [hname]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        exact List.mem_cons_of_mem (headName, headValue) (ih hlookup)

/-- In a unique-key substitution, list membership identifies the executable
    lookup result rather than a shadowed entry. -/
theorem subst_lookup_of_mem_of_keys_nodup (binding : Subst)
    (name : String) (value : Atom)
    (hnodup : (binding.map Prod.fst).Nodup)
    (hmem : (name, value) ∈ binding) :
    Metta.Subst.lookup binding name = some value := by
  induction binding with
  | nil => simp at hmem
  | cons entry rest ih =>
      rcases entry with ⟨headName, headValue⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        simp [Metta.Subst.lookup]
      · have hnameMem : name ∈ rest.map Prod.fst := by
          rw [List.mem_map]
          exact ⟨(name, value), htail, rfl⟩
        have hdifferent : name ≠ headName := by
          intro hequal
          subst name
          exact hnodup.1 hnameMem
        have hbeq : (name == headName) = false := by simp [hdifferent]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
        exact ih hnodup.2 htail

/-- One-pass application of a captured specialization binding is
    observationally invisible to a runtime substitution that realizes every
    captured equation.  This is the semantic bridge from the generic dynamic
    head to the concrete head inspected by callable-head lowering. -/
private theorem atomSize_le_sum_of_mem_specialize {atom : Atom} :
    (atoms : List Atom) → atom ∈ atoms →
      atom.size ≤ (atoms.map Atom.size).sum
  | [], hmem => by simp at hmem
  | head :: tail, hmem => by
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (atomSize_le_sum_of_mem_specialize tail htail)
          (Nat.le_add_left _ _)

/-- A fresh key avoided by every resolved source variable is avoided by the
    resolved compound atom as a whole. -/
private theorem not_mem_subst_of_not_mem_resolved (runtime : Subst)
    (forbidden : String) : (atom : Atom) →
    (∀ source, source ∈ atom.vars →
      forbidden ∉ (subst runtime (Atom.var source)).vars) →
    forbidden ∉ (subst runtime atom).vars
  | .sym symbol, _ => by simp [Atom.vars]
  | .var source, havoid => havoid source (by simp [Atom.vars])
  | .gnd ground, _ => by simp [Atom.vars]
  | .expr atoms, havoid => by
      simp only [subst_expr, Atom.vars, List.mem_flatten, List.mem_map]
      rintro ⟨variableList, ⟨resolvedChild, hresolvedChild, rfl⟩,
        hforbidden⟩
      obtain ⟨child, hchild, rfl⟩ := hresolvedChild
      exact not_mem_subst_of_not_mem_resolved runtime forbidden child (by
        intro source hsource
        apply havoid source
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hsource⟩) hforbidden
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_specialize atoms hchild)

/-- Applying the generated residual renaming replaces every covered source
    variable by a name strictly longer than the occupied-name bound. -/
theorem apply_residualFreshNames_vars_long (maxLength index : Nat)
    (sources : List String) :
    (atom : Atom) →
      (∀ source, source ∈ atom.vars → source ∈ sources) →
      ∀ target,
        target ∈ (Metta.Subst.apply
          (residualFreshNames maxLength index sources) atom).vars →
        maxLength < target.length
  | .sym name, _, target, htarget => by
      simp [Metta.Subst.apply, Atom.vars] at htarget
  | .gnd ground, _, target, htarget => by
      simp [Metta.Subst.apply, Atom.vars] at htarget
  | .var source, hcovered, target, htarget => by
      have hsource : source ∈ sources := hcovered source (by simp [Atom.vars])
      obtain ⟨fresh, hlookup, hlong⟩ :=
        residualFreshNames_lookup_long maxLength index sources source hsource
      simp [Metta.Subst.apply, hlookup, Atom.vars] at htarget
      subst target
      exact hlong
  | .expr atoms, hcovered, target, htarget => by
      simp only [Metta.Subst.apply, Atom.vars, List.map_map] at htarget
      rw [List.mem_flatten] at htarget
      obtain ⟨targetVars, htargetVars, htarget⟩ := htarget
      rw [List.mem_map] at htargetVars
      obtain ⟨child, hchild, rfl⟩ := htargetVars
      apply apply_residualFreshNames_vars_long maxLength index sources child
      · intro source hsource
        apply hcovered source
        simp only [Atom.vars, List.mem_flatten]
        exact ⟨child.vars, List.mem_map_of_mem hchild, hsource⟩
      · exact htarget
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_specialize atoms hchild)

/-- Every executable specialization entry retains its exact pre-copy origin.
    The same shared copy substitution is used for every entry, which is the
    constructional fact needed to preserve residual-variable sharing. -/
theorem freshenSpecializationBinding_mem_origin (clause : Clause)
    (source : Subst) (name : String) (value : Atom)
    (hmem : (name, value) ∈ freshenSpecializationBinding clause source) :
    ∃ sourceValue,
      (name, sourceValue) ∈ source ∧
        value = Metta.Subst.apply
          (specializationCopySubst clause source) sourceValue := by
  unfold freshenSpecializationBinding at hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨sourceName, sourceValue⟩, hsource, hp⟩ := hmem
  simp only [Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩
  exact ⟨sourceValue, hsource, rfl⟩

private theorem lookup_map_apply (copy source : Subst) (name : String)
    (value : Atom) (hlookup : Metta.Subst.lookup source name = some value) :
    Metta.Subst.lookup
      (source.map (fun entry =>
        (entry.1, Metta.Subst.apply copy entry.2))) name =
      some (Metta.Subst.apply copy value) := by
  induction source with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨headName, headValue⟩
      by_cases hname : name = headName
      · subst headName
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst headValue
        simp [Metta.Subst.lookup]
      · have hbeq : (name == headName) = false := by simp [hname]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        simpa [Metta.Subst.lookup, hbeq] using ih hlookup

/-- Lookup commutes with the candidate's shared alpha-copy operation. -/
theorem freshenSpecializationBinding_lookup (clause : Clause)
    (source : Subst) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup source name = some value) :
    Metta.Subst.lookup (freshenSpecializationBinding clause source) name =
      some (Metta.Subst.apply
        (specializationCopySubst clause source) value) := by
  exact lookup_map_apply (specializationCopySubst clause source) source name
    value hlookup

/-- Propositional construction evidence for the actual copier: no residual
    variable stored in a generated binding can alias a variable of the
    compiled callee clause. -/
theorem freshenSpecializationBinding_avoids_clause (clause : Clause)
    (binding : Subst) (name : String) (value : Atom)
    (hmem : (name, value) ∈ freshenSpecializationBinding clause binding)
    (target : String) (htarget : target ∈ value.vars) :
    target ∉ specializationClauseVars clause := by
  unfold freshenSpecializationBinding at hmem
  let residuals := (binding.flatMap (fun entry => entry.2.vars)).eraseDups
  let occupied := specializationClauseVars clause ++ residuals
  let maxLength := occupied.foldl
    (fun current item => max current item.length) 0
  let copySubst := residualFreshNames maxLength 0 residuals
  change (name, value) ∈ binding.map (fun entry =>
    (entry.1, Metta.Subst.apply copySubst entry.2)) at hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨sourceName, sourceValue⟩, hsourceMem, hp⟩ := hmem
  simp only [Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩
  have hcovered : ∀ source, source ∈ sourceValue.vars →
      source ∈ residuals := by
    intro source hsource
    simp only [residuals, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨(sourceName, sourceValue), hsourceMem, hsource⟩
  have hlong : maxLength < target.length := by
    exact apply_residualFreshNames_vars_long maxLength 0 residuals sourceValue
      hcovered target htarget
  intro hinClause
  have hinOccupied : target ∈ occupied :=
    List.mem_append_left residuals hinClause
  have hshort : target.length ≤ maxLength := by
    exact member_length_le_foldl_max occupied 0 target hinOccupied
  omega

theorem subst_apply_of_denotes (runtime binding : Subst)
    (hdenotes : SubstDenotesBinding runtime binding) :
    (atom : Atom) → subst runtime (Metta.Subst.apply binding atom) =
      subst runtime atom
  | .sym name => by simp [Metta.Subst.apply]
  | .gnd ground => by simp [Metta.Subst.apply]
  | .var name => by
      simp only [Metta.Subst.apply]
      cases hlookup : Metta.Subst.lookup binding name with
      | none => simp
      | some value =>
          simp only [Option.getD_some]
          exact (hdenotes name value
            (subst_lookup_mem binding name value hlookup)).symm
  | .expr atoms => by
      simp only [Metta.Subst.apply, subst_expr, Atom.expr.injEq, List.map_map]
      rw [List.map_congr_left]
      intro child hchild
      exact subst_apply_of_denotes runtime binding hdenotes child
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (atomSize_le_sum_of_mem_specialize atoms hchild)

/-- The first guard of a realized binding is a semantic stutter.  This is the
    open-partial generalization of `closed_binding_guard_step`. -/
theorem realized_binding_head_step (prog : Prog) (gt : GroundingTable)
    (c : Conf) (name : String) (value : Atom) (binding : Subst)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some
      (specializationGuards ((name, value) :: binding) ++ rest, b))
    (hrealized : SubstRealizesBinding b ((name, value) :: binding)) :
    Step prog gt c
      { c with cur := some (specializationGuards binding ++ rest,
          trimFor (specializationGuards binding ++ rest) c.qterm b) } := by
  have hentry := hrealized name value (by simp)
  apply redundant_eq_guard_step prog gt c value (Atom.var name)
    (specializationGuards binding ++ rest) b
  · simpa [specializationGuards] using hcur
  · exact hentry.symm

theorem specializationGuards_mem_of_binding_mem (binding : Subst)
    (name : String) (value : Atom) (hmem : (name, value) ∈ binding) :
    Goal.eq value (Atom.var name) ∈ specializationGuards binding := by
  induction binding with
  | nil => simp at hmem
  | cons entry rest ih =>
      rcases entry with ⟨headName, headValue⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        simp [specializationGuards]
      · change Goal.eq value (Atom.var name) ∈
          Goal.eq headValue (Atom.var headName) :: specializationGuards rest
        simp only [List.mem_cons]
        exact Or.inr (ih htail)

/-- After one or more satisfied guards are trimmed away, every remaining
    captured binding is still realized.  This uses denotation preservation of
    the executable `trimFor`, with liveness supplied by the actual remaining
    guard equalities rather than raw substitution equality. -/
theorem substRealizesBinding_trimFor_guards (binding : Subst)
    (rest : List Goal) (qterm : Atom) (b : Subst)
    (topological : SubstTopological b)
    (hrealized : SubstRealizesBinding b binding) :
    SubstRealizesBinding
      (trimFor (specializationGuards binding ++ rest) qterm b) binding := by
  intro name value hmem
  have hguard : Goal.eq value (Atom.var name) ∈
      specializationGuards binding :=
    specializationGuards_mem_of_binding_mem binding name value hmem
  have hgoal : Goal.eq value (Atom.var name) ∈
      specializationGuards binding ++ rest :=
    List.mem_append_left rest hguard
  have hleft := subst_trimFor_eq_of_topological
    (specializationGuards binding ++ rest) qterm b topological
    (Atom.var name) (by
      intro dependency hdependency
      simp only [Atom.vars, List.mem_singleton] at hdependency
      subst dependency
      exact isTrimRoot_eq_right_of_mem
        (specializationGuards binding ++ rest) qterm value (Atom.var name)
          name hgoal (by simp [Atom.vars]))
  have hright := subst_trimFor_eq_of_topological
    (specializationGuards binding ++ rest) qterm b topological value (by
      intro dependency hdependency
      exact isTrimRoot_eq_left_atom_of_mem
        (specializationGuards binding ++ rest) qterm value (Atom.var name)
        dependency hgoal hdependency)
  have hentry := hrealized name value hmem
  rw [hleft, hright]
  exact hentry

/-- Construction-independent evidence for the real ordered execution of a
    specialization guard prefix.  Each constructor records the concrete
    `unifyB` result, an exact witness for that guard (excluding coercive-only
    runtime equality), and the fact that the newly generated bindings are
    invisible to the caller query.  The recursive state is exactly the
    machine's liveness-trimmed state, not an idealized substitution. -/
inductive ExactBindingGuardsRun (qterm : Atom) (rest : List Goal) :
    Subst → Subst → Subst → Prop where
  | nil (b : Subst) (topological : SubstTopological b) :
      ExactBindingGuardsRun qterm rest [] b b
  | cons (name : String) (value : Atom) (tail : Subst)
      (b next final witness : Subst)
      (topological : SubstTopological b)
      (hwitness :
        subst witness (subst b value) =
          subst witness (subst b (Atom.var name)))
      (hresult : unifyB b value (Atom.var name) = some next)
      (queryInvisible : subst next qterm = subst b qterm)
      (tailRun : ExactBindingGuardsRun qterm rest tail
        (trimFor (specializationGuards tail ++ rest) qterm next) final) :
      ExactBindingGuardsRun qterm rest ((name, value) :: tail) b final

/-- The exact guard-run evidence elaborates to the real small-step prefix.
    It also returns the final topological certificate and exact caller-query
    denotation equality.  In particular, open guards may extend the
    substitution; they are not mislabeled as redundant stutters. -/
theorem exact_binding_guards_run (prog : Prog) (gt : GroundingTable)
    (c : Conf) (qterm : Atom) (binding : Subst) (rest : List Goal)
    (b final : Subst) (hqterm : c.qterm = qterm)
    (hcur : c.cur = some (specializationGuards binding ++ rest, b))
    (run : ExactBindingGuardsRun qterm rest binding b final) :
    StepStar prog gt c { c with cur := some (rest, final) } ∧
      Nonempty (SubstTopological final) ∧
        subst final qterm = subst b qterm := by
  induction run generalizing c with
  | nil b topological =>
      have hstate : { c with cur := some (rest, b) } = c := by
        cases c
        simp_all [specializationGuards]
      constructor
      · rw [hstate]
        exact StepStar.refl c
      · exact ⟨⟨topological⟩, rfl⟩
  | cons name value tail b next final witness topological hwitness hresult
      queryInvisible tailRun ih =>
      let goals := specializationGuards tail ++ rest
      let trimmed := trimFor goals qterm next
      let nextConf : Conf := { c with cur := some (goals, trimmed) }
      have hactive : c.cur = some
          (Goal.eq value (Atom.var name) :: goals, b) := by
        simpa [specializationGuards, goals] using hcur
      have hguard := exact_binding_guard_step prog gt c name value goals b
        next witness hactive topological hwitness hresult
      have hstep : Step prog gt c nextConf := by
        simpa [nextConf, trimmed, goals, hqterm] using hguard.1
      have hnextTopological : SubstTopological next :=
        unifyB_topological b value (Atom.var name) next topological hresult
      have htrimmedTopological : SubstTopological trimmed := by
        exact SubstTopological.trimFor goals qterm next hnextTopological
      obtain ⟨htailSteps, hfinalTopological, htailQuery⟩ :=
        ih (c := nextConf) (by simp [nextConf, hqterm]) (by
          simp [nextConf, trimmed, goals])
      have htrimQuery : subst trimmed qterm = subst next qterm := by
        exact subst_trimFor_eq_of_topological goals qterm next
          hnextTopological qterm (isTrimRoot_qterm_mem goals qterm)
      constructor
      · have hsteps := StepStar.tail c nextConf
          { nextConf with cur := some (rest, final) } hstep htailSteps
        simpa [nextConf] using hsteps
      · refine ⟨hfinalTopological, ?_⟩
        calc
          subst final qterm = subst trimmed qterm := htailQuery
          _ = subst next qterm := htrimQuery
          _ = subst b qterm := queryInvisible

/-- A realized specialization-guard prefix executes completely without
    changing the observable query denotation.  The witness is the actual
    substitution produced by the executable equality steps; its topological
    certificate is carried through every liveness trim. -/
theorem realized_binding_guards_run (prog : Prog) (gt : GroundingTable)
    (c : Conf) (binding : Subst) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (specializationGuards binding ++ rest, b))
    (topological : SubstTopological b)
    (hrealized : SubstRealizesBinding b binding) :
    ∃ finalSubst,
      StepStar prog gt c { c with cur := some (rest, finalSubst) } ∧
      ∃ _ : SubstTopological finalSubst,
        subst finalSubst c.qterm = subst b c.qterm := by
  induction binding generalizing c b with
  | nil =>
      have hstate : { c with cur := some (rest, b) } = c := by
        cases c
        simp_all [specializationGuards]
      refine ⟨b, ?_, topological, rfl⟩
      rw [hstate]
      exact StepStar.refl c
  | cons entry tail ih =>
      rcases entry with ⟨name, value⟩
      let goals := specializationGuards tail ++ rest
      let nextSubst := trimFor goals c.qterm b
      let nextConf : Conf := { c with cur := some (goals, nextSubst) }
      have hhead : Step prog gt c nextConf := by
        simpa [nextConf, goals, nextSubst] using
          realized_binding_head_step prog gt c name value tail rest b hcur
            hrealized
      have htailRealized : SubstRealizesBinding b tail := by
        intro tailName tailValue hmem
        exact hrealized tailName tailValue (List.mem_cons_of_mem (name, value) hmem)
      have hnextRealized : SubstRealizesBinding nextSubst tail := by
        exact substRealizesBinding_trimFor_guards tail rest c.qterm b
          topological htailRealized
      have hnextTopological : SubstTopological nextSubst := by
        exact SubstTopological.trimFor goals c.qterm b topological
      obtain ⟨finalSubst, htailSteps, hfinalTopological, htailQuery⟩ :=
        ih (c := nextConf) (b := nextSubst) (by
          simp [nextConf, goals]) hnextTopological hnextRealized
      have htrimQuery : subst nextSubst c.qterm = subst b c.qterm := by
        exact subst_trimFor_eq_of_topological goals c.qterm b topological
          c.qterm (isTrimRoot_qterm_mem goals c.qterm)
      refine ⟨finalSubst, ?_, hfinalTopological, ?_⟩
      · have hsteps := StepStar.tail c nextConf
          { nextConf with cur := some (rest, finalSubst) } hhead htailSteps
        simpa [nextConf] using hsteps
      · calc
          subst finalSubst c.qterm = subst finalSubst nextConf.qterm := by rfl
          _ = subst nextSubst nextConf.qterm := htailQuery
          _ = subst nextSubst c.qterm := by rfl
          _ = subst b c.qterm := htrimQuery

private theorem partialCallablePayload_sublist (isDefined isBin : String → Bool)
    (head : Atom) (args : List Atom) (res : Atom)
    (view : Option (String × List Atom)) :
    List.Sublist (nonHeadAtomsGoal (.callDyn head args res))
      (nonHeadAtomsGoal
        (match view with
        | some (base, bound) =>
            if isDefined base then .call base (bound ++ args) res
            else if isBin base then .bin base (bound ++ args) res
            else .callDyn head args res
        | none => .callDyn head args res)) := by
  cases view with
  | none => exact List.Sublist.refl _
  | some pair =>
      rcases pair with ⟨base, bound⟩
      cases hdef : isDefined base <;> cases hbin : isBin base <;>
        simp [hdef, hbin, nonHeadAtomsGoal, List.append_assoc]

/- Callable-head specialization preserves the non-head projection on every
   nested goal tree. -/
mutual
theorem specializeCallableHeadGoal_preserves_nonHead
    (isDefined isBin : String → Bool) (binding : Subst) (goal : Goal) :
    List.Sublist (nonHeadAtomsGoal goal)
      (nonHeadAtomsGoal
        (specializeCallableHeadGoal isDefined isBin binding goal)) := by
  cases goal with
  | call f args res => exact List.Sublist.refl _
  | bin op args res => exact List.Sublist.refl _
  | callDyn head args res =>
      simp only [specializeCallableHeadGoal]
      split
      next f hhead =>
        cases hdef : isDefined f
        · cases hbin : isBin f <;> exact List.Sublist.refl _
        · exact List.Sublist.refl _
      next concrete hhead =>
        exact partialCallablePayload_sublist isDefined isBin head args res _
  | evalg val res => exact List.Sublist.refl _
  | catchg tmpl sub res =>
      exact (specializeCallableHeadGoals_preserves_nonHead _ _ binding sub).cons_cons
        res |>.cons_cons tmpl
  | softcut tmpl sub thn els =>
      simpa [specializeCallableHeadGoal, nonHeadAtomsGoal, List.append_assoc] using
        ((specializeCallableHeadGoals_preserves_nonHead _ _ binding sub).append
          ((specializeCallableHeadGoals_preserves_nonHead _ _ binding thn).append
            (specializeCallableHeadGoals_preserves_nonHead _ _ binding els))).cons_cons tmpl
  | eq a b => exact List.Sublist.refl _
  | compileAlias a b => exact List.Sublist.refl _
  | cut => exact List.Sublist.refl _
  | cutAt n => exact List.Sublist.refl _
  | findall tmpl sub res =>
      exact (specializeCallableHeadGoals_preserves_nonHead _ _ binding sub).cons_cons
        res |>.cons_cons tmpl
  | onceg tmpl sub res =>
      exact (specializeCallableHeadGoals_preserves_nonHead _ _ binding sub).cons_cons
        res |>.cons_cons tmpl
  | transactiong tmpl sub =>
      exact (specializeCallableHeadGoals_preserves_nonHead _ _ binding sub).cons_cons tmpl
  | amb branches res =>
      exact (specializeCallableHeadBranches_preserves_nonHead _ _ binding branches).cons_cons
        res
  | spread val res => exact List.Sublist.refl _
  | ite cond thn els res =>
      simpa [specializeCallableHeadGoal, nonHeadAtomsGoal, List.append_assoc] using
        (((specializeCallableHeadGoals_preserves_nonHead _ _ binding thn.2).append
          (specializeCallableHeadGoals_preserves_nonHead _ _ binding els.2)).append_left
            [cond, thn.1, els.1, res])
  | smatch pat => exact List.Sublist.refl _
  | wact op args res => exact List.Sublist.refl _

theorem specializeCallableHeadGoals_preserves_nonHead
    (isDefined isBin : String → Bool) (binding : Subst)
    (goals : List Goal) :
    List.Sublist (nonHeadAtomsGoals goals)
      (nonHeadAtomsGoals
        (specializeCallableHeadGoals isDefined isBin binding goals)) := by
  cases goals with
  | nil => exact List.Sublist.refl _
  | cons goal rest =>
      exact (specializeCallableHeadGoal_preserves_nonHead _ _ binding goal).append
        (specializeCallableHeadGoals_preserves_nonHead _ _ binding rest)

theorem specializeCallableHeadBranches_preserves_nonHead
    (isDefined isBin : String → Bool) (binding : Subst)
    (branches : List (Atom × List Goal)) :
    List.Sublist (nonHeadAtomsBranches branches)
      (nonHeadAtomsBranches
        (specializeCallableHeadBranches isDefined isBin binding branches)) := by
  cases branches with
  | nil => exact List.Sublist.refl _
  | cons branch rest =>
      exact ((specializeCallableHeadGoals_preserves_nonHead _ _ binding branch.2).append
        (specializeCallableHeadBranches_preserves_nonHead _ _ binding rest)).cons_cons
          branch.1
end

/-- The actual guarded clause keeps the generic resolution head exactly,
    prefixes only pure guards, and preserves every non-head payload atom in
    the recursively lowered body. -/
theorem specializeClauseGuarded_exact (isDefined isBin : String → Bool)
    (binding : Subst) (clause : Clause) :
    (specializeClauseGuarded isDefined isBin binding clause).params =
        clause.params ∧
    (specializeClauseGuarded isDefined isBin binding clause).result =
        clause.result ∧
    PureBindingGuards binding (specializationGuards binding) ∧
    List.Sublist (nonHeadAtomsGoals clause.body)
      (nonHeadAtomsGoals
        (specializeCallableHeadGoals isDefined isBin binding clause.body)) := by
  exact ⟨rfl, rfl, specializationGuards_pure binding,
    specializeCallableHeadGoals_preserves_nonHead _ _ binding _⟩

/-! ## Executable validation is sound for the pure constructors -/

mutual

/-- In the explicitly checkable fragment, proof-facing structural equality
    reflects to propositional atom equality. -/
theorem proofAtomEq_eq_of_propositionallyCheckable :
    (left right : Atom) →
    propositionallyCheckableAtom left = true →
    propositionallyCheckableAtom right = true →
    proofAtomEq left right = true → left = right
  | .sym left, .sym right, _, _, heq => by
      simp [proofAtomEq] at heq
      subst right
      rfl
  | .var left, .var right, _, _, heq => by
      simp [proofAtomEq] at heq
      subst right
      rfl
  | .gnd left, .gnd right, hleft, hright, heq => by
      cases left <;> cases right <;>
        simp [propositionallyCheckableAtom, proofAtomEq, proofGroundEq] at hleft hright heq ⊢
      all_goals assumption
  | .expr left, .expr right, hleft, hright, heq => by
      simp only [propositionallyCheckableAtom] at hleft hright
      simp only [proofAtomEq] at heq
      exact congrArg Atom.expr
        (proofAtomsEq_eq_of_propositionallyCheckable left right hleft hright
          heq)
  | .sym _, .var _, _, _, heq
  | .sym _, .gnd _, _, _, heq
  | .sym _, .expr _, _, _, heq
  | .var _, .sym _, _, _, heq
  | .var _, .gnd _, _, _, heq
  | .var _, .expr _, _, _, heq
  | .gnd _, .sym _, _, _, heq
  | .gnd _, .var _, _, _, heq
  | .gnd _, .expr _, _, _, heq
  | .expr _, .sym _, _, _, heq
  | .expr _, .var _, _, _, heq
  | .expr _, .gnd _, _, _, heq => by
      simp [proofAtomEq] at heq

/-- List companion to propositional reflection of proof-facing equality. -/
theorem proofAtomsEq_eq_of_propositionallyCheckable :
    (left right : List Atom) →
    propositionallyCheckableAtoms left = true →
    propositionallyCheckableAtoms right = true →
    proofAtomsEq left right = true → left = right
  | [], [], _, _, _ => rfl
  | left :: leftRest, right :: rightRest, hleft, hright, heq => by
      simp only [propositionallyCheckableAtoms, Bool.and_eq_true] at hleft hright
      simp only [proofAtomsEq, Bool.and_eq_true] at heq
      have hhead := proofAtomEq_eq_of_propositionallyCheckable left right
        hleft.1 hright.1 heq.1
      have htail := proofAtomsEq_eq_of_propositionallyCheckable leftRest
        rightRest hleft.2 hright.2 heq.2
      subst right
      subst rightRest
      rfl
  | [], _ :: _, _, _, heq
  | _ :: _, [], _, _, heq => by
      simp [proofAtomsEq] at heq

end

/-- Reflection interface for the executable exact-atom guard. -/
theorem propositionallyExactAtom_eq (left right : Atom)
    (hexact : propositionallyExactAtom left right = true) : left = right := by
  unfold propositionallyExactAtom at hexact
  simp only [Bool.and_eq_true] at hexact
  exact proofAtomEq_eq_of_propositionallyCheckable left right
    hexact.1.1 hexact.1.2 hexact.2

/-- The executable guard validator constructs the complete ordered proof
    object consumed by the specialized-body simulation.  No success or
    query-preservation premise is assumed separately: both are reflected from
    the exact `unifyB`/`trimFor` computation. -/
theorem exactBindingGuardsRun?_sound (qterm : Atom) (rest : List Goal)
    (binding b final : Subst) (topological : SubstTopological b)
    (hcheck : exactBindingGuardsRun? qterm rest binding b = some final) :
    ExactBindingGuardsRun qterm rest binding b final := by
  induction binding generalizing b final with
  | nil =>
      simp [exactBindingGuardsRun?] at hcheck
      subst final
      exact .nil b topological
  | cons entry tail ih =>
      rcases entry with ⟨name, value⟩
      simp only [exactBindingGuardsRun?] at hcheck
      cases hresult : unifyB b value (Atom.var name) with
      | none => simp [hresult] at hcheck
      | some next =>
          rw [hresult] at hcheck
          let guardLeft := subst next (subst b value)
          let guardRight := subst next (subst b (Atom.var name))
          let nextQuery := subst next qterm
          let priorQuery := subst b qterm
          have hnextTopological : SubstTopological next :=
            unifyB_topological b value (Atom.var name) next topological hresult
          cases hcondition :
              propositionallyExactAtom guardLeft guardRight &&
                propositionallyExactAtom nextQuery priorQuery with
          | false => simp [guardLeft, guardRight, nextQuery, priorQuery,
              hcondition] at hcheck
          | true =>
              have hparts := Bool.and_eq_true_iff.mp hcondition
              have hwitness : guardLeft = guardRight :=
                propositionallyExactAtom_eq guardLeft guardRight hparts.1
              have hquery : nextQuery = priorQuery :=
                propositionallyExactAtom_eq nextQuery priorQuery hparts.2
              let trimmed := trimFor
                (specializationGuards tail ++ rest) qterm next
              have htrimmedTopological : SubstTopological trimmed :=
                SubstTopological.trimFor
                  (specializationGuards tail ++ rest) qterm next
                  hnextTopological
              have htailCheck : exactBindingGuardsRun? qterm rest tail
                  trimmed = some final := by
                simpa [guardLeft, guardRight, nextQuery, priorQuery,
                  hcondition, trimmed] using hcheck
              exact .cons name value tail b next final next topological
                (by simpa [guardLeft, guardRight] using hwitness)
                hresult (by simpa [nextQuery, priorQuery] using hquery)
                (ih trimmed final htrimmedTopological htailCheck)

/-- A nonempty exact-support check exposes the concrete runtime unifier and
    the propositional tuple equality certified by its resolved output. -/
theorem specializationBindingExactlySupported_witness
    (binding : Subst) (formals actuals : List Atom)
    (hbinding : binding ≠ [])
    (hsupported : specializationBindingExactlySupported binding formals actuals =
      true) :
    ∃ unifier,
      Metta.Unify.unifyTop
          (Atom.expr (formals.map (Metta.Subst.apply binding)))
          (Atom.expr actuals) = some unifier ∧
        subst unifier
            (Atom.expr (formals.map (Metta.Subst.apply binding))) =
          subst unifier (Atom.expr actuals) := by
  cases binding with
  | nil => contradiction
  | cons entry rest =>
      unfold specializationBindingExactlySupported at hsupported
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at hsupported
      split at hsupported
      · contradiction
      · split at hsupported
        · contradiction
        · cases hunifier : Metta.Unify.unifyTop
              (Atom.expr
                (formals.map
                  (Metta.Subst.apply (entry :: rest))))
              (Atom.expr actuals) with
          | none => simp [hunifier] at hsupported
          | some unifier =>
              simp only [hunifier, Bool.and_eq_true] at hsupported
              refine ⟨unifier, rfl, ?_⟩
              exact proofAtomEq_eq_of_propositionallyCheckable _ _
                hsupported.1.1 hsupported.1.2 hsupported.2

/-- Exact support realizes every copied source entry against the literal
    call-site subterm from which discovery selected it.  This is the static
    half of the later guard witness; clause-head narrowing supplies the other
    half for the formal variable. -/
theorem specializationBindingExactlySupported_sourceEntry
    (clause : Clause) (sourceBinding : Subst) (actuals : List Atom)
    (name : String) (sourceValue : Atom)
    (hkeys : (sourceBinding.map Prod.fst).Nodup)
    (hmem : (name, sourceValue) ∈ sourceBinding)
    (haligned : SpecializationAlignedList name sourceValue clause.params
      actuals)
    (hsupported : specializationBindingExactlySupported
      (freshenSpecializationBinding clause sourceBinding)
      clause.params actuals = true) :
    let copiedValue := Metta.Subst.apply
      (specializationCopySubst clause sourceBinding) sourceValue
    ∃ unifier,
      Metta.Unify.unifyTop
          (Atom.expr (clause.params.map
            (Metta.Subst.apply
              (freshenSpecializationBinding clause sourceBinding))))
          (Atom.expr actuals) = some unifier ∧
        subst unifier copiedValue = subst unifier sourceValue := by
  let executableBinding := freshenSpecializationBinding clause sourceBinding
  have hsourceLookup : Metta.Subst.lookup sourceBinding name =
      some sourceValue :=
    subst_lookup_of_mem_of_keys_nodup sourceBinding name sourceValue hkeys hmem
  have hexecutableLookup : Metta.Subst.lookup executableBinding name =
      some (Metta.Subst.apply
        (specializationCopySubst clause sourceBinding) sourceValue) := by
    exact freshenSpecializationBinding_lookup clause sourceBinding name
      sourceValue hsourceLookup
  have hexecutableNonempty : executableBinding ≠ [] := by
    intro hempty
    rw [hempty] at hexecutableLookup
    simp [Metta.Subst.lookup] at hexecutableLookup
  obtain ⟨unifier, hunifier, htuple⟩ :=
    specializationBindingExactlySupported_witness executableBinding
      clause.params actuals hexecutableNonempty hsupported
  have htupleLists :
      clause.params.map (fun formal =>
        subst unifier (Metta.Subst.apply executableBinding formal)) =
          actuals.map (subst unifier) := by
    simpa only [subst_expr, Atom.expr.injEq, List.map_map,
      Function.comp_def] using htuple
  refine ⟨unifier, hunifier, ?_⟩
  exact haligned.appliedDenotes unifier executableBinding
    (Metta.Subst.apply
      (specializationCopySubst clause sourceBinding) sourceValue)
    hexecutableLookup htupleLists

@[simp] theorem proofGroundEq_self (ground : Metta.Ground) :
    proofGroundEq ground ground = true := by
  cases ground <;> simp [proofGroundEq]

mutual

@[simp] theorem proofAtomEq_self (atom : Atom) :
    proofAtomEq atom atom = true := by
  cases atom with
  | sym name => simp [proofAtomEq]
  | var name => simp [proofAtomEq]
  | gnd ground => simp [proofAtomEq]
  | expr atoms => simp [proofAtomEq, proofAtomsEq_self atoms]

@[simp] theorem proofAtomsEq_self (atoms : List Atom) :
    proofAtomsEq atoms atoms = true := by
  cases atoms with
  | nil => rfl
  | cons atom rest =>
      simp [proofAtomsEq, proofAtomEq_self atom, proofAtomsEq_self rest]

end

mutual

@[simp] theorem proofGoalEq_self (goal : Goal) :
    proofGoalEq goal goal = true := by
  cases goal with
  | call f args res => simp [proofGoalEq]
  | bin op args res => simp [proofGoalEq]
  | callDyn head args res => simp [proofGoalEq]
  | evalg val res => simp [proofGoalEq]
  | catchg tmpl sub res => simp [proofGoalEq, proofGoalsEq_self sub]
  | softcut tmpl sub thn els =>
      simp [proofGoalEq, proofGoalsEq_self sub, proofGoalsEq_self thn,
        proofGoalsEq_self els]
  | eq a b => simp [proofGoalEq]
  | compileAlias a b => simp [proofGoalEq]
  | cut => rfl
  | cutAt n => simp [proofGoalEq]
  | findall tmpl sub res => simp [proofGoalEq, proofGoalsEq_self sub]
  | onceg tmpl sub res => simp [proofGoalEq, proofGoalsEq_self sub]
  | transactiong tmpl sub => simp [proofGoalEq, proofGoalsEq_self sub]
  | amb branches res => simp [proofGoalEq, proofBranchesEq_self branches]
  | spread val res => simp [proofGoalEq]
  | ite cond thn els res =>
      simp [proofGoalEq, proofGoalsEq_self thn.2, proofGoalsEq_self els.2]
  | smatch pat => simp [proofGoalEq]
  | wact op args res => simp [proofGoalEq]

@[simp] theorem proofGoalsEq_self (goals : List Goal) :
    proofGoalsEq goals goals = true := by
  cases goals with
  | nil => rfl
  | cons goal rest =>
      simp [proofGoalsEq, proofGoalEq_self goal, proofGoalsEq_self rest]

@[simp] theorem proofBranchesEq_self (branches : List (Atom × List Goal)) :
    proofBranchesEq branches branches = true := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      simp [proofBranchesEq, proofGoalsEq_self branch.2,
        proofBranchesEq_self rest]

end

@[simp] theorem proofClauseEq_self (clause : Clause) :
    proofClauseEq clause clause = true := by
  simp [proofClauseEq]

@[simp] theorem proofClausesEq_self (clauses : List Clause) :
    proofClausesEq clauses clauses = true := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih => simp [proofClausesEq, ih]

mutual

theorem callableHeadRewriteValid_specialize (isDefined isBin : String → Bool)
    (binding : Subst) (goal : Goal) :
    callableHeadRewriteValid binding goal
      (specializeCallableHeadGoal isDefined isBin binding goal) = true := by
  cases goal with
  | call f args res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | bin op args res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | callDyn head args res =>
      simp only [specializeCallableHeadGoal, callableHeadRewriteValid]
      cases hhead : Metta.Subst.apply binding head with
      | sym f =>
          cases hdef : isDefined f <;> cases hbin : isBin f <;>
            simp [hdef, hbin]
      | var v =>
          simp [partialHeadView?, partialView?]
      | gnd g =>
          simp [partialHeadView?, partialView?]
      | expr xs =>
          cases hp : partialHeadView? (.expr xs) with
          | none => simp [hp]
          | some view =>
              rcases view with ⟨base, bound⟩
              cases hdef : isDefined base <;> cases hbin : isBin base <;>
                simp [hp, hdef, hbin]
  | evalg val res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | catchg tmpl sub res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding sub]
  | softcut tmpl sub thn els =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding sub,
        callableHeadsRewriteValid_specialize isDefined isBin binding thn,
        callableHeadsRewriteValid_specialize isDefined isBin binding els]
  | eq a b =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | compileAlias a b =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | cut =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | cutAt n =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | findall tmpl sub res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding sub]
  | onceg tmpl sub res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding sub]
  | transactiong tmpl sub =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding sub]
  | amb branches res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadBranchesRewriteValid_specialize isDefined isBin binding
          branches]
  | spread val res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | ite cond thn els res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding thn.2,
        callableHeadsRewriteValid_specialize isDefined isBin binding els.2]
  | smatch pat =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]
  | wact op args res =>
      simp [specializeCallableHeadGoal, callableHeadRewriteValid]

theorem callableHeadsRewriteValid_specialize
    (isDefined isBin : String → Bool) (binding : Subst)
    (goals : List Goal) :
    callableHeadsRewriteValid binding goals
      (specializeCallableHeadGoals isDefined isBin binding goals) = true := by
  cases goals with
  | nil => rfl
  | cons goal rest =>
      simp [specializeCallableHeadGoals, callableHeadsRewriteValid,
        callableHeadRewriteValid_specialize isDefined isBin binding goal,
        callableHeadsRewriteValid_specialize isDefined isBin binding rest]

theorem callableHeadBranchesRewriteValid_specialize
    (isDefined isBin : String → Bool) (binding : Subst)
    (branches : List (Atom × List Goal)) :
    callableHeadBranchesRewriteValid binding branches
      (specializeCallableHeadBranches isDefined isBin binding branches) =
        true := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      simp [specializeCallableHeadBranches, callableHeadBranchesRewriteValid,
        callableHeadsRewriteValid_specialize isDefined isBin binding branch.2,
        callableHeadBranchesRewriteValid_specialize isDefined isBin binding
          rest]

end

/-- The executable guarded constructor always passes the independent exact
    shape validator. -/
theorem guardedClauseShapeValid_specializeClauseGuarded
    (isDefined isBin : String → Bool) (binding : Subst) (clause : Clause) :
    guardedClauseShapeValid binding clause
      (specializeClauseGuarded isDefined isBin binding clause) = true := by
  simp [guardedClauseShapeValid, specializeClauseGuarded,
    specializationGuards,
    callableHeadsRewriteValid_specialize isDefined isBin binding clause.body]

/-! ## Ordered clause-resolution transport -/

/-- A small dependency-free pairwise list relation.  Unlike a multiset
    relation, it records source order and multiplicity explicitly. -/
inductive SpecListRel {α β : Type} (rel : α → β → Prop) :
    List α → List β → Prop where
  | nil : SpecListRel rel [] []
  | cons {left right restLeft restRight}
      (head : rel left right)
      (tail : SpecListRel rel restLeft restRight) :
      SpecListRel rel (left :: restLeft) (right :: restRight)

namespace SpecListRel

theorem append {α β : Type} {rel : α → β → Prop}
    {xs xs' : List α} {ys ys' : List β}
    (hxs : SpecListRel rel xs ys) (hxs' : SpecListRel rel xs' ys') :
    SpecListRel rel (xs ++ xs') (ys ++ ys') := by
  induction hxs with
  | nil => exact hxs'
  | cons head tail ih => exact .cons head ih

theorem reverse {α β : Type} {rel : α → β → Prop}
    {xs : List α} {ys : List β} (h : SpecListRel rel xs ys) :
    SpecListRel rel xs.reverse ys.reverse := by
  induction h with
  | nil => exact .nil
  | @cons left right restLeft restRight head tail ih =>
      simpa using append ih (.cons head (.nil : SpecListRel rel [] []))

end SpecListRel

/-! ## Constructional profile-body relation -/

/- Exact semantic shape of the recursive profile builder.  A goal is either
    unchanged, retargeted to a concrete registry row naming the same parent,
    or contains recursively related subgoals.  This relation records the
    actual child record; it does not accept a generated-looking name alone. -/
mutual

inductive ProfileGoalRel (records : List SpecRecord) (binding : Subst) :
    Goal → Goal → Prop where
  | same (goal : Goal) : ProfileGoalRel records binding goal goal
  | retarget (parent child : String) (args : List Atom) (res : Atom)
      (record : SpecRecord) (member : record ∈ records)
      (name : record.name = child) (keyParent : record.key.parent = parent) :
      ProfileGoalRel records binding (.call parent args res)
        (.call child args res)
  | catchg (tmpl res : Atom) {sub rewritten : List Goal}
      (subRel : ProfileGoalsRel records binding sub rewritten) :
      ProfileGoalRel records binding (.catchg tmpl sub res)
        (.catchg tmpl rewritten res)
  | softcut (tmpl : Atom) {sub sub' thn thn' els els' : List Goal}
      (subRel : ProfileGoalsRel records binding sub sub')
      (thenRel : ProfileGoalsRel records binding thn thn')
      (elseRel : ProfileGoalsRel records binding els els') :
      ProfileGoalRel records binding (.softcut tmpl sub thn els)
        (.softcut tmpl sub' thn' els')
  | findall (tmpl res : Atom) {sub rewritten : List Goal}
      (subRel : ProfileGoalsRel records binding sub rewritten) :
      ProfileGoalRel records binding (.findall tmpl sub res)
        (.findall tmpl rewritten res)
  | onceg (tmpl res : Atom) {sub rewritten : List Goal}
      (subRel : ProfileGoalsRel records binding sub rewritten) :
      ProfileGoalRel records binding (.onceg tmpl sub res)
        (.onceg tmpl rewritten res)
  | transactiong (tmpl : Atom) {sub rewritten : List Goal}
      (subRel : ProfileGoalsRel records binding sub rewritten) :
      ProfileGoalRel records binding (.transactiong tmpl sub)
        (.transactiong tmpl rewritten)
  | amb (res : Atom) {branches rewritten : List (Atom × List Goal)}
      (branchesRel : ProfileBranchesRel records binding branches rewritten) :
      ProfileGoalRel records binding (.amb branches res)
        (.amb rewritten res)
  | ite (cond thenTemplate elseTemplate res : Atom)
      {thn thn' els els' : List Goal}
      (thenRel : ProfileGoalsRel records binding thn thn')
      (elseRel : ProfileGoalsRel records binding els els') :
      ProfileGoalRel records binding
        (.ite cond (thenTemplate, thn) (elseTemplate, els) res)
        (.ite cond (thenTemplate, thn') (elseTemplate, els') res)

inductive ProfileGoalsRel (records : List SpecRecord) (binding : Subst) :
    List Goal → List Goal → Prop where
  | nil : ProfileGoalsRel records binding [] []
  | cons {goal rewritten : Goal} {rest rewrittenRest : List Goal}
      (head : ProfileGoalRel records binding goal rewritten)
      (tail : ProfileGoalsRel records binding rest rewrittenRest) :
      ProfileGoalsRel records binding (goal :: rest)
        (rewritten :: rewrittenRest)

inductive ProfileBranchesRel (records : List SpecRecord) (binding : Subst) :
    List (Atom × List Goal) → List (Atom × List Goal) → Prop where
  | nil : ProfileBranchesRel records binding [] []
  | cons (tmpl : Atom) {goals rewritten : List Goal}
      {rest rewrittenRest : List (Atom × List Goal)}
      (head : ProfileGoalsRel records binding goals rewritten)
      (tail : ProfileBranchesRel records binding rest rewrittenRest) :
      ProfileBranchesRel records binding ((tmpl, goals) :: rest)
        ((tmpl, rewritten) :: rewrittenRest)

end

mutual

/-- Child evidence remains valid as later recursive construction grows the
    transaction registry. -/
theorem ProfileGoalRel.mono {before after : List SpecRecord}
    {binding : Subst} (records : before.Sublist after)
    {source target : Goal}
    (related : ProfileGoalRel before binding source target) :
    ProfileGoalRel after binding source target := by
  cases related with
  | same => exact .same source
  | retarget parent child args res record member name keyParent =>
      exact .retarget parent child args res record
        (List.Sublist.mem member records) name keyParent
  | catchg tmpl res subRel => exact .catchg tmpl res (subRel.mono records)
  | softcut tmpl subRel thenRel elseRel =>
      exact .softcut tmpl (subRel.mono records) (thenRel.mono records)
        (elseRel.mono records)
  | findall tmpl res subRel => exact .findall tmpl res (subRel.mono records)
  | onceg tmpl res subRel => exact .onceg tmpl res (subRel.mono records)
  | transactiong tmpl subRel =>
      exact .transactiong tmpl (subRel.mono records)
  | amb res branchesRel => exact .amb res (branchesRel.mono records)
  | ite cond thenTemplate elseTemplate res thenRel elseRel =>
      exact .ite cond thenTemplate elseTemplate res (thenRel.mono records)
        (elseRel.mono records)

theorem ProfileGoalsRel.mono {before after : List SpecRecord}
    {binding : Subst} (records : before.Sublist after)
    {source target : List Goal}
    (related : ProfileGoalsRel before binding source target) :
    ProfileGoalsRel after binding source target := by
  cases related with
  | nil => exact .nil
  | cons head tail => exact .cons (head.mono records) (tail.mono records)

theorem ProfileBranchesRel.mono {before after : List SpecRecord}
    {binding : Subst} (records : before.Sublist after)
    {source target : List (Atom × List Goal)}
    (related : ProfileBranchesRel before binding source target) :
    ProfileBranchesRel after binding source target := by
  cases related with
  | nil => exact .nil
  | cons tmpl head tail =>
      exact .cons tmpl (head.mono records) (tail.mono records)

end

mutual

/-- The constructional profile relation is equivariant under the actual
    suffix-based resolution freshener. -/
theorem ProfileGoalRel.renameSuffix {records : List SpecRecord}
    {binding : Subst} {source target : Goal}
    (related : ProfileGoalRel records binding source target)
    (suffix : String) (barrier : Nat) :
    ProfileGoalRel records (renameSpecBindingSuffix suffix binding)
      (renameGoalSuffix suffix barrier source)
      (renameGoalSuffix suffix barrier target) := by
  cases related with
  | same => exact .same (renameGoalSuffix suffix barrier source)
  | retarget parent child args res record member name keyParent =>
      exact .retarget parent child (args.map (renameAtomSuffix suffix))
        (renameAtomSuffix suffix res) record member name keyParent
  | catchg tmpl res subRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.catchg
        (renameAtomSuffix suffix tmpl) (renameAtomSuffix suffix res)
        (subRel.renameSuffix suffix barrier)
  | softcut tmpl subRel thenRel elseRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.softcut
        (renameAtomSuffix suffix tmpl) (subRel.renameSuffix suffix barrier)
        (thenRel.renameSuffix suffix barrier)
        (elseRel.renameSuffix suffix barrier)
  | findall tmpl res subRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.findall
        (renameAtomSuffix suffix tmpl) (renameAtomSuffix suffix res)
        (subRel.renameSuffix suffix barrier)
  | onceg tmpl res subRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.onceg
        (renameAtomSuffix suffix tmpl) (renameAtomSuffix suffix res)
        (subRel.renameSuffix suffix barrier)
  | transactiong tmpl subRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.transactiong
        (renameAtomSuffix suffix tmpl) (subRel.renameSuffix suffix barrier)
  | amb res branchesRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.amb
        (renameAtomSuffix suffix res) (branchesRel.renameSuffix suffix barrier)
  | ite cond thenTemplate elseTemplate res thenRel elseRel =>
      simpa [renameGoalSuffix] using ProfileGoalRel.ite
        (renameAtomSuffix suffix cond) (renameAtomSuffix suffix thenTemplate)
        (renameAtomSuffix suffix elseTemplate) (renameAtomSuffix suffix res)
        (thenRel.renameSuffix suffix barrier)
        (elseRel.renameSuffix suffix barrier)

theorem ProfileGoalsRel.renameSuffix {records : List SpecRecord}
    {binding : Subst} {source target : List Goal}
    (related : ProfileGoalsRel records binding source target)
    (suffix : String) (barrier : Nat) :
    ProfileGoalsRel records (renameSpecBindingSuffix suffix binding)
      (source.map (renameGoalSuffix suffix barrier))
      (target.map (renameGoalSuffix suffix barrier)) := by
  cases related with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.renameSuffix suffix barrier)
        (tail.renameSuffix suffix barrier)

theorem ProfileBranchesRel.renameSuffix {records : List SpecRecord}
    {binding : Subst} {source target : List (Atom × List Goal)}
    (related : ProfileBranchesRel records binding source target)
    (suffix : String) (barrier : Nat) :
    ProfileBranchesRel records (renameSpecBindingSuffix suffix binding)
      (source.map (fun branch =>
        (renameAtomSuffix suffix branch.1,
          branch.2.map (renameGoalSuffix suffix barrier))))
      (target.map (fun branch =>
        (renameAtomSuffix suffix branch.1,
          branch.2.map (renameGoalSuffix suffix barrier)))) := by
  cases related with
  | nil => exact .nil
  | cons tmpl head tail =>
      exact .cons (renameAtomSuffix suffix tmpl)
        (head.renameSuffix suffix barrier)
        (tail.renameSuffix suffix barrier)

end

/-- Internal prefix peeling keeps the construction relation's binding index
    fixed while the syntactic guard prefix shrinks. -/
private theorem ProfileGoalsRel.split_specializationGuards_aux
    (records : List SpecRecord) (wholeBinding binding : Subst)
    {source target : List Goal}
    (related : ProfileGoalsRel records wholeBinding
      (specializationGuards binding ++ source) target) :
    ∃ targetRest,
      target = specializationGuards binding ++ targetRest ∧
      ProfileGoalsRel records wholeBinding source targetRest := by
  induction binding generalizing target with
  | nil =>
      exact ⟨target, by simp [specializationGuards], by
        simpa [specializationGuards] using related⟩
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      simp only [specializationGuards] at related
      cases related with
      | cons head tail =>
          cases head with
          | same =>
              obtain ⟨targetRest, htarget, htail⟩ := ih tail
              refine ⟨targetRest, ?_, htail⟩
              rw [htarget]
              rfl

/-- The profile builder cannot rewrite a specialization guard: equality
    goals have only the reflexive arm of `ProfileGoalRel`.  Therefore an
    entire guard prefix peels off position-for-position, leaving the actual
    recursively profiled suffix. -/
theorem ProfileGoalsRel.split_specializationGuards
    (records : List SpecRecord) (binding : Subst)
    {source target : List Goal}
    (related : ProfileGoalsRel records binding
      (specializationGuards binding ++ source) target) :
    ∃ targetRest,
      target = specializationGuards binding ++ targetRest ∧
      ProfileGoalsRel records binding source targetRest := by
  exact ProfileGoalsRel.split_specializationGuards_aux records binding binding
    related

/-- One provenance row together with the actual pure callable-head snapshot
    and recursive child-call construction that produced its executable body.
    The equalities and inductive body relation are proof data; no Boolean
    validator is inverted to manufacture them. -/
inductive ProvenanceConstructed (records : List SpecRecord)
    (provenance : SpecClauseProvenance) : Prop where
  | intro (isDefined isBin : String → Bool)
      (freshened : provenance.binding =
        freshenSpecializationBinding provenance.parentClause
          provenance.sourceBinding)
      (sourceAligned : ∀ name value,
        (name, value) ∈ provenance.sourceBinding →
          SpecializationAlignedList name value
            provenance.parentClause.params provenance.discoveryActuals)
      (sourceKeysNodup :
        (provenance.sourceBinding.map Prod.fst).Nodup)
      (guarded : provenance.guardedClause =
        specializeClauseGuarded isDefined isBin provenance.binding
          provenance.parentClause)
      (body : ProfileGoalsRel records provenance.binding
        provenance.guardedClause.body provenance.executableClause.body) :
      ProvenanceConstructed records provenance

theorem ProvenanceConstructed.mono {before after : List SpecRecord}
    {provenance : SpecClauseProvenance} (records : before.Sublist after)
    (constructed : ProvenanceConstructed before provenance) :
    ProvenanceConstructed after provenance := by
  cases constructed with
  | intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded body =>
      exact .intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded
        (body.mono records)

/-- Construction exposes the exact alpha-copy equation retained in the
    provenance row; later simulation never has to reconstruct discovery. -/
theorem ProvenanceConstructed.binding_freshened
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance) :
    provenance.binding =
      freshenSpecializationBinding provenance.parentClause
        provenance.sourceBinding := by
  cases constructed with
  | intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded body =>
      exact freshened

/-- Construction exposes the literal static call-site origin of every
    pre-copy binding entry. -/
theorem ProvenanceConstructed.source_aligned
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance)
    (name : String) (value : Atom)
    (hmem : (name, value) ∈ provenance.sourceBinding) :
    SpecializationAlignedList name value provenance.parentClause.params
      provenance.discoveryActuals := by
  cases constructed with
  | intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded body =>
      exact sourceAligned name value hmem

/-- Construction exposes unique source-binding keys, as established by the
    real alignment algorithm. -/
theorem ProvenanceConstructed.source_keys_nodup
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance) :
    (provenance.sourceBinding.map Prod.fst).Nodup := by
  cases constructed with
  | intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded body =>
      exact sourceKeysNodup

/-- The shared alpha-copy changes only values, so executable binding keys
    remain unique. -/
theorem ProvenanceConstructed.binding_keys_nodup
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance) :
    (provenance.binding.map Prod.fst).Nodup := by
  rw [constructed.binding_freshened]
  have hkeys :
      ((freshenSpecializationBinding provenance.parentClause
        provenance.sourceBinding).map Prod.fst) =
        provenance.sourceBinding.map Prod.fst := by
    unfold freshenSpecializationBinding
    simp only [List.map_map]
    apply List.map_congr_left
    intro entry hentry
    rfl
  rw [hkeys]
  exact constructed.source_keys_nodup

/-- Suffix-freshened executable guard entries retain their exact source
    origin and discovery alignment. -/
theorem ProvenanceConstructed.renamed_binding_origin_suffix
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (renamedName : String) (renamedValue : Atom)
    (hmem : (renamedName, renamedValue) ∈
      renameSpecBindingSuffix suffix provenance.binding) :
    ∃ sourceName sourceValue,
      renamedName = sourceName ++ suffix ∧
      renamedValue = renameAtomSuffix suffix
        (Metta.Subst.apply
          (specializationCopySubst provenance.parentClause
            provenance.sourceBinding) sourceValue) ∧
      (sourceName, sourceValue) ∈ provenance.sourceBinding ∧
      SpecializationAlignedList sourceName sourceValue
        provenance.parentClause.params provenance.discoveryActuals := by
  unfold renameSpecBindingSuffix at hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨name, copiedValue⟩, hbinding, hp⟩ := hmem
  simp only [Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩
  have hfreshened := constructed.binding_freshened
  rw [hfreshened] at hbinding
  obtain ⟨sourceValue, hsource, hcopy⟩ :=
    freshenSpecializationBinding_mem_origin provenance.parentClause
      provenance.sourceBinding name copiedValue hbinding
  subst copiedValue
  exact ⟨name, sourceValue, rfl, rfl, hsource,
    constructed.source_aligned name sourceValue hsource⟩

/-- Every suffix-renamed guard entry is the unique lookup selected by
    one-pass binding application. -/
theorem ProvenanceConstructed.renamed_binding_lookup_suffix
    {records : List SpecRecord} {provenance : SpecClauseProvenance}
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (name : String) (value : Atom)
    (hmem : (name, value) ∈
      renameSpecBindingSuffix suffix provenance.binding) :
    Metta.Subst.lookup (renameSpecBindingSuffix suffix provenance.binding)
      name = some value := by
  apply subst_lookup_of_mem_of_keys_nodup
  · exact renameSpecBindingSuffix_keys_nodup suffix provenance.binding
      constructed.binding_keys_nodup
  · exact hmem

/-- Construction evidence exposes the executable body as the literal guard
    prefix followed by the recursively profiled callable-head rewrite. -/
theorem ProvenanceConstructed.body_shape (records : List SpecRecord)
    (provenance : SpecClauseProvenance)
    (constructed : ProvenanceConstructed records provenance) :
    ∃ isDefined isBin rewritten,
      provenance.executableClause.body =
        specializationGuards provenance.binding ++ rewritten ∧
      ProfileGoalsRel records provenance.binding
        (specializeCallableHeadGoals isDefined isBin provenance.binding
          provenance.parentClause.body) rewritten := by
  cases constructed with
  | intro isDefined isBin freshened sourceAligned sourceKeysNodup guarded body =>
      have hbody : ProfileGoalsRel records provenance.binding
          (specializationGuards provenance.binding ++
            specializeCallableHeadGoals isDefined isBin provenance.binding
              provenance.parentClause.body)
          provenance.executableClause.body := by
        rw [guarded] at body
        simpa [specializeClauseGuarded] using body
      obtain ⟨rewritten, hrewritten, hrelated⟩ :=
        hbody.split_specializationGuards records provenance.binding
      exact ⟨isDefined, isBin, rewritten, hrewritten, hrelated⟩

/-- Construction shape after the actual suffix-based standardizing-apart
    transformation used by `resolveAlts`. -/
theorem ProvenanceConstructed.renamed_body_shape_suffix
    (records : List SpecRecord) (provenance : SpecClauseProvenance)
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (barrier : Nat) :
    ∃ isDefined isBin sourceBody targetBody,
      sourceBody =
        (specializeCallableHeadGoals isDefined isBin provenance.binding
          provenance.parentClause.body).map
            (renameGoalSuffix suffix barrier) ∧
      provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) =
        specializationGuards
            (renameSpecBindingSuffix suffix provenance.binding) ++
          targetBody ∧
      ProfileGoalsRel records
        (renameSpecBindingSuffix suffix provenance.binding)
        sourceBody targetBody := by
  obtain ⟨isDefined, isBin, rewritten, hbody, hrelated⟩ :=
    constructed.body_shape records provenance
  refine ⟨isDefined, isBin,
    (specializeCallableHeadGoals isDefined isBin provenance.binding
      provenance.parentClause.body).map (renameGoalSuffix suffix barrier),
    rewritten.map (renameGoalSuffix suffix barrier), rfl, ?_, ?_⟩
  · rw [hbody, List.map_append, rename_specializationGuards_suffix]
  · exact hrelated.renameSuffix suffix barrier

/-- Every provenance row currently installed in a transaction was produced
    by the constructional profile-body relation over that transaction's
    complete committed-plus-provisional registry. -/
def SpecBuildConstructed (st : SpecBuildState) : Prop :=
  ∀ provenance, provenance ∈ st.world.specClauseProvenance →
    ProvenanceConstructed st.registry provenance

theorem SpecBuildConstructed.reindex {before after : SpecBuildState}
    (constructed : SpecBuildConstructed before)
    (provenance : after.world.specClauseProvenance =
      before.world.specClauseProvenance)
    (records : before.registry.Sublist after.registry) :
    SpecBuildConstructed after := by
  intro item hitem
  rw [provenance] at hitem
  exact (constructed item hitem).mono records

/-- Mutual construction theorem for the three profile-builder entry points.
    Successful execution returns the exact recursive relation above, indexed
    by the final transaction registry. -/
structure BuildProfileSemanticAtFuel (fuel : Nat) : Prop where
  goals : ∀ st binding source after target,
    SpecBuildOrdered st →
    buildProfileGoals fuel st binding source = some (after, target) →
    ProfileGoalsRel after.registry binding source target
  goal : ∀ st binding source after target,
    SpecBuildOrdered st →
    buildProfileGoal fuel st binding source = some (after, target) →
    ProfileGoalRel after.registry binding source target
  branches : ∀ st binding source after target,
    SpecBuildOrdered st →
    buildProfileBranches fuel st binding source = some (after, target) →
    ProfileBranchesRel after.registry binding source target

private theorem buildProfileSemanticAtFuel_zero :
    BuildProfileSemanticAtFuel 0 := by
  constructor
  · intro st binding source after target invariant hbuild
    cases source with
    | nil =>
        simp [buildProfileGoals] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact .nil
    | cons goal rest => simp [buildProfileGoals] at hbuild
  · intro st binding source after target invariant hbuild
    simp [buildProfileGoal] at hbuild
  · intro st binding source after target invariant hbuild
    cases source with
    | nil =>
        simp [buildProfileBranches] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact .nil
    | cons branch rest => simp [buildProfileBranches] at hbuild

private theorem buildProfileGoals_semantic_succ (fuel : Nat)
    (ih : BuildProfileSemanticAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : List Goal) (after : SpecBuildState)
    (target : List Goal) (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileGoals (fuel + 1) st binding source =
      some (after, target)) :
    ProfileGoalsRel after.registry binding source target := by
  cases source with
  | nil =>
      simp [buildProfileGoals] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact .nil
  | cons goal rest =>
      simp only [buildProfileGoals] at hbuild
      cases hgoal : buildProfileGoal fuel st binding goal with
      | none => simp [hgoal] at hbuild
      | some goalResult =>
          rcases goalResult with ⟨afterGoal, rewrittenGoal⟩
          simp only [hgoal] at hbuild
          cases hrest : buildProfileGoals fuel afterGoal binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hgoalFrame := (buildOrderedAtFuel fuel).goal st binding
                goal afterGoal rewrittenGoal invariant hgoal
              have hrestFrame := (buildOrderedAtFuel fuel).goals afterGoal
                binding rest afterRest rewrittenRest hgoalFrame.valid hrest
              have hhead := ih.goal st binding goal afterGoal rewrittenGoal
                invariant hgoal
              have htail := ih.goals afterGoal binding rest afterRest
                rewrittenRest hgoalFrame.valid hrest
              exact .cons (hhead.mono hrestFrame.registrySublist) htail

private theorem buildProfileBranches_semantic_succ (fuel : Nat)
    (ih : BuildProfileSemanticAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : List (Atom × List Goal))
    (after : SpecBuildState) (target : List (Atom × List Goal))
    (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileBranches (fuel + 1) st binding source =
      some (after, target)) :
    ProfileBranchesRel after.registry binding source target := by
  cases source with
  | nil =>
      simp [buildProfileBranches] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact .nil
  | cons branch rest =>
      rcases branch with ⟨tmpl, goals⟩
      simp only [buildProfileBranches] at hbuild
      cases hgoals : buildProfileGoals fuel st binding goals with
      | none => simp [hgoals] at hbuild
      | some goalsResult =>
          rcases goalsResult with ⟨afterGoals, rewrittenGoals⟩
          simp only [hgoals] at hbuild
          cases hrest : buildProfileBranches fuel afterGoals binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hgoalsFrame := (buildOrderedAtFuel fuel).goals st binding
                goals afterGoals rewrittenGoals invariant hgoals
              have hrestFrame := (buildOrderedAtFuel fuel).branches afterGoals
                binding rest afterRest rewrittenRest hgoalsFrame.valid hrest
              have hhead := ih.goals st binding goals afterGoals
                rewrittenGoals invariant hgoals
              have htail := ih.branches afterGoals binding rest afterRest
                rewrittenRest hgoalsFrame.valid hrest
              exact .cons tmpl (hhead.mono hrestFrame.registrySublist) htail

private theorem buildProfileGoal_semantic_succ (fuel : Nat)
    (ih : BuildProfileSemanticAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : Goal) (after : SpecBuildState)
    (target : Goal) (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileGoal (fuel + 1) st binding source =
      some (after, target)) :
    ProfileGoalRel after.registry binding source target := by
  cases source with
  | call parent args res =>
      simp only [buildProfileGoal] at hbuild
      cases hrequest : buildSpecRequest fuel st parent
          (args.map (Metta.Subst.apply binding)) with
      | none => simp [hrequest] at hbuild
      | some requestResult =>
          rcases requestResult with ⟨next, found⟩
          simp only [hrequest] at hbuild
          cases found with
          | none =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact .same (.call parent args res)
          | some child =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              obtain ⟨record, hmember, hname, hparent⟩ :=
                buildSpecRequest_success_record fuel st next parent
                  (args.map (Metta.Subst.apply binding)) child invariant
                  hrequest
              exact .retarget parent child args res record hmember hname
                hparent
  | catchg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact .catchg tmpl res
            (ih.goals st binding sub next rewritten invariant hsub)
  | softcut tmpl sub thn els =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨afterSub, sub'⟩
          simp only [hsub] at hbuild
          cases hthen : buildProfileGoals fuel afterSub binding thn with
          | none => simp [hthen] at hbuild
          | some thenResult =>
              rcases thenResult with ⟨afterThen, thn'⟩
              simp only [hthen] at hbuild
              cases helse : buildProfileGoals fuel afterThen binding els with
              | none => simp [helse] at hbuild
              | some elseResult =>
                  rcases elseResult with ⟨afterElse, els'⟩
                  simp [helse] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  have hsubFrame := (buildOrderedAtFuel fuel).goals st binding
                    sub afterSub sub' invariant hsub
                  have hthenFrame := (buildOrderedAtFuel fuel).goals afterSub
                    binding thn afterThen thn' hsubFrame.valid hthen
                  have helseFrame := (buildOrderedAtFuel fuel).goals afterThen
                    binding els afterElse els' hthenFrame.valid helse
                  have hsubRel := ih.goals st binding sub afterSub sub'
                    invariant hsub
                  have hthenRel := ih.goals afterSub binding thn afterThen thn'
                    hsubFrame.valid hthen
                  have helseRel := ih.goals afterThen binding els afterElse els'
                    hthenFrame.valid helse
                  exact .softcut tmpl
                    (hsubRel.mono (hthenFrame.registrySublist.trans
                      helseFrame.registrySublist))
                    (hthenRel.mono helseFrame.registrySublist) helseRel
  | findall tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact .findall tmpl res
            (ih.goals st binding sub next rewritten invariant hsub)
  | onceg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact .onceg tmpl res
            (ih.goals st binding sub next rewritten invariant hsub)
  | transactiong tmpl sub =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact .transactiong tmpl
            (ih.goals st binding sub next rewritten invariant hsub)
  | amb branches res =>
      simp only [buildProfileGoal] at hbuild
      cases hbranches : buildProfileBranches fuel st binding branches with
      | none => simp [hbranches] at hbuild
      | some branchResult =>
          rcases branchResult with ⟨next, rewritten⟩
          simp [hbranches] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact .amb res
            (ih.branches st binding branches next rewritten invariant
              hbranches)
  | ite cond thn els res =>
      simp only [buildProfileGoal] at hbuild
      cases hthen : buildProfileGoals fuel st binding thn.2 with
      | none => simp [hthen] at hbuild
      | some thenResult =>
          rcases thenResult with ⟨afterThen, thnGoals⟩
          simp only [hthen] at hbuild
          cases helse : buildProfileGoals fuel afterThen binding els.2 with
          | none => simp [helse] at hbuild
          | some elseResult =>
              rcases elseResult with ⟨afterElse, elsGoals⟩
              simp [helse] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hthenFrame := (buildOrderedAtFuel fuel).goals st binding
                thn.2 afterThen thnGoals invariant hthen
              have helseFrame := (buildOrderedAtFuel fuel).goals afterThen
                binding els.2 afterElse elsGoals hthenFrame.valid helse
              have hthenRel := ih.goals st binding thn.2 afterThen thnGoals
                invariant hthen
              have helseRel := ih.goals afterThen binding els.2 afterElse
                elsGoals hthenFrame.valid helse
              exact .ite cond thn.1 els.1 res
                (hthenRel.mono helseFrame.registrySublist) helseRel
  | _ =>
      simp [buildProfileGoal] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact .same _

theorem buildProfileSemanticAtFuel (fuel : Nat) :
    BuildProfileSemanticAtFuel fuel := by
  induction fuel with
  | zero => exact buildProfileSemanticAtFuel_zero
  | succ fuel ih =>
      constructor
      · intro st binding source after target invariant hbuild
        exact buildProfileGoals_semantic_succ fuel ih st binding source after
          target invariant hbuild
      · intro st binding source after target invariant hbuild
        exact buildProfileGoal_semantic_succ fuel ih st binding source after
          target invariant hbuild
      · intro st binding source after target invariant hbuild
        exact buildProfileBranches_semantic_succ fuel ih st binding source
          after target invariant hbuild

/-- Public construction theorem for clause-body building. -/
theorem buildProfileGoals_semantic (fuel : Nat) (st after : SpecBuildState)
    (binding : Subst) (source target : List Goal)
    (invariant : SpecBuildOrdered st)
    (hbuild : buildProfileGoals fuel st binding source = some (after, target)) :
    ProfileGoalsRel after.registry binding source target :=
  (buildProfileSemanticAtFuel fuel).goals st binding source after target
    invariant hbuild

/-- Every clause emitted by the real recursive clause builder carries the
    exact constructional provenance relation.  Later sibling construction is
    handled by monotonic transport of concrete child-record membership. -/
theorem buildSpecClauses_constructed (fuel : Nat) (st after : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate) (built : List BuiltSpecClause)
    (invariant : SpecBuildOrdered st)
    (sourceAligned : ∀ candidate, candidate ∈ candidates →
      candidate.SourceAligned)
    (sourceKeysNodup : ∀ candidate, candidate ∈ candidates →
      (candidate.sourceBinding.map Prod.fst).Nodup)
    (hbuild : buildSpecClauses fuel st key specName candidates =
      some (after, built)) :
    ∀ item, item ∈ built →
      ProvenanceConstructed after.registry item.provenance := by
  induction fuel generalizing st candidates after built with
  | zero =>
      cases candidates with
      | nil =>
          simp [buildSpecClauses] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          simp
      | cons candidate rest => simp [buildSpecClauses] at hbuild
  | succ fuel ih =>
      cases candidates with
      | nil =>
          simp [buildSpecClauses] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          simp
      | cons candidate rest =>
          simp only [buildSpecClauses] at hbuild
          let instantiated := instantiateGoals candidate.binding
            candidate.captured.compiled.body
          let gained := profileDynamicUseGoals st.isDefined st.isBin
            instantiated
          let base := specializeClauseGuarded st.isDefined st.isBin
            candidate.binding candidate.captured.compiled
          let gainedState := if gained then st.markGain key else st
          have hgainInvariant : SpecBuildOrdered gainedState := by
            dsimp only [gainedState]
            split
            · exact invariant.markGain st key
            · exact invariant
          cases hbody : buildProfileGoals fuel gainedState candidate.binding
              base.body with
          | none =>
              simp [instantiated, gained, base, gainedState, hbody] at hbuild
          | some bodyResult =>
              rcases bodyResult with ⟨afterBody, body⟩
              simp only [instantiated, gained, base, gainedState, hbody]
                at hbuild
              split at hbuild
              · contradiction
              · cases hrest : buildSpecClauses fuel afterBody key specName rest
                  with
                | none => simp [hrest] at hbuild
                | some restResult =>
                    rcases restResult with ⟨afterRest, builtRest⟩
                    simp [hrest] at hbuild
                    rcases hbuild with ⟨rfl, rfl⟩
                    have hbodyFrame := (buildOrderedAtFuel fuel).goals
                      gainedState candidate.binding base.body afterBody body
                      hgainInvariant hbody
                    have hrestFrame := (buildOrderedAtFuel fuel).clauses
                      afterBody key specName rest afterRest builtRest
                      hbodyFrame.valid hrest
                    have hbodyRel := buildProfileGoals_semantic fuel
                      gainedState afterBody candidate.binding base.body body
                      hgainInvariant hbody
                    intro item hitem
                    simp only [List.mem_cons] at hitem
                    rcases hitem with rfl | hitem
                    · refine .intro st.isDefined st.isBin ?_ ?_ ?_ rfl ?_
                      · rfl
                      · exact sourceAligned candidate (by simp)
                      · exact sourceKeysNodup candidate (by simp)
                      exact hbodyRel.mono hrestFrame.registrySublist
                    · exact ih afterBody afterRest rest builtRest
                        hbodyFrame.valid
                        (fun next hnext => sourceAligned next (by
                          simp [hnext]))
                        (fun next hnext => sourceKeysNodup next (by
                          simp [hnext])) hrest item hitem

/-- Mutual preservation theorem for constructional provenance across every
    recursive builder entry point. -/
structure BuildConstructedAtFuel (fuel : Nat) : Prop where
  request : ∀ st parent actuals after result,
    SpecBuildOrdered st → SpecBuildConstructed st →
    buildSpecRequest fuel st parent actuals = some (after, result) →
    SpecBuildConstructed after
  clauses : ∀ st key specName candidates after built,
    SpecBuildOrdered st → SpecBuildConstructed st →
    buildSpecClauses fuel st key specName candidates = some (after, built) →
    SpecBuildConstructed after
  goals : ∀ st binding source after target,
    SpecBuildOrdered st → SpecBuildConstructed st →
    buildProfileGoals fuel st binding source = some (after, target) →
    SpecBuildConstructed after
  goal : ∀ st binding source after target,
    SpecBuildOrdered st → SpecBuildConstructed st →
    buildProfileGoal fuel st binding source = some (after, target) →
    SpecBuildConstructed after
  branches : ∀ st binding source after target,
    SpecBuildOrdered st → SpecBuildConstructed st →
    buildProfileBranches fuel st binding source = some (after, target) →
    SpecBuildConstructed after

private theorem buildConstructedAtFuel_zero : BuildConstructedAtFuel 0 := by
  constructor
  · intro st parent actuals after result ordered constructed hbuild
    simp [buildSpecRequest] at hbuild
  · intro st key specName candidates after built ordered constructed hbuild
    cases candidates with
    | nil =>
        simp [buildSpecClauses] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact constructed
    | cons candidate rest => simp [buildSpecClauses] at hbuild
  · intro st binding source after target ordered constructed hbuild
    cases source with
    | nil =>
        simp [buildProfileGoals] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact constructed
    | cons goal rest => simp [buildProfileGoals] at hbuild
  · intro st binding source after target ordered constructed hbuild
    simp [buildProfileGoal] at hbuild
  · intro st binding source after target ordered constructed hbuild
    cases source with
    | nil =>
        simp [buildProfileBranches] at hbuild
        rcases hbuild with ⟨rfl, rfl⟩
        exact constructed
    | cons branch rest => simp [buildProfileBranches] at hbuild

private theorem buildProfileGoals_constructed_succ (fuel : Nat)
    (ih : BuildConstructedAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : List Goal) (after : SpecBuildState)
    (target : List Goal) (ordered : SpecBuildOrdered st)
    (constructed : SpecBuildConstructed st)
    (hbuild : buildProfileGoals (fuel + 1) st binding source =
      some (after, target)) :
    SpecBuildConstructed after := by
  cases source with
  | nil =>
      simp [buildProfileGoals] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact constructed
  | cons goal rest =>
      simp only [buildProfileGoals] at hbuild
      cases hgoal : buildProfileGoal fuel st binding goal with
      | none => simp [hgoal] at hbuild
      | some goalResult =>
          rcases goalResult with ⟨afterGoal, rewrittenGoal⟩
          simp only [hgoal] at hbuild
          cases hrest : buildProfileGoals fuel afterGoal binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hgoalOrdered := (buildOrderedAtFuel fuel).goal st binding
                goal afterGoal rewrittenGoal ordered hgoal
              have hgoalConstructed := ih.goal st binding goal afterGoal
                rewrittenGoal ordered constructed hgoal
              exact ih.goals afterGoal binding rest afterRest rewrittenRest
                hgoalOrdered.valid hgoalConstructed hrest

private theorem buildProfileBranches_constructed_succ (fuel : Nat)
    (ih : BuildConstructedAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : List (Atom × List Goal))
    (after : SpecBuildState) (target : List (Atom × List Goal))
    (ordered : SpecBuildOrdered st) (constructed : SpecBuildConstructed st)
    (hbuild : buildProfileBranches (fuel + 1) st binding source =
      some (after, target)) :
    SpecBuildConstructed after := by
  cases source with
  | nil =>
      simp [buildProfileBranches] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact constructed
  | cons branch rest =>
      rcases branch with ⟨tmpl, goals⟩
      simp only [buildProfileBranches] at hbuild
      cases hgoals : buildProfileGoals fuel st binding goals with
      | none => simp [hgoals] at hbuild
      | some goalsResult =>
          rcases goalsResult with ⟨afterGoals, rewrittenGoals⟩
          simp only [hgoals] at hbuild
          cases hrest : buildProfileBranches fuel afterGoals binding rest with
          | none => simp [hrest] at hbuild
          | some restResult =>
              rcases restResult with ⟨afterRest, rewrittenRest⟩
              simp [hrest] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hgoalsOrdered := (buildOrderedAtFuel fuel).goals st binding
                goals afterGoals rewrittenGoals ordered hgoals
              have hgoalsConstructed := ih.goals st binding goals afterGoals
                rewrittenGoals ordered constructed hgoals
              exact ih.branches afterGoals binding rest afterRest rewrittenRest
                hgoalsOrdered.valid hgoalsConstructed hrest

private theorem buildProfileGoal_constructed_succ (fuel : Nat)
    (ih : BuildConstructedAtFuel fuel) (st : SpecBuildState)
    (binding : Subst) (source : Goal) (after : SpecBuildState)
    (target : Goal) (ordered : SpecBuildOrdered st)
    (constructed : SpecBuildConstructed st)
    (hbuild : buildProfileGoal (fuel + 1) st binding source =
      some (after, target)) :
    SpecBuildConstructed after := by
  cases source with
  | call parent args res =>
      simp only [buildProfileGoal] at hbuild
      cases hrequest : buildSpecRequest fuel st parent
          (args.map (Metta.Subst.apply binding)) with
      | none => simp [hrequest] at hbuild
      | some requestResult =>
          rcases requestResult with ⟨next, found⟩
          simp only [hrequest] at hbuild
          cases found with
          | none =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st parent
                (args.map (Metta.Subst.apply binding)) next none ordered
                constructed hrequest
          | some child =>
              simp at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact ih.request st parent
                (args.map (Metta.Subst.apply binding)) next (some child)
                ordered constructed hrequest
  | catchg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next rewritten ordered constructed hsub
  | softcut tmpl sub thn els =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨afterSub, sub'⟩
          simp only [hsub] at hbuild
          cases hthen : buildProfileGoals fuel afterSub binding thn with
          | none => simp [hthen] at hbuild
          | some thenResult =>
              rcases thenResult with ⟨afterThen, thn'⟩
              simp only [hthen] at hbuild
              cases helse : buildProfileGoals fuel afterThen binding els with
              | none => simp [helse] at hbuild
              | some elseResult =>
                  rcases elseResult with ⟨afterElse, els'⟩
                  simp [helse] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  have hsubOrdered := (buildOrderedAtFuel fuel).goals st
                    binding sub afterSub sub' ordered hsub
                  have hsubConstructed := ih.goals st binding sub afterSub
                    sub' ordered constructed hsub
                  have hthenOrdered := (buildOrderedAtFuel fuel).goals
                    afterSub binding thn afterThen thn' hsubOrdered.valid hthen
                  have hthenConstructed := ih.goals afterSub binding thn
                    afterThen thn' hsubOrdered.valid hsubConstructed hthen
                  exact ih.goals afterThen binding els afterElse els'
                    hthenOrdered.valid hthenConstructed helse
  | findall tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next rewritten ordered constructed hsub
  | onceg tmpl sub res =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next rewritten ordered constructed hsub
  | transactiong tmpl sub =>
      simp only [buildProfileGoal] at hbuild
      cases hsub : buildProfileGoals fuel st binding sub with
      | none => simp [hsub] at hbuild
      | some subResult =>
          rcases subResult with ⟨next, rewritten⟩
          simp [hsub] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.goals st binding sub next rewritten ordered constructed hsub
  | amb branches res =>
      simp only [buildProfileGoal] at hbuild
      cases hbranches : buildProfileBranches fuel st binding branches with
      | none => simp [hbranches] at hbuild
      | some branchResult =>
          rcases branchResult with ⟨next, rewritten⟩
          simp [hbranches] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact ih.branches st binding branches next rewritten ordered
            constructed hbranches
  | ite cond thn els res =>
      simp only [buildProfileGoal] at hbuild
      cases hthen : buildProfileGoals fuel st binding thn.2 with
      | none => simp [hthen] at hbuild
      | some thenResult =>
          rcases thenResult with ⟨afterThen, thnGoals⟩
          simp only [hthen] at hbuild
          cases helse : buildProfileGoals fuel afterThen binding els.2 with
          | none => simp [helse] at hbuild
          | some elseResult =>
              rcases elseResult with ⟨afterElse, elsGoals⟩
              simp [helse] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              have hthenOrdered := (buildOrderedAtFuel fuel).goals st binding
                thn.2 afterThen thnGoals ordered hthen
              have hthenConstructed := ih.goals st binding thn.2 afterThen
                thnGoals ordered constructed hthen
              exact ih.goals afterThen binding els.2 afterElse elsGoals
                hthenOrdered.valid hthenConstructed helse
  | _ =>
      simp [buildProfileGoal] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact constructed

private theorem buildSpecClauses_constructed_invariant_succ (fuel : Nat)
    (ih : BuildConstructedAtFuel fuel) (st : SpecBuildState)
    (key : SpecKey) (specName : String)
    (candidates : List SpecClauseCandidate) (after : SpecBuildState)
    (built : List BuiltSpecClause) (ordered : SpecBuildOrdered st)
    (constructed : SpecBuildConstructed st)
    (hbuild : buildSpecClauses (fuel + 1) st key specName candidates =
      some (after, built)) :
    SpecBuildConstructed after := by
  cases candidates with
  | nil =>
      simp [buildSpecClauses] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact constructed
  | cons candidate rest =>
      simp only [buildSpecClauses] at hbuild
      let instantiated := instantiateGoals candidate.binding
        candidate.captured.compiled.body
      let gained := profileDynamicUseGoals st.isDefined st.isBin instantiated
      let base := specializeClauseGuarded st.isDefined st.isBin
        candidate.binding candidate.captured.compiled
      let gainedState := if gained then st.markGain key else st
      have hgainOrdered : SpecBuildOrdered gainedState := by
        dsimp only [gainedState]
        split
        · exact ordered.markGain st key
        · exact ordered
      have hgainConstructed : SpecBuildConstructed gainedState := by
        dsimp only [gainedState]
        split
        · unfold SpecBuildState.markGain
          split <;> exact constructed
        · exact constructed
      cases hbody : buildProfileGoals fuel gainedState candidate.binding
          base.body with
      | none => simp [instantiated, gained, base, gainedState, hbody] at hbuild
      | some bodyResult =>
          rcases bodyResult with ⟨afterBody, body⟩
          simp only [instantiated, gained, base, gainedState, hbody] at hbuild
          split at hbuild
          · contradiction
          · cases hrest : buildSpecClauses fuel afterBody key specName rest with
            | none => simp [hrest] at hbuild
            | some restResult =>
                rcases restResult with ⟨afterRest, builtRest⟩
                simp [hrest] at hbuild
                rcases hbuild with ⟨rfl, rfl⟩
                have hbodyOrdered := (buildOrderedAtFuel fuel).goals
                  gainedState candidate.binding base.body afterBody body
                  hgainOrdered hbody
                have hbodyConstructed := ih.goals gainedState
                  candidate.binding base.body afterBody body hgainOrdered
                  hgainConstructed hbody
                exact ih.clauses afterBody key specName rest afterRest
                  builtRest hbodyOrdered.valid hbodyConstructed hrest

private theorem buildSpecRequest_constructed_succ (fuel : Nat)
    (ih : BuildConstructedAtFuel fuel) (st : SpecBuildState)
    (parent : String) (actuals : List Atom) (after : SpecBuildState)
    (result : Option String) (ordered : SpecBuildOrdered st)
    (constructed : SpecBuildConstructed st)
    (hbuild : buildSpecRequest (fuel + 1) st parent actuals =
      some (after, result)) :
    SpecBuildConstructed after := by
  cases hdiscover : discoverSpecialization st.isSpecializable st.hasMeta
      parent actuals st.world.metaClauses with
  | none =>
      simp [buildSpecRequest, hdiscover] at hbuild
      rcases hbuild with ⟨rfl, rfl⟩
      exact constructed
  | some candidate =>
      cases hsafe : candidate.clauses.all SpecClauseCandidate.safe with
      | false =>
          simp [buildSpecRequest, hdiscover, hsafe] at hbuild
          rcases hbuild with ⟨rfl, rfl⟩
          exact constructed
      | true =>
          cases hfound : st.findRecord? candidate.key with
          | some record =>
              simp [buildSpecRequest, hdiscover, hsafe, hfound] at hbuild
              rcases hbuild with ⟨rfl, rfl⟩
              exact constructed
          | none =>
              let record : SpecRecord :=
                { key := candidate.key
                  name := specializationName candidate.key }
              cases hcollision : st.isNameOccupied record.name with
              | true =>
                  simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                    hcollision] at hbuild
                  rcases hbuild with ⟨rfl, rfl⟩
                  exact constructed
              | false =>
                  let registered : SpecBuildState :=
                    { st with
                        provisional := st.provisional ++ [record]
                        pending := st.pending ++ [candidate.key]
                        world := installCopiedTypes st.world parent
                          record.name }
                  cases hclauses : buildSpecClauses fuel registered
                      candidate.key record.name candidate.clauses with
                  | none =>
                      simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                        registered, hcollision, hclauses] at hbuild
                  | some clausesResult =>
                      rcases clausesResult with ⟨expanded, built⟩
                      simp [buildSpecRequest, hdiscover, hsafe, hfound, record,
                        registered, hcollision, hclauses] at hbuild
                      rcases hbuild with ⟨rfl, rfl⟩
                      have hspecEmpty :
                          st.world.clausesOf record.name = [] := by
                        cases hclausesAtName : st.world.clausesOf record.name with
                        | nil => rfl
                        | cons clause rest =>
                            simp [SpecBuildState.isNameOccupied,
                              SpecBuildState.isDefined, hclausesAtName]
                              at hcollision
                      have hnameFresh :=
                        ordered.name_not_mem_of_not_occupied record.name
                          hcollision
                      have hregisteredOrdered : SpecBuildOrdered registered := by
                        exact ordered.register st parent record hspecEmpty
                          hnameFresh
                      have hregisteredRecords :
                          st.registry.Sublist registered.registry := by
                        change
                          (st.world.specializations ++ st.provisional).Sublist
                            ((installCopiedTypes st.world parent record.name
                              ).specializations ++
                              (st.provisional ++ [record]))
                        rw [installCopiedTypes_specializations]
                        exact
                          (List.Sublist.refl st.world.specializations).append
                            (List.sublist_append_left st.provisional [record])
                      have hregisteredConstructed :
                          SpecBuildConstructed registered := by
                        exact constructed.reindex
                          (installCopiedTypes_specClauseProvenance st.world
                            parent record.name)
                          hregisteredRecords
                      have hrecursiveOrdered := (buildOrderedAtFuel fuel).clauses
                        registered candidate.key record.name candidate.clauses
                        expanded built hregisteredOrdered hclauses
                      have hrecursiveConstructed := ih.clauses registered
                        candidate.key record.name candidate.clauses expanded
                        built hregisteredOrdered hregisteredConstructed hclauses
                      have hcandidateAligned : ∀ clause,
                          clause ∈ candidate.clauses →
                            clause.SourceAligned :=
                        discoverSpecialization_clauses_sourceAligned
                          st.isSpecializable st.hasMeta parent actuals
                          st.world.metaClauses candidate hdiscover
                      have hcandidateKeysNodup : ∀ clause,
                          clause ∈ candidate.clauses →
                            (clause.sourceBinding.map Prod.fst).Nodup :=
                        discoverSpecialization_clauses_sourceKeysNodup
                          st.isSpecializable st.hasMeta parent actuals
                          st.world.metaClauses candidate hdiscover
                      have hbuiltRows := buildSpecClauses_constructed fuel
                        registered expanded candidate.key record.name
                        candidate.clauses built hregisteredOrdered
                        hcandidateAligned hcandidateKeysNodup hclauses
                      let finished : SpecBuildState :=
                        { expanded with
                            world := installBuiltClauses expanded.world
                              record.name built
                            pending := expanded.pending.filter
                              (· != candidate.key)
                            expanded := expanded.expanded ++ [candidate.key] }
                      change SpecBuildConstructed finished
                      have hfinishedProvenance :
                          finished.world.specClauseProvenance =
                            expanded.world.specClauseProvenance ++
                              built.reverse.map (·.provenance) := by
                        exact (installBuiltClauses_exact_fields expanded.world
                          record.name built).2
                      have hfinishedRegistry :
                          finished.registry = expanded.registry := by
                        simp [finished, SpecBuildState.registry,
                          installBuiltClauses_specializations]
                      intro provenance hprovenance
                      rw [hfinishedProvenance] at hprovenance
                      rcases List.mem_append.mp hprovenance with
                        hold | hnew
                      · rw [hfinishedRegistry]
                        exact hrecursiveConstructed provenance hold
                      · rcases List.mem_map.mp hnew with
                          ⟨item, hitem, rfl⟩
                        have hitemBuilt : item ∈ built := by
                          simpa using hitem
                        rw [hfinishedRegistry]
                        exact hbuiltRows item hitemBuilt

theorem buildConstructedAtFuel (fuel : Nat) : BuildConstructedAtFuel fuel := by
  induction fuel with
  | zero => exact buildConstructedAtFuel_zero
  | succ fuel ih =>
      constructor
      · intro st parent actuals after result ordered constructed hbuild
        exact buildSpecRequest_constructed_succ fuel ih st parent actuals after
          result ordered constructed hbuild
      · intro st key specName candidates after built ordered constructed hbuild
        exact buildSpecClauses_constructed_invariant_succ fuel ih st key
          specName candidates after built ordered constructed hbuild
      · intro st binding source after target ordered constructed hbuild
        exact buildProfileGoals_constructed_succ fuel ih st binding source
          after target ordered constructed hbuild
      · intro st binding source after target ordered constructed hbuild
        exact buildProfileGoal_constructed_succ fuel ih st binding source after
          target ordered constructed hbuild
      · intro st binding source after target ordered constructed hbuild
        exact buildProfileBranches_constructed_succ fuel ih st binding source
          after target ordered constructed hbuild

theorem buildSpecRequest_preserves_constructed (fuel : Nat)
    (st after : SpecBuildState) (parent : String) (actuals : List Atom)
    (result : Option String) (ordered : SpecBuildOrdered st)
    (constructed : SpecBuildConstructed st)
    (hbuild : buildSpecRequest fuel st parent actuals = some (after, result)) :
    SpecBuildConstructed after :=
  (buildConstructedAtFuel fuel).request st parent actuals after result ordered
    constructed hbuild

/-- Final-world form of the constructional provenance invariant. -/
def PWorld.SpecializationsConstructed (w : PWorld) : Prop :=
  ∀ provenance, provenance ∈ w.specClauseProvenance →
    ProvenanceConstructed w.specializations provenance

theorem SpecBuildConstructed.commit (st : SpecBuildState)
    (constructed : SpecBuildConstructed st) :
    st.commit.SpecializationsConstructed := by
  intro provenance hprovenance
  simpa [PWorld.SpecializationsConstructed, SpecBuildState.registry,
    SpecBuildState.commit] using constructed provenance hprovenance

theorem SpecBuildConstructed.world_of_provisional_nil (st : SpecBuildState)
    (constructed : SpecBuildConstructed st) (hprovisional : st.provisional = []) :
    st.world.SpecializationsConstructed := by
  intro provenance hprovenance
  simpa [PWorld.SpecializationsConstructed, SpecBuildState.registry,
    hprovisional] using constructed provenance hprovenance

/-- The atomic profile boundary preserves constructional provenance in both
    fallback and commit cases.  This theorem follows the real transaction and
    is independent of the executable Boolean check used to accept a call. -/
theorem attemptSpecializeCall_preserves_constructed
    (isBin : String → Bool) (buildFuel : Nat) (w : PWorld)
    (f : String) (args : List Atom) (res : Atom)
    (hwell : WellSpecializedWorld w)
    (hcaptured : w.CapturedFamiliesOrdered)
    (hunique : (w.specializations.map (fun record => record.name)).Nodup)
    (hconstructed : w.SpecializationsConstructed) :
    (attemptSpecializeCall isBin buildFuel w f args res).1
      |>.SpecializationsConstructed := by
  let initial : SpecBuildState := { world := w, isBin }
  have hinitialOrdered : SpecBuildOrdered initial := by
    constructor
    · intro record hmember
      exact hwell.ordered record hmember
    · intro record hmember
      simp [initial] at hmember
    · exact hcaptured
    · simpa [initial, List.map_append] using hunique
  have hinitialConstructed : SpecBuildConstructed initial := by
    intro provenance hprovenance
    simpa [initial, SpecBuildState.registry,
      PWorld.SpecializationsConstructed] using
      hconstructed provenance hprovenance
  unfold attemptSpecializeCall
  split
  next built specName hbuild =>
    have hbuildInitial : buildSpecRequest buildFuel initial f args =
        some (built, some specName) := by
      simpa [initial] using hbuild
    have hbuiltConstructed := buildSpecRequest_preserves_constructed
      buildFuel initial built f args (some specName) hinitialOrdered
      hinitialConstructed hbuildInitial
    by_cases hrollback : built.provisional ≠ [] ∧ built.directGain = []
    · simp [hrollback]
      exact hconstructed
    · let committed := if built.provisional.isEmpty then built.world
        else built.commit
      have hcommittedConstructed : committed.SpecializationsConstructed := by
        by_cases hempty : built.provisional = []
        · simp [committed, hempty]
          exact hbuiltConstructed.world_of_provisional_nil built hempty
        · have hnotEmpty : built.provisional.isEmpty = false := by
            simpa using hempty
          simp [committed, hnotEmpty]
          exact hbuiltConstructed.commit built
      by_cases hchecked : committed.specializationProvenanceValid = true ∧
          committed.childCallSiteValid [] f specName args = true
      · have hcondition :
            PWorld.specializationProvenanceValid
                (if built.provisional = [] then built.world else built.commit) =
              true ∧
            PWorld.childCallSiteValid
                (if built.provisional = [] then built.world else built.commit)
                [] f specName args = true := by
            simpa [committed] using hchecked
        have hworld :
            PWorld.SpecializationsConstructed
              (if built.provisional = [] then built.world else built.commit) := by
            simpa [committed] using hcommittedConstructed
        simpa [hrollback, hcondition.1, hcondition.2] using hworld
      · have hcondition : ¬(
            PWorld.specializationProvenanceValid
                (if built.provisional = [] then built.world else built.commit) =
              true ∧
            PWorld.childCallSiteValid
                (if built.provisional = [] then built.world else built.commit)
                [] f specName args = true) := by
            simpa [committed] using hchecked
        simp [hrollback, hcondition]
        exact hconstructed
  all_goals simp
  exact hconstructed

/-- Two clauses have identical resolution heads and related bodies. -/
structure ClauseBodyRel (bodyRel : List Goal → List Goal → Prop)
    (generic specialized : Clause) : Prop where
  params : generic.params = specialized.params
  result : generic.result = specialized.result
  body : bodyRel generic.body specialized.body

/-- The exact branch shape produced by `resolveAlts`: the narrowing goal and
    incoming substitution are identical; only the renamed clause body and
    related continuation may differ. -/
inductive ResolvedAltRel (bodyRel : List Goal → List Goal → Prop)
    (rest : List Goal) : Alt → Alt → Prop where
  | branch (head : Goal) (genericBody specializedBody : List Goal) (b : Subst)
      (body : bodyRel genericBody specializedBody) :
      ResolvedAltRel bodyRel rest
        (.br (head :: genericBody ++ rest) b)
        (.br (head :: specializedBody ++ rest) b)

private def resolveFoldStep (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (bc : Nat) :
    (List Alt × Nat) → Clause → List Alt × Nat :=
  fun acc clause =>
    if clause.params.length != argsv.length then acc
    else if !prologMatchCompatList argsv clause.params then acc
    else if !prologMatchCompat (subst b res) clause.result then acc
    else
      let k := acc.2
      let copied := freshenResolutionClause argsv args res rest b qterm k bc clause
      let params := copied.params
      let result := copied.result
      let body := copied.body
      let goals := Goal.eq (Atom.expr (args ++ [res]))
          (Atom.expr (params ++ [result])) :: body ++ rest
      (Alt.br goals b :: acc.1, k + 1)

private theorem resolveAlts_eq_resolveFoldStep (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (qterm : Atom) (bc counter : Nat) :
    resolveAlts clauses argsv args res rest b qterm bc counter =
      let folded := clauses.foldl
        (resolveFoldStep argsv args res rest b qterm bc) ([], counter)
      (folded.1.reverse, folded.2) := by
  rfl

private theorem resolveFoldStep_preserves
    (rest : List Goal)
    (bodyRel renamedBodyRel : List Goal → List Goal → Prop)
    (renamePreserves : ∀ suffix bc generic specialized,
      bodyRel generic specialized →
        renamedBodyRel (generic.map (renameGoalSuffix suffix bc))
          (specialized.map (renameGoalSuffix suffix bc)))
    (argsv args : List Atom) (res : Atom) (b : Subst) (qterm : Atom)
    (bc : Nat)
    {genericClause specializedClause : Clause}
    (clauseRel : ClauseBodyRel bodyRel genericClause specializedClause)
    {genericAlts specializedAlts : List Alt} (counter : Nat)
    (altsRel : SpecListRel
      (ResolvedAltRel renamedBodyRel rest)
      genericAlts specializedAlts) :
    let generic := resolveFoldStep argsv args res rest b qterm bc
      (genericAlts, counter) genericClause
    let specialized := resolveFoldStep argsv args res rest b qterm bc
      (specializedAlts, counter) specializedClause
    generic.2 = specialized.2 ∧
      SpecListRel (ResolvedAltRel renamedBodyRel rest)
        generic.1 specialized.1 := by
  rcases clauseRel with ⟨hparams, hresult, hbody⟩
  by_cases harity : genericClause.params.length != argsv.length
  · simp [resolveFoldStep, harity, ← hparams, altsRel]
  by_cases hparamsCompat :
      prologMatchCompatList argsv genericClause.params = false
  · simp [resolveFoldStep, harity, hparamsCompat, ← hparams, altsRel]
  by_cases hresultCompat :
      prologMatchCompat (subst b res) genericClause.result = false
  · simp [resolveFoldStep, harity, hparamsCompat, hresultCompat,
      ← hparams, ← hresult, altsRel]
  · have hparamsTrue :
        prologMatchCompatList argsv genericClause.params = true :=
      by
        cases h : prologMatchCompatList argsv genericClause.params <;>
          simp_all
    have hresultTrue :
        prologMatchCompat (subst b res) genericClause.result = true :=
      by
        cases h :
            prologMatchCompat (subst b res) genericClause.result <;>
          simp_all
    let suffix := resolutionFreshSuffix argsv res rest b qterm counter
    have hrenamed := renamePreserves suffix bc _ _ hbody
    simp only [resolveFoldStep, freshenResolutionClause]
    rw [← hparams, ← hresult]
    simp only [harity, hparamsTrue, hresultTrue,
      Bool.not_true, Bool.false_eq_true, if_false]
    exact ⟨trivial, .cons (.branch _ _ _ _ hrenamed) altsRel⟩

private theorem resolveFold_preserves
    (rest : List Goal)
    (bodyRel renamedBodyRel : List Goal → List Goal → Prop)
    (renamePreserves : ∀ suffix bc generic specialized,
      bodyRel generic specialized →
        renamedBodyRel (generic.map (renameGoalSuffix suffix bc))
          (specialized.map (renameGoalSuffix suffix bc)))
    (argsv args : List Atom) (res : Atom) (b : Subst) (qterm : Atom)
    (bc : Nat)
    {genericClauses specializedClauses : List Clause}
    (clausesRel : SpecListRel (ClauseBodyRel bodyRel)
      genericClauses specializedClauses)
    {genericAlts specializedAlts : List Alt} (counter : Nat)
    (altsRel : SpecListRel
      (ResolvedAltRel renamedBodyRel rest)
      genericAlts specializedAlts) :
    let generic := genericClauses.foldl
      (resolveFoldStep argsv args res rest b qterm bc)
      (genericAlts, counter)
    let specialized := specializedClauses.foldl
      (resolveFoldStep argsv args res rest b qterm bc)
      (specializedAlts, counter)
    generic.2 = specialized.2 ∧
      SpecListRel (ResolvedAltRel renamedBodyRel rest)
        generic.1 specialized.1 := by
  induction clausesRel generalizing genericAlts specializedAlts counter with
  | nil => exact ⟨rfl, altsRel⟩
  | cons clauseRel tail ih =>
      simp only [List.foldl_cons]
      have hstep := resolveFoldStep_preserves rest bodyRel renamedBodyRel
        renamePreserves argsv args res b qterm bc clauseRel
        counter altsRel
      rcases hstep with ⟨hcounter, hAlts⟩
      generalize hg : resolveFoldStep argsv args res rest b qterm bc
          (genericAlts, counter) _ = genericStep at hcounter hAlts ⊢
      generalize hs : resolveFoldStep argsv args res rest b qterm bc
          (specializedAlts, counter) _ = specializedStep at hcounter hAlts ⊢
      rcases genericStep with ⟨nextGeneric, nextCounter⟩
      rcases specializedStep with ⟨nextSpecialized, specializedCounter⟩
      simp only at hcounter hAlts ⊢
      subst specializedCounter
      exact ih nextCounter hAlts

/-- Ordered resolution transport.  Equal clause heads and a rename-stable
    body relation preserve the exact alternative order, multiplicity, and
    fresh-counter result of `resolveAlts`. -/
theorem resolveAlts_preserves_clause_rewrite
    (rest : List Goal)
    (bodyRel renamedBodyRel : List Goal → List Goal → Prop)
    (renamePreserves : ∀ suffix bc generic specialized,
      bodyRel generic specialized →
        renamedBodyRel (generic.map (renameGoalSuffix suffix bc))
          (specialized.map (renameGoalSuffix suffix bc)))
    (genericClauses specializedClauses : List Clause)
    (clausesRel : SpecListRel (ClauseBodyRel bodyRel)
      genericClauses specializedClauses)
    (argsv args : List Atom) (res : Atom) (b : Subst) (qterm : Atom)
    (bc counter : Nat) :
    let generic := resolveAlts genericClauses argsv args res rest b qterm
      bc counter
    let specialized := resolveAlts specializedClauses argsv args res
      rest b qterm bc counter
    generic.2 = specialized.2 ∧
      SpecListRel (ResolvedAltRel renamedBodyRel rest)
        generic.1 specialized.1 := by
  rw [resolveAlts_eq_resolveFoldStep, resolveAlts_eq_resolveFoldStep]
  have hfold := resolveFold_preserves rest bodyRel renamedBodyRel
    renamePreserves argsv args res b qterm bc clausesRel counter
    (.nil : SpecListRel
      (ResolvedAltRel renamedBodyRel rest) [] [])
  rcases hfold with ⟨hcounter, halts⟩
  exact ⟨hcounter, halts.reverse⟩

theorem unifyB_congr_of_subst_eq (b : Subst) (left left' right right' : Atom)
    (hleft : subst b left = subst b left')
    (hright : subst b right = subst b right') :
    unifyB b left right = unifyB b left' right' := by
  simp only [unifyB]
  rw [hleft, hright]

/-- Clause-head narrowing cannot distinguish raw call arguments with the same
    runtime denotation.  This is the local healing point for open partials. -/
theorem unifyB_callHead_of_args_denote_same (b : Subst)
    (leftArgs rightArgs : List Atom) (res : Atom)
    (params : List Atom) (result : Atom)
    (hargs : leftArgs.map (subst b) = rightArgs.map (subst b)) :
    unifyB b (Atom.expr (leftArgs ++ [res]))
        (Atom.expr (params ++ [result])) =
      unifyB b (Atom.expr (rightArgs ++ [res]))
        (Atom.expr (params ++ [result])) := by
  apply unifyB_congr_of_subst_eq b
  · simp only [subst_expr, List.map_append, List.map_singleton, hargs]
  · rfl

/-- Resolution branches built from two raw argument lists differ only in the
    deferred clause-head equality.  Clause order, body, incoming substitution,
    and continuation are identical. -/
inductive ResolvedArgsAltRel (leftArgs rightArgs : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) : Alt → Alt → Prop where
  | branch (params : List Atom) (result : Atom) (body : List Goal) :
      ResolvedArgsAltRel leftArgs rightArgs res rest b
        (.br (Goal.eq (Atom.expr (leftArgs ++ [res]))
            (Atom.expr (params ++ [result])) :: body ++ rest) b)
        (.br (Goal.eq (Atom.expr (rightArgs ++ [res]))
            (Atom.expr (params ++ [result])) :: body ++ rest) b)

private theorem resolveFoldStep_rawArgs_preserves
    (argsv leftArgs rightArgs : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (bc : Nat)
    (clause : Clause)
    {leftAlts rightAlts : List Alt} (counter : Nat)
    (altsRel : SpecListRel
      (ResolvedArgsAltRel leftArgs rightArgs res rest b)
      leftAlts rightAlts) :
    let left := resolveFoldStep argsv leftArgs res rest b qterm bc
      (leftAlts, counter) clause
    let right := resolveFoldStep argsv rightArgs res rest b qterm bc
      (rightAlts, counter) clause
    left.2 = right.2 ∧
      SpecListRel (ResolvedArgsAltRel leftArgs rightArgs res rest b)
        left.1 right.1 := by
  by_cases harity : clause.params.length != argsv.length
  · simp [resolveFoldStep, harity, altsRel]
  by_cases hparams : prologMatchCompatList argsv clause.params = false
  · simp [resolveFoldStep, harity, hparams, altsRel]
  by_cases hresult : prologMatchCompat (subst b res) clause.result = false
  · simp [resolveFoldStep, harity, hparams, hresult, altsRel]
  · have hparamsTrue : prologMatchCompatList argsv clause.params = true := by
      cases h : prologMatchCompatList argsv clause.params <;> simp_all
    have hresultTrue :
        prologMatchCompat (subst b res) clause.result = true := by
      cases h : prologMatchCompat (subst b res) clause.result <;> simp_all
    simp only [resolveFoldStep, harity, hparamsTrue, hresultTrue,
      Bool.not_true, Bool.false_eq_true, if_false]
    exact ⟨trivial, .cons (.branch _ _ _) altsRel⟩

private theorem resolveFold_rawArgs_preserves
    (argsv leftArgs rightArgs : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (bc : Nat)
    (clauses : List Clause)
    {leftAlts rightAlts : List Alt} (counter : Nat)
    (altsRel : SpecListRel
      (ResolvedArgsAltRel leftArgs rightArgs res rest b)
      leftAlts rightAlts) :
    let left := clauses.foldl
      (resolveFoldStep argsv leftArgs res rest b qterm bc) (leftAlts, counter)
    let right := clauses.foldl
      (resolveFoldStep argsv rightArgs res rest b qterm bc) (rightAlts, counter)
    left.2 = right.2 ∧
      SpecListRel (ResolvedArgsAltRel leftArgs rightArgs res rest b)
        left.1 right.1 := by
  induction clauses generalizing leftAlts rightAlts counter with
  | nil => exact ⟨rfl, altsRel⟩
  | cons clause tail ih =>
      simp only [List.foldl_cons]
      have hstep := resolveFoldStep_rawArgs_preserves argsv leftArgs
        rightArgs res rest b qterm bc clause counter altsRel
      rcases hstep with ⟨hcounter, hAlts⟩
      generalize hl : resolveFoldStep argsv leftArgs res rest b qterm bc
          (leftAlts, counter) clause = leftStep at hcounter hAlts ⊢
      generalize hr : resolveFoldStep argsv rightArgs res rest b qterm bc
          (rightAlts, counter) clause = rightStep at hcounter hAlts ⊢
      rcases leftStep with ⟨nextLeft, nextCounter⟩
      rcases rightStep with ⟨nextRight, rightCounter⟩
      simp only at hcounter hAlts ⊢
      subst rightCounter
      exact ih nextCounter hAlts

/-- Changing only the raw argument syntax while keeping the indexed runtime
    arguments fixed preserves exact branch order, multiplicity, and counter.
    Each paired branch defers the sole syntactic difference to its first
    clause-head equality. -/
theorem resolveAlts_rawArgs_related (clauses : List Clause)
    (argsv leftArgs rightArgs : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (bc counter : Nat) :
    let left := resolveAlts clauses argsv leftArgs res rest b qterm bc counter
    let right := resolveAlts clauses argsv rightArgs res rest b qterm bc counter
    left.2 = right.2 ∧
      SpecListRel (ResolvedArgsAltRel leftArgs rightArgs res rest b)
        left.1 right.1 := by
  rw [resolveAlts_eq_resolveFoldStep, resolveAlts_eq_resolveFoldStep]
  have hfold := resolveFold_rawArgs_preserves argsv leftArgs rightArgs res
    rest b qterm bc clauses counter
    (.nil : SpecListRel
      (ResolvedArgsAltRel leftArgs rightArgs res rest b) [] [])
  exact ⟨hfold.1, hfold.2.reverse⟩

/-- The deferred head equalities in an argument-related resolution branch
    invoke the exact same `unifyB` whenever the raw arguments have the same
    runtime denotation. -/
theorem ResolvedArgsAltRel.unify_eq
    (leftArgs rightArgs : List Atom) (res : Atom) (rest : List Goal)
    (b : Subst) {left right : Alt}
    (related : ResolvedArgsAltRel leftArgs rightArgs res rest b left right)
    (hargs : leftArgs.map (subst b) = rightArgs.map (subst b)) :
    ∃ params result body,
      left = .br (Goal.eq (Atom.expr (leftArgs ++ [res]))
          (Atom.expr (params ++ [result])) :: body ++ rest) b ∧
      right = .br (Goal.eq (Atom.expr (rightArgs ++ [res]))
          (Atom.expr (params ++ [result])) :: body ++ rest) b ∧
      unifyB b (Atom.expr (leftArgs ++ [res]))
          (Atom.expr (params ++ [result])) =
        unifyB b (Atom.expr (rightArgs ++ [res]))
          (Atom.expr (params ++ [result])) := by
  cases related with
  | branch params result body =>
      exact ⟨params, result, body, rfl, rfl,
        unifyB_callHead_of_args_denote_same b leftArgs rightArgs res params
          result hargs⟩

private def activateGoals (c : Conf) (goals : List Goal) (b : Subst) : Conf :=
  { c with cur := some (goals, b) }

/-- Once a paired resolution branch is activated against the same background
    configuration, its first real equality step converges to one literal
    successor configuration.  Success installs the same composed/trimmed
    substitution; failure pulls the same background alternatives. -/
theorem ResolvedArgsAltRel.head_steps_converge (prog : Prog)
    (gt : GroundingTable) (c : Conf)
    (leftArgs rightArgs : List Atom) (res : Atom) (rest : List Goal)
    (b : Subst) {left right : Alt}
    (related : ResolvedArgsAltRel leftArgs rightArgs res rest b left right)
    (hargs : leftArgs.map (subst b) = rightArgs.map (subst b)) :
    ∃ params result body target,
      left = .br (Goal.eq (Atom.expr (leftArgs ++ [res]))
          (Atom.expr (params ++ [result])) :: body ++ rest) b ∧
      right = .br (Goal.eq (Atom.expr (rightArgs ++ [res]))
          (Atom.expr (params ++ [result])) :: body ++ rest) b ∧
      Step prog gt
        (activateGoals c
          (Goal.eq (Atom.expr (leftArgs ++ [res]))
            (Atom.expr (params ++ [result])) :: body ++ rest) b)
        target ∧
      Step prog gt
        (activateGoals c
          (Goal.eq (Atom.expr (rightArgs ++ [res]))
            (Atom.expr (params ++ [result])) :: body ++ rest) b)
        target := by
  cases related with
  | branch params result body =>
      have hunify := unifyB_callHead_of_args_denote_same b leftArgs rightArgs
        res params result hargs
      cases hleft : unifyB b (Atom.expr (leftArgs ++ [res]))
          (Atom.expr (params ++ [result])) with
      | none =>
          have hright : unifyB b (Atom.expr (rightArgs ++ [res]))
              (Atom.expr (params ++ [result])) = none := by
            rw [← hunify]
            exact hleft
          let target := pull { c with cur := none }
          refine ⟨params, result, body, target, rfl, rfl, ?_, ?_⟩
          · simpa [activateGoals] using
              (Step.eq_fail (prog := prog) (gt := gt) _ _ _ _ _ rfl hleft)
          · simpa [activateGoals] using
              (Step.eq_fail (prog := prog) (gt := gt) _ _ _ _ _ rfl hright)
      | some nextSubst =>
          have hright : unifyB b (Atom.expr (rightArgs ++ [res]))
              (Atom.expr (params ++ [result])) = some nextSubst := by
            rw [← hunify]
            exact hleft
          let target : Conf := activateGoals c (body ++ rest)
            (trimFor (body ++ rest) c.qterm nextSubst)
          refine ⟨params, result, body, target, rfl, rfl, ?_, ?_⟩
          · simpa [activateGoals, target] using
              (Step.eq_ok (prog := prog) (gt := gt) _ _ _ _ _ _ rfl hleft)
          · simpa [activateGoals, target] using
              (Step.eq_ok (prog := prog) (gt := gt) _ _ _ _ _ _ rfl hright)

/-- Constructional body pair named by one exact provenance row.  The row is
    admitted only with the real builder evidence for its guarded and
    recursively retargeted body; ledger membership alone is insufficient. -/
inductive ProvenanceBodyRel (records : List SpecRecord) :
    List Goal → List Goal → Prop where
  | linked (provenance : SpecClauseProvenance)
      (constructed : ProvenanceConstructed records provenance) :
      ProvenanceBodyRel records provenance.parentClause.body
        provenance.executableClause.body

/-- The same pair after the common clause-freshening transformation. -/
inductive RenamedProvenanceBodyRel (records : List SpecRecord) :
    List Goal → List Goal → Prop where
  | linked (provenance : SpecClauseProvenance) (suffix : String) (barrier : Nat)
      (constructed : ProvenanceConstructed records provenance) :
      RenamedProvenanceBodyRel records
        (provenance.parentClause.body.map (renameGoalSuffix suffix barrier))
        (provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier))

theorem provenanceBodyRel_rename (suffix : String) (barrier : Nat)
    (records : List SpecRecord)
    (generic specialized : List Goal)
    (h : ProvenanceBodyRel records generic specialized) :
    RenamedProvenanceBodyRel records
      (generic.map (renameGoalSuffix suffix barrier))
      (specialized.map (renameGoalSuffix suffix barrier)) := by
  cases h with
  | linked provenance constructed =>
      exact .linked provenance suffix barrier constructed

theorem provenanceClauseMaps_related (records : List SpecRecord)
    (provenance : List SpecClauseProvenance)
    (exactHeads : ∀ item, item ∈ provenance →
      item.parentClause.params = item.executableClause.params ∧
        item.parentClause.result = item.executableClause.result)
    (constructed : ∀ item, item ∈ provenance →
      ProvenanceConstructed records item) :
    SpecListRel (ClauseBodyRel (ProvenanceBodyRel records))
      (provenance.map (·.parentClause))
      (provenance.map (·.executableClause)) := by
  induction provenance with
  | nil => exact .nil
  | cons item rest ih =>
      have hhead := exactHeads item (by simp)
      exact .cons
        { params := hhead.1
          result := hhead.2
          body := .linked item (constructed item (by simp)) }
        (ih (fun next hnext => exactHeads next (by simp [hnext]))
          (fun next hnext => constructed next (by simp [hnext])))

/-- The constructional part of `WellSpecializedWorld` supplies the exact
    clause-list relation consumed by ordered resolution transport. -/
theorem specializationRecord_clause_lists_related (w : PWorld)
    (record : SpecRecord) (ordered : w.SpecializationRecordOrdered record)
    (constructed : ∀ provenance, provenance ∈ w.recordProvenance record →
      ProvenanceConstructed w.specializations provenance) :
    SpecListRel
      (ClauseBodyRel (ProvenanceBodyRel w.specializations))
      (w.clausesOf record.key.parent) (w.clausesOf record.name) := by
  rw [ordered.parentClauses, ordered.executableClauses]
  exact provenanceClauseMaps_related w.specializations _ ordered.exactHeads
    constructed

/-- One committed specialization record preserves resolution branch order,
    multiplicity, and fresh counters.  The remaining semantic obligation is
    precisely the relation between each paired branch body. -/
theorem resolveAlts_preserves_specialization_record
    (w : PWorld) (record : SpecRecord)
    (ordered : w.SpecializationRecordOrdered record)
    (constructed : ∀ provenance, provenance ∈ w.recordProvenance record →
      ProvenanceConstructed w.specializations provenance)
    (rest : List Goal)
    (argsv args : List Atom) (res : Atom) (b : Subst)
    (qterm : Atom) (barrier counter : Nat) :
    let generic := resolveAlts (w.clausesOf record.key.parent) argsv args res
      rest b qterm barrier counter
    let specialized := resolveAlts (w.clausesOf record.name) argsv args res
      rest b qterm barrier counter
    generic.2 = specialized.2 ∧
      SpecListRel
        (ResolvedAltRel (RenamedProvenanceBodyRel w.specializations)
          rest)
        generic.1 specialized.1 := by
  exact resolveAlts_preserves_clause_rewrite rest
    (ProvenanceBodyRel w.specializations)
    (RenamedProvenanceBodyRel w.specializations)
    (provenanceBodyRel_rename · · w.specializations)
    (w.clausesOf record.key.parent) (w.clausesOf record.name)
    (specializationRecord_clause_lists_related w record ordered constructed)
    argsv args res b qterm barrier counter

@[simp] theorem attemptSpecializeCall_zero (isBin : String → Bool)
    (w : PWorld) (f : String) (args : List Atom) (res : Atom) :
    attemptSpecializeCall isBin 0 w f args res =
      (w, Goal.call f args res) := by
  rfl

/-- A specialized call can cross the atomic transaction boundary only with
    the full constructional world invariant.  This combines the recursive
    builder proof with the executable integrity check without deriving exact
    clause equalities from Boolean atom equality. -/
theorem attemptSpecializeCall_well (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (f : String) (args : List Atom)
    (res : Atom) (hwell : WellSpecializedWorld w)
    (hcaptured : w.CapturedFamiliesOrdered)
    (hunique : (w.specializations.map (fun record => record.name)).Nodup) :
    let result := attemptSpecializeCall isBin buildFuel w f args res
    result = (w, Goal.call f args res) ∨
      ∃ specName,
        result.2 = Goal.call specName args res ∧
          SpecializationProfileInvariant result.1 ∧
          result.1.childCallSiteValid [] f specName args = true := by
  let initial : SpecBuildState := { world := w, isBin }
  have hinitial : SpecBuildOrdered initial := by
    constructor
    · intro record hmember
      exact hwell.ordered record hmember
    · intro record hmember
      simp [initial] at hmember
    · exact hcaptured
    · simpa [initial, List.map_append] using hunique
  unfold attemptSpecializeCall
  split
  next built specName hbuild =>
    have hbuildInitial : buildSpecRequest buildFuel initial f args =
        some (built, some specName) := by
      simpa [initial] using hbuild
    have hbuilt := (buildSpecRequest_preserves_ordered buildFuel initial f args
      built (some specName) hinitial hbuildInitial).valid
    by_cases hrollback : built.provisional ≠ [] ∧ built.directGain = []
    · simp [hrollback]
    · let committed := if built.provisional.isEmpty then built.world
        else built.commit
      by_cases hchecked : committed.specializationProvenanceValid = true ∧
          committed.childCallSiteValid [] f specName args = true
      · have hcommitted : SpecializationProfileInvariant committed := by
          exact hbuilt.committed_profile built hchecked.1
        have hcondition :
            PWorld.specializationProvenanceValid
                (if built.provisional = [] then built.world else built.commit) =
              true ∧
              PWorld.childCallSiteValid
                (if built.provisional = [] then built.world else built.commit)
                [] f specName args = true := by
          simpa [committed] using hchecked
        have hworld : SpecializationProfileInvariant
            (if built.provisional = [] then built.world else built.commit) := by
          simpa [committed] using hcommitted
        right
        refine ⟨specName, ?_⟩
        simpa [hrollback, hcondition.1, hcondition.2] using
          (show SpecializationProfileInvariant
                (if built.provisional = [] then built.world else built.commit) ∧
              PWorld.childCallSiteValid
                (if built.provisional = [] then built.world else built.commit)
                [] f specName args = true from ⟨hworld, hcondition.2⟩)
      · have hcondition : ¬(
            PWorld.specializationProvenanceValid
                (if built.provisional = [] then built.world else built.commit) =
              true ∧
              PWorld.childCallSiteValid
                (if built.provisional = [] then built.world else built.commit)
                [] f specName args = true) := by
          simpa [committed] using hchecked
        left
        simp [hrollback, hcondition]
  all_goals simp

/-- The executable retargeting gate exposes the exact static-support fact for
    every provenance clause belonging to the selected child. -/
theorem PWorld.childCallSiteValid_exactSupport (w : PWorld)
    (outerBinding : Subst) (parent child : String) (args : List Atom)
    (provenance : SpecClauseProvenance)
    (hdifferent : parent ≠ child)
    (hvalid : w.childCallSiteValid outerBinding parent child args = true)
    (hmember : provenance ∈ w.specClauseProvenance)
    (hname : provenance.name = child)
    (hparent : provenance.parent = parent) :
    specializationBindingExactlySupported provenance.binding
      provenance.parentClause.params
      (args.map (Metta.Subst.apply outerBinding)) = true := by
  unfold PWorld.childCallSiteValid at hvalid
  have hparentFalse : (parent == child) = false := by simp [hdifferent]
  rw [hparentFalse] at hvalid
  simp only [Bool.false_or, Bool.and_eq_true] at hvalid
  have hfiltered : provenance ∈ w.specClauseProvenance.filter (fun item =>
      item.name == child && item.parent == parent) := by
    rw [List.mem_filter]
    exact ⟨hmember, by simp [hname, hparent]⟩
  have hrow := List.all_eq_true.mp hvalid.2 provenance hfiltered
  simp only [Bool.and_eq_true] at hrow
  exact hrow.1

/-- The same retargeting gate identifies the current static actual tuple with
    the literal discovery tuple retained by every selected provenance row. -/
theorem PWorld.childCallSiteValid_discoveryActuals_eq (w : PWorld)
    (outerBinding : Subst) (parent child : String) (args : List Atom)
    (provenance : SpecClauseProvenance)
    (hdifferent : parent ≠ child)
    (hvalid : w.childCallSiteValid outerBinding parent child args = true)
    (hmember : provenance ∈ w.specClauseProvenance)
    (hname : provenance.name = child)
    (hparent : provenance.parent = parent) :
    provenance.discoveryActuals =
      args.map (Metta.Subst.apply outerBinding) := by
  unfold PWorld.childCallSiteValid at hvalid
  have hparentFalse : (parent == child) = false := by simp [hdifferent]
  rw [hparentFalse] at hvalid
  simp only [Bool.false_or, Bool.and_eq_true] at hvalid
  have hfiltered : provenance ∈ w.specClauseProvenance.filter (fun item =>
      item.name == child && item.parent == parent) := by
    rw [List.mem_filter]
    exact ⟨hmember, by simp [hname, hparent]⟩
  have hrow := List.all_eq_true.mp hvalid.2 provenance hfiltered
  simp only [Bool.and_eq_true] at hrow
  have hexact := hrow.2
  unfold propositionallyExactAtoms at hexact
  simp only [Bool.and_eq_true] at hexact
  exact proofAtomsEq_eq_of_propositionallyCheckable _ _
    hexact.1.1 hexact.1.2 hexact.2

/-- The global checked-world gate validates every installed provenance row. -/
theorem PWorld.specializationProvenanceValid_row (w : PWorld)
    (provenance : SpecClauseProvenance)
    (hchecked : w.specializationProvenanceValid = true)
    (hmember : provenance ∈ w.specClauseProvenance) :
    w.specClauseProvenanceValid provenance = true := by
  unfold PWorld.specializationProvenanceValid at hchecked
  simp only [Bool.and_eq_true] at hchecked
  exact List.all_eq_true.mp hchecked.1 provenance hmember

/-- One valid provenance row retains the executable call-site checks for its
    complete recursively rewritten body. -/
theorem PWorld.specClauseProvenanceValid_childSites (w : PWorld)
    (provenance : SpecClauseProvenance)
    (hvalid : w.specClauseProvenanceValid provenance = true) :
    w.childCallSitesValidList provenance.binding
      provenance.guardedClause.body provenance.executableClause.body = true := by
  unfold PWorld.specClauseProvenanceValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  exact hvalid.2

/-- A valid row's generated guards are reflexive for the runtime unifier. -/
theorem PWorld.specClauseProvenanceValid_runtimeSafe (w : PWorld)
    (provenance : SpecClauseProvenance)
    (hvalid : w.specClauseProvenanceValid provenance = true) :
    specializationBindingRuntimeSafe provenance.binding = true := by
  unfold PWorld.specClauseProvenanceValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1.1.1.1.1.2

/-- A valid row retains exact (not merely runtime-equivalent) alignment
    between its pre-copy binding and discovery tuple. -/
theorem PWorld.specClauseProvenanceValid_sourceExact (w : PWorld)
    (provenance : SpecClauseProvenance)
    (hvalid : w.specClauseProvenanceValid provenance = true) :
    specializationSourceBindingExact provenance.sourceBinding
      provenance.parentClause.params provenance.discoveryActuals = true := by
  unfold PWorld.specClauseProvenanceValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1.1.1.1.2

/-- A valid row is supported by the exact discovery tuple retained in its
    provenance metadata. -/
theorem PWorld.specClauseProvenanceValid_discoveryExactSupport (w : PWorld)
    (provenance : SpecClauseProvenance)
    (hvalid : w.specClauseProvenanceValid provenance = true) :
    specializationBindingExactlySupported provenance.binding
      provenance.parentClause.params provenance.discoveryActuals = true := by
  unfold PWorld.specClauseProvenanceValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1.1.1.2

mutual

/-- The shared pure profile pass threads the complete constructional
    invariant through an arbitrary goal tree. -/
theorem specializeGoals_preserves_profile (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goals : List Goal)
    (invariant : SpecializationProfileInvariant w) :
    SpecializationProfileInvariant
      (specializeGoals isBin buildFuel w goals).1 := by
  cases goals with
  | nil => exact invariant
  | cons goal rest =>
      simp only [specializeGoals]
      let first := specializeGoal isBin buildFuel w goal
      have hfirst := specializeGoal_preserves_profile isBin buildFuel w goal
        invariant
      exact specializeGoals_preserves_profile isBin buildFuel first.1 rest
        hfirst

theorem specializeGoal_preserves_profile (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goal : Goal)
    (invariant : SpecializationProfileInvariant w) :
    SpecializationProfileInvariant
      (specializeGoal isBin buildFuel w goal).1 := by
  cases goal with
  | call f args res =>
      change SpecializationProfileInvariant
        (attemptSpecializeCall isBin buildFuel w f args res).1
      rcases attemptSpecializeCall_well isBin buildFuel w f args res
        invariant.well invariant.captured invariant.uniqueNames with
        hfallback | hspecialized
      · rw [hfallback]
        exact invariant
      · rcases hspecialized with
          ⟨specName, hgoal, hprofile, hcall⟩
        exact hprofile
  | catchg tmpl sub res =>
      exact specializeGoals_preserves_profile isBin buildFuel w sub invariant
  | softcut tmpl sub thn els =>
      let first := specializeGoals isBin buildFuel w sub
      have hfirst := specializeGoals_preserves_profile isBin buildFuel w sub
        invariant
      let second := specializeGoals isBin buildFuel first.1 thn
      have hsecond := specializeGoals_preserves_profile isBin buildFuel
        first.1 thn hfirst
      exact specializeGoals_preserves_profile isBin buildFuel second.1 els
        hsecond
  | findall tmpl sub res =>
      exact specializeGoals_preserves_profile isBin buildFuel w sub invariant
  | onceg tmpl sub res =>
      exact specializeGoals_preserves_profile isBin buildFuel w sub invariant
  | transactiong tmpl sub =>
      exact specializeGoals_preserves_profile isBin buildFuel w sub invariant
  | amb branches res =>
      exact specializeBranches_preserves_profile isBin buildFuel w branches
        invariant
  | ite cond thn els res =>
      let first := specializeGoals isBin buildFuel w thn.2
      have hfirst := specializeGoals_preserves_profile isBin buildFuel w thn.2
        invariant
      exact specializeGoals_preserves_profile isBin buildFuel first.1 els.2
        hfirst
  | _ => exact invariant

theorem specializeBranches_preserves_profile (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld)
    (branches : List (Atom × List Goal))
    (invariant : SpecializationProfileInvariant w) :
    SpecializationProfileInvariant
      (specializeBranches isBin buildFuel w branches).1 := by
  cases branches with
  | nil => exact invariant
  | cons branch rest =>
      let first := specializeGoals isBin buildFuel w branch.2
      have hfirst := specializeGoals_preserves_profile isBin buildFuel w
        branch.2 invariant
      exact specializeBranches_preserves_profile isBin buildFuel first.1 rest
        hfirst

end

mutual

theorem specializeGoals_preserves_constructed (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goals : List Goal)
    (profile : SpecializationProfileInvariant w)
    (constructed : w.SpecializationsConstructed) :
    (specializeGoals isBin buildFuel w goals).1
      |>.SpecializationsConstructed := by
  cases goals with
  | nil => exact constructed
  | cons goal rest =>
      simp only [specializeGoals]
      let first := specializeGoal isBin buildFuel w goal
      have hfirstProfile := specializeGoal_preserves_profile isBin buildFuel
        w goal profile
      have hfirstConstructed := specializeGoal_preserves_constructed isBin
        buildFuel w goal profile constructed
      exact specializeGoals_preserves_constructed isBin buildFuel first.1 rest
        hfirstProfile hfirstConstructed

theorem specializeGoal_preserves_constructed (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goal : Goal)
    (profile : SpecializationProfileInvariant w)
    (constructed : w.SpecializationsConstructed) :
    (specializeGoal isBin buildFuel w goal).1
      |>.SpecializationsConstructed := by
  cases goal with
  | call f args res =>
      exact attemptSpecializeCall_preserves_constructed isBin buildFuel w f
        args res profile.well profile.captured profile.uniqueNames constructed
  | catchg tmpl sub res =>
      exact specializeGoals_preserves_constructed isBin buildFuel w sub profile
        constructed
  | softcut tmpl sub thn els =>
      let first := specializeGoals isBin buildFuel w sub
      have hfirstProfile := specializeGoals_preserves_profile isBin buildFuel w
        sub profile
      have hfirstConstructed := specializeGoals_preserves_constructed isBin
        buildFuel w sub profile constructed
      let second := specializeGoals isBin buildFuel first.1 thn
      have hsecondProfile := specializeGoals_preserves_profile isBin buildFuel
        first.1 thn hfirstProfile
      have hsecondConstructed := specializeGoals_preserves_constructed isBin
        buildFuel first.1 thn hfirstProfile hfirstConstructed
      exact specializeGoals_preserves_constructed isBin buildFuel second.1 els
        hsecondProfile hsecondConstructed
  | findall tmpl sub res =>
      exact specializeGoals_preserves_constructed isBin buildFuel w sub profile
        constructed
  | onceg tmpl sub res =>
      exact specializeGoals_preserves_constructed isBin buildFuel w sub profile
        constructed
  | transactiong tmpl sub =>
      exact specializeGoals_preserves_constructed isBin buildFuel w sub profile
        constructed
  | amb branches res =>
      exact specializeBranches_preserves_constructed isBin buildFuel w branches
        profile constructed
  | ite cond thn els res =>
      let first := specializeGoals isBin buildFuel w thn.2
      have hfirstProfile := specializeGoals_preserves_profile isBin buildFuel w
        thn.2 profile
      have hfirstConstructed := specializeGoals_preserves_constructed isBin
        buildFuel w thn.2 profile constructed
      exact specializeGoals_preserves_constructed isBin buildFuel first.1 els.2
        hfirstProfile hfirstConstructed
  | _ => exact constructed

theorem specializeBranches_preserves_constructed (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld)
    (branches : List (Atom × List Goal))
    (profile : SpecializationProfileInvariant w)
    (constructed : w.SpecializationsConstructed) :
    (specializeBranches isBin buildFuel w branches).1
      |>.SpecializationsConstructed := by
  cases branches with
  | nil => exact constructed
  | cons branch rest =>
      let first := specializeGoals isBin buildFuel w branch.2
      have hfirstProfile := specializeGoals_preserves_profile isBin buildFuel w
        branch.2 profile
      have hfirstConstructed := specializeGoals_preserves_constructed isBin
        buildFuel w branch.2 profile constructed
      exact specializeBranches_preserves_constructed isBin buildFuel first.1
        rest hfirstProfile hfirstConstructed

end

/-- Combined invariant consumed by the semantic simulation after the shared
    profile pass. -/
structure SpecializationSemanticInvariant (w : PWorld) : Prop where
  profile : SpecializationProfileInvariant w
  constructed : w.SpecializationsConstructed

theorem specializeGoals_preserves_semantic (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goals : List Goal)
    (invariant : SpecializationSemanticInvariant w) :
    SpecializationSemanticInvariant
      (specializeGoals isBin buildFuel w goals).1 :=
  { profile := specializeGoals_preserves_profile isBin buildFuel w goals
      invariant.profile
    constructed := specializeGoals_preserves_constructed isBin buildFuel w
      goals invariant.profile invariant.constructed }

/-- The transaction boundary never exposes an unchecked specialized call.
    This is a construction postcondition, not the semantic simulation: the
    latter still proves that a checked specialized call refines its generic
    parent. -/
theorem attemptSpecializeCall_checked (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (f : String) (args : List Atom)
    (res : Atom) :
    let result := attemptSpecializeCall isBin buildFuel w f args res
    result = (w, Goal.call f args res) ∨
      ∃ specName,
        result.2 = Goal.call specName args res ∧
          result.1.specializationProvenanceValid = true ∧
          result.1.childCallSiteValid [] f specName args = true := by
  unfold attemptSpecializeCall
  split
  next built specName hbuild =>
    by_cases hrollback : built.provisional ≠ [] ∧ built.directGain = []
    · simp [hrollback]
    · let committed := if built.provisional = [] then built.world
        else built.commit
      by_cases hchecked : committed.specializationProvenanceValid = true ∧
          committed.childCallSiteValid [] f specName args = true
      · simp [hrollback, committed, hchecked]
      · simp [hrollback, committed, hchecked]
  all_goals simp

mutual

/-- The shared profile pass preserves its global executable integrity check
    across an arbitrary goal tree. -/
theorem specializeGoals_preserves_checked (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goals : List Goal)
    (hchecked : w.specializationProvenanceValid = true) :
    (specializeGoals isBin buildFuel w goals).1.specializationProvenanceValid =
      true := by
  cases goals with
  | nil => exact hchecked
  | cons goal rest =>
      simp only [specializeGoals]
      let first := specializeGoal isBin buildFuel w goal
      have hfirst := specializeGoal_preserves_checked isBin buildFuel w goal
        hchecked
      exact specializeGoals_preserves_checked isBin buildFuel first.1 rest hfirst

theorem specializeGoal_preserves_checked (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (goal : Goal)
    (hchecked : w.specializationProvenanceValid = true) :
    (specializeGoal isBin buildFuel w goal).1.specializationProvenanceValid =
      true := by
  cases goal with
  | call f args res =>
      change PWorld.specializationProvenanceValid
        (attemptSpecializeCall isBin buildFuel w f args res).1 = true
      rcases attemptSpecializeCall_checked isBin buildFuel w f args res with
        hfallback | hspecialized
      · rw [hfallback]
        exact hchecked
      · rcases hspecialized with ⟨specName, hgoal, hworld, hcall⟩
        exact hworld
  | catchg tmpl sub res =>
      exact specializeGoals_preserves_checked isBin buildFuel w sub hchecked
  | softcut tmpl sub thn els =>
      let first := specializeGoals isBin buildFuel w sub
      have hfirst := specializeGoals_preserves_checked isBin buildFuel w sub
        hchecked
      let second := specializeGoals isBin buildFuel first.1 thn
      have hsecond := specializeGoals_preserves_checked isBin buildFuel
        first.1 thn hfirst
      exact specializeGoals_preserves_checked isBin buildFuel second.1 els
        hsecond
  | findall tmpl sub res =>
      exact specializeGoals_preserves_checked isBin buildFuel w sub hchecked
  | onceg tmpl sub res =>
      exact specializeGoals_preserves_checked isBin buildFuel w sub hchecked
  | transactiong tmpl sub =>
      exact specializeGoals_preserves_checked isBin buildFuel w sub hchecked
  | amb branches res =>
      exact specializeBranches_preserves_checked isBin buildFuel w branches
        hchecked
  | ite cond thn els res =>
      let first := specializeGoals isBin buildFuel w thn.2
      have hfirst := specializeGoals_preserves_checked isBin buildFuel w thn.2
        hchecked
      exact specializeGoals_preserves_checked isBin buildFuel first.1 els.2
        hfirst
  | _ => exact hchecked

theorem specializeBranches_preserves_checked (isBin : String → Bool)
    (buildFuel : Nat) (w : PWorld) (branches : List (Atom × List Goal))
    (hchecked : w.specializationProvenanceValid = true) :
    (specializeBranches isBin buildFuel w branches).1.specializationProvenanceValid =
      true := by
  cases branches with
  | nil => exact hchecked
  | cons branch rest =>
      let first := specializeGoals isBin buildFuel w branch.2
      have hfirst := specializeGoals_preserves_checked isBin buildFuel w
        branch.2 hchecked
      exact specializeBranches_preserves_checked isBin buildFuel first.1 rest
        hfirst

end

theorem invalidateSpecializations_of_no_descendants (w : PWorld)
    (parent : String) (h : w.specializationDescendants parent = []) :
    w.invalidateSpecializations parent = w := by
  simp [PWorld.invalidateSpecializations, h]

theorem invalidateSpecializations_clauseIndexCoherent (w : PWorld)
    (parent : String) (coherent : w.ClauseIndexCoherent) :
    (w.invalidateSpecializations parent).ClauseIndexCoherent := by
  unfold PWorld.invalidateSpecializations
  dsimp only
  split
  next _ => exact coherent
  next _ =>
    apply PWorld.replaceProgClauses_coherent
    exact coherent

theorem invalidateSpecializations_spaceIndexCoherent (w : PWorld)
    (parent : String) (coherent : w.SpaceIndexCoherent) :
    (w.invalidateSpecializations parent).SpaceIndexCoherent := by
  unfold PWorld.invalidateSpecializations
  dsimp only
  split
  next _ => exact coherent
  next _ =>
    apply PWorld.replaceProgClauses_spaceCoherent
    exact PWorld.replaceSelfAtoms_spaceCoherent w _ coherent

/-- The successful dynamic rule-assertion branch preserves both the visible
    space index and its later specialization invalidation. -/
theorem dynamicRuleAdd_spaceIndexCoherent (w : PWorld) (space source : Atom)
    (functionName : String) (clause : Clause)
    (coherent : w.SpaceIndexCoherent) :
    let captured := (w.addAtom space (chainify source)).captureMeta source clause
    let withClause := captured.appendProgClause (functionName, clause)
    let updated := { withClause with
      progClauseKeys := captured.effectiveProgClauseKeys ++
        [clauseAlphaKey clause] }
    (updated.invalidateSpecializations functionName).SpaceIndexCoherent := by
  dsimp only
  apply invalidateSpecializations_spaceIndexCoherent
  apply PWorld.appendProgClause_spaceCoherent
  apply PWorld.captureMeta_spaceCoherent
  exact PWorld.addAtom_spaceCoherent w space (chainify source) coherent

theorem dynamicRuleAdd_clauseIndexCoherent (w : PWorld) (space source : Atom)
    (functionName : String) (clause : Clause)
    (coherent : w.ClauseIndexCoherent) :
    let captured := (w.addAtom space (chainify source)).captureMeta source clause
    let withClause := captured.appendProgClause (functionName, clause)
    let updated := { withClause with
      progClauseKeys := captured.effectiveProgClauseKeys ++
        [clauseAlphaKey clause] }
    (updated.invalidateSpecializations functionName).ClauseIndexCoherent := by
  dsimp only
  apply invalidateSpecializations_clauseIndexCoherent
  apply PWorld.appendProgClause_coherent
  apply PWorld.captureMeta_coherent
  exact PWorld.addAtom_coherent w space (chainify source) coherent

/-- The successful dynamic rule-retraction branch preserves the space index
    through visible removal, metadata removal, clause replacement, and
    specialization invalidation. -/
theorem dynamicRuleRemove_spaceIndexCoherent (w : PWorld)
    (space source : Atom) (functionName key : String)
    (remainingClauses : List (String × Clause))
    (remainingKeys : List String) (coherent : w.SpaceIndexCoherent) :
    let uncaptured :=
      (w.removeAtom space (chainify source)).removeCapturedMeta functionName key
    let withoutClause := uncaptured.replaceProgClauses remainingClauses
    let updated := { withoutClause with progClauseKeys := remainingKeys }
    (updated.invalidateSpecializations functionName).SpaceIndexCoherent := by
  dsimp only
  apply invalidateSpecializations_spaceIndexCoherent
  apply PWorld.replaceProgClauses_spaceCoherent
  apply PWorld.removeCapturedMeta_spaceCoherent
  exact PWorld.removeAtom_spaceCoherent w space (chainify source) coherent

theorem dynamicRuleRemove_clauseIndexCoherent (w : PWorld)
    (space source : Atom) (functionName key : String)
    (remainingClauses : List (String × Clause))
    (remainingKeys : List String) (coherent : w.ClauseIndexCoherent) :
    let uncaptured :=
      (w.removeAtom space (chainify source)).removeCapturedMeta functionName key
    let withoutClause := uncaptured.replaceProgClauses remainingClauses
    let updated := { withoutClause with progClauseKeys := remainingKeys }
    (updated.invalidateSpecializations functionName).ClauseIndexCoherent := by
  dsimp only
  apply invalidateSpecializations_clauseIndexCoherent
  apply PWorld.replaceProgClauses_coherent
  apply PWorld.removeCapturedMeta_coherent
  exact PWorld.removeAtom_coherent w space (chainify source) coherent

/-- A function with no forward generated children is outside every
    invalidation family rooted at that function.  In particular, reverse
    mentions in specialization bindings or generated callers do not create
    invalidation edges. -/
theorem invalidateSpecializations_of_no_children (w : PWorld)
    (parent : String) (h : w.specializationChildren parent = []) :
    w.invalidateSpecializations parent = w := by
  apply invalidateSpecializations_of_no_descendants
  exact w.specializationDescendants_eq_nil_of_children_eq_nil parent h

/-- The semantic dispatch step justified by a direct specialization rewrite.
    This is a genuine stuttering step of the generic path: it checks the
    concrete head under the current substitution and the live clause database,
    and changes neither answers nor world. -/
theorem callDyn_defined_steps_to_direct (prog : Prog) (gt : GroundingTable)
    (c : Conf) (head : Atom) (f : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hhead : subst b head = Atom.sym f)
    (hdefined : c.world.clauseHeadCandidates f ≠ []) :
    Step prog gt c { c with cur := some (Goal.call f args res :: rest, b) } := by
  exact Step.callDyn_call c head f args res rest b hcur hhead hdefined

/-- Fuel-shifted executable form of `callDyn_defined_steps_to_direct`.  Both
    runs have the exact same terminal configuration, hence the same ordered
    answer list (including multiplicity) and the same world effects. -/
theorem runClean_callDyn_defined_eq_direct (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (c : Conf) (head : Atom) (f : String)
    (args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hhead : subst b head = Atom.sym f)
    (hdefined : c.world.clauseHeadCandidates f ≠ []) :
    runClean prog gt (fuel + 2) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (Goal.call f args res :: rest, b) } none := by
  have hterminal : c.isTerminalB = false := by
    simp [Conf.isTerminalB, hcur]
  have hstep : step prog gt fuel c =
      { c with cur := some (Goal.call f args res :: rest, b) } := by
    unfold step
    rw [hcur]
    simp [hhead, hdefined]
  have hclean : stepClean prog gt (fuel + 1) c =
      .progressed { c with cur := some (Goal.call f args res :: rest, b) } := by
    simp [stepClean, hcur, hstep]
  simp [runClean, hterminal, Conf.limitReachedB, hclean]

/-- Under a realized captured binding, the actual callable-head rewrite from
    `callDyn` to a defined direct call is one genuine generic-path step. -/
theorem denoted_callDyn_defined_steps_to_rewrite (prog : Prog)
    (gt : GroundingTable) (isDefined isBin : String → Bool)
    (c : Conf) (runtime binding : Subst) (head : Atom) (f : String)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, runtime))
    (hdenotes : SubstDenotesBinding runtime binding)
    (hbindingHead : Metta.Subst.apply binding head = Atom.sym f)
    (hselected : isDefined f = true)
    (hdefined : c.world.clauseHeadCandidates f ≠ []) :
    Step prog gt c
      { c with cur := some ((specializeCallableHeadGoal isDefined isBin binding
            (Goal.callDyn head args res)) :: rest, runtime) } := by
  have hinvisible := subst_apply_of_denotes runtime binding hdenotes head
  rw [hbindingHead] at hinvisible
  have hhead : subst runtime head = Atom.sym f := by
    simpa using hinvisible.symm
  simpa [specializeCallableHeadGoal, hbindingHead, hselected] using
    callDyn_defined_steps_to_direct prog gt c head f args res rest runtime
      hcur hhead hdefined

/-- Fuel-parametric executable convergence for the actual defined-function
    rewrite.  The common suffix may recurse or branch arbitrarily; both runs
    therefore retain exact ordered answers, multiplicity, and world effects. -/
theorem runClean_denoted_callDyn_defined_eq_rewrite (prog : Prog)
    (gt : GroundingTable) (fuel : Nat)
    (isDefined isBin : String → Bool) (c : Conf)
    (runtime binding : Subst) (head : Atom) (f : String)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, runtime))
    (hdenotes : SubstDenotesBinding runtime binding)
    (hbindingHead : Metta.Subst.apply binding head = Atom.sym f)
    (hselected : isDefined f = true)
    (hdefined : c.world.clauseHeadCandidates f ≠ []) :
    runClean prog gt (fuel + 2) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some ((specializeCallableHeadGoal isDefined isBin binding
              (Goal.callDyn head args res)) :: rest, runtime) } none := by
  have hinvisible := subst_apply_of_denotes runtime binding hdenotes head
  rw [hbindingHead] at hinvisible
  have hhead : subst runtime head = Atom.sym f := by
    simpa using hinvisible.symm
  simpa [specializeCallableHeadGoal, hbindingHead, hselected] using
    runClean_callDyn_defined_eq_direct prog gt fuel c head f args res rest
      runtime hcur hhead hdefined

/-- A concrete dynamic builtin head is exactly one dispatch step away from
    the direct builtin goal emitted by profile lowering. -/
theorem callDyn_builtin_steps_to_direct (prog : Prog) (gt : GroundingTable)
    (c : Conf) (head : Atom) (op : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hhead : subst b head = Atom.sym op)
    (hundefined : c.world.clauseHeadCandidates op = [])
    (hbuiltin : (GroundingTable.lookup gt op).isSome) :
    Step prog gt c { c with cur := some (Goal.bin op args res :: rest, b) } := by
  exact Step.callDyn_bin c head op args res rest b hcur hhead hundefined hbuiltin

theorem runClean_callDyn_builtin_eq_direct (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (c : Conf) (head : Atom) (op : String)
    (args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hhead : subst b head = Atom.sym op)
    (hundefined : c.world.clauseHeadCandidates op = [])
    (hbuiltin : (GroundingTable.lookup gt op).isSome) :
    runClean prog gt (fuel + 2) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (Goal.bin op args res :: rest, b) } none := by
  have hterminal : c.isTerminalB = false := by
    simp [Conf.isTerminalB, hcur]
  have hstep : step prog gt fuel c =
      { c with cur := some (Goal.bin op args res :: rest, b) } := by
    unfold step
    rw [hcur]
    simp [hhead, hundefined, hbuiltin]
  have hclean : stepClean prog gt (fuel + 1) c =
      .progressed { c with cur := some (Goal.bin op args res :: rest, b) } := by
    simp [stepClean, hcur, hstep]
  simp [runClean, hterminal, Conf.limitReachedB, hclean]

/-- The builtin arm of the actual callable-head rewrite has the same
    one-step/fuel-shifted convergence property. -/
theorem runClean_denoted_callDyn_builtin_eq_rewrite (prog : Prog)
    (gt : GroundingTable) (fuel : Nat)
    (isDefined isBin : String → Bool) (c : Conf)
    (runtime binding : Subst) (head : Atom) (op : String)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, runtime))
    (hdenotes : SubstDenotesBinding runtime binding)
    (hbindingHead : Metta.Subst.apply binding head = Atom.sym op)
    (hnotDefined : isDefined op = false) (hselected : isBin op = true)
    (hundefined : c.world.clauseHeadCandidates op = [])
    (hbuiltin : (GroundingTable.lookup gt op).isSome) :
    runClean prog gt (fuel + 2) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some ((specializeCallableHeadGoal isDefined isBin binding
              (Goal.callDyn head args res)) :: rest, runtime) } none := by
  have hinvisible := subst_apply_of_denotes runtime binding hdenotes head
  rw [hbindingHead] at hinvisible
  have hhead : subst runtime head = Atom.sym op := by
    simpa using hinvisible.symm
  simpa [specializeCallableHeadGoal, hbindingHead, hnotDefined, hselected] using
    runClean_callDyn_builtin_eq_direct prog gt fuel c head op args res rest
      runtime hcur hhead hundefined hbuiltin

/-- Applying a partial value performs one semantics-only redispatch step.
    This theorem deliberately exposes the runtime-substituted bound arguments;
    the subsequent direct-call theorem can then be reused for functions or
    builtins without assuming that partial bindings are closed. -/
theorem subst_chainOf (b : Subst) (atoms : List Atom) :
    subst b (chainOf atoms) = chainOf (atoms.map (subst b)) := by
  induction atoms with
  | nil => simp [chainOf, nilA]
  | cons head tail ih =>
      change subst b (consC head (chainOf tail)) =
        consC (subst b head) (chainOf (tail.map (subst b)))
      simp [consC, ih]

@[simp] theorem chainListM_chainOf (atoms : List Atom) :
    chainListM (chainOf atoms) = some atoms := by
  induction atoms with
  | nil => simp [chainOf, nilA, chainListM]
  | cons head tail ih =>
      change chainListM (consC head (chainOf tail)) = some (head :: tail)
      simp [consC, chainListM, ih]

/-- Successful decoding is lossless: a parsed spine is exactly its canonical
    internal cons-chain. -/
theorem chainListM_sound : (atom : Atom) → (atoms : List Atom) →
    chainListM atom = some atoms → atom = chainOf atoms
  := by
  intro atom atoms hparse
  fun_induction chainListM atom generalizing atoms
  case case1 =>
    simp at hparse
    subst atoms
    rfl
  case case2 head tail ih =>
    simp only [Option.map_eq_some_iff] at hparse
    rcases hparse with ⟨tailAtoms, htail, rfl⟩
    change consC head tail = consC head (chainOf tailAtoms)
    rw [ih tailAtoms htail]
  case case3 => simp at hparse

/-- The specialization view and runtime view agree on both the outer partial
    spine and its bound-argument spine. -/
theorem partialHeadView?_sound (concrete : Atom) (base : String)
    (bound : List Atom)
    (hview : partialHeadView? concrete = some (base, bound)) :
    partialView? concrete = some (base, chainOf bound) := by
  unfold partialHeadView? at hview
  split at hview
  next parsedBase boundList houter =>
    simp only [Option.map_eq_some_iff] at hview
    rcases hview with ⟨parsedBound, hbound, hpair⟩
    cases hpair
    have hboundShape := chainListM_sound boundList bound hbound
    simpa [hboundShape] using houter
  next houter => simp at hview

/-- A partial head selected from a captured binding is seen by the generic
    runtime as the same partial, with deep substitution applied exactly to
    its bound arguments. -/
theorem subst_denoted_partialHeadView (runtime binding : Subst)
    (head : Atom) (base : String) (bound : List Atom)
    (hdenotes : SubstDenotesBinding runtime binding)
    (hview : partialHeadView? (Metta.Subst.apply binding head) =
      some (base, bound)) :
    subst runtime head =
      partialC base (chainOf (bound.map (subst runtime))) := by
  let concrete := Metta.Subst.apply binding head
  have houter := partialHeadView?_sound concrete base bound hview
  have hshape : concrete = partialC base (chainOf bound) :=
    partialView?_sound houter
  have hinvisible := subst_apply_of_denotes runtime binding hdenotes head
  calc
    subst runtime head = subst runtime concrete := hinvisible.symm
    _ = subst runtime (partialC base (chainOf bound)) := by rw [hshape]
    _ = partialC base (chainOf (bound.map (subst runtime))) := by
        simp [partialC, partialTagA, subst_chainOf]

theorem partialView?_subst_denoted_partialHeadView (runtime binding : Subst)
    (head : Atom) (base : String) (bound : List Atom)
    (hdenotes : SubstDenotesBinding runtime binding)
    (hview : partialHeadView? (Metta.Subst.apply binding head) =
      some (base, bound)) :
    partialView? (subst runtime head) =
      some (base, chainOf (bound.map (subst runtime))) := by
  rw [subst_denoted_partialHeadView runtime binding head base bound
    hdenotes hview]
  simp [partialC, partialView?, partialTagA]

/-- Every atom supported by source residuals is literally fixed by a
    sequential residual state. -/
theorem FreshResidualLookupState.source_atom_fixed
    {fresh : String → String} {allowed : List String} {runtime : Subst}
    (state : FreshResidualLookupState fresh allowed runtime)
    (atom : Atom) (hsupported : ∀ source, source ∈ atom.vars →
      source ∈ allowed) :
    subst runtime atom = atom := by
  apply subst_eq_self_of_domain_free runtime atom
  intro source hsource
  exact (state source (hsupported source hsource)).1

/-- Generic fixed-suffix guard theorem for a copied pattern that may already
    contain source variables established by earlier guards.  `FreshVariant`
    records both still-fresh variables and reflexive shared-variable reuse. -/
theorem freshVariant_guard_unifyB_succeeds_queryInvisible
    (fresh : String → String) (copied source : Atom) (base : Subst)
    (qterm formalName : Atom) (topological : SubstTopological base)
    (variant : FreshVariant fresh (subst base copied) source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right)
    (hqueryFresh : ∀ sourceName, sourceName ∈ source.vars →
      ∀ visible, visible ∈ (subst base qterm).vars →
        fresh sourceName ≠ visible)
    (hformal : subst base formalName = source) :
    ∃ next,
      unifyB base copied formalName = some next ∧
        subst next qterm = subst base qterm := by
  obtain ⟨generated, hgenerated, hdomain⟩ :=
    variant.unifyTopExact_succeeds_with_domain hinjective hdisjoint
  have hunify : unifyTopExact (subst base copied)
      (subst base formalName) = some generated := by
    simpa [hformal] using hgenerated
  have hgeneratedFree : ∀ visible,
      visible ∈ (subst base qterm).vars →
        Metta.Subst.lookup generated visible = none := by
    intro visible hvisible
    apply hdomain.lookup_none_of_forbidden
    intro sourceName hsource
    exact hqueryFresh sourceName hsource visible hvisible
  cases generated with
  | nil =>
      have hresult : unifyB base copied formalName = some base := by
        simp [unifyB, hunify]
      exact ⟨base, hresult, rfl⟩
  | cons generatedHead generatedTail =>
      let generated : Subst := generatedHead :: generatedTail
      let next := Metta.Subst.compose generated base
      have hresult : unifyB base copied formalName = some next := by
        simp [unifyB, hunify, generated, next]
      have hnextFree : ∀ visible,
          visible ∈ (subst base qterm).vars →
            Metta.Subst.lookup next visible = none := by
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none :=
          topological.subst_resolvesDomain base qterm visible hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          simpa [generated] using hgeneratedFree visible hvisible
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have hfixed : subst next (subst base qterm) = subst base qterm :=
        subst_eq_self_of_domain_free next (subst base qterm) hnextFree
      have habsorbs : subst next (subst base qterm) = subst next qterm :=
        unifyB_absorbs_base base copied formalName next topological hresult qterm
      exact ⟨next, hresult, habsorbs.symm.trans hfixed⟩

/-- Exact evidence for one ordered guard constructor: the same structural
    relation supplies a concrete propositional witness, executable success,
    and caller-query invisibility. -/
theorem freshVariant_guard_exact_evidence
    (fresh : String → String) (copied source : Atom) (base : Subst)
    (qterm formalName : Atom) (topological : SubstTopological base)
    (variant : FreshVariant fresh (subst base copied) source)
    (hinjective : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right)
    (hqueryFresh : ∀ sourceName, sourceName ∈ source.vars →
      ∀ visible, visible ∈ (subst base qterm).vars →
        fresh sourceName ≠ visible)
    (hformal : subst base formalName = source) :
    ∃ next witness,
      unifyB base copied formalName = some next ∧
        subst witness (subst base copied) =
          subst witness (subst base formalName) ∧
        subst next qterm = subst base qterm := by
  obtain ⟨next, hresult, hquery⟩ :=
    freshVariant_guard_unifyB_succeeds_queryInvisible fresh copied source base
      qterm formalName topological variant hinjective hdisjoint hqueryFresh
      hformal
  obtain ⟨witness, hwitness⟩ := variant.exact_witness hinjective hdisjoint
  exact ⟨next, witness, hresult, by simpa [hformal] using hwitness, hquery⟩

/-- One guard advances the executable substitution while preserving the
    lookup invariant for the complete residual family.  This is the
    induction step for constructing an ordered `ExactBindingGuardsRun`; it
    exposes the generated unifier rather than recomputing the clause suffix
    after each guard. -/
theorem freshVariant_guard_exact_evidence_state
    (fresh : String → String) (allowed : List String)
    (copied source : Atom) (base : Subst)
    (qterm formalName : Atom) (topological : SubstTopological base)
    (state : FreshResidualLookupState fresh allowed base)
    (variant : FreshVariant fresh (subst base copied) source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (hdisjoint : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed → fresh left ≠ right)
    (hsource : ∀ name, name ∈ source.vars → name ∈ allowed)
    (hqueryFresh : ∀ sourceName, sourceName ∈ source.vars →
      ∀ visible, visible ∈ (subst base qterm).vars →
        fresh sourceName ≠ visible)
    (hformal : subst base formalName = source) :
    ∃ next witness, ∃ _ : SubstTopological next,
      unifyB base copied formalName = some next ∧
        subst witness (subst base copied) =
          subst witness (subst base formalName) ∧
        subst next qterm = subst base qterm ∧
        FreshResidualLookupState fresh allowed next := by
  have hinjectiveSource : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars →
        fresh left = fresh right → left = right := by
    intro left hleft right hright hequal
    exact hinjective left (hsource left hleft) right (hsource right hright)
      hequal
  have hdisjointSource : ∀ left, left ∈ source.vars →
      ∀ right, right ∈ source.vars → fresh left ≠ right := by
    intro left hleft right hright
    exact hdisjoint left (hsource left hleft) right (hsource right hright)
  obtain ⟨generated, hgenerated, hdomain⟩ :=
    variant.unifyTopExact_succeeds_with_domain hinjectiveSource
      hdisjointSource
  obtain ⟨witness, hwitness⟩ :=
    variant.exact_witness hinjectiveSource hdisjointSource
  have hunify : unifyTopExact (subst base copied)
      (subst base formalName) = some generated := by
    simpa [hformal] using hgenerated
  have hgeneratedFree : ∀ visible,
      visible ∈ (subst base qterm).vars →
        Metta.Subst.lookup generated visible = none := by
    intro visible hvisible
    apply hdomain.lookup_none_of_forbidden
    intro sourceName hsourceName
    exact hqueryFresh sourceName hsourceName visible hvisible
  cases generated with
  | nil =>
      have hresult : unifyB base copied formalName = some base := by
        simp [unifyB, hunify]
      exact ⟨base, witness, topological, hresult,
        by simpa [hformal] using hwitness, rfl, state⟩
  | cons generatedHead generatedTail =>
      let generated : Subst := generatedHead :: generatedTail
      let next := Metta.Subst.compose generated base
      have hresult : unifyB base copied formalName = some next := by
        simp [unifyB, hunify, generated, next]
      have hnextFree : ∀ visible,
          visible ∈ (subst base qterm).vars →
            Metta.Subst.lookup next visible = none := by
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none :=
          topological.subst_resolvesDomain base qterm visible hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          simpa [generated] using hgeneratedFree visible hvisible
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have hfixed : subst next (subst base qterm) = subst base qterm :=
        subst_eq_self_of_domain_free next (subst base qterm) hnextFree
      have habsorbs : subst next (subst base qterm) = subst next qterm :=
        unifyB_absorbs_base base copied formalName next topological hresult qterm
      have hnextState : FreshResidualLookupState fresh allowed next := by
        apply state.compose_generated fresh allowed source.vars base generated
          hinjective hdisjoint hsource
        simpa [generated] using hdomain
      exact ⟨next, witness,
        unifyB_topological base copied formalName next topological hresult,
        hresult, by simpa [hformal] using hwitness,
        habsorbs.symm.trans hfixed, hnextState⟩

/-- General one-guard induction step after arbitrary caller instantiation of
    source residuals.  Generated bindings still have only fresh-copy keys,
    but their targets are the current source denotations. -/
theorem freshInstance_guard_exact_evidence_state
    (fresh : String → String) (allowed : List String)
    (copied sourcePattern : Atom) (base : Subst)
    (qterm formalName : Atom) (topological : SubstTopological base)
    (state : FreshResidualDenotationState fresh allowed base)
    (related : FreshInstance fresh
      (fun name => subst base (Atom.var name)) allowed
      (subst base copied) (subst base sourcePattern))
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (subst base (Atom.var right)).vars)
    (hqueryFresh : ∀ source, source ∈ allowed →
      ∀ visible, visible ∈ (subst base qterm).vars →
        fresh source ≠ visible)
    (hformal : subst base formalName = subst base sourcePattern) :
    ∃ next witness, ∃ _ : SubstTopological next,
      unifyB base copied formalName = some next ∧
        subst witness (subst base copied) =
        subst witness (subst base formalName) ∧
        subst next qterm = subst base qterm ∧
        (∀ source, source ∈ allowed →
          subst next (Atom.var source) =
            subst base (Atom.var source)) ∧
        FreshResidualDenotationState fresh allowed next ∧
        (∀ key value, Metta.Subst.lookup base key = some value →
          (∀ source, source ∈ allowed → fresh source ∉ value.vars) →
          Metta.Subst.lookup next key = some value) := by
  obtain ⟨generated, hgenerated, hdomain⟩ :=
    related.unifyTop_succeeds_with_domain hinjective havoids
  obtain ⟨witness, hwitness⟩ :=
    related.exact_witness hinjective havoids
  have hgeneratedExact : unifyTopExact (subst base copied)
      (subst base sourcePattern) = some generated :=
    unifyTopExact_of_exact_witness (subst base copied)
      (subst base sourcePattern) generated witness hwitness hgenerated
  have hunify : unifyTopExact (subst base copied)
      (subst base formalName) = some generated := by
    simpa [hformal] using hgeneratedExact
  have hgeneratedFree : ∀ visible,
      visible ∈ (subst base qterm).vars →
        Metta.Subst.lookup generated visible = none := by
    intro visible hvisible
    apply hdomain.lookup_none_of_forbidden
    intro source hsource
    exact hqueryFresh source hsource visible hvisible
  cases generated with
  | nil =>
      have hresult : unifyB base copied formalName = some base := by
        simp [unifyB, hunify]
      exact ⟨base, witness, topological, hresult,
        by simpa [hformal] using hwitness, rfl,
        by intro source hsource; rfl, state,
        by intro key value hlookup hfree; exact hlookup⟩
  | cons generatedHead generatedTail =>
      let generated : Subst := generatedHead :: generatedTail
      let next := Metta.Subst.compose generated base
      have hresult : unifyB base copied formalName = some next := by
        simp [unifyB, hunify, generated, next]
      have nextTopological : SubstTopological next :=
        unifyB_topological base copied formalName next topological hresult
      have hnextFree : ∀ visible,
          visible ∈ (subst base qterm).vars →
            Metta.Subst.lookup next visible = none := by
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none :=
          topological.subst_resolvesDomain base qterm visible hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          simpa [generated] using hgeneratedFree visible hvisible
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have hfixed : subst next (subst base qterm) = subst base qterm :=
        subst_eq_self_of_domain_free next (subst base qterm) hnextFree
      have habsorbs : subst next (subst base qterm) = subst next qterm :=
        unifyB_absorbs_base base copied formalName next topological hresult qterm
      have hsourcePreserved : ∀ source, source ∈ allowed →
          subst next (Atom.var source) =
            subst base (Atom.var source) := by
        intro source hsource
        have hresolvedFree : ∀ visible,
            visible ∈ (subst base (Atom.var source)).vars →
              Metta.Subst.lookup next visible = none := by
          intro visible hvisible
          have hbaseNone : Metta.Subst.lookup base visible = none :=
            topological.subst_resolvesDomain base (Atom.var source) visible
              hvisible
          have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
            apply hdomain.lookup_none_of_forbidden
            intro origin horigin hequal
            exact havoids origin horigin source hsource (by
              simpa [hequal] using hvisible)
          simp [next, lookup_compose, hbaseNone, hgeneratedNone]
        have hfixed :
            subst next (subst base (Atom.var source)) =
              subst base (Atom.var source) :=
          subst_eq_self_of_domain_free next
            (subst base (Atom.var source)) hresolvedFree
        have habsorbs :
            subst next (subst base (Atom.var source)) =
              subst next (Atom.var source) :=
          unifyB_absorbs_base base copied formalName next topological hresult
            (Atom.var source)
        exact habsorbs.symm.trans hfixed
      have nextState : FreshResidualDenotationState fresh allowed next := by
        intro source hsource
        rcases state source hsource with hfreshNone | hsemantic
        · cases hlookup : Metta.Subst.lookup generated (fresh source) with
          | none =>
              left
              simp [next, lookup_compose, hfreshNone, hlookup]
          | some target =>
              right
              obtain ⟨origin, horigin, hname, htarget⟩ :=
                hdomain.lookup_shape fresh
                  (fun name => subst base (Atom.var name)) allowed generated
                  (fresh source) target (by simpa [generated] using hlookup)
              have hequal : source = origin :=
                hinjective source hsource origin horigin hname
              subst origin
              subst target
              have hnextLookup : Metta.Subst.lookup next (fresh source) =
                  some (subst base (Atom.var source)) := by
                simp [next, lookup_compose, hfreshNone, generated, hlookup]
              have hfreshDenotes := nextTopological.subst_var_of_lookup next
                (fresh source) (subst base (Atom.var source)) hnextLookup
              exact hfreshDenotes.trans
                (unifyB_absorbs_base base copied formalName next topological
                  hresult (Atom.var source))
        · right
          exact unifyB_preserves_denotation base copied formalName next
            topological hresult (Atom.var (fresh source)) (Atom.var source)
            hsemantic
      have hlookupPreserved : ∀ key value,
          Metta.Subst.lookup base key = some value →
          (∀ source, source ∈ allowed → fresh source ∉ value.vars) →
          Metta.Subst.lookup next key = some value := by
        intro key value hlookup hfree
        have hvalueFixed : Metta.Subst.apply generated value = value := by
          exact apply_eq_self_of_lookup_none generated value (by
            intro variableName hvariable
            apply hdomain.lookup_none_of_forbidden
            intro source hsource hequal
            exact hfree source hsource (by simpa [hequal] using hvariable))
        rw [lookup_compose, hlookup]
        exact congrArg some hvalueFixed
      exact ⟨next, witness, nextTopological, hresult,
        by simpa [hformal] using hwitness,
        habsorbs.symm.trans hfixed, hsourcePreserved, nextState,
        hlookupPreserved⟩

/-- One guard relative to the immutable head-time residual denotation.  The
    source variable itself may have been removed by liveness; only the saved
    resolved target and its alpha-copy are carried through the run. -/
theorem freshSnapshot_guard_exact_evidence_state
    (fresh : String → String) (resolve : String → Atom)
    (allowed : List String) (copied target : Atom) (base : Subst)
    (qterm formalName : Atom) (topological : SubstTopological base)
    (state : FreshResidualSnapshotState fresh resolve allowed base)
    (related : FreshInstance fresh resolve allowed
      (subst base copied) target)
    (hresolveFixed : ∀ source, source ∈ allowed →
      subst base (resolve source) = resolve source)
    (hinjective : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left = fresh right → left = right)
    (havoids : ∀ left, left ∈ allowed →
      ∀ right, right ∈ allowed →
        fresh left ∉ (resolve right).vars)
    (hqueryFresh : ∀ source, source ∈ allowed →
      ∀ visible, visible ∈ (subst base qterm).vars →
        fresh source ≠ visible)
    (hformal : subst base formalName = target) :
    ∃ next witness, ∃ _ : SubstTopological next,
      unifyB base copied formalName = some next ∧
        subst witness (subst base copied) =
          subst witness (subst base formalName) ∧
        subst next qterm = subst base qterm ∧
        (∀ source, source ∈ allowed →
          subst next (resolve source) = resolve source) ∧
        FreshResidualSnapshotState fresh resolve allowed next ∧
        (∀ key value, Metta.Subst.lookup base key = some value →
          (∀ source, source ∈ allowed → fresh source ∉ value.vars) →
          Metta.Subst.lookup next key = some value) := by
  obtain ⟨generated, hgenerated, hdomain⟩ :=
    related.unifyTop_succeeds_with_domain hinjective havoids
  obtain ⟨witness, hwitness⟩ :=
    related.exact_witness hinjective havoids
  have hgeneratedExact : unifyTopExact (subst base copied) target =
      some generated :=
    unifyTopExact_of_exact_witness (subst base copied) target generated
      witness hwitness hgenerated
  have hunify : unifyTopExact (subst base copied)
      (subst base formalName) = some generated := by
    simpa [hformal] using hgeneratedExact
  have hgeneratedFree : ∀ visible,
      visible ∈ (subst base qterm).vars →
        Metta.Subst.lookup generated visible = none := by
    intro visible hvisible
    apply hdomain.lookup_none_of_forbidden
    intro source hsource
    exact hqueryFresh source hsource visible hvisible
  cases generated with
  | nil =>
      have hresult : unifyB base copied formalName = some base := by
        simp [unifyB, hunify]
      exact ⟨base, witness, topological, hresult,
        by simpa [hformal] using hwitness, rfl, hresolveFixed, state,
        by intro key value hlookup hfree; exact hlookup⟩
  | cons generatedHead generatedTail =>
      let generated : Subst := generatedHead :: generatedTail
      let next := Metta.Subst.compose generated base
      have hresult : unifyB base copied formalName = some next := by
        simp [unifyB, hunify, generated, next]
      have nextTopological : SubstTopological next :=
        unifyB_topological base copied formalName next topological hresult
      have hnextFree : ∀ visible,
          visible ∈ (subst base qterm).vars →
            Metta.Subst.lookup next visible = none := by
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none :=
          topological.subst_resolvesDomain base qterm visible hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          simpa [generated] using hgeneratedFree visible hvisible
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have hfixed : subst next (subst base qterm) = subst base qterm :=
        subst_eq_self_of_domain_free next (subst base qterm) hnextFree
      have habsorbs : subst next (subst base qterm) = subst next qterm :=
        unifyB_absorbs_base base copied formalName next topological hresult qterm
      have hresolveNext : ∀ source, source ∈ allowed →
          subst next (resolve source) = resolve source := by
        intro source hsource
        apply subst_eq_self_of_domain_free next (resolve source)
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none := by
          apply topological.subst_resolvesDomain base (resolve source)
          rw [hresolveFixed source hsource]
          exact hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          apply hdomain.lookup_none_of_forbidden
          intro origin horigin hequal
          exact havoids origin horigin source hsource (by
            simpa [hequal] using hvisible)
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have nextState : FreshResidualSnapshotState fresh resolve allowed next := by
        intro source hsource
        rcases state source hsource with hfreshNone | hsemantic
        · cases hlookup : Metta.Subst.lookup generated (fresh source) with
          | none =>
              left
              simp [next, lookup_compose, hfreshNone, hlookup]
          | some resolved =>
              right
              obtain ⟨origin, horigin, hname, htarget⟩ :=
                hdomain.lookup_shape fresh resolve allowed generated
                  (fresh source) resolved (by
                    simpa [generated] using hlookup)
              have hequal : source = origin :=
                hinjective source hsource origin horigin hname
              subst origin
              subst resolved
              have hnextLookup : Metta.Subst.lookup next (fresh source) =
                  some (resolve source) := by
                simp [next, lookup_compose, hfreshNone, generated, hlookup]
              exact (nextTopological.subst_var_of_lookup next
                (fresh source) (resolve source) hnextLookup).trans
                (hresolveNext source hsource)
        · right
          have hprior : subst base (Atom.var (fresh source)) =
              subst base (resolve source) :=
            hsemantic.trans (hresolveFixed source hsource).symm
          exact (unifyB_preserves_denotation base copied formalName next
            topological hresult (Atom.var (fresh source)) (resolve source)
            hprior).trans (hresolveNext source hsource)
      have hlookupPreserved : ∀ key value,
          Metta.Subst.lookup base key = some value →
          (∀ source, source ∈ allowed → fresh source ∉ value.vars) →
          Metta.Subst.lookup next key = some value := by
        intro key value hlookup hfree
        have hvalueFixed : Metta.Subst.apply generated value = value := by
          exact apply_eq_self_of_lookup_none generated value (by
            intro variableName hvariable
            apply hdomain.lookup_none_of_forbidden
            intro source hsource hequal
            exact hfree source hsource (by
              simpa [hequal] using hvariable))
        rw [lookup_compose, hlookup]
        exact congrArg some hvalueFixed
      exact ⟨next, witness, nextTopological, hresult,
        by simpa [hformal] using hwitness,
        habsorbs.symm.trans hfixed, hresolveNext, nextState,
        hlookupPreserved⟩

/-- Complete ordered guard-run constructor for arbitrary instantiated source
    residuals.  The copy map and suffix stay fixed clause-wide; the active
    residual set shrinks with the remaining source-binding tail. -/
theorem specialization_exactBindingGuardsRun_general
    (clause : Clause) (allBinding remaining : Subst) (suffix : String)
    (qterm : Atom) (rest : List Goal) (base : Subst)
    (hremaining : ∀ name value, (name, value) ∈ remaining →
      (name, value) ∈ allBinding)
    (topological : SubstTopological base)
    (residualState : FreshResidualDenotationState
      (copiedResidualNameSuffix
        (specializationCopySubst clause allBinding) suffix)
      (specializationResiduals remaining) base)
    (headLookup : SourceBindingHeadLookupState suffix remaining base)
    (hreflexive : ∀ name value, (name, value) ∈ allBinding →
      Metta.Atom.equiv
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value)
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value) = true)
    (hinjective : ∀ left, left ∈ specializationResiduals allBinding →
      ∀ right, right ∈ specializationResiduals allBinding →
        copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix left =
          copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix right →
        left = right)
    (hrawDisjoint : ∀ left,
      left ∈ specializationResiduals allBinding →
      ∀ right, right ∈ specializationResiduals allBinding →
        copiedResidualNameSuffix
          (specializationCopySubst clause allBinding) suffix left ≠ right)
    (hresolvedReflexive : ∀ source,
      source ∈ specializationResiduals remaining →
      Metta.Atom.equiv (subst base (Atom.var source))
        (subst base (Atom.var source)) = true)
    (havoids : ∀ left, left ∈ specializationResiduals remaining →
      ∀ right, right ∈ specializationResiduals remaining →
        copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix left ∉
          (subst base (Atom.var right)).vars)
    (hqueryFresh : ∀ source,
      source ∈ specializationResiduals remaining →
      ∀ visible, visible ∈ (subst base qterm).vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause allBinding) suffix source ≠
            visible) :
    ∃ final,
      ExactBindingGuardsRun qterm rest
        (specializationGuardBindingSuffix clause allBinding suffix remaining)
        base final := by
  induction remaining generalizing base with
  | nil => exact ⟨base, .nil base topological⟩
  | cons entry tail ih =>
      rcases entry with ⟨name, value⟩
      let copy := specializationCopySubst clause allBinding
      let fresh := copiedResidualNameSuffix copy suffix
      let copied := renameAtomSuffix suffix (Metta.Subst.apply copy value)
      let tailBinding :=
        specializationGuardBindingSuffix clause allBinding suffix tail
      let allowed := specializationResiduals ((name, value) :: tail)
      let tailAllowed := specializationResiduals tail
      have hentryAll : (name, value) ∈ allBinding :=
        hremaining name value (by simp)
      have hsource : ∀ source, source ∈ value.vars →
          source ∈ allowed := by
        intro source hsource
        exact sourceBinding_value_var_mem_residuals
          ((name, value) :: tail) name value (by simp) source hsource
      have hallowedAll : ∀ source, source ∈ allowed →
          source ∈ specializationResiduals allBinding := by
        intro source hsourceAllowed
        obtain ⟨originName, originValue, horigin, hsourceValue⟩ :=
          specializationResiduals_mem_origin ((name, value) :: tail) source
            hsourceAllowed
        exact sourceBinding_value_var_mem_residuals allBinding originName
          originValue (hremaining originName originValue horigin) source
          hsourceValue
      have related : FreshInstance fresh
          (fun source => subst base (Atom.var source)) allowed
          (subst base copied) (subst base value) := by
        apply specializationCopy_current_freshInstance clause allBinding name
          value hentryAll suffix base allowed hsource residualState
          (hreflexive name value hentryAll)
        · intro source hsourceAllowed
          exact hrawDisjoint source (hallowedAll source hsourceAllowed)
            source (hallowedAll source hsourceAllowed)
        · intro left hleft right hright
          exact havoids left hleft right hright
      have hformal : subst base (Atom.var (name ++ suffix)) =
          subst base value := by
        exact topological.subst_var_of_lookup base (name ++ suffix) value
          (headLookup name value (by simp))
      have hinjectiveAllowed : ∀ left, left ∈ allowed →
          ∀ right, right ∈ allowed →
            fresh left = fresh right → left = right := by
        intro left hleft right hright hequal
        exact hinjective left (hallowedAll left hleft) right
          (hallowedAll right hright) hequal
      obtain ⟨next, witness, nextTopological, hresult, hwitness, hquery,
          hsourceNext, nextState, lookupPreserved⟩ :=
        freshInstance_guard_exact_evidence_state fresh allowed copied value
          base qterm (Atom.var (name ++ suffix)) topological residualState
          related hinjectiveAllowed havoids hqueryFresh hformal
      let goals := specializationGuards tailBinding ++ rest
      let trimmed := PLeaTTa.trimFor goals qterm next
      have trimmedTopological : SubstTopological trimmed :=
        SubstTopological.trimFor goals qterm next nextTopological
      have htailAllowed : ∀ source, source ∈ tailAllowed →
          source ∈ allowed := by
        intro source hsourceTail
        obtain ⟨tailName, tailValue, htailEntry, hsourceValue⟩ :=
          specializationResiduals_mem_origin tail source hsourceTail
        exact sourceBinding_value_var_mem_residuals
          ((name, value) :: tail) tailName tailValue (by simp [htailEntry])
          source hsourceValue
      have nextHeadLookup : SourceBindingHeadLookupState suffix tail next := by
        intro tailName tailValue htailEntry
        apply lookupPreserved (tailName ++ suffix) tailValue
        · exact headLookup tailName tailValue (by simp [htailEntry])
        · intro source hsourceAllowed hmem
          have hsourceAll := hallowedAll source hsourceAllowed
          have hfreshAll : fresh source ∈
              specializationResiduals allBinding :=
            sourceBinding_value_var_mem_residuals allBinding tailName
              tailValue
              (hremaining tailName tailValue (by simp [htailEntry]))
              (fresh source) hmem
          exact hrawDisjoint source hsourceAll (fresh source) hfreshAll rfl
      have trimmedHeadLookup :
          SourceBindingHeadLookupState suffix tail trimmed := by
        intro tailName tailValue htailEntry
        have htailExecutable :
            (tailName ++ suffix,
              renameAtomSuffix suffix (Metta.Subst.apply copy tailValue)) ∈
              tailBinding := by
          unfold tailBinding specializationGuardBindingSuffix
          rw [List.mem_map]
          exact ⟨(tailName, tailValue), htailEntry, rfl⟩
        have hguard : Goal.eq
              (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
              (Atom.var (tailName ++ suffix)) ∈ goals := by
          apply List.mem_append_left rest
          exact specializationGuards_mem_of_binding_mem tailBinding
            (tailName ++ suffix)
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            htailExecutable
        rw [trimFor_lookup_of_root goals qterm next (tailName ++ suffix)
          (isTrimRoot_eq_right_of_mem goals qterm
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            (Atom.var (tailName ++ suffix)) (tailName ++ suffix) hguard
            (by simp [Atom.vars]))]
        exact nextHeadLookup tailName tailValue htailEntry
      have hsourcePreserved : ∀ source, source ∈ tailAllowed →
          subst trimmed (Atom.var source) = subst next (Atom.var source) := by
        intro source hsourceTail
        obtain ⟨tailName, tailValue, htailEntry, hsourceValue⟩ :=
          specializationResiduals_mem_origin tail source hsourceTail
        have hnextLookup := nextHeadLookup tailName tailValue htailEntry
        have htrimmedLookup := trimmedHeadLookup tailName tailValue htailEntry
        have hnextDenotes := nextTopological.subst_var_of_lookup next
          (tailName ++ suffix) tailValue hnextLookup
        have htrimmedDenotes := trimmedTopological.subst_var_of_lookup trimmed
          (tailName ++ suffix) tailValue htrimmedLookup
        have hformalPreserved := subst_trimFor_var_eq_of_lookup_some goals qterm
          next nextTopological (tailName ++ suffix) tailValue htrimmedLookup
        have hvaluePreserved : subst trimmed tailValue = subst next tailValue :=
          htrimmedDenotes.symm.trans (hformalPreserved.trans hnextDenotes)
        exact subst_var_eq_of_mem trimmed next tailValue source hsourceValue
          hvaluePreserved
      have trimmedState : FreshResidualDenotationState fresh tailAllowed
          trimmed := by
        exact (nextState.mono htailAllowed).trimFor fresh tailAllowed next goals
          qterm nextTopological hsourcePreserved
      have htrimQuery : subst trimmed qterm = subst next qterm := by
        apply subst_trimFor_eq_of_topological goals qterm next nextTopological
          qterm
        intro source hsourceQterm
        exact isTrimRoot_qterm_mem goals qterm source hsourceQterm
      have htrimQueryBase : subst trimmed qterm = subst base qterm :=
        htrimQuery.trans hquery
      have htailRemaining : ∀ tailName tailValue,
          (tailName, tailValue) ∈ tail →
            (tailName, tailValue) ∈ allBinding := by
        intro tailName tailValue htailEntry
        exact hremaining tailName tailValue (by simp [htailEntry])
      have htailResolved : ∀ source, source ∈ tailAllowed →
          Metta.Atom.equiv (subst trimmed (Atom.var source))
            (subst trimmed (Atom.var source)) = true := by
        intro source hsourceTail
        rw [hsourcePreserved source hsourceTail]
        rw [hsourceNext source (htailAllowed source hsourceTail)]
        exact hresolvedReflexive source (htailAllowed source hsourceTail)
      have htailAvoids : ∀ left, left ∈ tailAllowed →
          ∀ right, right ∈ tailAllowed →
            fresh left ∉ (subst trimmed (Atom.var right)).vars := by
        intro left hleft right hright
        rw [hsourcePreserved right hright]
        rw [hsourceNext right (htailAllowed right hright)]
        exact havoids left (htailAllowed left hleft) right
          (htailAllowed right hright)
      have htailQueryFresh : ∀ source, source ∈ tailAllowed →
          ∀ visible, visible ∈ (subst trimmed qterm).vars →
            fresh source ≠ visible := by
        intro source hsourceTail visible hvisible
        rw [htrimQueryBase] at hvisible
        exact hqueryFresh source (htailAllowed source hsourceTail) visible
          hvisible
      obtain ⟨final, tailRun⟩ := ih trimmed htailRemaining
        trimmedTopological trimmedState trimmedHeadLookup htailResolved
        htailAvoids htailQueryFresh
      refine ⟨final, ?_⟩
      exact .cons (name ++ suffix) copied tailBinding base next final witness
        topological hwitness hresult hquery
        (by simpa [trimmed, goals] using tailRun)

/-- Complete guard-run construction from the immutable denotation installed
    by clause-head narrowing.  Unlike the source-name formulation above,
    this theorem remains valid when a caller residual is resolved before the
    first guard and is later removed by liveness trimming. -/
theorem specialization_exactBindingGuardsRun_snapshot
    (clause : Clause) (allBinding remaining : Subst) (suffix : String)
    (qterm : Atom) (rest : List Goal) (origin base : Subst)
    (hremaining : ∀ name value, (name, value) ∈ remaining →
      (name, value) ∈ allBinding)
    (topological : SubstTopological base)
    (residualState : FreshResidualSnapshotState
      (copiedResidualNameSuffix
        (specializationCopySubst clause allBinding) suffix)
      (fun source => subst origin (Atom.var source))
      (specializationResiduals remaining) base)
    (headLookup : SourceBindingHeadSnapshotLookupState suffix origin
      remaining base)
    (hreflexive : ∀ name value, (name, value) ∈ allBinding →
      Metta.Atom.equiv
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value)
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value) = true)
    (hinjective : ∀ left, left ∈ specializationResiduals allBinding →
      ∀ right, right ∈ specializationResiduals allBinding →
        copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix left =
          copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix right →
        left = right)
    (hresolveFixed : ∀ source,
      source ∈ specializationResiduals remaining →
      subst base (subst origin (Atom.var source)) =
        subst origin (Atom.var source))
    (hresolvedReflexive : ∀ source,
      source ∈ specializationResiduals remaining →
      Metta.Atom.equiv (subst origin (Atom.var source))
        (subst origin (Atom.var source)) = true)
    (havoids : ∀ left, left ∈ specializationResiduals remaining →
      ∀ right, right ∈ specializationResiduals remaining →
        copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix left ∉
          (subst origin (Atom.var right)).vars)
    (hqueryFresh : ∀ source,
      source ∈ specializationResiduals remaining →
      ∀ visible, visible ∈ (subst base qterm).vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause allBinding) suffix source ≠
            visible) :
    ∃ final,
      ExactBindingGuardsRun qterm rest
        (specializationGuardBindingSuffix clause allBinding suffix remaining)
        base final := by
  induction remaining generalizing base with
  | nil => exact ⟨base, .nil base topological⟩
  | cons entry tail ih =>
      rcases entry with ⟨name, value⟩
      let copy := specializationCopySubst clause allBinding
      let fresh := copiedResidualNameSuffix copy suffix
      let resolve := fun source => subst origin (Atom.var source)
      let copied := renameAtomSuffix suffix (Metta.Subst.apply copy value)
      let target := subst origin value
      let tailBinding :=
        specializationGuardBindingSuffix clause allBinding suffix tail
      let allowed := specializationResiduals ((name, value) :: tail)
      let tailAllowed := specializationResiduals tail
      have hentryAll : (name, value) ∈ allBinding :=
        hremaining name value (by simp)
      have hsource : ∀ source, source ∈ value.vars →
          source ∈ allowed := by
        intro source hsource
        exact sourceBinding_value_var_mem_residuals
          ((name, value) :: tail) name value (by simp) source hsource
      have hallowedAll : ∀ source, source ∈ allowed →
          source ∈ specializationResiduals allBinding := by
        intro source hsourceAllowed
        obtain ⟨originName, originValue, horigin, hsourceValue⟩ :=
          specializationResiduals_mem_origin ((name, value) :: tail) source
            hsourceAllowed
        exact sourceBinding_value_var_mem_residuals allBinding originName
          originValue (hremaining originName originValue horigin) source
          hsourceValue
      have hlookupCopy : ∀ source, source ∈ value.vars →
          ∃ target,
            Metta.Subst.lookup copy source = some (Atom.var target) := by
        intro source hsourceValue
        exact specializationCopySubst_lookup_var clause allBinding source
          (hallowedAll source (hsource source hsourceValue))
      obtain ⟨related, htargetFixed⟩ :=
        rename_apply_current_freshSnapshotInstance copy suffix value origin
          base allowed hlookupCopy hsource residualState hresolveFixed
          havoids (hreflexive name value hentryAll)
      have hformal : subst base (Atom.var (name ++ suffix)) = target := by
        have hlookup := headLookup name value (by simp)
        exact (topological.subst_var_of_lookup base (name ++ suffix)
          (subst origin value) hlookup).trans htargetFixed
      have hinjectiveAllowed : ∀ left, left ∈ allowed →
          ∀ right, right ∈ allowed →
            fresh left = fresh right → left = right := by
        intro left hleft right hright hequal
        exact hinjective left (hallowedAll left hleft) right
          (hallowedAll right hright) hequal
      obtain ⟨next, witness, nextTopological, hresult, hwitness, hquery,
          hresolveNext, nextState, lookupPreserved⟩ :=
        freshSnapshot_guard_exact_evidence_state fresh resolve allowed copied
          target base qterm (Atom.var (name ++ suffix)) topological
          residualState related hresolveFixed hinjectiveAllowed havoids
          hqueryFresh hformal
      let goals := specializationGuards tailBinding ++ rest
      let trimmed := PLeaTTa.trimFor goals qterm next
      have trimmedTopological : SubstTopological trimmed :=
        SubstTopological.trimFor goals qterm next nextTopological
      have htailAllowed : ∀ source, source ∈ tailAllowed →
          source ∈ allowed := by
        intro source hsourceTail
        obtain ⟨tailName, tailValue, htailEntry, hsourceValue⟩ :=
          specializationResiduals_mem_origin tail source hsourceTail
        exact sourceBinding_value_var_mem_residuals
          ((name, value) :: tail) tailName tailValue (by simp [htailEntry])
          source hsourceValue
      have nextHeadLookup : SourceBindingHeadSnapshotLookupState suffix origin
          tail next := by
        intro tailName tailValue htailEntry
        apply lookupPreserved (tailName ++ suffix) (subst origin tailValue)
        · exact headLookup tailName tailValue (by simp [htailEntry])
        · intro source hsourceAllowed
          apply not_mem_subst_of_not_mem_resolved origin (fresh source)
            tailValue
          intro residual hresidual
          exact havoids source hsourceAllowed residual
            (sourceBinding_value_var_mem_residuals
              ((name, value) :: tail) tailName tailValue
              (by simp [htailEntry]) residual hresidual)
      have trimmedHeadLookup :
          SourceBindingHeadSnapshotLookupState suffix origin tail trimmed := by
        intro tailName tailValue htailEntry
        have htailExecutable :
            (tailName ++ suffix,
              renameAtomSuffix suffix (Metta.Subst.apply copy tailValue)) ∈
              tailBinding := by
          unfold tailBinding specializationGuardBindingSuffix
          rw [List.mem_map]
          exact ⟨(tailName, tailValue), htailEntry, rfl⟩
        have hguard : Goal.eq
              (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
              (Atom.var (tailName ++ suffix)) ∈ goals := by
          apply List.mem_append_left rest
          exact specializationGuards_mem_of_binding_mem tailBinding
            (tailName ++ suffix)
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            htailExecutable
        rw [trimFor_lookup_of_root goals qterm next (tailName ++ suffix)
          (isTrimRoot_eq_right_of_mem goals qterm
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            (Atom.var (tailName ++ suffix)) (tailName ++ suffix) hguard
            (by simp [Atom.vars]))]
        exact nextHeadLookup tailName tailValue htailEntry
      have trimmedState : FreshResidualSnapshotState fresh resolve tailAllowed
          trimmed := by
        exact (nextState.mono htailAllowed).trimFor fresh resolve tailAllowed
          next goals qterm nextTopological
      have htrimQuery : subst trimmed qterm = subst next qterm := by
        apply subst_trimFor_eq_of_topological goals qterm next nextTopological
          qterm
        intro source hsourceQterm
        exact isTrimRoot_qterm_mem goals qterm source hsourceQterm
      have htrimQueryBase : subst trimmed qterm = subst base qterm :=
        htrimQuery.trans hquery
      have htailRemaining : ∀ tailName tailValue,
          (tailName, tailValue) ∈ tail →
            (tailName, tailValue) ∈ allBinding := by
        intro tailName tailValue htailEntry
        exact hremaining tailName tailValue (by simp [htailEntry])
      have htailResolveFixed : ∀ source, source ∈ tailAllowed →
          subst trimmed (resolve source) = resolve source := by
        intro source hsourceTail
        apply subst_eq_self_of_domain_free trimmed (resolve source)
        intro visible hvisible
        have hnextNone : Metta.Subst.lookup next visible = none := by
          apply nextTopological.subst_resolvesDomain next (resolve source)
          rw [hresolveNext source (htailAllowed source hsourceTail)]
          exact hvisible
        cases htrimmedLookup : Metta.Subst.lookup trimmed visible with
        | none => rfl
        | some resolved =>
            have horiginal := trimFor_lookup_eq_original_of_some goals qterm
              next visible resolved htrimmedLookup
            rw [hnextNone] at horiginal
            contradiction
      have htailQueryFresh : ∀ source, source ∈ tailAllowed →
          ∀ visible, visible ∈ (subst trimmed qterm).vars →
            fresh source ≠ visible := by
        intro source hsourceTail visible hvisible
        rw [htrimQueryBase] at hvisible
        exact hqueryFresh source (htailAllowed source hsourceTail) visible
          hvisible
      obtain ⟨final, tailRun⟩ := ih trimmed htailRemaining
        trimmedTopological trimmedState trimmedHeadLookup htailResolveFixed
        (fun source hsourceTail =>
          hresolvedReflexive source (htailAllowed source hsourceTail))
        (fun left hleft right hright =>
          havoids left (htailAllowed left hleft) right
            (htailAllowed right hright))
        htailQueryFresh
      refine ⟨final, ?_⟩
      exact .cons (name ++ suffix) copied tailBinding base next final witness
        topological hwitness hresult hquery
        (by simpa [trimmed, goals] using tailRun)

/-- From the literal post-head state, construct the complete ordered guard
    run for the actual fixed alpha-copy and fixed clause-wide suffix.  The
    theorem handles arbitrary binding length and shared open residuals;
    liveness trimming is part of the recursive state. -/
theorem specialization_exactBindingGuardsRun_of_headState
    (clause : Clause) (allBinding remaining : Subst) (suffix : String)
    (qterm : Atom) (rest : List Goal) (base : Subst)
    (hremaining : ∀ name value, (name, value) ∈ remaining →
      (name, value) ∈ allBinding)
    (topological : SubstTopological base)
    (residualState : FreshResidualLookupState
      (copiedResidualNameSuffix
        (specializationCopySubst clause allBinding) suffix)
      (specializationResiduals allBinding) base)
    (headState : SourceBindingHeadState suffix remaining base)
    (hreflexive : ∀ name value, (name, value) ∈ allBinding →
      Metta.Atom.equiv
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value)
        (Metta.Subst.apply
          (specializationCopySubst clause allBinding) value) = true)
    (hinjective : ∀ left, left ∈ specializationResiduals allBinding →
      ∀ right, right ∈ specializationResiduals allBinding →
        copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix left =
          copiedResidualNameSuffix
            (specializationCopySubst clause allBinding) suffix right →
        left = right)
    (hdisjoint : ∀ copied, copied ∈ specializationResiduals allBinding →
      ∀ source, source ∈ specializationResiduals allBinding →
        copiedResidualNameSuffix
          (specializationCopySubst clause allBinding) suffix copied ≠ source)
    (hqueryFresh : ∀ source, source ∈ specializationResiduals allBinding →
      ∀ visible, visible ∈ (subst base qterm).vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause allBinding) suffix source ≠
            visible) :
    ∃ final,
      ExactBindingGuardsRun qterm rest
        (specializationGuardBindingSuffix clause allBinding suffix remaining)
        base final := by
  induction remaining generalizing base with
  | nil =>
      exact ⟨base, .nil base topological⟩
  | cons entry tail ih =>
      rcases entry with ⟨name, value⟩
      let copy := specializationCopySubst clause allBinding
      let fresh := copiedResidualNameSuffix copy suffix
      let copied := renameAtomSuffix suffix (Metta.Subst.apply copy value)
      let tailBinding :=
        specializationGuardBindingSuffix clause allBinding suffix tail
      have hentryAll : (name, value) ∈ allBinding :=
        hremaining name value (by simp)
      have hsource : ∀ source, source ∈ value.vars →
          source ∈ specializationResiduals allBinding := by
        intro source hsource
        exact sourceBinding_value_var_mem_residuals allBinding name value
          hentryAll source hsource
      have variant : FreshVariant fresh (subst base copied) value := by
        exact specializationCopy_current_freshVariant clause allBinding name
          value hentryAll suffix base topological residualState
          (hreflexive name value hentryAll) hdisjoint
      have hformal : subst base (Atom.var (name ++ suffix)) = value :=
        headState name value (by simp)
      have hqueryFreshValue : ∀ source, source ∈ value.vars →
          ∀ visible, visible ∈ (subst base qterm).vars →
            fresh source ≠ visible := by
        intro source hsourceValue visible hvisible
        exact hqueryFresh source (hsource source hsourceValue) visible hvisible
      obtain ⟨next, witness, nextTopological, hresult, hwitness,
          hquery, nextResidualState⟩ :=
        freshVariant_guard_exact_evidence_state fresh
          (specializationResiduals allBinding) copied value base qterm
          (Atom.var (name ++ suffix)) topological residualState variant
          hinjective hdisjoint hsource hqueryFreshValue hformal
      let goals := specializationGuards tailBinding ++ rest
      let trimmed := PLeaTTa.trimFor goals qterm next
      have trimmedTopological : SubstTopological trimmed := by
        exact SubstTopological.trimFor goals qterm next nextTopological
      have trimmedResidualState : FreshResidualLookupState fresh
          (specializationResiduals allBinding) trimmed := by
        exact nextResidualState.trimFor fresh
          (specializationResiduals allBinding) next goals qterm
      have htrimQuery : subst trimmed qterm = subst next qterm := by
        apply subst_trimFor_eq_of_topological goals qterm next
          nextTopological qterm
        intro source hsourceQterm
        exact isTrimRoot_qterm_mem goals qterm source hsourceQterm
      have htrimQueryBase : subst trimmed qterm = subst base qterm :=
        htrimQuery.trans hquery
      have trimmedHeadState : SourceBindingHeadState suffix tail trimmed := by
        intro tailName tailValue htailEntry
        have htailAll : (tailName, tailValue) ∈ allBinding :=
          hremaining tailName tailValue (by simp [htailEntry])
        have hbaseFormal :
            subst base (Atom.var (tailName ++ suffix)) = tailValue :=
          headState tailName tailValue (by simp [htailEntry])
        have hnextValue : subst next tailValue = tailValue := by
          apply nextResidualState.source_atom_fixed tailValue
          intro source hsourceValue
          exact sourceBinding_value_var_mem_residuals allBinding tailName
            tailValue htailAll source hsourceValue
        have hnextFormal :
            subst next (Atom.var (tailName ++ suffix)) = tailValue := by
          calc
            subst next (Atom.var (tailName ++ suffix)) =
                subst next (subst base (Atom.var (tailName ++ suffix))) :=
              (unifyB_absorbs_base base copied (Atom.var (name ++ suffix))
                next topological hresult
                (Atom.var (tailName ++ suffix))).symm
            _ = subst next tailValue := congrArg (subst next) hbaseFormal
            _ = tailValue := hnextValue
        have htailExecutable :
            (tailName ++ suffix,
              renameAtomSuffix suffix (Metta.Subst.apply copy tailValue)) ∈
              tailBinding := by
          unfold tailBinding specializationGuardBindingSuffix
          rw [List.mem_map]
          exact ⟨(tailName, tailValue), htailEntry, rfl⟩
        have hguard : Goal.eq
              (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
              (Atom.var (tailName ++ suffix)) ∈ goals := by
          apply List.mem_append_left rest
          exact specializationGuards_mem_of_binding_mem tailBinding
            (tailName ++ suffix)
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            htailExecutable
        have htrimFormal :
            subst trimmed (Atom.var (tailName ++ suffix)) =
              subst next (Atom.var (tailName ++ suffix)) := by
          apply subst_trimFor_eq_of_topological goals qterm next
            nextTopological (Atom.var (tailName ++ suffix))
          intro source hsourceFormal
          simp only [Atom.vars, List.mem_singleton] at hsourceFormal
          subst source
          exact isTrimRoot_eq_right_of_mem goals qterm
            (renameAtomSuffix suffix (Metta.Subst.apply copy tailValue))
            (Atom.var (tailName ++ suffix)) (tailName ++ suffix) hguard
            (by simp [Atom.vars])
        exact htrimFormal.trans hnextFormal
      have htailRemaining : ∀ tailName tailValue,
          (tailName, tailValue) ∈ tail →
            (tailName, tailValue) ∈ allBinding := by
        intro tailName tailValue htailEntry
        exact hremaining tailName tailValue (by simp [htailEntry])
      have htrimQueryFresh : ∀ source,
          source ∈ specializationResiduals allBinding →
          ∀ visible, visible ∈ (subst trimmed qterm).vars →
            fresh source ≠ visible := by
        intro source hsourceAllowed visible hvisible
        rw [htrimQueryBase] at hvisible
        exact hqueryFresh source hsourceAllowed visible hvisible
      obtain ⟨final, tailRun⟩ := ih trimmed htailRemaining
        trimmedTopological trimmedResidualState trimmedHeadState
        htrimQueryFresh
      refine ⟨final, ?_⟩
      exact .cons (name ++ suffix) copied tailBinding base next final witness
        topological hwitness hresult hquery (by simpa [trimmed, goals] using tailRun)

/-- A copied-residual guard using the machine's fixed clause-wide suffix
    succeeds without changing the caller query.  The freshness premises are
    stable across an ordered guard prefix, unlike recomputing a suffix from
    the substitution produced by each preceding guard. -/
theorem specialization_guard_unifyB_succeeds_queryInvisible_fixedSuffix
    (clause : Clause) (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding)
    (suffix : String) (base : Subst) (qterm formalName : Atom)
    (topological : SubstTopological base)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hcopyDisjoint : ∀ left, left ∈ sourceValue.vars →
      ∀ right, right ∈ sourceValue.vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix left ≠ right)
    (hqueryFresh : ∀ source, source ∈ sourceValue.vars →
      ∀ visible, visible ∈ (subst base qterm).vars →
        copiedResidualNameSuffix
          (specializationCopySubst clause binding) suffix source ≠ visible)
    (hcopiedFixed : subst base
      (renameAtomSuffix suffix
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue)) =
      renameAtomSuffix suffix
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue))
    (hformal : subst base formalName = sourceValue) :
    ∃ next,
      unifyB base
        (renameAtomSuffix suffix
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        formalName = some next ∧
      subst next qterm = subst base qterm := by
  let copy := specializationCopySubst clause binding
  let copied := renameAtomSuffix suffix (Metta.Subst.apply copy sourceValue)
  obtain ⟨generated, hgeneratedUnderlying, hgenerated, hdomain⟩ :=
    specializationCopy_unifyTop_succeeds_with_domain clause binding name
      sourceValue hentry suffix hreflexive hcopyDisjoint
  have hunify : unifyTopExact (subst base copied)
      (subst base formalName) = some generated := by
    simpa [copy, copied, hcopiedFixed, hformal] using hgenerated
  have hgeneratedFree : ∀ visible,
      visible ∈ (subst base qterm).vars →
        Metta.Subst.lookup generated visible = none := by
    intro visible hvisible
    apply hdomain.lookup_none_of_forbidden
    intro source hsource
    exact hqueryFresh source hsource visible hvisible
  cases generated with
  | nil =>
      have hresult : unifyB base copied formalName = some base := by
        simp [unifyB, hunify]
      exact ⟨base, by simpa [copy, copied] using hresult, rfl⟩
  | cons generatedHead generatedTail =>
      let generated : Subst := generatedHead :: generatedTail
      let next := Metta.Subst.compose generated base
      have hresult : unifyB base copied formalName = some next := by
        simp [unifyB, hunify, generated, next]
      have hnextFree : ∀ visible,
          visible ∈ (subst base qterm).vars →
            Metta.Subst.lookup next visible = none := by
        intro visible hvisible
        have hbaseNone : Metta.Subst.lookup base visible = none :=
          topological.subst_resolvesDomain base qterm visible hvisible
        have hgeneratedNone : Metta.Subst.lookup generated visible = none := by
          simpa [generated] using hgeneratedFree visible hvisible
        simp [next, lookup_compose, hbaseNone, hgeneratedNone]
      have hfixed : subst next (subst base qterm) = subst base qterm :=
        subst_eq_self_of_domain_free next (subst base qterm) hnextFree
      have habsorbs : subst next (subst base qterm) = subst next qterm :=
        unifyB_absorbs_base base copied formalName next topological hresult qterm
      refine ⟨next, ?_, ?_⟩
      · simpa [copy, copied] using hresult
      · exact habsorbs.symm.trans hfixed

/-- First-guard specialization of the fixed-suffix theorem.  The executable
    resolution suffix discharges both freshness premises from the original
    caller live set. -/
theorem specialization_guard_unifyB_succeeds_queryInvisible
    (clause : Clause) (binding : Subst) (name : String) (sourceValue : Atom)
    (hentry : (name, sourceValue) ∈ binding)
    (argsv : List Atom) (res : Atom) (rest : List Goal) (base : Subst)
    (qterm formalName : Atom) (seed : Nat)
    (hhighWater : resolutionSeedHighWaterNames
      (resolutionOccupiedVars argsv res rest base qterm) ≤ seed)
    (topological : SubstTopological base)
    (hreflexive : Metta.Atom.equiv
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue)
      (Metta.Subst.apply (specializationCopySubst clause binding) sourceValue) =
        true)
    (hoccupied : ∀ source, source ∈ sourceValue.vars →
      source ∈ resolutionOccupiedVars argsv res rest base qterm)
    (hcopiedFixed : subst base
      (renameAtomSuffix
        (resolutionFreshSuffix argsv res rest base qterm seed)
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue)) =
      renameAtomSuffix
        (resolutionFreshSuffix argsv res rest base qterm seed)
        (Metta.Subst.apply (specializationCopySubst clause binding)
          sourceValue))
    (hformal : subst base formalName = sourceValue) :
    ∃ next,
      unifyB base
        (renameAtomSuffix
          (resolutionFreshSuffix argsv res rest base qterm seed)
          (Metta.Subst.apply (specializationCopySubst clause binding)
            sourceValue))
        formalName = some next ∧
      subst next qterm = subst base qterm := by
  apply specialization_guard_unifyB_succeeds_queryInvisible_fixedSuffix
    clause binding name sourceValue hentry
    (resolutionFreshSuffix argsv res rest base qterm seed) base qterm formalName
    topological hreflexive
  · intro left hleft right hright
    obtain ⟨target, htarget⟩ := specializationCopySubst_lookup_var clause
      binding left (sourceBinding_value_var_mem_residuals binding name
        sourceValue hentry left hleft)
    have hfresh : copiedResidualNameSuffix
        (specializationCopySubst clause binding)
        (resolutionFreshSuffix argsv res rest base qterm seed) left =
          target ++ resolutionFreshSuffix argsv res rest base qterm seed := by
      simp [copiedResidualNameSuffix, htarget]
    rw [hfresh]
    exact resolutionFreshSuffix_target_ne argsv res rest base qterm seed
      hhighWater target right (hoccupied right hright)
  · intro source hsource visible hvisible
    obtain ⟨target, htarget⟩ := specializationCopySubst_lookup_var clause
      binding source (sourceBinding_value_var_mem_residuals binding name
        sourceValue hentry source hsource)
    have hfresh : copiedResidualNameSuffix
        (specializationCopySubst clause binding)
        (resolutionFreshSuffix argsv res rest base qterm seed) source =
          target ++ resolutionFreshSuffix argsv res rest base qterm seed := by
      simp [copiedResidualNameSuffix, htarget]
    rw [hfresh]
    exact resolutionFreshSuffix_target_ne argsv res rest base qterm seed
      hhighWater target visible
      (subst_qterm_var_mem_resolutionOccupiedVars argsv res rest base qterm
        visible hvisible)
  · exact hcopiedFixed
  · exact hformal

/-- Parametric open-residual sanity theorem for the critical `copy_term`
    direction.  When the generic head has bound its clause-local formal to a
    caller residual, the guarded copied residual is unified *toward* that
    caller.  The result binds only the fresh residual and leaves the caller
    variable free. -/
theorem open_residual_guard_unify (formal fresh caller : String)
    (hformalFresh : formal ≠ fresh)
    (hformalCaller : formal ≠ caller)
    (hfreshCaller : fresh ≠ caller) :
    let source := Atom.expr [Atom.sym "partial", Atom.var caller]
    let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
    unifyB [(formal, source)] copied (Atom.var formal) =
      some [(formal, source), (fresh, Atom.var caller)] := by
  let source := Atom.expr [Atom.sym "partial", Atom.var caller]
  let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
  let base : Subst := [(formal, source)]
  have hunifyBase : Metta.Unify.unifyTop (Atom.var formal) source =
      some base := by
    simp [source, base, Atom.size, Metta.Unify.unifyTop,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Subst.occurs, Metta.Subst.extend,
      Metta.Subst.erase, hformalCaller]
  have hbaseTopological : SubstTopological base :=
    unifyTop_topological (Atom.var formal) source base hunifyBase
  have hsourceFixed : subst base source = source := by
    apply subst_eq_self_of_domain_free base source
    intro name hname
    simp [source, Atom.vars] at hname
    subst name
    simp [base, Metta.Subst.lookup, Ne.symm hformalCaller]
  have hformalValue : subst base (Atom.var formal) = source := by
    exact (hbaseTopological.subst_var_of_lookup base formal source
      (by simp [base, Metta.Subst.lookup])).trans hsourceFixed
  have hcopiedFixed : subst base copied = copied := by
    apply subst_eq_self_of_domain_free base copied
    intro name hname
    simp [copied, Atom.vars] at hname
    subst name
    simp [base, Metta.Subst.lookup, Ne.symm hformalFresh]
  let generated : Subst := [(fresh, Atom.var caller)]
  have hgenerated :
      Metta.Unify.unifyTopWith prologGroundIdentical copied source =
        some generated := by
    simp [copied, source, generated, Atom.size, Metta.Unify.unifyTopWith,
      Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
      Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase,
      hfreshCaller]
  have hgeneratedTopological : SubstTopological generated :=
    unifyTopWith_topological prologGroundIdentical copied source generated
      hgenerated
  have hfreshLookup : Metta.Subst.lookup generated fresh =
      some (Atom.var caller) := by
    simp [generated, Metta.Subst.lookup]
  have hvariableExact : subst generated (Atom.var fresh) =
      subst generated (Atom.var caller) :=
    hgeneratedTopological.subst_var_of_lookup generated fresh
      (Atom.var caller) hfreshLookup
  have hgeneratedExact : subst generated copied = subst generated source := by
    calc
      subst generated copied =
          Atom.expr [Atom.sym "partial", subst generated (Atom.var fresh)] := by
        simp [copied]
      _ = Atom.expr
          [Atom.sym "partial", subst generated (Atom.var caller)] := by
        rw [hvariableExact]
      _ = subst generated source := by simp [source]
  have hwrapped : unifyTopExact copied source = some generated :=
    unifyTopExact_of_underlying_exact copied source generated hgenerated
      hgeneratedExact
  change unifyB base copied (Atom.var formal) =
    some [(formal, source), (fresh, Atom.var caller)]
  unfold unifyB
  rw [hcopiedFixed, hformalValue, hwrapped]
  simp [generated, source, base, Metta.Subst.apply,
    Metta.Subst.compose, Metta.Subst.lookup,
    Ne.symm hfreshCaller]

/-- The parametric open-residual guard supplies exactly the evidence consumed
    by `ExactBindingGuardsRun`: a successful concrete result, a propositional
    unifier witness, and preservation of the caller residual itself. -/
theorem open_residual_guard_exact_evidence (formal fresh caller : String)
    (hformalFresh : formal ≠ fresh)
    (hformalCaller : formal ≠ caller)
    (hfreshCaller : fresh ≠ caller) :
    let source := Atom.expr [Atom.sym "partial", Atom.var caller]
    let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
    let base : Subst := [(formal, source)]
    let next : Subst := [(formal, source), (fresh, Atom.var caller)]
    let witness : Subst := [(fresh, Atom.var caller)]
    unifyB base copied (Atom.var formal) = some next ∧
      subst witness (subst base copied) =
        subst witness (subst base (Atom.var formal)) ∧
      subst next (Atom.var caller) = subst base (Atom.var caller) := by
  let source := Atom.expr [Atom.sym "partial", Atom.var caller]
  let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
  let base : Subst := [(formal, source)]
  let next : Subst := [(formal, source), (fresh, Atom.var caller)]
  let witness : Subst := [(fresh, Atom.var caller)]
  have hresult : unifyB base copied (Atom.var formal) = some next := by
    simpa [source, copied, base, next] using
      open_residual_guard_unify formal fresh caller hformalFresh
        hformalCaller hfreshCaller
  have hunifyBase : Metta.Unify.unifyTop (Atom.var formal) source =
      some base := by
    simp [source, base, Atom.size, Metta.Unify.unifyTop,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Subst.occurs, Metta.Subst.extend,
      Metta.Subst.erase, hformalCaller]
  have hbaseTopological : SubstTopological base :=
    unifyTop_topological (Atom.var formal) source base hunifyBase
  have hsourceFixed : subst base source = source := by
    apply subst_eq_self_of_domain_free base source
    intro name hname
    simp [source, Atom.vars] at hname
    subst name
    simp [base, Metta.Subst.lookup, Ne.symm hformalCaller]
  have hformalValue : subst base (Atom.var formal) = source := by
    exact (hbaseTopological.subst_var_of_lookup base formal source
      (by simp [base, Metta.Subst.lookup])).trans hsourceFixed
  have hcopiedFixed : subst base copied = copied := by
    apply subst_eq_self_of_domain_free base copied
    intro name hname
    simp [copied, Atom.vars] at hname
    subst name
    simp [base, Metta.Subst.lookup, Ne.symm hformalFresh]
  have hwitnessSource : subst witness source = source := by
    apply subst_eq_self_of_domain_free witness source
    intro name hname
    simp [source, Atom.vars] at hname
    subst name
    simp [witness, Metta.Subst.lookup, Ne.symm hfreshCaller]
  have hwitnessCopied : subst witness copied = source := by
    have hwitnessTopological : SubstTopological witness := by
      have hunify : Metta.Unify.unifyTop (Atom.var fresh)
          (Atom.var caller) = some witness := by
        simp [witness, Atom.size, Metta.Unify.unifyTop,
          Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
          Metta.Unify.decomposeEq, Metta.Subst.occurs,
          Metta.Subst.extend, Metta.Subst.erase, hfreshCaller]
      exact unifyTop_topological (Atom.var fresh) (Atom.var caller)
        witness hunify
    change subst witness
      (Atom.expr [Atom.sym "partial", Atom.var fresh]) = source
    rw [subst_expr]
    have hfreshValue := hwitnessTopological.subst_var_of_lookup witness fresh
      (Atom.var caller) (by simp [witness, Metta.Subst.lookup])
    have hcallerWitness : subst witness (Atom.var caller) =
        Atom.var caller := by
      apply subst_var_of_lookup_none
      simp [witness, Metta.Subst.lookup, Ne.symm hfreshCaller]
    simp [source, hfreshValue, hcallerWitness]
  have hcallerBase : subst base (Atom.var caller) = Atom.var caller := by
    apply subst_var_of_lookup_none
    simp [base, Metta.Subst.lookup, Ne.symm hformalCaller]
  have hcallerNext : subst next (Atom.var caller) = Atom.var caller := by
    apply subst_var_of_lookup_none
    simp [next, Metta.Subst.lookup, Ne.symm hformalCaller,
      Ne.symm hfreshCaller]
  refine ⟨hresult, ?_, ?_⟩
  · rw [hcopiedFixed, hformalValue, hwitnessCopied, hwitnessSource]
  · rw [hcallerNext, hcallerBase]

/-- The one-open-residual base case constructs the complete executable guard
    trace for an arbitrary continuation.  This is the first non-closed case:
    the guard genuinely adds `fresh ↦ caller`, preserves the caller query,
    and then performs the machine's real continuation-sensitive trim. -/
theorem open_residual_exact_guard_run (formal fresh caller : String)
    (rest : List Goal)
    (hformalFresh : formal ≠ fresh)
    (hformalCaller : formal ≠ caller)
    (hfreshCaller : fresh ≠ caller) :
    let source := Atom.expr [Atom.sym "partial", Atom.var caller]
    let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
    let base : Subst := [(formal, source)]
    let next : Subst := [(formal, source), (fresh, Atom.var caller)]
    ExactBindingGuardsRun (Atom.var caller) rest [(formal, copied)] base
      (trimFor rest (Atom.var caller) next) := by
  let source := Atom.expr [Atom.sym "partial", Atom.var caller]
  let copied := Atom.expr [Atom.sym "partial", Atom.var fresh]
  let base : Subst := [(formal, source)]
  let next : Subst := [(formal, source), (fresh, Atom.var caller)]
  let witness : Subst := [(fresh, Atom.var caller)]
  obtain ⟨hresult, hwitness, hquery⟩ :=
    open_residual_guard_exact_evidence formal fresh caller hformalFresh
      hformalCaller hfreshCaller
  have hunifyBase : Metta.Unify.unifyTop (Atom.var formal) source =
      some base := by
    simp [source, base, Atom.size, Metta.Unify.unifyTop,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Subst.occurs, Metta.Subst.extend,
      Metta.Subst.erase, hformalCaller]
  have hbaseTopological : SubstTopological base :=
    unifyTop_topological (Atom.var formal) source base hunifyBase
  have hnextTopological : SubstTopological next :=
    unifyB_topological base copied (Atom.var formal) next
      hbaseTopological hresult
  have htrimTopological :
      SubstTopological (trimFor rest (Atom.var caller) next) := by
    exact SubstTopological.trimFor rest (Atom.var caller) next
      hnextTopological
  exact .cons formal copied [] base next
    (trimFor rest (Atom.var caller) next) witness hbaseTopological hwitness
      hresult hquery (.nil _ htrimTopological)

/-- Reachable topological substitutions are genuine semantic fixpoints, not
    merely stable at larger fuel bounds. -/
theorem subst_idempotent_of_topological (b : Subst)
    (topological : SubstTopological b) (atom : Atom) :
    subst b (subst b atom) = subst b atom := by
  apply subst_eq_self_of_domain_free b (subst b atom)
  intro name hname
  exact SubstTopological.subst_resolvesDomain b topological atom name hname

theorem map_subst_idempotent_of_topological (b : Subst)
    (topological : SubstTopological b) (atoms : List Atom) :
    (atoms.map (subst b)).map (subst b) = atoms.map (subst b) := by
  rw [List.map_map, List.map_congr_left]
  intro atom _
  exact subst_idempotent_of_topological b topological atom

theorem partialBoundArgs_denote_same (b : Subst)
    (topological : SubstTopological b) (bound args : List Atom) :
    ((bound.map (subst b)) ++ args).map (subst b) =
      (bound ++ args).map (subst b) := by
  simp only [List.map_append]
  rw [map_subst_idempotent_of_topological b topological bound]

/-- Actual clause resolution for the runtime-substituted and source-form
    partial prefixes preserves exact branch order/multiplicity/counters.  In
    every paired branch, the only raw difference is the first equality, whose
    two `unifyB` calls are equal by `ResolvedArgsAltRel.unify_eq`. -/
theorem resolveAlts_openPartial_related (clauses : List Clause)
    (bound args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (qterm : Atom) (topological : SubstTopological b) (bc counter : Nat) :
    let runtimeArgs := (bound.map (subst b)) ++ args
    let sourceArgs := bound ++ args
    let left := resolveAlts clauses (runtimeArgs.map (subst b)) runtimeArgs
      res rest b qterm bc counter
    let right := resolveAlts clauses (sourceArgs.map (subst b)) sourceArgs
      res rest b qterm bc counter
    left.2 = right.2 ∧
      SpecListRel (ResolvedArgsAltRel runtimeArgs sourceArgs res rest b)
        left.1 right.1 := by
  let runtimeArgs := (bound.map (subst b)) ++ args
  let sourceArgs := bound ++ args
  have hargs : runtimeArgs.map (subst b) = sourceArgs.map (subst b) := by
    exact partialBoundArgs_denote_same b topological bound args
  simpa [runtimeArgs, sourceArgs, hargs] using
    resolveAlts_rawArgs_related clauses (sourceArgs.map (subst b))
      runtimeArgs sourceArgs res rest b qterm bc counter

/-- Both sides take the real `call_resolve` transition.  Their resulting
    alternatives are paired position-for-position and share the exact fresh
    counter; no set or permutation quotient hides multiplicity/order. -/
theorem openPartial_call_resolution_steps_related (prog : Prog)
    (gt : GroundingTable) (c : Conf) (base : String)
    (bound args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (topological : SubstTopological b)
    (hne : c.world.clauseHeadCandidates base ≠ [])
    (ha : (c.world.resolutionCandidates base (bound ++ args).length).any
      (fun clause => clause.params.length == (bound ++ args).length)) :
    let runtimeArgs := (bound.map (subst b)) ++ args
    let sourceArgs := bound ++ args
    let leftConf : Conf :=
      { c with cur := some (Goal.call base runtimeArgs res :: rest, b) }
    let rightConf : Conf :=
      { c with cur := some (Goal.call base sourceArgs res :: rest, b) }
    let left := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (runtimeArgs.map (subst b)) runtimeArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    let right := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (sourceArgs.map (subst b)) sourceArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    left.2 = right.2 ∧
      SpecListRel (ResolvedArgsAltRel runtimeArgs sourceArgs res rest b)
        left.1 right.1 ∧
      Step prog gt leftConf
        (pull { c with
          cur := none
          counter := left.2
          alts := left.1 ++ (Alt.barrier :: c.alts)
          barriers := pushBarrierCache c.barriers }) ∧
      Step prog gt rightConf
        (pull { c with
          cur := none
          counter := right.2
          alts := right.1 ++ (Alt.barrier :: c.alts)
          barriers := pushBarrierCache c.barriers }) := by
  let runtimeArgs := (bound.map (subst b)) ++ args
  let sourceArgs := bound ++ args
  let leftConf : Conf :=
    { c with cur := some (Goal.call base runtimeArgs res :: rest, b) }
  let rightConf : Conf :=
    { c with cur := some (Goal.call base sourceArgs res :: rest, b) }
  let left := resolveAlts
    (c.world.resolutionCandidates base (bound ++ args).length)
    (runtimeArgs.map (subst b)) runtimeArgs res rest b
    c.qterm (barrierDepth c + 1) c.counter
  let right := resolveAlts
    (c.world.resolutionCandidates base (bound ++ args).length)
    (sourceArgs.map (subst b)) sourceArgs res rest b
    c.qterm (barrierDepth c + 1) c.counter
  have hrelated := resolveAlts_openPartial_related
    (c.world.resolutionCandidates base (bound ++ args).length)
    bound args res rest b c.qterm topological
    (barrierDepth c + 1) c.counter
  have hleft : resolveAlts
      (leftConf.world.resolutionCandidates base runtimeArgs.length)
      (runtimeArgs.map (subst b)) runtimeArgs res rest b
      leftConf.qterm (barrierDepth leftConf + 1) leftConf.counter = left := by
    simp [leftConf, runtimeArgs, left, barrierDepth]
  have hright : resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (sourceArgs.map (subst b)) sourceArgs res rest b
      rightConf.qterm (barrierDepth rightConf + 1) rightConf.counter = right := by
    rfl
  have haRuntime :
      (c.world.resolutionCandidates base runtimeArgs.length).any
      (fun clause => clause.params.length == runtimeArgs.length) := by
    simpa [runtimeArgs, sourceArgs] using ha
  refine ⟨hrelated.1, hrelated.2, ?_, ?_⟩
  · simpa [leftConf, left, runtimeArgs] using
      (Step.call_resolve (prog := prog) (gt := gt) leftConf base runtimeArgs
        res rest b left.1 left.2 rfl hne haRuntime hleft)
  · simpa [rightConf, right, sourceArgs] using
      (Step.call_resolve (prog := prog) (gt := gt) rightConf base sourceArgs
        res rest b right.1 right.2 rfl hne ha hright)

theorem callDyn_partial_steps_to_redispatch (prog : Prog) (gt : GroundingTable)
    (c : Conf) (head : Atom) (base : String) (boundList : Atom)
    (bound args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hns : ∀ f, subst b head ≠ Atom.sym f)
    (hp : partialView? (subst b head) = some (base, boundList))
    (hbound : bound = (chainListM boundList).getD []) :
    Step prog gt c
      { c with cur := some (
          Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) } := by
  exact Step.callDyn_partial c head args res rest b base boundList bound
    hcur hns hp hbound _ rfl

theorem runClean_callDyn_partial_eq_redispatch (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (c : Conf) (head : Atom)
    (base : String) (boundList : Atom) (bound args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hns : ∀ f, subst b head ≠ Atom.sym f)
    (hp : partialView? (subst b head) = some (base, boundList))
    (hbound : bound = (chainListM boundList).getD []) :
    runClean prog gt (fuel + 2) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (
            Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) }
          none := by
  have hterminal : c.isTerminalB = false := by
    simp [Conf.isTerminalB, hcur]
  have hstep : step prog gt fuel c =
      { c with cur := some (
          Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) } := by
    unfold step
    rw [hcur]
    simp [hp, hbound]
  have hclean : stepClean prog gt (fuel + 1) c =
      .progressed
        { c with cur := some (
            Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) } := by
    simp [stepClean, hcur, hstep]
  simp [runClean, hterminal, Conf.limitReachedB, hclean]

/-- The two generic dispatch steps for a partial-defined function converge
    to the same direct goal as profile lowering, with exact ordered execution
    thereafter.  Recursion is harmless here: the theorem is fuel-parametric
    and assumes no correctness fact about `base`. -/
theorem runClean_callDyn_partial_defined_eq_direct (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (c : Conf) (head : Atom)
    (base : String) (boundList : Atom) (bound args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hns : ∀ f, subst b head ≠ Atom.sym f)
    (hp : partialView? (subst b head) = some (base, boundList))
    (hbound : bound = (chainListM boundList).getD [])
    (hdefined : c.world.clauseHeadCandidates base ≠ []) :
    runClean prog gt (fuel + 3) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (
            Goal.call base (bound ++ args) res :: rest, b) } none := by
  let redispatched : Conf :=
    { c with cur := some (
        Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) }
  calc
    runClean prog gt (fuel + 3) c none =
        runClean prog gt (fuel + 2) redispatched none := by
          simpa [redispatched, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using runClean_callDyn_partial_eq_redispatch prog gt (fuel + 1)
              c head base boundList bound args res rest b hcur hns hp hbound
    _ = runClean prog gt (fuel + 1)
          { c with cur := some (
              Goal.call base (bound ++ args) res :: rest, b) } none := by
        simpa [redispatched, subst] using
          runClean_callDyn_defined_eq_direct prog gt fuel redispatched
            (Atom.sym base) base (bound ++ args) res rest b rfl (by simp)
              hdefined

/-- Builtin partials obey the same two-step convergence equation. -/
theorem runClean_callDyn_partial_builtin_eq_direct (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (c : Conf) (head : Atom)
    (base : String) (boundList : Atom) (bound args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, b))
    (hns : ∀ f, subst b head ≠ Atom.sym f)
    (hp : partialView? (subst b head) = some (base, boundList))
    (hbound : bound = (chainListM boundList).getD [])
    (hundefined : c.world.clauseHeadCandidates base = [])
    (hbuiltin : (GroundingTable.lookup gt base).isSome) :
    runClean prog gt (fuel + 3) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (
            Goal.bin base (bound ++ args) res :: rest, b) } none := by
  let redispatched : Conf :=
    { c with cur := some (
        Goal.callDyn (Atom.sym base) (bound ++ args) res :: rest, b) }
  calc
    runClean prog gt (fuel + 3) c none =
        runClean prog gt (fuel + 2) redispatched none := by
          simpa [redispatched, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using runClean_callDyn_partial_eq_redispatch prog gt (fuel + 1)
              c head base boundList bound args res rest b hcur hns hp hbound
    _ = runClean prog gt (fuel + 1)
          { c with cur := some (
              Goal.bin base (bound ++ args) res :: rest, b) } none := by
        simpa [redispatched, subst] using
          runClean_callDyn_builtin_eq_direct prog gt fuel redispatched
            (Atom.sym base) base (bound ++ args) res rest b rfl (by simp)
              hundefined hbuiltin

/-- The actual partial-function lowering first converges to a generic direct
    call whose bound prefix has been substituted at runtime.  The following
    `partialBoundArgs_denote_same` theorem relates that prefix to the source
    prefix retained by the specialized IR, including open partial values. -/
theorem runClean_denoted_callDyn_partial_defined_eq_runtimeDirect
    (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
    (runtime binding : Subst) (head : Atom) (base : String)
    (bound args : List Atom) (res : Atom) (rest : List Goal)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, runtime))
    (hdenotes : SubstDenotesBinding runtime binding)
    (hview : partialHeadView? (Metta.Subst.apply binding head) =
      some (base, bound))
    (hdefined : c.world.clauseHeadCandidates base ≠ []) :
    runClean prog gt (fuel + 3) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (Goal.call base
            ((bound.map (subst runtime)) ++ args) res :: rest, runtime) }
        none := by
  have hshape := subst_denoted_partialHeadView runtime binding head base bound
    hdenotes hview
  have hnotSymbol : ∀ f, subst runtime head ≠ Atom.sym f := by
    intro f
    rw [hshape]
    simp [partialC, chainOf]
  have hpartial := partialView?_subst_denoted_partialHeadView runtime binding
    head base bound hdenotes hview
  have hbound : bound.map (subst runtime) =
      (chainListM (chainOf (bound.map (subst runtime)))).getD [] := by
    simp
  exact runClean_callDyn_partial_defined_eq_direct prog gt fuel c head base
    (chainOf (bound.map (subst runtime))) (bound.map (subst runtime)) args res
    rest runtime hcur hnotSymbol hpartial hbound hdefined

theorem runClean_denoted_callDyn_partial_builtin_eq_runtimeDirect
    (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
    (runtime binding : Subst) (head : Atom) (base : String)
    (bound args : List Atom) (res : Atom) (rest : List Goal)
    (hcur : c.cur = some (Goal.callDyn head args res :: rest, runtime))
    (hdenotes : SubstDenotesBinding runtime binding)
    (hview : partialHeadView? (Metta.Subst.apply binding head) =
      some (base, bound))
    (hundefined : c.world.clauseHeadCandidates base = [])
    (hbuiltin : (GroundingTable.lookup gt base).isSome) :
    runClean prog gt (fuel + 3) c none =
      runClean prog gt (fuel + 1)
        { c with cur := some (Goal.bin base
            ((bound.map (subst runtime)) ++ args) res :: rest, runtime) }
        none := by
  have hshape := subst_denoted_partialHeadView runtime binding head base bound
    hdenotes hview
  have hnotSymbol : ∀ f, subst runtime head ≠ Atom.sym f := by
    intro f
    rw [hshape]
    simp [partialC, chainOf]
  have hpartial := partialView?_subst_denoted_partialHeadView runtime binding
    head base bound hdenotes hview
  have hbound : bound.map (subst runtime) =
      (chainListM (chainOf (bound.map (subst runtime)))).getD [] := by
    simp
  exact runClean_callDyn_partial_builtin_eq_direct prog gt fuel c head base
    (chainOf (bound.map (subst runtime))) (bound.map (subst runtime)) args res
    rest runtime hcur hnotSymbol hpartial hbound hundefined hbuiltin

/-! ## Executable base-case witness over the actual clause rewrite -/

private structure WorldObservation where
  answers : List Atom
  selfAtoms : List Atom
  spaceAtoms : List (Atom × List Atom)
  store : List (Atom × Atom)
  nextId : Nat
  progClauses : List (String × Clause)
  knownHeads : List String
  knownArities : List (String × Nat)
  tabledArities : List (String × Nat)
  tableActive : List Atom
  tableCache : List (Atom × List Atom)
  typeDecls : List (Atom × Atom)
deriving BEq

private def observeRun (outcome : RunOutcome) : WorldObservation :=
  let c := runOutcomeConf outcome
  { answers := c.answers
    selfAtoms := c.world.selfAtoms
    spaceAtoms := c.world.spaceAtoms
    store := c.world.store
    nextId := c.world.nextId
    progClauses := c.world.progClauses
    knownHeads := c.world.knownHeads
    knownArities := c.world.knownArities
    tabledArities := c.world.tabledArities
    tableActive := c.world.tableActive
    tableCache := c.world.tableCache
    typeDecls := c.world.typeDecls }

private def baseParentClause : Clause :=
  { params := [Atom.var "hof", Atom.var "x"]
    result := Atom.var "result"
    body := [Goal.callDyn (Atom.var "hof") [Atom.var "x"]
      (Atom.var "result")] }

private def baseSpecializedClause : Clause :=
  specializeClauseGuarded (fun name => name == "g") (fun _ => false)
    [("hof", Atom.sym "g")] baseParentClause

private def baseTargetClause (answer : Int) (marker : String) : Clause :=
  { params := [Atom.var "targetArg"]
    result := Atom.gnd (.int answer)
    body := [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult")] }

private def baseWorld : PWorld :=
  { progClauses :=
      [("f", baseParentClause),
       ("f_Spec_[g]", baseSpecializedClause),
       ("g", baseTargetClause 1 "first-effect"),
       ("g", baseTargetClause 2 "second-effect")]
    knownHeads := ["f", "f_Spec_[g]", "g"]
    knownArities := [("f", 2), ("f_Spec_[g]", 2), ("g", 1)] }

private def baseConf (head : String) : Conf :=
  { cur := some
      ([Goal.call head [Atom.sym "g", Atom.sym "input"] (Atom.var "answer")], [])
    alts := []
    world := baseWorld
    counter := 10
    qterm := Atom.var "answer" }

private def baseProg : Prog :=
  { clauses := [], facts := [], typeDecls := [] }

-- Executable check over the actual guarded-head rewrite.  The two target
-- clauses deliberately produce two ordered answers and two persistent
-- effects; comparing every world field catches set-based, reordered, or
-- effect-erasing simulations.  The parametric theorem above remains the
-- proof boundary; this check is its effectful/nondeterministic regression.
#guard observeRun (runClean baseProg [] 100 (baseConf "f") none) ==
  observeRun (runClean baseProg [] 100 (baseConf "f_Spec_[g]") none)

private def finiteTargetClause (answer marker : String) : Clause :=
  { params := [Atom.var "targetArg"]
    result := Atom.sym answer
    body := [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult")] }

private def finiteSpecializedClause (g : String) : Clause :=
  specializeClauseGuarded (fun name => name == g) (fun _ => false)
    [("hof", Atom.sym g)] baseParentClause

private theorem finiteSpecializedClause_eq (g : String) :
    finiteSpecializedClause g =
      { params := [Atom.var "hof", Atom.var "x"]
        result := Atom.var "result"
        body := [Goal.eq (Atom.sym g) (Atom.var "hof"),
          Goal.call g [Atom.var "x"] (Atom.var "result")] } := by
  simp [finiteSpecializedClause, specializeClauseGuarded,
    specializationGuards, baseParentClause, specializeCallableHeadGoals,
    specializeCallableHeadGoal, Metta.Subst.apply, Metta.Subst.lookup]

private def finiteWorld (g answer marker : String) : PWorld :=
  { progClauses :=
      [("f", baseParentClause),
       ("f_Spec", finiteSpecializedClause g),
       (g, finiteTargetClause answer marker)]
    knownHeads := ["f", "f_Spec", g]
    knownArities := [("f", 2), ("f_Spec", 2), (g, 1)] }

@[simp] private theorem finiteWorld_clauseIndexReady
    (g answer marker : String) :
    (finiteWorld g answer marker).clauseIndexReady = false := rfl

private def finiteConf (g input answer marker head : String) : Conf :=
  { cur := some
      ([Goal.call head [Atom.sym g, Atom.sym input] (Atom.var "answer")], [])
    alts := []
    world := finiteWorld g answer marker
    counter := 10
    qterm := Atom.var "answer" }

private def advance : Nat → Conf → Conf
  | 0, c => c
  | n + 1, c => advance n (step baseProg [] 100 c)

private def genericParentGoals (g input : String) : List Goal :=
  [Goal.eq
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10", Atom.var "result#r10"]),
   Goal.callDyn (Atom.var "hof#r10") [Atom.var "x#r10"] (Atom.var "result#r10")]

private def specializedParentGoals (g input : String) : List Goal :=
  [Goal.eq
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10", Atom.var "result#r10"]),
   Goal.eq (Atom.sym g) (Atom.var "hof#r10"),
   Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]

private def genericParentSubst (g input : String) : Subst :=
  [("answer", Atom.var "result#r10"),
   ("x#r10", Atom.sym input),
   ("hof#r10", Atom.sym g)]

private def specializedParentSubst (input : String) : Subst :=
  [("answer", Atom.var "result#r10"), ("x#r10", Atom.sym input)]

private def prefixConf (g answer marker : String) (goals : List Goal)
    (b : Subst) (alts : List Alt) (counter : Nat) : Conf :=
  { cur := some (goals, b)
    alts := alts
    world := finiteWorld g answer marker
    counter := counter
    qterm := Atom.var "answer" }

private def genericAfterParentResolution (g input answer marker : String) : Conf :=
  prefixConf g answer marker (genericParentGoals g input) [] [.barrier] 11

private def specializedAfterParentResolution (g input answer marker : String) : Conf :=
  prefixConf g answer marker (specializedParentGoals g input) [] [.barrier] 11

private def genericAfterParentBinding (g input answer marker : String) : Conf :=
  prefixConf g answer marker
    [Goal.callDyn (Atom.var "hof#r10") [Atom.var "x#r10"]
      (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private def specializedAfterParentBinding (g input answer marker : String) : Conf :=
  prefixConf g answer marker
    [Goal.eq (Atom.sym g) (Atom.var "hof#r10"),
     Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private def specializedAfterGuard (g input answer marker : String) : Conf :=
  prefixConf g answer marker
    [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (specializedParentSubst input) [.barrier] 11

private theorem generic_parent_resolution (g input answer marker : String)
    (hgf : g ≠ "f") :
    step baseProg [] 100 (finiteConf g input answer marker "f") =
      genericAfterParentResolution g input answer marker := by
  simp [finiteConf, finiteWorld, genericAfterParentResolution, prefixConf,
    genericParentGoals, baseParentClause, finiteSpecializedClause_eq, step,
    PWorld.clausesOf, PWorld.canTableCall, PWorld.isTabled,
    resolveAlts, prologMatchCompatList, prologMatchCompat,
    freshenResolutionClause, resolutionFreshSuffix,
    renameAtomSuffix, renameGoalSuffix, Atom.vars, hgf]
  rw [pull_of_alts_branch (h := rfl)]
  simp [finiteTargetClause]
  decide

private theorem generic_parent_unify (g input : String) :
    unifyB []
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10", Atom.var "result#r10"]) =
        some (genericParentSubst g input) := by
  let generated := genericParentSubst g input
  have hgenerated : Metta.Unify.unifyTopWith prologGroundIdentical
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10",
        Atom.var "result#r10"]) = some generated := by
    simp [generated, genericParentSubst, Atom.size,
      Metta.Unify.unifyTopWith, Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith,
      Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase,
      Metta.Subst.apply, Metta.Subst.lookup]
  have htopological : SubstTopological generated :=
    unifyTopWith_topological prologGroundIdentical
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10",
        Atom.var "result#r10"])
      generated hgenerated
  have hanswerLookup : Metta.Subst.lookup generated "answer" =
      some (Atom.var "result#r10") := by
    simp [generated, genericParentSubst, Metta.Subst.lookup]
  have hanswerExact : subst generated (Atom.var "answer") =
      subst generated (Atom.var "result#r10") :=
    htopological.subst_var_of_lookup generated "answer"
      (Atom.var "result#r10") hanswerLookup
  have hgeneratedExact :
      subst generated
          (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"]) =
        subst generated
          (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10",
            Atom.var "result#r10"]) := by
    calc
      subst generated
          (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"]) =
          Atom.expr [Atom.sym g, Atom.sym input,
            subst generated (Atom.var "answer")] := by simp
      _ = Atom.expr [Atom.sym g, Atom.sym input,
            subst generated (Atom.var "result#r10")] := by rw [hanswerExact]
      _ = subst generated
          (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10",
            Atom.var "result#r10"]) := by
        simp [generated, genericParentSubst, Metta.Subst.lookup]
  have hwrapped : unifyTopExact
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10",
        Atom.var "result#r10"]) = some generated :=
    unifyTopExact_of_underlying_exact _ _ generated hgenerated hgeneratedExact
  simp [unifyB, hwrapped, generated, genericParentSubst,
    Metta.Subst.compose]

private theorem specialized_parent_unify (g input : String) :
    unifyB []
      (Atom.expr [Atom.sym g, Atom.sym input, Atom.var "answer"])
      (Atom.expr [Atom.var "hof#r10", Atom.var "x#r10", Atom.var "result#r10"]) =
        some (genericParentSubst g input) := by
  exact generic_parent_unify g input

private theorem generic_parent_trim (g input : String) :
    trimFor
      [Goal.callDyn (Atom.var "hof#r10") [Atom.var "x#r10"]
        (Atom.var "result#r10")]
      (Atom.var "answer") (genericParentSubst g input) =
        genericParentSubst g input := by
  apply trimFor_eq_self_of_root_keys
  · intro x a hmem
    simp only [genericParentSubst, List.mem_cons] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals try contradiction
    all_goals
      have hx := congrArg Prod.fst hmem
      simp at hx
      subst x
      simp
  · simp [genericParentSubst]

private theorem specialized_parent_trim (g input : String) :
    trimFor
      [Goal.eq (Atom.sym g) (Atom.var "hof#r10"),
       Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
      (Atom.var "answer") (genericParentSubst g input) =
        genericParentSubst g input := by
  apply trimFor_eq_self_of_root_keys
  · intro x a hmem
    simp only [genericParentSubst, List.mem_cons] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals try contradiction
    all_goals
      have hx := congrArg Prod.fst hmem
      simp at hx
      subst x
      simp
  · simp [genericParentSubst]

private theorem generic_parent_binding (g input answer marker : String) :
    step baseProg [] 100 (genericAfterParentResolution g input answer marker) =
      genericAfterParentBinding g input answer marker := by
  simp [genericAfterParentResolution, genericAfterParentBinding, prefixConf,
    genericParentGoals, finiteWorld, baseParentClause,
    finiteSpecializedClause_eq, step, generic_parent_unify,
    generic_parent_trim]

private theorem specialized_parent_binding (g input answer marker : String) :
    step baseProg [] 100 (specializedAfterParentResolution g input answer marker) =
      specializedAfterParentBinding g input answer marker := by
  simp [specializedAfterParentResolution, specializedAfterParentBinding,
    prefixConf, specializedParentGoals, finiteWorld, baseParentClause,
    finiteSpecializedClause_eq, step, specialized_parent_unify,
    specialized_parent_trim]

private theorem specialized_guard (g input answer marker : String) :
    step baseProg [] 100 (specializedAfterParentBinding g input answer marker) =
      specializedAfterGuard g input answer marker := by
  simp [specializedAfterParentBinding, specializedAfterGuard, prefixConf,
    specializedParentSubst, genericParentSubst, finiteWorld,
    baseParentClause, finiteSpecializedClause_eq, step, unifyB, unifyTopExact,
    Atom.size,
    Metta.Unify.unifyTopWith, Metta.Unify.unifyRoundsWith,
    Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
    Metta.Subst.lookup, trimFor_specialization_guard_direct]

private def genericAfterDispatch (g input answer marker : String) : Conf :=
  prefixConf g answer marker
    [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private def targetGoals (answer marker : String) : List Goal :=
  [Goal.eq
      (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
      (Atom.expr [Atom.var "targetArg#r11", Atom.sym answer]),
   Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")]

private def genericAfterTargetResolution (g input answer marker : String) : Conf :=
  prefixConf g answer marker (targetGoals answer marker)
    (genericParentSubst g input) [.barrier, .barrier] 12

private def specializedAfterTargetResolution (g input answer marker : String) : Conf :=
  prefixConf g answer marker (targetGoals answer marker)
    (specializedParentSubst input) [.barrier, .barrier] 12

private def commonAfterTargetBinding (g answer marker : String) : Conf :=
  prefixConf g answer marker
    [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")]
    [("answer", Atom.sym answer)] [.barrier, .barrier] 12

private theorem specialized_parent_resolution (g input answer marker : String)
    (hgs : g ≠ "f_Spec") :
    step baseProg [] 100 (finiteConf g input answer marker "f_Spec") =
      specializedAfterParentResolution g input answer marker := by
  simp [finiteConf, finiteWorld, specializedAfterParentResolution, prefixConf,
    specializedParentGoals, baseParentClause, finiteSpecializedClause_eq, step,
    PWorld.clausesOf, PWorld.canTableCall, PWorld.isTabled,
    resolveAlts, prologMatchCompatList, prologMatchCompat,
    freshenResolutionClause, resolutionFreshSuffix,
    renameAtomSuffix, renameGoalSuffix, Atom.vars, hgs]
  rw [pull_of_alts_branch (h := rfl)]
  simp [finiteTargetClause]
  decide

private theorem generic_dispatch (g input answer marker : String) :
    step baseProg [] 100 (genericAfterParentBinding g input answer marker) =
      genericAfterDispatch g input answer marker := by
  simp [genericAfterParentBinding, genericAfterDispatch, prefixConf,
    genericParentSubst, finiteWorld, baseParentClause,
    finiteSpecializedClause_eq, step, PWorld.clausesOf,
    Metta.Subst.lookup]

private theorem generic_target_resolution (g input answer marker : String)
    (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    step baseProg [] 100 (genericAfterDispatch g input answer marker) =
      genericAfterTargetResolution g input answer marker := by
  have hfg : "f" ≠ g := Ne.symm hgf
  have hfsg : "f_Spec" ≠ g := Ne.symm hgs
  simp [genericAfterDispatch, genericAfterTargetResolution, targetGoals,
    prefixConf, genericParentSubst, finiteWorld, baseParentClause,
    finiteSpecializedClause_eq, finiteTargetClause, step, PWorld.clausesOf,
    PWorld.canTableCall, PWorld.isTabled, resolveAlts,
    prologMatchCompatList, prologMatchCompat, freshenResolutionClause,
    resolutionFreshSuffix, renameAtomSuffix,
    renameGoalSuffix, Atom.vars,
    Metta.Subst.lookup, hfg, hfsg]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private theorem specialized_target_resolution (g input answer marker : String)
    (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    step baseProg [] 100 (specializedAfterGuard g input answer marker) =
      specializedAfterTargetResolution g input answer marker := by
  have hfg : "f" ≠ g := Ne.symm hgf
  have hfsg : "f_Spec" ≠ g := Ne.symm hgs
  simp [specializedAfterGuard, specializedAfterTargetResolution,
    targetGoals, prefixConf, specializedParentSubst, finiteWorld,
    baseParentClause, finiteSpecializedClause_eq, finiteTargetClause, step,
    PWorld.clausesOf, PWorld.canTableCall, PWorld.isTabled, resolveAlts,
    prologMatchCompatList, prologMatchCompat, freshenResolutionClause,
    resolutionFreshSuffix, renameAtomSuffix,
    renameGoalSuffix, Atom.vars,
    Metta.Subst.lookup, hfg, hfsg]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private def genericTargetSubst (g input answer : String) : Subst :=
  [("answer", Atom.sym answer),
   ("x#r10", Atom.sym input),
   ("hof#r10", Atom.sym g),
   ("result#r10", Atom.sym answer),
   ("targetArg#r11", Atom.sym input)]

private def specializedTargetSubst (input answer : String) : Subst :=
  [("answer", Atom.sym answer),
   ("x#r10", Atom.sym input),
   ("result#r10", Atom.sym answer),
   ("targetArg#r11", Atom.sym input)]

private theorem generic_target_unify (g input answer : String) :
    unifyB (genericParentSubst g input)
      (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
      (Atom.expr [Atom.var "targetArg#r11", Atom.sym answer]) =
        some (genericTargetSubst g input answer) := by
  simp [unifyB, unifyTopExact, genericParentSubst, genericTargetSubst,
    Atom.size,
    Metta.Unify.unifyTopWith, Metta.Unify.unifyRoundsWith,
    Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
    Metta.Unify.decomposeListWith, Metta.Subst.occurs,
    Metta.Subst.extend, Metta.Subst.erase, Metta.Subst.apply,
    Metta.Subst.compose, Metta.Subst.lookup]

private theorem specialized_target_unify (input answer : String) :
    unifyB (specializedParentSubst input)
      (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
      (Atom.expr [Atom.var "targetArg#r11", Atom.sym answer]) =
        some (specializedTargetSubst input answer) := by
  simp [unifyB, unifyTopExact, specializedParentSubst,
    specializedTargetSubst, Atom.size, Metta.Unify.unifyTopWith,
    Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
    Metta.Subst.occurs,
    Metta.Subst.extend, Metta.Subst.erase, Metta.Subst.apply,
    Metta.Subst.compose, Metta.Subst.lookup]

private theorem generic_target_binding (g input answer marker : String) :
    step baseProg [] 100 (genericAfterTargetResolution g input answer marker) =
      commonAfterTargetBinding g answer marker := by
  simp [genericAfterTargetResolution, commonAfterTargetBinding, targetGoals,
    prefixConf, finiteWorld, baseParentClause, finiteSpecializedClause_eq,
    step, generic_target_unify, genericTargetSubst,
    trimFor_target_effect_generic]

private theorem specialized_target_binding (g input answer marker : String) :
    step baseProg [] 100
      (specializedAfterTargetResolution g input answer marker) =
      commonAfterTargetBinding g answer marker := by
  simp [specializedAfterTargetResolution, commonAfterTargetBinding,
    targetGoals, prefixConf, finiteWorld, baseParentClause,
    finiteSpecializedClause_eq, step, specialized_target_unify,
    specializedTargetSubst, trimFor_target_effect_specialized]

/-- One-binding guarded-base simulation for arbitrary concrete function,
    argument, and result symbols.  Generic dispatch and the specialization
    guard each contribute one pure stuttering step, after which both
    executions reach the identical configuration, including world,
    alternatives, counter, and ordered answers. -/
theorem baseCase_finite_convergence (g input answer marker : String)
    (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    advance 5 (finiteConf g input answer marker "f") =
      advance 5 (finiteConf g input answer marker "f_Spec") := by
  simp [advance, generic_parent_resolution, generic_parent_binding,
    generic_dispatch, generic_target_resolution, generic_target_binding,
    specialized_parent_resolution, specialized_parent_binding,
    specialized_guard, specialized_target_resolution,
    specialized_target_binding, hgf, hgs]

theorem baseCase_continuation_convergence (g input answer marker : String)
    (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") (steps : Nat) :
    advance steps (advance 5 (finiteConf g input answer marker "f")) =
      advance steps (advance 5 (finiteConf g input answer marker "f_Spec")) := by
  rw [baseCase_finite_convergence g input answer marker hgf hgs]

#guard (advance 5 (finiteConf "g" "input" "answer-value" "finite-effect" "f")).cur ==
  (advance 5
    (finiteConf "g" "input" "answer-value" "finite-effect" "f_Spec")).cur

/-! ## Ordered multiplicity for an arbitrary concrete target family -/

private def orderedTargetClause (input answer : String) : Clause :=
  { params := [Atom.sym input]
    result := Atom.sym answer
    body := [] }

@[simp] private theorem orderedTargetClause_arity (input answer : String) :
    (orderedTargetClause input answer).params.length = 1 := by
  rfl

private def orderedWorld (g input : String) (answers : List String) : PWorld :=
  { progClauses :=
      [("f", baseParentClause),
       ("f_Spec", finiteSpecializedClause g)] ++
        answers.map (fun answer => (g, orderedTargetClause input answer))
    knownHeads := ["f", "f_Spec", g]
    knownArities := [("f", 2), ("f_Spec", 2), (g, 1)] }

@[simp] private theorem orderedWorld_clauseIndexReady
    (g input : String) (answers : List String) :
    (orderedWorld g input answers).clauseIndexReady = false := rfl

private theorem orderedWorld_clauses_f (g input : String)
    (answers : List String) (hgf : g ≠ "f") :
    (orderedWorld g input answers).clausesOf "f" = [baseParentClause] := by
  induction answers with
  | nil => simp [orderedWorld, PWorld.clausesOf]
  | cons answer rest ih =>
      simp [orderedWorld, PWorld.clausesOf, hgf]

private theorem orderedWorld_clauses_fSpec (g input : String)
    (answers : List String) (hgs : g ≠ "f_Spec") :
    (orderedWorld g input answers).clausesOf "f_Spec" =
      [finiteSpecializedClause g] := by
  induction answers with
  | nil => simp [orderedWorld, PWorld.clausesOf]
  | cons answer rest ih =>
      simp [orderedWorld, PWorld.clausesOf, hgs]

private theorem orderedWorld_clauses_g (g input : String)
    (answers : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    (orderedWorld g input answers).clausesOf g =
      answers.map (orderedTargetClause input) := by
  have hfg : "f" ≠ g := Ne.symm hgf
  have hfsg : "f_Spec" ≠ g := Ne.symm hgs
  unfold orderedWorld PWorld.clausesOf
  simp [hfg, hfsg]

private theorem orderedWorld_canTableCall_false (g input : String)
    (answers : List String) (f : String) (args : List Atom) :
    (orderedWorld g input answers).canTableCall f args = false := by
  simp [orderedWorld, PWorld.canTableCall, PWorld.isTabled]

private def orderedConf (g input head : String) (answers : List String) : Conf :=
  { cur := some
      ([Goal.call head [Atom.sym g, Atom.sym input] (Atom.var "answer")], [])
    alts := []
    world := orderedWorld g input answers
    counter := 10
    qterm := Atom.var "answer" }

private def orderedPrefixConf (g input : String) (answers : List String)
    (goals : List Goal) (b : Subst) (alts : List Alt) (counter : Nat)
    (found : List Atom := []) : Conf :=
  { cur := some (goals, b)
    alts := alts
    world := orderedWorld g input answers
    counter := counter
    qterm := Atom.var "answer"
    answers := found }

private def orderedGenericAfterParentResolution (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers (genericParentGoals g input) [] [.barrier] 11

private def orderedSpecializedAfterParentResolution (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers (specializedParentGoals g input) [] [.barrier] 11

private def orderedGenericAfterParentBinding (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers
    [Goal.callDyn (Atom.var "hof#r10") [Atom.var "x#r10"]
      (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private def orderedSpecializedAfterParentBinding (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers
    [Goal.eq (Atom.sym g) (Atom.var "hof#r10"),
     Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private def orderedSpecializedAfterGuard (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers
    [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (specializedParentSubst input) [.barrier] 11

private def orderedGenericAfterDispatch (g input : String)
    (answers : List String) : Conf :=
  orderedPrefixConf g input answers
    [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
    (genericParentSubst g input) [.barrier] 11

private theorem ordered_generic_parent_resolution (g input : String)
    (answers : List String) (hgf : g ≠ "f") :
    step baseProg [] 100 (orderedConf g input "f" answers) =
      orderedGenericAfterParentResolution g input answers := by
  simp [orderedConf, orderedGenericAfterParentResolution,
    orderedPrefixConf, genericParentGoals, baseParentClause,
    step, orderedWorld_clauses_f,
    orderedWorld_canTableCall_false, resolveAlts,
    prologMatchCompatList, prologMatchCompat, freshenResolutionClause,
    resolutionFreshSuffix, renameAtomSuffix,
    renameGoalSuffix, Atom.vars,
    hgf]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private theorem ordered_specialized_parent_resolution (g input : String)
    (answers : List String) (hgs : g ≠ "f_Spec") :
    step baseProg [] 100 (orderedConf g input "f_Spec" answers) =
      orderedSpecializedAfterParentResolution g input answers := by
  simp [orderedConf, orderedSpecializedAfterParentResolution,
    orderedPrefixConf, specializedParentGoals,
    finiteSpecializedClause_eq, step, orderedWorld_clauses_fSpec,
    orderedWorld_canTableCall_false, resolveAlts,
    prologMatchCompatList, prologMatchCompat, freshenResolutionClause,
    resolutionFreshSuffix, renameAtomSuffix,
    renameGoalSuffix, Atom.vars,
    hgs]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private theorem ordered_generic_parent_binding (g input : String)
    (answers : List String) :
    step baseProg [] 100
      (orderedGenericAfterParentResolution g input answers) =
      orderedGenericAfterParentBinding g input answers := by
  simp [orderedGenericAfterParentResolution, orderedGenericAfterParentBinding,
    orderedPrefixConf, genericParentGoals, orderedWorld, baseParentClause,
    finiteSpecializedClause_eq, step, generic_parent_unify,
    generic_parent_trim]

private theorem ordered_specialized_parent_binding (g input : String)
    (answers : List String) :
    step baseProg [] 100
      (orderedSpecializedAfterParentResolution g input answers) =
      orderedSpecializedAfterParentBinding g input answers := by
  simp [orderedSpecializedAfterParentResolution,
    orderedSpecializedAfterParentBinding, orderedPrefixConf,
    specializedParentGoals, orderedWorld, baseParentClause,
    finiteSpecializedClause_eq, step, specialized_parent_unify,
    specialized_parent_trim]

private theorem ordered_specialized_guard (g input : String)
    (answers : List String) :
    step baseProg [] 100
      (orderedSpecializedAfterParentBinding g input answers) =
      orderedSpecializedAfterGuard g input answers := by
  simp [orderedSpecializedAfterParentBinding, orderedSpecializedAfterGuard,
    orderedPrefixConf, specializedParentSubst, genericParentSubst,
    orderedWorld, baseParentClause, finiteSpecializedClause_eq, step, unifyB,
    unifyTopExact, Atom.size, Metta.Unify.unifyTopWith,
    Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith,
    Metta.Subst.lookup, trimFor_specialization_guard_direct]

private theorem ordered_generic_dispatch (g input : String)
    (answers : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec")
    (hanswers : answers ≠ []) :
    step baseProg [] 100 (orderedGenericAfterParentBinding g input answers) =
      orderedGenericAfterDispatch g input answers := by
  simp [orderedGenericAfterParentBinding, orderedGenericAfterDispatch,
    orderedPrefixConf, genericParentSubst, step, Metta.Subst.lookup,
    orderedWorld_clauses_g, hgf, hgs, hanswers]

private def orderedTargetGoals (input answer : String) : List Goal :=
  [Goal.eq
    (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
    (Atom.expr [Atom.sym input, Atom.sym answer])]

private def orderedAlt (input answer : String) (b : Subst) : Alt :=
  Alt.br (orderedTargetGoals input answer) b

private def orderedPush (input : String) (b : Subst)
    (acc : List Alt × Nat) (answer : String) : List Alt × Nat :=
  (orderedAlt input answer b :: acc.1, acc.2 + 1)

private theorem orderedPush_fold (input : String) (b : Subst)
    (answers : List String) (rev : List Alt) (counter : Nat) :
    answers.foldl (orderedPush input b) (rev, counter) =
      (answers.reverse.map (fun answer => orderedAlt input answer b) ++ rev,
       counter + answers.length) := by
  induction answers generalizing rev counter with
  | nil => simp
  | cons answer rest ih =>
      simp only [List.foldl_cons, orderedPush]
      rw [ih]
      simp [List.map_append, Nat.add_comm, Nat.add_left_comm]

private theorem ordered_resolve_generic (g input : String)
    (answers : List String) (counter : Nat) :
    resolveAlts (answers.map (orderedTargetClause input))
        [Atom.sym input] [Atom.var "x#r10"] (Atom.var "result#r10") []
        (genericParentSubst g input) (Atom.var "answer") 2 counter =
      (answers.map (fun answer =>
          orderedAlt input answer (genericParentSubst g input)),
       counter + answers.length) := by
  have hres : subst (genericParentSubst g input) (Atom.var "result#r10") =
      Atom.var "result#r10" := by
    simp [genericParentSubst, Metta.Subst.lookup]
  unfold resolveAlts
  simp only [hres]
  rw [List.foldl_map]
  simp only [orderedTargetClause, prologMatchCompatList, prologMatchCompat,
    freshenResolutionClause, renameAtomSuffix,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    beq_self_eq_true, List.append_nil]
  change
    let folded := answers.foldl
      (orderedPush input (genericParentSubst g input)) ([], counter)
    (folded.1.reverse, folded.2) = _
  rw [orderedPush_fold]
  simp [orderedAlt, orderedTargetGoals]

private theorem ordered_resolve_specialized (input : String)
    (answers : List String) (counter : Nat) :
    resolveAlts (answers.map (orderedTargetClause input))
        [Atom.sym input] [Atom.var "x#r10"] (Atom.var "result#r10") []
        (specializedParentSubst input) (Atom.var "answer") 2 counter =
      (answers.map (fun answer =>
          orderedAlt input answer (specializedParentSubst input)),
       counter + answers.length) := by
  have hres : subst (specializedParentSubst input) (Atom.var "result#r10") =
      Atom.var "result#r10" := by
    simp [specializedParentSubst, Metta.Subst.lookup]
  unfold resolveAlts
  simp only [hres]
  rw [List.foldl_map]
  simp only [orderedTargetClause, prologMatchCompatList, prologMatchCompat,
    freshenResolutionClause, renameAtomSuffix,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    beq_self_eq_true, List.append_nil]
  change
    let folded := answers.foldl
      (orderedPush input (specializedParentSubst input)) ([], counter)
    (folded.1.reverse, folded.2) = _
  rw [orderedPush_fold]
  simp [orderedAlt, orderedTargetGoals]

private def orderedChoiceConf (g input : String) (all : List String)
    (b : Subst) (remaining : List String) (found : List Atom) : Conf :=
  match remaining with
  | [] =>
      { cur := none
        alts := []
        world := orderedWorld g input all
        counter := 11 + all.length
        qterm := Atom.var "answer"
        answers := found }
  | answer :: rest =>
      { cur := some (orderedTargetGoals input answer, b)
        alts := rest.map (fun next => orderedAlt input next b) ++
          [.barrier, .barrier]
        world := orderedWorld g input all
        counter := 11 + all.length
        qterm := Atom.var "answer"
        answers := found }

private theorem ordered_generic_target_resolution (g input answer : String)
    (rest : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    step baseProg [] 100
      (orderedGenericAfterDispatch g input (answer :: rest)) =
      orderedChoiceConf g input (answer :: rest)
        (genericParentSubst g input) (answer :: rest) [] := by
  have hx : subst (genericParentSubst g input) (Atom.var "x#r10") =
      Atom.sym input := by
    simp [genericParentSubst, Metta.Subst.lookup]
  simp [orderedGenericAfterDispatch, orderedPrefixConf, step,
    orderedWorld_canTableCall_false, orderedWorld_clauses_g, hgf, hgs,
    orderedChoiceConf, orderedAlt, orderedTargetGoals, hx, barrierDepth, barrierCount]
  rw [show orderedTargetClause input answer ::
      rest.map (orderedTargetClause input) =
      (answer :: rest).map (orderedTargetClause input) by rfl]
  rw [ordered_resolve_generic]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private theorem ordered_specialized_target_resolution
    (g input answer : String) (rest : List String)
    (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    step baseProg [] 100
      (orderedSpecializedAfterGuard g input (answer :: rest)) =
      orderedChoiceConf g input (answer :: rest)
        (specializedParentSubst input) (answer :: rest) [] := by
  have hx : subst (specializedParentSubst input) (Atom.var "x#r10") =
      Atom.sym input := by
    simp [specializedParentSubst, Metta.Subst.lookup]
  simp [orderedSpecializedAfterGuard, orderedPrefixConf, step,
    orderedWorld_canTableCall_false, orderedWorld_clauses_g, hgf, hgs,
    orderedChoiceConf, orderedAlt, orderedTargetGoals, hx, barrierDepth, barrierCount]
  rw [show orderedTargetClause input answer ::
      rest.map (orderedTargetClause input) =
      (answer :: rest).map (orderedTargetClause input) by rfl]
  rw [ordered_resolve_specialized]
  rw [pull_of_alts_branch (h := rfl)]
  rfl

private def orderedGenericTargetSubst (g input answer : String) : Subst :=
  [("answer", Atom.sym answer),
   ("x#r10", Atom.sym input),
   ("hof#r10", Atom.sym g),
   ("result#r10", Atom.sym answer)]

private def orderedSpecializedTargetSubst (input answer : String) : Subst :=
  [("answer", Atom.sym answer),
   ("x#r10", Atom.sym input),
   ("result#r10", Atom.sym answer)]

private theorem ordered_generic_target_unify (g input answer : String) :
    unifyB (genericParentSubst g input)
      (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
      (Atom.expr [Atom.sym input, Atom.sym answer]) =
        some (orderedGenericTargetSubst g input answer) := by
  simp [unifyB, unifyTopExact, genericParentSubst,
    orderedGenericTargetSubst, Atom.size, Metta.Unify.unifyTopWith,
    Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
    Metta.Subst.occurs,
    Metta.Subst.extend, Metta.Subst.erase, Metta.Subst.apply,
    Metta.Subst.compose, Metta.Subst.lookup]

private theorem ordered_specialized_target_unify (input answer : String) :
    unifyB (specializedParentSubst input)
      (Atom.expr [Atom.var "x#r10", Atom.var "result#r10"])
      (Atom.expr [Atom.sym input, Atom.sym answer]) =
        some (orderedSpecializedTargetSubst input answer) := by
  simp [unifyB, unifyTopExact, specializedParentSubst,
    orderedSpecializedTargetSubst, Atom.size, Metta.Unify.unifyTopWith,
    Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
    Metta.Subst.occurs,
    Metta.Subst.extend, Metta.Subst.erase, Metta.Subst.apply,
    Metta.Subst.compose, Metta.Subst.lookup]

private theorem ordered_choice_generic_two_steps (g input answer : String)
    (all rest : List String) (found : List Atom) :
    advance 2
      (orderedChoiceConf g input all (genericParentSubst g input)
        (answer :: rest) found) =
      orderedChoiceConf g input all (genericParentSubst g input) rest
        (Atom.sym answer :: found) := by
  cases rest with
  | nil =>
      simp [advance, orderedChoiceConf, orderedTargetGoals, step,
        ordered_generic_target_unify, orderedGenericTargetSubst,
        trimFor_ordered_target_generic,
        Metta.Subst.lookup]
      rw [pull_of_two_barriers (h := rfl) (hb := rfl)]
  | cons next tail =>
      simp [advance, orderedChoiceConf, orderedTargetGoals, orderedAlt, step,
        ordered_generic_target_unify, orderedGenericTargetSubst,
        trimFor_ordered_target_generic,
        Metta.Subst.lookup]
      rw [pull_of_alts_branch (h := rfl)]

private theorem ordered_choice_specialized_two_steps
    (g input answer : String) (all rest : List String) (found : List Atom) :
    advance 2
      (orderedChoiceConf g input all (specializedParentSubst input)
        (answer :: rest) found) =
      orderedChoiceConf g input all (specializedParentSubst input) rest
        (Atom.sym answer :: found) := by
  cases rest with
  | nil =>
      simp [advance, orderedChoiceConf, orderedTargetGoals, step,
        ordered_specialized_target_unify, orderedSpecializedTargetSubst,
        trimFor_ordered_target_specialized,
        Metta.Subst.lookup]
      rw [pull_of_two_barriers (h := rfl) (hb := rfl)]
  | cons next tail =>
      simp [advance, orderedChoiceConf, orderedTargetGoals, orderedAlt, step,
        ordered_specialized_target_unify, orderedSpecializedTargetSubst,
        trimFor_ordered_target_specialized,
        Metta.Subst.lookup]
      rw [pull_of_alts_branch (h := rfl)]

private theorem advance_add (m n : Nat) (c : Conf) :
    advance (m + n) c = advance n (advance m c) := by
  induction m generalizing c with
  | zero => simp [advance]
  | succ m ih =>
      simp only [Nat.succ_add, advance]
      exact ih (step baseProg [] 100 c)

private theorem ordered_choices_converge (g input : String)
    (all remaining : List String) (found : List Atom) :
    advance (2 * remaining.length)
        (orderedChoiceConf g input all (genericParentSubst g input)
          remaining found) =
      advance (2 * remaining.length)
        (orderedChoiceConf g input all (specializedParentSubst input)
          remaining found) := by
  induction remaining generalizing found with
  | nil => simp [orderedChoiceConf, advance]
  | cons answer rest ih =>
      rw [show 2 * (answer :: rest).length = 2 + 2 * rest.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [advance_add 2, ordered_choice_generic_two_steps]
      rw [advance_add 2, ordered_choice_specialized_two_steps]
      exact ih (Atom.sym answer :: found)

private theorem ordered_generic_to_choices (g input answer : String)
    (rest : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    advance 4 (orderedConf g input "f" (answer :: rest)) =
      orderedChoiceConf g input (answer :: rest)
        (genericParentSubst g input) (answer :: rest) [] := by
  simp [advance, ordered_generic_parent_resolution,
    ordered_generic_parent_binding, ordered_generic_dispatch,
    ordered_generic_target_resolution, hgf, hgs]

private theorem ordered_specialized_to_choices (g input answer : String)
    (rest : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    advance 4 (orderedConf g input "f_Spec" (answer :: rest)) =
      orderedChoiceConf g input (answer :: rest)
        (specializedParentSubst input) (answer :: rest) [] := by
  simp [advance, ordered_specialized_parent_resolution,
    ordered_specialized_parent_binding, ordered_specialized_guard,
    ordered_specialized_target_resolution, hgf, hgs]

/-- The canonical one-binding rewrite preserves every answer, its order, and
    its multiplicity for an arbitrary nonempty ordered family of concrete
    target clauses.  Both sides finish in the identical configuration. -/
theorem baseCase_ordered_multiplicity (g input answer : String)
    (rest : List String) (hgf : g ≠ "f") (hgs : g ≠ "f_Spec") :
    advance (4 + 2 * (answer :: rest).length)
        (orderedConf g input "f" (answer :: rest)) =
      advance (4 + 2 * (answer :: rest).length)
        (orderedConf g input "f_Spec" (answer :: rest)) := by
  rw [advance_add 4, ordered_generic_to_choices g input answer rest hgf hgs]
  rw [advance_add 4,
    ordered_specialized_to_choices g input answer rest hgf hgs]
  exact ordered_choices_converge g input (answer :: rest) (answer :: rest) []

end PLeaTTa
