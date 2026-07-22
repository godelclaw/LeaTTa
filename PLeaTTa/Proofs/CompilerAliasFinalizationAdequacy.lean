-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerAliasFinalizationAdequacy
Purpose: Prove the executable algorithm used to solve compiler-only alias
  ledgers, including reflexive and repeated aliases.
Trusted boundary: none
Main exports: resolveCompileAliases_aliasPairs, AliasLedgerAgrees.resolveBoth,
  compileSuperposeBranches_alias_resolution_sound
-/
import PLeaTTa.Proofs.CompilerFinalization
import PLeaTTa.Proofs.CompilerTypedSharedResultAdequacy

namespace PLeaTTa.CompilerAliasFinalizationAdequacy

open Metta (Atom Subst)
open PLeaTTa
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerTypedSharedResultAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution

/-- Canonical executable state after distinct source names have been aliased
to one shared target.  The source list records first-occurrence order. -/
def aliasBinding (target : String) (sources : List String) : Subst :=
  sources.map (fun source => (source, .var target))

/-- Executable variable-variable ledger corresponding to a source-ordered
list of aliases to one target. -/
def aliasPairs (target : String) (sources : List String) :
    List (Atom × Atom) :=
  sources.map (fun source => (.var source, .var target))

/-- Add one source to the canonical alias domain.  A reflexive alias and a
repeated alias leave the state unchanged. -/
def insertAliasSource {α : Type} [DecidableEq α] (target source : α)
    (seen : List α) : List α :=
  if source = target ∨ source ∈ seen then seen else seen ++ [source]

/-- Membership in the canonical domain determines its executable lookup. -/
theorem lookup_aliasBinding_of_mem {target source : String}
    {sources : List String} (member : source ∈ sources) :
    Metta.Subst.lookup (aliasBinding target sources) source =
      some (.var target) := by
  induction sources with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      change (if source == head then some (.var target)
        else Metta.Subst.lookup (aliasBinding target tail) source) =
          some (.var target)
      by_cases same : source = head
      · simp [same]
      · simp only [beq_iff_eq, same, ↓reduceIte]
        exact induction (member.resolve_left same)

/-- Names outside the canonical domain have no executable assignment. -/
theorem lookup_aliasBinding_of_not_mem {target source : String}
    {sources : List String} (absent : source ∉ sources) :
    Metta.Subst.lookup (aliasBinding target sources) source = none := by
  induction sources with
  | nil => rfl
  | cons head tail induction =>
      have headNe : source ≠ head :=
        fun same => absent (by simp [same])
      have tailAbsent : source ∉ tail :=
        fun member => absent (by simp [member])
      change (if source == head then some (.var target)
        else Metta.Subst.lookup (aliasBinding target tail) source) = none
      simp only [beq_iff_eq, headNe, ↓reduceIte]
      exact induction tailAbsent

/-- A duplicate-free canonical alias binding is topologically ordered when
the shared target is outside its domain. -/
def aliasBinding_topological {target : String} {sources : List String}
    (nodup : sources.Nodup) (targetFresh : target ∉ sources) :
    SubstTopological (aliasBinding target sources) := by
  induction sources with
  | nil => exact emptySubstTopological
  | cons source sources induction =>
      rw [List.nodup_cons] at nodup
      have sourceNeTarget : source ≠ target := by
        intro same
        apply targetFresh
        simp [same]
      have targetTail : target ∉ sources := by
        intro member
        exact targetFresh (by simp [member])
      change SubstTopological
        ((source, .var target) :: aliasBinding target sources)
      apply SubstTopological.cons_of_fresh
        (aliasBinding target sources)
        (induction nodup.2 targetTail)
      · exact lookup_aliasBinding_of_not_mem nodup.1
      · simpa [Atom.vars] using sourceNeTarget
      · intro dependency member
        simp only [Atom.vars, List.mem_singleton] at member
        subst dependency
        exact lookup_aliasBinding_of_not_mem targetTail

/-- A canonical alias binding leaves its shared target open. -/
theorem subst_aliasBinding_target {target : String} {sources : List String}
    (targetFresh : target ∉ sources) :
    subst (aliasBinding target sources) (.var target) = .var target := by
  apply subst_eq_self_of_domain_free
  intro name member
  simp only [Atom.vars, List.mem_singleton] at member
  subst name
  exact lookup_aliasBinding_of_not_mem targetFresh

/-- Every source already in the canonical domain denotes the shared target. -/
theorem subst_aliasBinding_of_mem {target source : String}
    {sources : List String} (nodup : sources.Nodup)
    (targetFresh : target ∉ sources) (member : source ∈ sources) :
    subst (aliasBinding target sources) (.var source) = .var target := by
  have topological := aliasBinding_topological nodup targetFresh
  have lookup := lookup_aliasBinding_of_mem (target := target) member
  exact (topological.subst_var_of_lookup (aliasBinding target sources)
    source (.var target) lookup).trans
      (subst_aliasBinding_target targetFresh)

/-- A variable outside the canonical alias domain remains open. -/
theorem subst_aliasBinding_of_not_mem {target source : String}
    {sources : List String} (absent : source ∉ sources) :
    subst (aliasBinding target sources) (.var source) = .var source := by
  apply subst_eq_self_of_domain_free
  intro name member
  simp only [Atom.vars, List.mem_singleton] at member
  subst name
  exact lookup_aliasBinding_of_not_mem absent

/-- Applying the empty one-pass substitution is the identity. -/
theorem apply_empty (atom : Atom) : Metta.Subst.apply [] atom = atom := by
  induction atom with
  | sym name => simp [Metta.Subst.apply]
  | var name => simp [Metta.Subst.apply, Metta.Subst.lookup]
  | gnd ground => simp [Metta.Subst.apply]
  | expr atoms induction =>
      simp only [Metta.Subst.apply, Atom.expr.injEq]
      calc
        List.map (Metta.Subst.apply []) atoms = List.map id atoms := by
          apply List.map_congr_left
          intro atom member
          exact induction atom member
        _ = atoms := List.map_id atoms

/-- Composing an empty generated unifier leaves the accumulated binding
unchanged.  Reflexive and duplicate aliases use this case. -/
theorem compose_empty_left (binding : Subst) :
    Metta.Subst.compose [] binding = binding := by
  unfold Metta.Subst.compose
  have mapped : binding.map (fun pair =>
      (pair.fst, Metta.Subst.apply [] pair.snd)) = binding := by
    calc
      binding.map (fun pair =>
          (pair.fst, Metta.Subst.apply [] pair.snd)) =
          binding.map id := by
            apply List.map_congr_left
            intro pair _member
            rcases pair with ⟨name, value⟩
            simp [apply_empty]
      _ = binding := List.map_id binding
  rw [mapped]
  simp

/-- Composing a genuinely fresh source-to-target alias appends exactly that
source to the canonical binding. -/
theorem compose_singleton_aliasBinding {target source : String}
    {sources : List String} (different : source ≠ target) :
    Metta.Subst.compose [(source, .var target)]
        (aliasBinding target sources) =
      aliasBinding target (sources ++ [source]) := by
  simp [Metta.Subst.compose, aliasBinding, Metta.Subst.apply,
    Metta.Subst.lookup, Ne.symm different]

/-- Canonical insertion preserves the two structural invariants needed by
the next exact-unification step. -/
theorem insertAliasSource_wellFormed {α : Type} [DecidableEq α]
    {target source : α} {seen : List α} (nodup : seen.Nodup)
    (targetFresh : target ∉ seen) :
    (insertAliasSource target source seen).Nodup ∧
      target ∉ insertAliasSource target source seen := by
  unfold insertAliasSource
  split
  · exact ⟨nodup, targetFresh⟩
  · rename_i new
    have sourceFresh : source ∉ seen := by tauto
    have sourceNeTarget : source ≠ target := by tauto
    exact ⟨List.Nodup.append nodup (by simp)
        (by simp [sourceFresh]),
      by simp [targetFresh, Ne.symm sourceNeTarget]⟩

/-- A fold of canonical insertions remains duplicate-free and never places
the shared target in its domain. -/
theorem foldInsert_wellFormed {α : Type} [DecidableEq α]
    (target : α) (sources seen : List α) (nodup : seen.Nodup)
    (targetFresh : target ∉ seen) :
    let result := sources.foldl
      (fun seen source => insertAliasSource target source seen) seen
    result.Nodup ∧ target ∉ result := by
  induction sources generalizing seen with
  | nil => exact ⟨nodup, targetFresh⟩
  | cons source sources induction =>
      have inserted := insertAliasSource_wellFormed
        (source := source) nodup targetFresh
      simpa only [List.foldl_cons] using
        induction (insertAliasSource target source seen)
          inserted.1 inserted.2

/-- Membership after canonical insertion: retain the old domain and add the
new source exactly when it is not the shared target. -/
theorem mem_insertAliasSource_iff {α : Type} [DecidableEq α]
    {target source identity : α} {seen : List α} :
    identity ∈ insertAliasSource target source seen ↔
      identity ∈ seen ∨ (identity = source ∧ source ≠ target) := by
  unfold insertAliasSource
  by_cases condition : source = target ∨ source ∈ seen
  · rw [if_pos condition]
    constructor
    · exact Or.inl
    · intro member
      rcases member with old | ⟨rfl, different⟩
      · exact old
      · rcases condition with same | present
        · exact False.elim (different same)
        · exact present
  · rw [if_neg condition]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro member
      rcases member with old | rfl
      · exact Or.inl old
      · exact Or.inr ⟨rfl, fun same => condition (Or.inl same)⟩
    · intro member
      rcases member with old | ⟨rfl, _different⟩
      · exact Or.inl old
      · exact Or.inr rfl

/-- Extensional domain of a complete canonical fold. -/
theorem mem_foldInsert_iff {α : Type} [DecidableEq α]
    (target identity : α) (sources seen : List α) :
    identity ∈ sources.foldl
        (fun seen source => insertAliasSource target source seen) seen ↔
      identity ∈ seen ∨ (identity ∈ sources ∧ identity ≠ target) := by
  induction sources generalizing seen with
  | nil => simp
  | cons source sources induction =>
      rw [List.foldl_cons, induction,
        mem_insertAliasSource_iff]
      simp only [List.mem_cons]
      constructor
      · intro member
        rcases member with (old | ⟨same, sourceNeTarget⟩) |
            ⟨tail, identityNeTarget⟩
        · exact Or.inl old
        · exact Or.inr ⟨Or.inl same,
            fun identityEq => sourceNeTarget (same.symm.trans identityEq)⟩
        · exact Or.inr ⟨Or.inr tail, identityNeTarget⟩
      · intro member
        rcases member with old |
            ⟨headOrTail, identityNeTarget⟩
        · exact Or.inl (Or.inl old)
        · rcases headOrTail with same | tail
          · exact Or.inl (Or.inr ⟨same,
              fun sourceEq => identityNeTarget (same.trans sourceEq)⟩)
          · exact Or.inr ⟨tail, identityNeTarget⟩

/-- One executable alias-resolution step realizes canonical insertion.  The
proof covers a reflexive alias, a repeated source, and a fresh source without
assuming success of the executable unifier. -/
theorem resolve_alias_step {target source : String} {seen : List String}
    (nodup : seen.Nodup) (targetFresh : target ∉ seen) :
    (match unifyTopExact
        (subst (aliasBinding target seen) (.var source))
        (subst (aliasBinding target seen) (.var target)) with
      | some generated =>
          Except.ok
            (Metta.Subst.compose generated (aliasBinding target seen))
      | none =>
          Except.error
            "compiler aliases: incompatible translation-time sharing") =
      Except.ok
        (aliasBinding target (insertAliasSource target source seen)) := by
  rw [subst_aliasBinding_target targetFresh]
  by_cases same : source = target
  · subst source
    rw [subst_aliasBinding_target targetFresh, unifyTopExact_var_self]
    change Except.ok
      (Metta.Subst.compose [] (aliasBinding target seen)) = _
    rw [compose_empty_left]
    simp [insertAliasSource]
  · by_cases member : source ∈ seen
    · rw [subst_aliasBinding_of_mem nodup targetFresh member,
        unifyTopExact_var_self]
      change Except.ok
        (Metta.Subst.compose [] (aliasBinding target seen)) = _
      rw [compose_empty_left]
      simp [insertAliasSource, member]
    · rw [subst_aliasBinding_of_not_mem member]
      have occurs : Metta.Subst.occurs source (.var target) = false := by
        simp [Metta.Subst.occurs, same]
      rw [unifyTopExact_fresh_variable source (.var target) occurs]
      change Except.ok
        (Metta.Subst.compose [(source, .var target)]
          (aliasBinding target seen)) = _
      rw [compose_singleton_aliasBinding same]
      simp [insertAliasSource, same, member]

/-- Accumulator-general correctness of the executable left fold over a
variable-to-shared-target alias ledger. -/
theorem resolve_alias_pairs_from {target : String} {seen : List String}
    (sources : List String) (nodup : seen.Nodup)
    (targetFresh : target ∉ seen) :
    List.foldlM
      (fun binding pair =>
        match unifyTopExact (subst binding pair.1)
            (subst binding pair.2) with
        | some generated =>
            Except.ok (Metta.Subst.compose generated binding)
        | none =>
            Except.error
              "compiler aliases: incompatible translation-time sharing")
      (aliasBinding target seen) (aliasPairs target sources) =
      Except.ok (aliasBinding target
        (sources.foldl
          (fun seen source => insertAliasSource target source seen)
          seen)) := by
  induction sources generalizing seen with
  | nil => rfl
  | cons source sources induction =>
      simp only [aliasPairs, List.map_cons, List.foldlM_cons]
      rw [resolve_alias_step nodup targetFresh]
      dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
      have wellFormed := insertAliasSource_wellFormed
        (source := source) nodup targetFresh
      simpa only [List.foldl_cons, aliasPairs] using
        induction (seen := insertAliasSource target source seen)
          wellFormed.1 wellFormed.2

/-- The public executable resolver succeeds on every ordered
variable-to-shared-target ledger.  Repetitions preserve first-occurrence
order and multiplicity is not silently turned into an error. -/
theorem resolveCompileAliases_aliasPairs (target : String)
    (sources : List String) :
    resolveCompileAliases (aliasPairs target sources) =
      Except.ok (aliasBinding target
        (sources.foldl
          (fun seen source => insertAliasSource target source seen) [])) := by
  unfold resolveCompileAliases
  exact resolve_alias_pairs_from sources (seen := []) (by simp) (by simp)

/-! ## Cross-representation alias ledgers -/

/-- Agreement on a logical variable determines its current executable
spelling.  Anonymous variables are intentionally absent from `TermAgrees`'s
supported compiler fragment. -/
theorem variable_name_eq {identity : LogicVar} {name : String}
    (agreement : TermAgrees (.variable identity) (.var name)) :
    logicVarExecutableName identity = name := by
  cases agreement <;> rfl

/-- Source identities and executable source names are pointwise related by
the same projection used by `TermAgrees`, rather than by a second manually
maintained naming table. -/
theorem AliasLedgerAgrees.sourceNames_eq
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals) :
    sourceNames = sources.map logicVarExecutableName := by
  induction agreement with
  | nil => rfl
  | cons sourceAgreement _ induction =>
      simp [variable_name_eq sourceAgreement, induction]

/-- Canonical insertion introduces no identity other than the new source. -/
theorem mem_insertAliasSource {α : Type} [DecidableEq α]
    {target source identity : α} {seen : List α}
    (member : identity ∈ insertAliasSource target source seen) :
    identity ∈ seen ∨ identity = source := by
  unfold insertAliasSource at member
  split at member
  · exact Or.inl member
  · simpa [List.mem_append] using member

/-- On an explicitly injective finite compiler domain, canonical alias
insertion commutes with the executable variable-name projection. -/
theorem map_insertAliasSource
    {domain : List LogicVar} {target source : LogicVar}
    {seen : List LogicVar}
    (injective : EncodingInjectiveOn domain)
    (targetMember : target ∈ domain) (sourceMember : source ∈ domain)
    (seenWithin : ∀ identity, identity ∈ seen → identity ∈ domain) :
    (insertAliasSource target source seen).map logicVarExecutableName =
      insertAliasSource (logicVarExecutableName target)
        (logicVarExecutableName source)
        (seen.map logicVarExecutableName) := by
  have sameIff :
      logicVarExecutableName source = logicVarExecutableName target ↔
        source = target := by
    constructor
    · exact injective sourceMember targetMember
    · intro same
      exact congrArg logicVarExecutableName same
  have memberIff :
      logicVarExecutableName source ∈ seen.map logicVarExecutableName ↔
        source ∈ seen := by
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨identity, identityMember, sameName⟩
      have identityEq : identity = source :=
        injective (seenWithin identity identityMember) sourceMember sameName
      simpa [identityEq] using identityMember
    · intro member
      exact List.mem_map.mpr ⟨source, member, rfl⟩
  unfold insertAliasSource
  by_cases condition : source = target ∨ source ∈ seen
  · have executableCondition :
        logicVarExecutableName source = logicVarExecutableName target ∨
          logicVarExecutableName source ∈
            seen.map logicVarExecutableName := by
      simpa only [sameIff, memberIff] using condition
    rw [if_pos condition, if_pos executableCondition]
  · have executableCondition :
        ¬ (logicVarExecutableName source = logicVarExecutableName target ∨
          logicVarExecutableName source ∈
            seen.map logicVarExecutableName) := by
      simpa only [sameIff, memberIff] using condition
    rw [if_neg condition, if_neg executableCondition, List.map_append]
    rfl

/-- Accumulator-general commutation of stable alias deduplication with an
injective executable name projection. -/
theorem foldInsert_names_eq_from
    {domain : List LogicVar} {target : LogicVar}
    (injective : EncodingInjectiveOn domain)
    (targetMember : target ∈ domain)
    (sources seen : List LogicVar)
    (sourcesWithin : ∀ identity, identity ∈ sources → identity ∈ domain)
    (seenWithin : ∀ identity, identity ∈ seen → identity ∈ domain) :
    (sources.map logicVarExecutableName).foldl
        (fun seen source => insertAliasSource
          (logicVarExecutableName target) source seen)
        (seen.map logicVarExecutableName) =
      (sources.foldl
        (fun seen source => insertAliasSource target source seen) seen).map
          logicVarExecutableName := by
  induction sources generalizing seen with
  | nil => rfl
  | cons source sources induction =>
      have sourceMember : source ∈ domain :=
        sourcesWithin source (by simp)
      have tailWithin : ∀ identity, identity ∈ sources →
          identity ∈ domain := by
        intro identity member
        exact sourcesWithin identity (by simp [member])
      have insertedWithin : ∀ identity,
          identity ∈ insertAliasSource target source seen →
            identity ∈ domain := by
        intro identity member
        rcases mem_insertAliasSource member with old | rfl
        · exact seenWithin identity old
        · exact sourceMember
      simp only [List.map_cons, List.foldl_cons]
      rw [← map_insertAliasSource injective targetMember sourceMember
        seenWithin]
      exact induction (insertAliasSource target source seen) tailWithin
        insertedWithin

/-- Empty-accumulator specialization on the complete alias-source domain. -/
theorem foldInsert_names_eq (target : LogicVar) (sources : List LogicVar)
    (injective : EncodingInjectiveOn (target :: sources)) :
    (sources.map logicVarExecutableName).foldl
        (fun seen source => insertAliasSource
          (logicVarExecutableName target) source seen) [] =
      (sources.foldl
        (fun seen source => insertAliasSource target source seen) []).map
          logicVarExecutableName := by
  apply foldInsert_names_eq_from injective (by simp) sources []
  · intro identity member
    simp [member]
  · simp

/-- Every related compiler-alias ledger is accepted by the executable
resolver, with a canonical binding whose domain is the stable first-occurrence
deduplication of its ordered source names. -/
theorem AliasLedgerAgrees.resolveCompileAliases
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals) :
    resolveCompileAliases (collectCompileAliasesGoals executableGoals) =
      Except.ok (aliasBinding targetName
        (sourceNames.foldl
          (fun seen source => insertAliasSource targetName source seen)
          [])) := by
  rw [agreement.collect_eq]
  simpa [aliasPairs] using
    resolveCompileAliases_aliasPairs targetName sourceNames

/-! ## Exact independent alias state -/

/-- Extensional independent state after processing a source list.  The
shared target and every listed source denote the target; every other logical
identity remains open.  This is stronger than `AliasStateFor` and is what the
cross-representation bridge needs. -/
structure AliasStateExactly (target : LogicVar) (sources : List LogicVar)
    (bindings : Substitution) : Prop where
  targetFixed :
    bindings.applyTerm (.variable target) = .variable target
  sourceAliases : ∀ source, source ∈ sources →
    bindings.applyTerm (.variable source) = .variable target
  outsideFixed : ∀ identity, identity ≠ target → identity ∉ sources →
    bindings.applyTerm (.variable identity) = .variable identity

/-- No aliases have been installed in the empty independent state. -/
theorem aliasStateExactly_empty (target : LogicVar) :
    AliasStateExactly target [] [] where
  targetFixed := rfl
  sourceAliases := by simp
  outsideFixed := by intros; rfl

/-- One independent source-to-target equation realizes the same canonical
insertion used to describe the executable state.  Reflexive and repeated
sources stutter; a new source is prepended to the finite substitution while
the extensional source order remains append-only. -/
theorem AliasStateExactly.unifySource
    {target source : LogicVar} {seen : List LogicVar}
    {bindings : Substitution}
    (state : AliasStateExactly target seen bindings) :
    ∃ result,
      Unifies bindings (.variable source) (.variable target) result ∧
      AliasStateExactly target (insertAliasSource target source seen)
        result := by
  by_cases same : source = target
  · subst source
    refine ⟨bindings, ?_, ?_⟩
    · apply Unifies.normalize bindings [] (.variable target)
        (.variable target)
      simpa [state.targetFixed] using
        (RootUnifies.reflexive (.variable target))
    · simpa [insertAliasSource] using state
  · by_cases member : source ∈ seen
    · refine ⟨bindings, ?_, ?_⟩
      · apply Unifies.normalize bindings [] (.variable source)
          (.variable target)
        rw [state.sourceAliases source member, state.targetFixed]
        exact .reflexive (.variable target)
      · simpa [insertAliasSource, same, member] using state
    · let result : Substitution :=
        (source, .variable target) :: bindings
      refine ⟨result, ?_, ?_⟩
      · apply Unifies.normalize bindings [(source, .variable target)]
          (.variable source) (.variable target)
        rw [state.outsideFixed source same member, state.targetFixed]
        exact .bindLeft source (.variable target)
          (by simpa using Ne.symm same)
          (by simp [Term.occurs, Ne.symm same])
      · have inserted :
            insertAliasSource target source seen = seen ++ [source] := by
          simp [insertAliasSource, same, member]
        rw [inserted]
        refine
          { targetFixed := ?_
            sourceAliases := ?_
            outsideFixed := ?_ }
        · change Term.instantiateOne source (.variable target)
            (bindings.applyTerm (.variable target)) = .variable target
          rw [state.targetFixed]
          simp [Term.instantiateOne, Ne.symm same]
        · intro identity identityMember
          rw [List.mem_append, List.mem_singleton] at identityMember
          rcases identityMember with oldMember | newMember
          · change Term.instantiateOne source (.variable target)
              (bindings.applyTerm (.variable identity)) = .variable target
            rw [state.sourceAliases identity oldMember]
            simp [Term.instantiateOne, Ne.symm same]
          · have identityEq : identity = source := newMember
            subst identity
            change Term.instantiateOne source (.variable target)
              (bindings.applyTerm (.variable source)) = .variable target
            rw [state.outsideFixed source same member]
            simp [Term.instantiateOne]
        · intro identity identityNeTarget identityOutside
          have identityNeSource : identity ≠ source := by
            intro equality
            subst identity
            exact identityOutside (by simp)
          have identityOutsideOld : identity ∉ seen := by
            intro oldMember
            exact identityOutside (by simp [oldMember])
          change Term.instantiateOne source (.variable target)
            (bindings.applyTerm (.variable identity)) = .variable identity
          rw [state.outsideFixed identity identityNeTarget
            identityOutsideOld]
          simp [Term.instantiateOne, identityNeSource]

/-- Accumulator-general independent resolution for a cross-representation
alias ledger.  The resulting extensional state records exactly the stable
first-occurrence insertion of its source identities. -/
theorem AliasLedgerAgrees.resolveReferenceFrom
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    {seen : List LogicVar} {bindings : Substitution}
    (state : AliasStateExactly target seen bindings) :
    ∃ result,
      ResolvesAliasGoals bindings referenceGoals result ∧
      AliasStateExactly target
        (sources.foldl
          (fun seen source => insertAliasSource target source seen) seen)
        result := by
  induction agreement generalizing seen bindings with
  | nil => exact ⟨bindings, .nil bindings, state⟩
  | @cons source sourceName sources sourceNames referenceGoals
      executableGoals sourceAgreement tail induction =>
      obtain ⟨middle, headResolution, middleState⟩ :=
        state.unifySource (source := source)
      obtain ⟨result, tailResolution, resultState⟩ :=
        induction middleState
      exact ⟨result,
        .cons bindings middle result (.variable source) (.variable target)
          referenceGoals headResolution tailResolution,
        by simpa only [List.foldl_cons] using resultState⟩

/-- Empty-state specialization paired with the public independent resolver. -/
theorem AliasLedgerAgrees.resolveReference
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals) :
    ∃ result,
      ResolvesAliasGoals [] referenceGoals result ∧
      AliasStateExactly target
        (sources.foldl
          (fun seen source => insertAliasSource target source seen) [])
        result :=
  resolveReferenceFrom agreement (aliasStateExactly_empty target)

/-! ## Bidirectional cross-representation resolution -/

/-- Ordered source-variable observation surface of an alias ledger.  The two
lists have equal length whenever this function is used through
`AliasLedgerAgrees`; mismatched tails deliberately contribute no invented
pair. -/
def aliasSourcePairs : List LogicVar → List String → List (Term × Atom)
  | source :: sources, sourceName :: sourceNames =>
      (.variable source, .var sourceName) ::
        aliasSourcePairs sources sourceNames
  | _, _ => []

/-- The shared target followed by every source occurrence, preserving ledger
order and duplicate occurrences for the agreement audit. -/
def aliasSurfacePairs (target : LogicVar) (targetName : String)
    (sources : List LogicVar) (sourceNames : List String) :
    List (Term × Atom) :=
  ((.variable target, .var targetName) ::
    aliasSourcePairs sources sourceNames)

/-- Pointwise post-substitution agreement for every source occurrence in a
related ledger, given extensional source and target facts on both states. -/
theorem AliasLedgerAgrees.sourcePairs_bindingsAgree
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    {reference : Substitution} {executable : Subst}
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (referenceSources : ∀ source, source ∈ sources →
      reference.applyTerm (.variable source) = .variable target)
    (executableSources : ∀ sourceName, sourceName ∈ sourceNames →
      subst executable (.var sourceName) = .var targetName) :
    BindingsAgreeOn reference executable
      (aliasSourcePairs sources sourceNames) := by
  induction agreement with
  | nil =>
      intro pair member
      simp [aliasSourcePairs] at member
  | @cons source sourceName sources sourceNames referenceGoals
      executableGoals sourceAgreement tail induction =>
      intro pair member
      simp only [aliasSourcePairs, List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨sourceAgreement, ?_⟩
        unfold TermStateAgrees
        rw [referenceSources source (by simp),
          executableSources sourceName (by simp)]
        exact targetAgreement
      · apply induction
          (fun identity identityMember =>
            referenceSources identity (by simp [identityMember]))
          (fun name nameMember =>
            executableSources name (by simp [nameMember]))
          pair member

/-- Complete target-plus-sources binding agreement on the observable alias
surface. -/
theorem AliasLedgerAgrees.surface_bindingsAgree
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    {reference : Substitution} {executable : Subst}
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (referenceTarget :
      reference.applyTerm (.variable target) = .variable target)
    (executableTarget :
      subst executable (.var targetName) = .var targetName)
    (referenceSources : ∀ source, source ∈ sources →
      reference.applyTerm (.variable source) = .variable target)
    (executableSources : ∀ sourceName, sourceName ∈ sourceNames →
      subst executable (.var sourceName) = .var targetName) :
    BindingsAgreeOn reference executable
      (aliasSurfacePairs target targetName sources sourceNames) := by
  have sourceAgreement := sourcePairs_bindingsAgree agreement
    targetAgreement referenceSources executableSources
  intro pair member
  simp only [aliasSurfacePairs, List.mem_cons] at member
  rcases member with rfl | member
  · refine ⟨targetAgreement, ?_⟩
    unfold TermStateAgrees
    rw [referenceTarget, executableTarget]
    exact targetAgreement
  · exact sourceAgreement pair member

/-- Result package for the two independently defined alias resolvers.  The
reference derivation and executable equation are both retained, while
`bindingsAgree` states their pointwise correspondence on the complete ordered
alias surface. -/
def AliasResolutionAgreement (target : LogicVar) (targetName : String)
    (sources : List LogicVar) (sourceNames : List String)
    (referenceGoals : List PeTTaSpec.PrologCore.Goal)
    (executableGoals : List PLeaTTa.Goal) : Prop :=
  ∃ reference : Substitution, ∃ executable : Subst,
    ResolvesAliasGoals [] referenceGoals reference ∧
    resolveCompileAliases (collectCompileAliasesGoals executableGoals) =
      Except.ok executable ∧
    BindingsAgreeOn reference executable
      (aliasSurfacePairs target targetName sources sourceNames)

/-- Main bridge theorem: every cross-representation alias ledger resolves on
both independently defined sides, and the resulting states agree in ledger
order.  Executable name injectivity is explicit and finite; the known
source/generated collision is therefore rejected by the theorem premise
rather than hidden as compiler freshness. -/
theorem AliasLedgerAgrees.resolveBoth
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (injective : EncodingInjectiveOn (target :: sources)) :
    AliasResolutionAgreement target targetName sources sourceNames
      referenceGoals executableGoals := by
  let referenceSeen := sources.foldl
    (fun seen source => insertAliasSource target source seen) []
  let executableSeen := sourceNames.foldl
    (fun seen source => insertAliasSource targetName source seen) []
  obtain ⟨referenceBinding, referenceResolution, referenceState⟩ :=
    resolveReference agreement
  have executableResolution :=
    PLeaTTa.CompilerAliasFinalizationAdequacy.AliasLedgerAgrees.resolveCompileAliases
      agreement
  have targetNameEq : logicVarExecutableName target = targetName :=
    variable_name_eq targetAgreement
  have sourceNamesEq := sourceNames_eq agreement
  have seenNamesEq :
      executableSeen = referenceSeen.map logicVarExecutableName := by
    unfold executableSeen referenceSeen
    rw [sourceNamesEq, ← targetNameEq]
    exact foldInsert_names_eq target sources injective
  have executableWellFormed : executableSeen.Nodup ∧
      targetName ∉ executableSeen := by
    exact foldInsert_wellFormed targetName sourceNames [] (by simp) (by simp)
  let executableBinding := aliasBinding targetName executableSeen
  have executableTarget :
      subst executableBinding (.var targetName) = .var targetName :=
    subst_aliasBinding_target executableWellFormed.2
  have referenceSources : ∀ source, source ∈ sources →
      referenceBinding.applyTerm (.variable source) = .variable target := by
    intro source member
    by_cases same : source = target
    · subst source
      exact referenceState.targetFixed
    · apply referenceState.sourceAliases source
      exact (mem_foldInsert_iff target source sources []).2
        (Or.inr ⟨member, same⟩)
  have executableSources : ∀ sourceName, sourceName ∈ sourceNames →
      subst executableBinding (.var sourceName) = .var targetName := by
    intro sourceName member
    by_cases same : sourceName = targetName
    · subst sourceName
      exact executableTarget
    · apply subst_aliasBinding_of_mem executableWellFormed.1
        executableWellFormed.2
      rw [seenNamesEq]
      have mappedMember :
          sourceName ∈ sources.map logicVarExecutableName := by
        simpa only [sourceNamesEq] using member
      rcases List.mem_map.mp mappedMember with
        ⟨source, sourceMember, sourceEq⟩
      have sourceNeTarget : source ≠ target := by
        intro sourceTarget
        subst source
        exact same (sourceEq.symm.trans targetNameEq)
      apply List.mem_map.mpr
      refine ⟨source, ?_, sourceEq⟩
      exact (mem_foldInsert_iff target source sources []).2
        (Or.inr ⟨sourceMember, sourceNeTarget⟩)
  refine ⟨referenceBinding, executableBinding, referenceResolution, ?_, ?_⟩
  · simpa [executableBinding, executableSeen] using executableResolution
  · apply surface_bindingsAgree agreement targetAgreement
    · exact referenceState.targetFixed
    · exact executableTarget
    · exact referenceSources
    · exact executableSources

/-! ## Compiler traversal composition -/

/-- The compiler's complete ordered `build_superpose_branches/3` traversal
feeds the generic bidirectional alias resolver.  The sole additional premise
is a supported-source certificate that the finite aliases actually emitted by
the independent traversal have an injective executable spelling. -/
theorem compileSuperposeBranches_alias_resolution_sound
    {state : TranslatorState} (env : CEnv) (envAgreement : EnvAgrees state env)
    {outputIndex counter nextCounter : Nat} {sources : List Atom}
    {referenceAliases referenceBranches :
      List PeTTaSpec.PrologCore.Goal}
    (native : TranslatesSuperposeBranches state
      (.variable (.generated outputIndex)) counter sources referenceAliases
      referenceBranches nextCounter)
    (aliasesInjective :
      ∀ {aliasSources aliasNames executableAliases},
        AliasLedgerAgrees (.generated outputIndex) s!"_q{outputIndex}"
          aliasSources aliasNames referenceAliases executableAliases →
        EncodingInjectiveOn (.generated outputIndex :: aliasSources)) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel accumulator,
        ∃ rawBranches aliasSources aliasNames executableAliases
            executableBranches,
          List.foldlM
            (fun (acc : List (Atom × List PLeaTTa.Goal) × Nat)
                expression => do
              let (term, goals, next) ←
                compileExprFuel (baseFuel + extraFuel) env acc.2 expression
              .ok (acc.1 ++ [(term, goals)], next))
            (accumulator, counter) sources =
              .ok (accumulator ++ rawBranches, nextCounter) ∧
          compileSuperposeBranches (.var s!"_q{outputIndex}") rawBranches =
            (executableAliases, executableBranches) ∧
          AliasResolutionAgreement (.generated outputIndex)
            s!"_q{outputIndex}" aliasSources aliasNames referenceAliases
            executableAliases ∧
          SuperposeBranchesAgree (.variable (.generated outputIndex))
            (.var s!"_q{outputIndex}") referenceBranches
            executableBranches := by
  obtain ⟨baseFuel, positive, bounded, compiles⟩ :=
    compileSuperposeBranchesFuel_initial_sound env envAgreement native
  refine ⟨baseFuel, positive, bounded, ?_⟩
  intro extraFuel accumulator
  obtain ⟨rawBranches, aliasSources, aliasNames, executableAliases,
      executableBranches, compiled, normalized, aliasLedger,
      branchesAgreement⟩ := compiles extraFuel accumulator
  refine ⟨rawBranches, aliasSources, aliasNames, executableAliases,
    executableBranches, compiled, normalized, ?_, branchesAgreement⟩
  exact
    PLeaTTa.CompilerAliasFinalizationAdequacy.AliasLedgerAgrees.resolveBoth
      aliasLedger (.generatedVariable outputIndex)
      (aliasesInjective aliasLedger)

end PLeaTTa.CompilerAliasFinalizationAdequacy
