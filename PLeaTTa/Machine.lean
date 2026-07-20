-- SPDX-License-Identifier: Apache-2.0

/-
PLeaTTa executable machine (PETTA-LP.md §3): deterministic, fuel-bounded DFS
over configurations ⟨current branch | alternatives-with-barriers | world⟩.
Mirrors the Step relation (PLeaTTa/Semantics.lean) constructor-for-
constructor; total (structural on fuel), no `partial` — the correspondence
proof needs transparency.

Prolog disciplines built in: clause order; cut pops the alternative stack to
its tagged barrier; builtins delay until ground (bounded by fuel); world
mutations are immediate, sequenced, and NOT undone on backtracking; an open
space match sees a snapshot (logical update view).
-/
import PLeaTTa.Types
import PLeaTTa.OrderedIndex
import PLeaTTa.PersistentSubstCore
import PLeaTTa.Chain
import PLeaTTa.Builtins
import PLeaTTa.HostProtocol
import PLeaTTa.Specialize
import MettaHyperonFull.Runtime.Parser
import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.FreeVars
import MettaHyperonFull.Core.Grounding
import MettaHyperonFull.Core.Builtins
import Std.Data.HashSet.Lemmas
import Batteries.Data.List.Perm

namespace PLeaTTa

open Metta (Atom Subst GroundingTable ReduceResult callGrounded)

/-- The mutable world: the `&self` space and state cells. Space atom lists are
    stored newest-first for O(1) `add-atom`; `atomsOf` exposes insertion order,
    matching Prolog `assertz` enumeration. -/
structure PWorld where
  selfAtoms : List Atom := []
  /-- Additional named spaces. `&self` stays in `selfAtoms`; every other
      space key owns its own atom list. -/
  spaceAtoms : List (Atom × List Atom) := []
  /-- Derived ordered candidate index for `&self`.  `selfAtoms` remains the
      semantic reference. -/
  selfAtomIndex : SpaceIndex.State := SpaceIndex.empty
  /-- Derived ordered candidate indices aligned by named-space key. -/
  spaceAtomIndices : List (Atom × SpaceIndex.State) := []
  /-- False permits legacy/proof fixtures to use canonical full scans. -/
  spaceIndexReady : Bool := false
  /-- Named state cells [SPEC metta.pl:240-242]: `nb_setval`/`nb_getval` —
      global variables keyed by the NAME atom, set/read immediately, never
      undone on backtracking. -/
  store : List (Atom × Atom) := []
  nextId : Nat := 0
  /-- The LIVE clause database (Prolog assert/retract discipline): seeded
      from the compiled program; `add-atom` of a rule form asserts a freshly
      compiled clause, `remove-atom` retracts. -/
  progClauses : List (String × Clause) := []
  /-- Derived ordered buckets for executable clause dispatch.  The canonical
      `progClauses` list remains the semantic reference. -/
  clauseIndex : ClauseIndex := ClauseIndex.empty
  /-- False permits legacy/proof fixtures to use the canonical fallback.
      Executable worlds enable the index before processing top-level events. -/
  clauseIndexReady : Bool := false
  /-- Canonical source key aligned with each live clause.  Ordinary clauses
      use their compiled α-key; guarded specializations retain the key of
      their native-visible concretized source, so retraction cannot desync the
      visible atom, captured metadata, and proof-oriented executable IR. -/
  progClauseKeys : List String := []
  /-- Source/IR pairs available to the profile specializer.  Like native
      `fun_meta`, these are newest-first [SPEC translator.pl:18-24]. -/
  metaClauses : List MetaClause := []
  /-- Successfully committed specializations.  A provisional recursive build
      remains local and reaches this registry only on atomic commit.
      [SPEC specializer.pl:27-55] -/
  specializations : List SpecRecord := []
  /-- Write-only provenance for generated executable clauses.  Resolution and
      world actions never inspect it; proofs use it to relate each guarded,
      recursively rewritten clause to the exact captured parent clause. -/
  specClauseProvenance : List SpecClauseProvenance := []
  /-- Source-registered heads/arities known from the parse pass. These guide
      runtime compilation of asserted rules, but `clausesOf` still reads only
      `progClauses`, preserving sequential top-level visibility. -/
  knownHeads : List String := []
  knownArities : List (String × Nat) := []
  /-- Prolog functions made callable by source-level registration. Their
      module paths remain runtime-only; the pure world records names only. -/
  prologFunctions : List String := []
  /-- Heads marked by native `:- table f/n` via `lib_tabling.metta`'s
      `(tabled (f ...))` directive. Cache keys are ground input calls. -/
  tabledArities : List (String × Nat) := []
  tableActive : List Atom := []
  tableCache : List (Atom × List Atom) := []
  /-- Type declarations `(: subject T)` (surface form). -/
  typeDecls : List (Atom × Atom) := []
deriving Repr, Inhabited

def PWorld.atomsOf (w : PWorld) (sp : Atom) : List Atom :=
  if sp == selfSpace then w.selfAtoms.reverse
  else ((w.spaceAtoms.lookup sp).getD []).reverse

def PWorld.derivedSpaceIndices (spaces : List (Atom × List Atom)) :
    List (Atom × SpaceIndex.State) :=
  spaces.map fun entry => (entry.1, SpaceIndex.build entry.2)

/-- A ready mutable-space index is derived exactly from canonical newest-first
    storage.  Disabled worlds are correct by canonical fallback. -/
def PWorld.SpaceIndexCoherent (w : PWorld) : Prop :=
  w.spaceIndexReady = true →
    SpaceIndex.Valid w.selfAtomIndex w.selfAtoms ∧
    w.spaceAtomIndices = derivedSpaceIndices w.spaceAtoms

/-- Enable or rebuild every mutable-space index from canonical state. -/
def PWorld.reindexSpaces (w : PWorld) : PWorld :=
  { w with
      selfAtomIndex := SpaceIndex.build w.selfAtoms
      spaceAtomIndices := derivedSpaceIndices w.spaceAtoms
      spaceIndexReady := true }

/-- Replace newest-first `&self` storage and rebuild its ready index. -/
def PWorld.replaceSelfAtoms (w : PWorld) (atomsNewest : List Atom) : PWorld :=
  { w with
      selfAtoms := atomsNewest
      selfAtomIndex := if w.spaceIndexReady then
        SpaceIndex.build atomsNewest
      else
        w.selfAtomIndex }

def PWorld.setAtoms (w : PWorld) (sp : Atom) (xs : List Atom) : PWorld :=
  if sp == selfSpace then w.replaceSelfAtoms xs.reverse
  else
    let atomsNewest := xs.reverse
    let spaces := (sp, atomsNewest) ::
      (w.spaceAtoms.filter fun entry => entry.1 != sp)
    { w with
        spaceAtoms := spaces
        spaceAtomIndices := if w.spaceIndexReady then
          derivedSpaceIndices spaces
        else
          w.spaceAtomIndices }

def PWorld.addAtom (w : PWorld) (sp a : Atom) : PWorld :=
  if sp == selfSpace then
    { w with
        selfAtoms := a :: w.selfAtoms
        selfAtomIndex := if w.spaceIndexReady then
          SpaceIndex.push w.selfAtomIndex a
        else
          w.selfAtomIndex }
  else
    let xs := (w.spaceAtoms.lookup sp).getD []
    let spaces := (sp, a :: xs) ::
      (w.spaceAtoms.filter fun entry => entry.1 != sp)
    let current := (w.spaceAtomIndices.lookup sp).getD SpaceIndex.empty
    { w with
        spaceAtoms := spaces
        spaceAtomIndices := if w.spaceIndexReady then
          (sp, SpaceIndex.push current a) ::
            (w.spaceAtomIndices.filter fun entry => entry.1 != sp)
        else
          w.spaceAtomIndices }

/-- Add an atom whose insertion metadata has already been computed by the
substitution engine.  Canonical storage remains the raw atom; only the
derived index consumes the prepared fields. -/
def PWorld.addIndexedAtom (w : PWorld) (sp : Atom)
    (prepared : SpaceIndex.IndexedAtom) : PWorld :=
  if sp == selfSpace then
    { w with
        selfAtoms := prepared.atom :: w.selfAtoms
        selfAtomIndex := if w.spaceIndexReady then
          SpaceIndex.pushPrepared w.selfAtomIndex prepared
        else
          w.selfAtomIndex }
  else
    let xs := (w.spaceAtoms.lookup sp).getD []
    let spaces := (sp, prepared.atom :: xs) ::
      (w.spaceAtoms.filter fun entry => entry.1 != sp)
    let current := (w.spaceAtomIndices.lookup sp).getD SpaceIndex.empty
    { w with
        spaceAtoms := spaces
        spaceAtomIndices := if w.spaceIndexReady then
          (sp, SpaceIndex.pushPrepared current prepared) ::
            (w.spaceAtomIndices.filter fun entry => entry.1 != sp)
        else
          w.spaceAtomIndices }

theorem PWorld.addIndexedAtom_eq_addAtom (w : PWorld) (sp : Atom)
    (prepared : SpaceIndex.IndexedAtom) :
    w.addIndexedAtom sp prepared = w.addAtom sp prepared.atom := by
  rw [← SpaceIndex.prepareAtom_atom_eq prepared]
  rfl

def PWorld.removeAtom (w : PWorld) (sp a : Atom) : PWorld :=
  let keep := fun x => (Metta.Unify.unifyTop x a).isNone
  if sp == selfSpace then
    let atomsNewest := w.selfAtoms.filter keep
    { w with
        selfAtoms := atomsNewest
        selfAtomIndex := if w.spaceIndexReady then
          if atomsNewest.length == w.selfAtoms.length then w.selfAtomIndex
          else SpaceIndex.build atomsNewest
        else
          w.selfAtomIndex }
  else
    let xs := (w.spaceAtoms.lookup sp).getD []
    let atomsNewest := xs.filter keep
    let spaces := (sp, atomsNewest) ::
      (w.spaceAtoms.filter fun entry => entry.1 != sp)
    let current := (w.spaceAtomIndices.lookup sp).getD SpaceIndex.empty
    { w with
        spaceAtoms := spaces
        spaceAtomIndices := if w.spaceIndexReady then
          (sp, if atomsNewest.length == xs.length then current
               else SpaceIndex.build atomsNewest) ::
            (w.spaceAtomIndices.filter fun entry => entry.1 != sp)
        else
          w.spaceAtomIndices }

private theorem filter_eq_self_of_length_eq {α : Type} (items : List α)
    (keep : α → Bool) (sameLength : (items.filter keep).length = items.length) :
    items.filter keep = items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases hkeep : keep item
      · simp [List.filter, hkeep] at sameLength
        have hle := List.length_filter_le keep rest
        omega
      · have hrest : (rest.filter keep).length = rest.length := by
          simp only [List.filter_cons_of_pos hkeep, List.length_cons]
            at sameLength
          omega
        simp only [List.filter_cons_of_pos hkeep]
        rw [ih hrest]

/-- Ordered space-match candidates.  The canonical list remains available to
    state and trace operations through `atomsOf`. -/
def PWorld.atomCandidates (w : PWorld) (sp query : Atom) : List Atom :=
  if !w.spaceIndexReady then w.atomsOf sp
  else if sp == selfSpace then
    SpaceIndex.candidates w.selfAtomIndex w.selfAtoms query
  else
    let atomsNewest := (w.spaceAtoms.lookup sp).getD []
    let index := (w.spaceAtomIndices.lookup sp).getD SpaceIndex.empty
    SpaceIndex.candidates index atomsNewest query

/-- Mutable-space candidates paired with insertion-time atom metadata.  The
    raw atom projection is exactly `atomCandidates`; the extra fields only
    avoid rescanning structurally shared terms in the executable matcher. -/
def PWorld.preparedAtomCandidates (w : PWorld) (sp query : Atom) :
    List SpaceIndex.IndexedAtom :=
  if !w.spaceIndexReady then (w.atomsOf sp).map SpaceIndex.prepareAtom
  else if sp == selfSpace then
    SpaceIndex.preparedCandidates w.selfAtomIndex query
  else
    let index := (w.spaceAtomIndices.lookup sp).getD SpaceIndex.empty
    SpaceIndex.preparedCandidates index query

theorem PWorld.derivedSpaceIndices_lookup (spaces : List (Atom × List Atom))
    (sp : Atom) :
    (derivedSpaceIndices spaces).lookup sp =
      (spaces.lookup sp).map SpaceIndex.build := by
  induction spaces with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨space, atoms⟩
      have ih' :
          (rest.map fun entry => (entry.1, SpaceIndex.build entry.2)).lookup sp =
            (rest.lookup sp).map SpaceIndex.build := by
        simpa [derivedSpaceIndices] using ih
      cases hmatch : sp == space <;>
        simp [derivedSpaceIndices, List.lookup_cons, hmatch, ih']

theorem PWorld.derivedSpaceIndices_lookup_getD
    (spaces : List (Atom × List Atom)) (sp : Atom) :
    ((derivedSpaceIndices spaces).lookup sp).getD SpaceIndex.empty =
      SpaceIndex.build ((spaces.lookup sp).getD []) := by
  rw [derivedSpaceIndices_lookup]
  cases spaces.lookup sp <;> rfl

theorem PWorld.derivedSpaceIndices_filter (spaces : List (Atom × List Atom))
    (sp : Atom) :
    derivedSpaceIndices (spaces.filter fun entry => entry.1 != sp) =
      (derivedSpaceIndices spaces).filter fun entry => entry.1 != sp := by
  induction spaces with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨space, atoms⟩
      have ih' := by
        simpa [derivedSpaceIndices] using ih
      cases hkeep : space != sp <;>
        simp [derivedSpaceIndices, hkeep, ih']

theorem PWorld.reindexSpaces_coherent (w : PWorld) :
    w.reindexSpaces.SpaceIndexCoherent := by
  intro _
  exact ⟨SpaceIndex.build_valid w.selfAtoms, rfl⟩

theorem PWorld.replaceSelfAtoms_spaceCoherent (w : PWorld)
    (atomsNewest : List Atom) (coherent : w.SpaceIndexCoherent) :
    (w.replaceSelfAtoms atomsNewest).SpaceIndexCoherent := by
  intro hready
  have hsource : w.spaceIndexReady = true := hready
  rcases coherent hsource with ⟨_, hnamed⟩
  constructor
  · unfold replaceSelfAtoms
    simp [hsource, SpaceIndex.Valid]
  · exact hnamed

theorem PWorld.setAtoms_spaceCoherent (w : PWorld) (space : Atom)
    (atoms : List Atom) (coherent : w.SpaceIndexCoherent) :
    (w.setAtoms space atoms).SpaceIndexCoherent := by
  unfold setAtoms
  split
  · exact replaceSelfAtoms_spaceCoherent w atoms.reverse coherent
  · intro hready
    change w.spaceIndexReady = true at hready
    dsimp only
    constructor
    · exact (coherent hready).1
    · rw [if_pos hready]

theorem PWorld.addAtom_spaceCoherent (w : PWorld) (space atom : Atom)
    (coherent : w.SpaceIndexCoherent) :
    (w.addAtom space atom).SpaceIndexCoherent := by
  unfold addAtom
  split
  · intro hready
    change w.spaceIndexReady = true at hready
    rcases coherent hready with ⟨hself, hnamed⟩
    constructor
    · rw [if_pos hready]
      exact hself.push atom
    · exact hnamed
  · dsimp only
    intro hready
    change w.spaceIndexReady = true at hready
    rcases coherent hready with ⟨hself, hnamed⟩
    constructor
    · exact hself
    · rw [if_pos hready]
      let xs := (w.spaceAtoms.lookup space).getD []
      have hcurrent :
          ((w.spaceAtoms.map fun entry =>
              (entry.1, SpaceIndex.build entry.2)).lookup space).getD
                SpaceIndex.empty =
            SpaceIndex.build xs := by
        simpa [derivedSpaceIndices] using
          derivedSpaceIndices_lookup_getD w.spaceAtoms space
      have hfilter :
          (w.spaceAtoms.map fun entry =>
              (entry.1, SpaceIndex.build entry.2)).filter
                (fun entry => entry.1 != space) =
            (w.spaceAtoms.filter fun entry => entry.1 != space).map
              (fun entry => (entry.1, SpaceIndex.build entry.2)) := by
        simpa [derivedSpaceIndices] using
          (derivedSpaceIndices_filter w.spaceAtoms space).symm
      change
        (space, SpaceIndex.push
            ((w.spaceAtomIndices.lookup space).getD SpaceIndex.empty) atom) ::
            (w.spaceAtomIndices.filter fun entry => entry.1 != space) =
          derivedSpaceIndices
            ((space, atom :: xs) ::
              (w.spaceAtoms.filter fun entry => entry.1 != space))
      rw [hnamed]
      simp only [derivedSpaceIndices, List.map_cons]
      rw [hfilter]
      congr 1
      rw [hcurrent]
      rfl

theorem PWorld.removeAtom_spaceCoherent (w : PWorld) (space atom : Atom)
    (coherent : w.SpaceIndexCoherent) :
    (w.removeAtom space atom).SpaceIndexCoherent := by
  unfold removeAtom
  dsimp only
  split
  · intro hready
    change w.spaceIndexReady = true at hready
    rcases coherent hready with ⟨hself, hnamed⟩
    constructor
    · rw [if_pos hready]
      split
      next hsame =>
        have hlength :
            (w.selfAtoms.filter fun x =>
              (Metta.Unify.unifyTop x atom).isNone).length =
                w.selfAtoms.length := by
          simpa using hsame
        rw [filter_eq_self_of_length_eq w.selfAtoms _ hlength]
        exact hself
      next _ => exact SpaceIndex.build_valid _
    · exact hnamed
  · intro hready
    change w.spaceIndexReady = true at hready
    rcases coherent hready with ⟨hself, hnamed⟩
    constructor
    · exact hself
    · rw [if_pos hready]
      let keep := fun x => (Metta.Unify.unifyTop x atom).isNone
      let xs := (w.spaceAtoms.lookup space).getD []
      let atomsNewest := xs.filter keep
      let current :=
        (w.spaceAtomIndices.lookup space).getD SpaceIndex.empty
      have hcurrent :
          ((w.spaceAtoms.map fun entry =>
              (entry.1, SpaceIndex.build entry.2)).lookup space).getD
                SpaceIndex.empty =
            SpaceIndex.build xs := by
        simpa [derivedSpaceIndices] using
          derivedSpaceIndices_lookup_getD w.spaceAtoms space
      have hfilter :
          (w.spaceAtoms.map fun entry =>
              (entry.1, SpaceIndex.build entry.2)).filter
                (fun entry => entry.1 != space) =
            (w.spaceAtoms.filter fun entry => entry.1 != space).map
              (fun entry => (entry.1, SpaceIndex.build entry.2)) := by
        simpa [derivedSpaceIndices] using
          (derivedSpaceIndices_filter w.spaceAtoms space).symm
      change
        (space, if atomsNewest.length == xs.length then current
                else SpaceIndex.build atomsNewest) ::
            (w.spaceAtomIndices.filter fun entry => entry.1 != space) =
          derivedSpaceIndices
            ((space, atomsNewest) ::
              (w.spaceAtoms.filter fun entry => entry.1 != space))
      rw [hnamed]
      simp only [derivedSpaceIndices, List.map_cons]
      rw [hfilter]
      congr 1
      apply Prod.ext
      · rfl
      · dsimp only
        split
        next hsame =>
          have hlength : atomsNewest.length = xs.length := by
            simpa using hsame
          have hatoms : atomsNewest = xs :=
            filter_eq_self_of_length_eq xs keep hlength
          rw [hatoms]
          dsimp [current]
          rw [hnamed]
          exact hcurrent
        next _ => rfl

theorem PWorld.selfAtomIndex_valid (w : PWorld)
    (coherent : w.SpaceIndexCoherent)
    (hready : w.spaceIndexReady = true) :
    SpaceIndex.Valid w.selfAtomIndex w.selfAtoms :=
  (coherent hready).1

theorem PWorld.namedAtomIndex_valid (w : PWorld) (space : Atom)
    (coherent : w.SpaceIndexCoherent)
    (hready : w.spaceIndexReady = true) :
    SpaceIndex.Valid
      ((w.spaceAtomIndices.lookup space).getD SpaceIndex.empty)
      ((w.spaceAtoms.lookup space).getD []) := by
  rw [(coherent hready).2, derivedSpaceIndices_lookup_getD]
  exact SpaceIndex.build_valid _

/-- Prepared candidate metadata erases to the existing ordered candidate
    snapshot, including disabled-index and named-space fallbacks. -/
theorem PWorld.preparedAtomCandidates_eq (w : PWorld) (space query : Atom)
    : w.preparedAtomCandidates space query =
      (w.atomCandidates space query).map SpaceIndex.prepareAtom := by
  unfold preparedAtomCandidates atomCandidates SpaceIndex.candidates
  split
  · simp [*]
  · split <;> simp [*, Function.comp_def]

/-- A coherent derived space index never returns more candidates than exist
    in canonical storage.  This is also immediate for the disabled-index
    fallback, which returns the canonical list itself. -/
theorem PWorld.atomCandidates_length_le (w : PWorld)
    (space query : Atom) (coherent : w.SpaceIndexCoherent) :
    (w.atomCandidates space query).length ≤ (w.atomsOf space).length := by
  by_cases hready : w.spaceIndexReady = true
  · unfold atomCandidates atomsOf
    simp only [hready, Bool.not_true]
    by_cases hself : space == selfSpace
    · simp only [hself, if_true, List.length_reverse]
      exact SpaceIndex.Valid.candidates_length_le
        (w.selfAtomIndex_valid coherent hready) query
    · simp only [hself, Bool.false_eq_true, if_false, List.length_reverse]
      exact SpaceIndex.Valid.candidates_length_le
        (w.namedAtomIndex_valid space coherent hready) query
  · have hfalse : w.spaceIndexReady = false := by
      cases hvalue : w.spaceIndexReady
      · rfl
      · exact False.elim (hready hvalue)
    simp [atomCandidates, hfalse]

/-- Independent denotation theorem for mutable-space candidate pruning. -/
theorem PWorld.atomCandidates_filter_compatible (w : PWorld)
    (space query : Atom) (coherent : w.SpaceIndexCoherent) :
    (w.atomCandidates space query).filter (SpaceIndex.compatible query) =
      (w.atomsOf space).filter (SpaceIndex.compatible query) := by
  by_cases hready : w.spaceIndexReady = true
  · unfold atomCandidates atomsOf
    simp only [hready, Bool.not_true]
    by_cases hself : space == selfSpace
    · simp only [hself, if_true]
      exact (w.selfAtomIndex_valid coherent hready).filteredCandidates query
    · simp only [hself]
      exact (w.namedAtomIndex_valid space coherent hready).filteredCandidates
        query
  · have hfalse : w.spaceIndexReady = false := by
      cases hvalue : w.spaceIndexReady
      · rfl
      · exact False.elim (hready hvalue)
    simp [atomCandidates, hfalse]

def PWorld.clausesOf (w : PWorld) (f : String) : List Clause :=
  w.progClauses.filterMap (fun (n, c) => if n == f then some c else none)

/-- The derived live-clause index agrees with the canonical list whenever it
    is enabled.  Disabled worlds are correct by canonical fallback. -/
def PWorld.ClauseIndexCoherent (w : PWorld) : Prop :=
  w.clauseIndexReady = true → ClauseIndex.Valid w.clauseIndex w.progClauses

/-- Enable or rebuild the derived clause index from canonical state. -/
def PWorld.reindexClauses (w : PWorld) : PWorld :=
  { w with
      clauseIndex := ClauseIndex.build w.progClauses
      clauseIndexReady := true }

/-- Append one live clause while preserving a ready index in O(1) per bucket.
    Disabled proof fixtures continue to use the canonical fallback. -/
def PWorld.appendProgClause (w : PWorld) (entry : String × Clause) : PWorld :=
  if w.clauseIndexReady then
    { w with
        progClauses := w.progClauses ++ [entry]
        clauseIndex := ClauseIndex.push w.clauseIndex entry }
  else
    { w with progClauses := w.progClauses ++ [entry] }

/-- Replace the canonical live-clause list, rebuilding a previously enabled
    index.  Retraction and transitive invalidation use this path. -/
def PWorld.replaceProgClauses (w : PWorld)
    (clauses : List (String × Clause)) : PWorld :=
  if w.clauseIndexReady then
    { w with
        progClauses := clauses
        clauseIndex := ClauseIndex.build clauses }
  else
    { w with progClauses := clauses }

/-- Head-only dispatch in exact canonical order. -/
def PWorld.clauseHeadCandidates (w : PWorld) (f : String) : List Clause :=
  if w.clauseIndexReady then
    ClauseIndex.headCandidates w.clauseIndex f
  else
    w.clausesOf f

/-- Head-and-arity dispatch in exact canonical order. -/
def PWorld.clauseCandidates (w : PWorld) (f : String) (arity : Nat) :
    List Clause :=
  if w.clauseIndexReady then
    ClauseIndex.candidates w.clauseIndex f arity
  else
    (w.clausesOf f).filter fun clause => clause.params.length == arity

/-- Resolution candidates.  Indexed executable worlds receive only the
    selected head-and-arity bucket.  Disabled proof fixtures retain the old
    head-only list, whose arity check remains inside `resolveAlts`. -/
def PWorld.resolutionCandidates (w : PWorld) (f : String) (arity : Nat) :
    List Clause :=
  if w.clauseIndexReady then
    ClauseIndex.candidates w.clauseIndex f arity
  else
    w.clausesOf f

@[simp] theorem PWorld.clauseHeadCandidates_of_not_ready (w : PWorld)
    (f : String) (hready : w.clauseIndexReady = false) :
    w.clauseHeadCandidates f = w.clausesOf f := by
  simp [clauseHeadCandidates, hready]

@[simp] theorem PWorld.clauseCandidates_of_not_ready (w : PWorld)
    (f : String) (arity : Nat) (hready : w.clauseIndexReady = false) :
    w.clauseCandidates f arity =
      (w.clausesOf f).filter fun clause =>
        clause.params.length == arity := by
  simp [clauseCandidates, hready]

@[simp] theorem PWorld.resolutionCandidates_of_not_ready (w : PWorld)
    (f : String) (arity : Nat) (hready : w.clauseIndexReady = false) :
    w.resolutionCandidates f arity = w.clausesOf f := by
  simp [resolutionCandidates, hready]

@[simp] theorem PWorld.replaceProgClauses_progClauses (w : PWorld)
    (clauses : List (String × Clause)) :
    (w.replaceProgClauses clauses).progClauses = clauses := by
  cases hready : w.clauseIndexReady <;>
    simp [replaceProgClauses, hready]

theorem PWorld.reindexClauses_coherent (w : PWorld) :
    w.reindexClauses.ClauseIndexCoherent := by
  intro _
  exact ClauseIndex.build_valid w.progClauses

theorem PWorld.appendProgClause_coherent (w : PWorld)
    (entry : String × Clause) (coherent : w.ClauseIndexCoherent) :
    (w.appendProgClause entry).ClauseIndexCoherent := by
  unfold appendProgClause ClauseIndexCoherent
  split
  next hready =>
    intro _
    exact (coherent hready).push entry
  next hready =>
    intro hfalse
    simp [hready] at hfalse

theorem PWorld.replaceProgClauses_coherent (w : PWorld)
    (clauses : List (String × Clause)) (_coherent : w.ClauseIndexCoherent) :
    (w.replaceProgClauses clauses).ClauseIndexCoherent := by
  unfold replaceProgClauses ClauseIndexCoherent
  split
  next _ =>
    intro _
    exact ClauseIndex.build_valid clauses
  next hready =>
    intro hfalse
    simp [hready] at hfalse

theorem PWorld.appendProgClause_spaceCoherent (w : PWorld)
    (entry : String × Clause) (coherent : w.SpaceIndexCoherent) :
    (w.appendProgClause entry).SpaceIndexCoherent := by
  unfold appendProgClause
  split <;> exact coherent

theorem PWorld.replaceProgClauses_spaceCoherent (w : PWorld)
    (clauses : List (String × Clause)) (coherent : w.SpaceIndexCoherent) :
    (w.replaceProgClauses clauses).SpaceIndexCoherent := by
  unfold replaceProgClauses
  split <;> exact coherent

theorem PWorld.setAtoms_coherent (w : PWorld) (space : Atom) (atoms : List Atom)
    (coherent : w.ClauseIndexCoherent) :
    (w.setAtoms space atoms).ClauseIndexCoherent := by
  unfold setAtoms
  split
  · unfold replaceSelfAtoms
    split <;> exact coherent
  · split <;> exact coherent

theorem PWorld.addAtom_coherent (w : PWorld) (space atom : Atom)
    (coherent : w.ClauseIndexCoherent) :
    (w.addAtom space atom).ClauseIndexCoherent := by
  unfold addAtom
  split
  · split <;> exact coherent
  · dsimp only
    split <;> exact coherent

theorem PWorld.removeAtom_coherent (w : PWorld) (space atom : Atom)
    (coherent : w.ClauseIndexCoherent) :
    (w.removeAtom space atom).ClauseIndexCoherent := by
  unfold removeAtom
  dsimp only
  split <;> exact coherent

/-- Independent denotation theorem for head-only indexed selection. -/
theorem PWorld.clauseHeadCandidates_eq_clausesOf (w : PWorld) (f : String)
    (coherent : w.ClauseIndexCoherent) :
    w.clauseHeadCandidates f = w.clausesOf f := by
  unfold clauseHeadCandidates
  split
  next hready =>
    rw [(coherent hready).headCandidates]
    rfl
  next _ => rfl

/-- Independent denotation theorem for head-and-arity indexed selection. -/
theorem PWorld.clauseCandidates_eq_filter (w : PWorld) (f : String)
    (arity : Nat) (coherent : w.ClauseIndexCoherent) :
    w.clauseCandidates f arity =
      (w.clausesOf f).filter fun clause =>
        clause.params.length == arity := by
  unfold clauseCandidates
  split
  next hready =>
    rw [(coherent hready).candidates]
    exact ClauseIndex.naiveCandidates_eq_head_filter w.progClauses f arity
  next _ => rfl

theorem PWorld.resolutionCandidates_eq (w : PWorld) (f : String)
    (arity : Nat) (coherent : w.ClauseIndexCoherent) :
    w.resolutionCandidates f arity =
      if w.clauseIndexReady then
        (w.clausesOf f).filter fun clause => clause.params.length == arity
      else
        w.clausesOf f := by
  unfold resolutionCandidates
  split
  next hready =>
    rw [(coherent hready).candidates]
    exact ClauseIndex.naiveCandidates_eq_head_filter w.progClauses f arity
  next _ => rfl

/-- Capture a live ordinary rule for specialization, preserving native
    newest-first metadata order.  Non-rule sources leave the world unchanged. -/
def PWorld.captureMeta (w : PWorld) (source : Atom) (compiled : Clause) :
    PWorld :=
  match MetaClause.ofRule? source compiled with
  | some mc => { w with metaClauses := mc :: w.metaClauses }
  | none => w

/-- Capture executable metadata while retaining a distinct α-key for the
    visible source clause.  Generated specializations need both identities:
    executable IR for recursive specialization, source IR for retraction. -/
def PWorld.captureMetaWithSourceKey (w : PWorld) (source : Atom)
    (compiled : Clause) (sourceKey : String) : PWorld :=
  match MetaClause.ofRule? source compiled with
  | some mc =>
      { w with metaClauses := { mc with sourceKey } :: w.metaClauses }
  | none => w

theorem PWorld.captureMeta_coherent (w : PWorld) (source : Atom)
    (compiled : Clause) (coherent : w.ClauseIndexCoherent) :
    (w.captureMeta source compiled).ClauseIndexCoherent := by
  unfold captureMeta
  split <;> exact coherent

theorem PWorld.captureMeta_spaceCoherent (w : PWorld) (source : Atom)
    (compiled : Clause) (coherent : w.SpaceIndexCoherent) :
    (w.captureMeta source compiled).SpaceIndexCoherent := by
  unfold captureMeta
  split <;> exact coherent

theorem PWorld.captureMetaWithSourceKey_coherent (w : PWorld)
    (source : Atom) (compiled : Clause) (sourceKey : String)
    (coherent : w.ClauseIndexCoherent) :
    (w.captureMetaWithSourceKey source compiled sourceKey).ClauseIndexCoherent := by
  unfold captureMetaWithSourceKey
  split <;> exact coherent

theorem PWorld.captureMetaWithSourceKey_spaceCoherent (w : PWorld)
    (source : Atom) (compiled : Clause) (sourceKey : String)
    (coherent : w.SpaceIndexCoherent) :
    (w.captureMetaWithSourceKey source compiled sourceKey).SpaceIndexCoherent := by
  unfold captureMetaWithSourceKey
  split <;> exact coherent

def PWorld.compileHeads (w : PWorld) : List String :=
  (w.knownHeads ++ w.progClauses.map (·.1)).eraseDups

def PWorld.compileArities (w : PWorld) : List (String × Nat) :=
  w.knownArities ++
    w.progClauses.map (fun (p : String × Clause) => (p.1, p.2.params.length))

def tableKey (f : String) (args : List Atom) : Atom :=
  Atom.expr (Atom.sym f :: args)

def PWorld.isTabled (w : PWorld) (f : String) (arity : Nat) : Bool :=
  w.tabledArities.any (fun p => p.1 == f && p.2 == arity)

def PWorld.tableLookup (w : PWorld) (key : Atom) : Option (List Atom) :=
  w.tableCache.lookup key

def PWorld.tableInsert (w : PWorld) (key : Atom) (answers : List Atom) : PWorld :=
  { w with tableCache := (key, answers) ::
      (w.tableCache.filter (fun p => p.1 != key)) }

def PWorld.canTableCall (w : PWorld) (f : String) (argsv : List Atom) : Bool :=
  w.isTabled f argsv.length && argsv.all Metta.isGround &&
    !(w.tableActive.contains (tableKey f argsv))

def PWorld.needsTableCompute (w : PWorld) (f : String) (argsv : List Atom) : Bool :=
  w.canTableCall f argsv && (w.tableLookup (tableKey f argsv)).isNone

def PWorld.deactivateTable (w : PWorld) (key : Atom) : PWorld :=
  { w with tableActive := w.tableActive.filter (fun k => k != key) }

/-- One pending alternative, or a clause barrier (choice-point marker). -/
inductive Alt (Binding : Type := Subst) where
  | br (goals : List Goal) (bnd : Binding)
  | barrier
deriving Repr, Inhabited

def nilExactKey : PersistentSubst.AtomExactKey :=
  mixHash 1 (hash "#nil")

def consExactKey (head tail : PersistentSubst.AtomExactKey) :
    PersistentSubst.AtomExactKey :=
  mixHash 8
    (mixHash (mixHash 10 (mixHash 1 (hash "#c")))
      (mixHash (mixHash 10 head) (mixHash (mixHash 10 tail) 9)))

def chainExactKeys : List (Option PersistentSubst.AtomExactKey) →
    Option PersistentSubst.AtomExactKey
  | [] => some nilExactKey
  | none :: _ => none
  | some head :: rest =>
      (chainExactKeys rest).map (consExactKey head)

theorem chainExactKeys_sound (atoms : List Atom) :
    chainExactKeys (atoms.map PersistentSubst.atomExactKey) =
      PersistentSubst.atomExactKey (chainOf atoms) := by
  induction atoms with
  | nil => simp [chainExactKeys, chainOf, nilA, nilExactKey,
      PersistentSubst.atomExactKey]
  | cons atom rest ih =>
      change chainExactKeys
          (PersistentSubst.atomExactKey atom ::
            rest.map PersistentSubst.atomExactKey) =
        PersistentSubst.atomExactKey (consC atom (chainOf rest))
      cases head : PersistentSubst.atomExactKey atom with
      | none =>
          simp [chainExactKeys, head, consC,
            PersistentSubst.atomExactKey,
            PersistentSubst.atomExactKeyList]
      | some key =>
          simp only [chainExactKeys]
          rw [ih]
          cases tail : PersistentSubst.atomExactKey (chainOf rest) with
          | none =>
              simp [head, tail, consC, PersistentSubst.atomExactKey,
                PersistentSubst.atomExactKeyList]
          | some tailKey =>
              simp [head, tail, consC, consExactKey,
                PersistentSubst.atomExactKey,
                PersistentSubst.atomExactKeyList]

/-- Machine configuration. `qterm` is the term whose instances are answers.
`answers` is an internal reverse accumulator; use `answerValues` whenever a
completed nested or top-level run publishes its answers. -/
structure Conf (Binding : Type := Subst) where
  cur : Option (List Goal × Binding)
  alts : List (Alt Binding)
  world : PWorld
  counter : Nat
  qterm : Atom
  answers : List Atom := []
  /-- Exact keys parallel to the reverse answer accumulator.  The executable
  obtains these from prepared results, so nested collectors can summarize a
  shared answer DAG without walking it again. -/
  answerKeys : List (Option PersistentSubst.AtomExactKey) :=
    answers.map PersistentSubst.atomExactKey
  answerKeys_sound :
    answerKeys = answers.map PersistentSubst.atomExactKey := by rfl
  /-- Optional cached number of clause barriers in `alts`. `none` is the
  reference path and derives the count from `alts`; executable entry points
  seed `some 0` and preserve an exact count without rescanning the stack. -/
  barriers : Option Nat := none
deriving Repr, Inhabited

@[ext] theorem Conf.ext {Binding : Type} {left right : Conf Binding}
    (cur : left.cur = right.cur) (alts : left.alts = right.alts)
    (world : left.world = right.world) (counter : left.counter = right.counter)
    (qterm : left.qterm = right.qterm) (answers : left.answers = right.answers)
    (answerKeys : left.answerKeys = right.answerKeys)
    (barriers : left.barriers = right.barriers) : left = right := by
  cases left
  cases right
  simp_all

/-- Answers in discovery order.  Reversing once at a run boundary makes each
internal answer insertion constant time while preserving PeTTa order. -/
def Conf.answerValues {Binding : Type} (conf : Conf Binding) : List Atom :=
  conf.answers.reverse

def Conf.answerKeyValues {Binding : Type} (conf : Conf Binding) :
    List (Option PersistentSubst.AtomExactKey) :=
  conf.answerKeys.reverse

theorem Conf.answerKeyValues_sound {Binding : Type} (conf : Conf Binding) :
    conf.answerKeyValues =
      conf.answerValues.map PersistentSubst.atomExactKey := by
  unfold answerKeyValues answerValues
  rw [conf.answerKeys_sound, List.map_reverse]

/-- Variable-name surface used to seed and state the monotone resolution-name
invariant. Derived indices and string-valued function names are omitted: they
either duplicate canonical atoms/clauses or are not variable names. -/
def resolutionClauseVars (clause : Clause) : List String :=
  clause.params.flatMap Atom.vars ++ clause.result.vars ++
    specializationGoalsVars clause.body

def resolutionSubstVars (binding : Subst) : List String :=
  binding.flatMap fun entry => entry.1 :: entry.2.vars

def resolutionMetaClauseVars (metaClause : MetaClause) : List String :=
  metaClause.sourceParams.flatMap Atom.vars ++ metaClause.sourceBody.vars ++
    resolutionClauseVars metaClause.compiled

def resolutionSpecRecordVars (record : SpecRecord) : List String :=
  record.key.bindings.flatMap Atom.vars

def resolutionProvenanceVars (provenance : SpecClauseProvenance) :
    List String :=
  resolutionClauseVars provenance.parentClause ++
    resolutionSubstVars provenance.sourceBinding ++
    provenance.discoveryActuals.flatMap Atom.vars ++
    resolutionSubstVars provenance.binding ++
    resolutionClauseVars provenance.guardedClause ++
    resolutionClauseVars provenance.executableClause

def resolutionWorldVars (world : PWorld) : List String :=
  world.selfAtoms.flatMap Atom.vars ++
    world.spaceAtoms.flatMap (fun entry =>
      entry.1.vars ++ entry.2.flatMap Atom.vars) ++
    world.store.flatMap (fun entry => entry.1.vars ++ entry.2.vars) ++
    world.progClauses.flatMap (fun entry => resolutionClauseVars entry.2) ++
    world.metaClauses.flatMap resolutionMetaClauseVars ++
    world.specializations.flatMap resolutionSpecRecordVars ++
    world.specClauseProvenance.flatMap resolutionProvenanceVars ++
    world.tableActive.flatMap Atom.vars ++
    world.tableCache.flatMap (fun entry =>
      entry.1.vars ++ entry.2.flatMap Atom.vars) ++
    world.typeDecls.flatMap (fun entry => entry.1.vars ++ entry.2.vars)

def resolutionAltVars : Alt → List String
  | .barrier => []
  | .br goals binding =>
      specializationGoalsVars goals ++ resolutionSubstVars binding

def resolutionConfVars (conf : Conf) : List String :=
  (match conf.cur with
    | none => []
    | some (goals, binding) =>
        specializationGoalsVars goals ++ resolutionSubstVars binding) ++
  conf.alts.flatMap resolutionAltVars ++ resolutionWorldVars conf.world ++
  conf.qterm.vars ++ conf.answers.flatMap Atom.vars

/-- Variable names that can collide with the next standardized-apart clause.
Stored world atoms and clauses are excluded because they cross into this
surface only after suffix-renaming or an explicit counter advance. -/
def resolutionLiveVars (conf : Conf) : List String :=
  (match conf.cur with
    | none => []
    | some (goals, binding) =>
        specializationGoalsVars goals ++ resolutionSubstVars binding) ++
  conf.alts.flatMap resolutionAltVars ++
  conf.qterm.vars ++ conf.answers.flatMap Atom.vars

def resolutionLiveHighWater (conf : Conf) : Nat :=
  resolutionSeedHighWaterNames (resolutionLiveVars conf)

def advanceCounterPastGoals (counter : Nat) (goals : List Goal) : Nat :=
  max counter (resolutionSeedHighWaterNames (specializationGoalsVars goals))

def resolutionProgVars (prog : Prog) : List String :=
  prog.clauses.flatMap (fun entry => resolutionClauseVars entry.2) ++
    prog.facts.flatMap Atom.vars ++
    prog.typeDecls.flatMap (fun entry => entry.1.vars ++ entry.2.vars)

def resolutionConfHighWater (prog : Prog) (conf : Conf) : Nat :=
  resolutionSeedHighWaterNames
    (resolutionProgVars prog ++ resolutionConfVars conf)

def trueA : Atom := Atom.sym "True"

private theorem substLookup_mem (b : Subst) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup b name = some value) :
    (name, value) ∈ b := by
  induction b with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, target⟩
      by_cases heq : name = key
      · subst key
        simp only [Metta.Subst.lookup, beq_self_eq_true, if_true,
          Option.some.injEq] at hlookup
        subst target
        simp
      · have hbeq : (name == key) = false := by simp [heq]
        simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          at hlookup
        exact List.mem_cons_of_mem (key, target) (ih hlookup)

/-- `runtime` propositionally realizes every lookup performed by `binding`.
    This is the finite-substitution interface used to compose deep unifiers
    without exposing `substN`'s implementation fuel. -/
def SubstLookupDenotes (runtime binding : Subst) : Prop :=
  ∀ name value, Metta.Subst.lookup binding name = some value →
    subst runtime (Atom.var name) = subst runtime value

private theorem atomSize_le_sum_of_mem {a : Atom} : (xs : List Atom) →
    a ∈ xs → a.size ≤ (xs.map Atom.size).sum
  | [], h => by simp at h
  | x :: xs, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (atomSize_le_sum_of_mem xs h)
          (Nat.le_add_left _ _)

@[elab_as_elim, induction_eliminator]
private def machineAtomRecAux {motive : Atom → Prop}
    (sym : ∀ s, motive (Atom.sym s))
    (var : ∀ v, motive (Atom.var v))
    (gnd : ∀ g, motive (Atom.gnd g))
    (expr : ∀ xs, (∀ a ∈ xs, motive a) → motive (Atom.expr xs)) :
    (a : Atom) → motive a
  | .sym s => sym s
  | .var v => var v
  | .gnd g => gnd g
  | .expr xs => expr xs (fun a _ha => machineAtomRecAux sym var gnd expr a)
termination_by a => a.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using
    Nat.lt_add_one_of_le (atomSize_le_sum_of_mem xs _ha)

private theorem substN_vars_origin (b : Subst) :
    ∀ fuel atom name, name ∈ (substN fuel b atom).vars →
      name ∈ atom.vars ∨
        name ∈ b.flatMap (fun entry => entry.2.vars) := by
  intro fuel
  induction fuel with
  | zero =>
      intro atom name hname
      exact Or.inl (by simpa [substN] using hname)
  | succ fuel fuelIH =>
      intro atom
      induction atom using machineAtomRecAux with
      | sym symbol => simp [substN, Atom.vars]
      | gnd ground => simp [substN, Atom.vars]
      | var source =>
          intro name hname
          cases hlookup : Metta.Subst.lookup b source with
          | none =>
              simp only [substN, hlookup, Atom.vars, List.mem_singleton] at hname
              subst name
              exact Or.inl (by simp [Atom.vars])
          | some value =>
              simp only [substN, hlookup] at hname
              rcases fuelIH value name hname with hvalue | hrange
              · exact Or.inr (by
                  simp only [List.mem_flatMap]
                  exact ⟨(source, value), substLookup_mem b source value hlookup,
                    hvalue⟩)
              · exact Or.inr hrange
      | expr atoms atomIH =>
          intro name hname
          simp only [substN, Atom.vars] at hname
          rw [List.mem_flatten] at hname
          obtain ⟨variableList, hvariableList, hname⟩ := hname
          rcases List.mem_map.mp hvariableList with
            ⟨substitutedChild, hsubstitutedChild, rfl⟩
          rcases List.mem_map.mp hsubstitutedChild with
            ⟨child, hchild, rfl⟩
          rcases atomIH child hchild name hname with hsource | hrange
          · exact Or.inl (by
              simp only [Atom.vars, List.mem_flatten, List.mem_map]
              exact ⟨child.vars, ⟨child, hchild, rfl⟩, hsource⟩)
          · exact Or.inr hrange

/-- Deep substitution cannot invent variable names: every variable in its
    output came from the input atom or from a stored substitution value. -/
theorem subst_vars_origin (b : Subst) (atom : Atom) (name : String)
    (hname : name ∈ (subst b atom).vars) :
    name ∈ atom.vars ∨
      name ∈ b.flatMap (fun entry => entry.2.vars) := by
  exact substN_vars_origin b (b.length + 1) atom name hname

private theorem substN_nil_succ (k : Nat) : (a : Atom) →
    substN (k + 1) [] a = a
  | .sym _ => by simp [substN]
  | .var _ => by simp [substN, Metta.Subst.lookup]
  | .gnd _ => by simp [substN]
  | .expr xs => by
      simp only [substN, Atom.expr.injEq]
      rw [List.map_congr_left (fun a ha => substN_nil_succ k a)]
      simp
termination_by a => a.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using
    Nat.lt_add_one_of_le (atomSize_le_sum_of_mem xs ha)

theorem substN_of_closed (k : Nat) (b : Subst) : (a : Atom) →
    a.vars = [] → substN k b a = a
  | .sym _, _ => by cases k <;> simp [substN]
  | .var x, h => by simp [Atom.vars] at h
  | .gnd _, _ => by cases k <;> simp [substN]
  | .expr xs, h => by
      cases k with
      | zero => simp [substN]
      | succ k =>
          simp only [substN, Atom.expr.injEq]
          simp only [Atom.vars] at h
          rw [List.flatten_eq_nil_iff] at h
          have hx : ∀ a ∈ xs, substN (k + 1) b a = a := by
            intro a ha
            apply substN_of_closed (k + 1) b a
            exact h (Atom.vars a) (List.mem_map_of_mem ha)
          rw [List.map_congr_left hx]
          simp
termination_by a => a.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using
    Nat.lt_add_one_of_le (atomSize_le_sum_of_mem xs ha)

@[simp] theorem subst_nil (a : Atom) : subst [] a = a := by
  exact substN_nil_succ 0 a

/-- Deep substitution fixes a variable-free atom.  This is the semantic fact
    needed to discharge specialization guards whose captured values are
    concrete. -/
@[simp] theorem subst_of_closed (b : Subst) (a : Atom) (h : a.vars = []) :
    subst b a = a := by
  exact substN_of_closed (b.length + 1) b a h

@[simp] theorem subst_var_of_lookup_closed (b : Subst) (x : String) (a : Atom)
    (hlookup : Metta.Subst.lookup b x = some a) (hclosed : a.vars = []) :
    subst b (Atom.var x) = a := by
  simp [subst, substN, hlookup, substN_of_closed _ b a hclosed]

private theorem substN_sym (k : Nat) (b : Subst) (f : String) :
    substN k b (Atom.sym f) = Atom.sym f := by
  cases k <;> simp [substN]

@[simp] theorem subst_var_of_lookup_sym (b : Subst) (x f : String)
    (h : Metta.Subst.lookup b x = some (Atom.sym f)) :
    subst b (Atom.var x) = Atom.sym f := by
  simp [subst, substN, h, substN_sym]

@[simp] theorem subst_var_of_lookup_none (b : Subst) (x : String)
    (h : Metta.Subst.lookup b x = none) :
    subst b (Atom.var x) = Atom.var x := by
  simp [subst, substN, h]

@[simp] theorem subst_sym (b : Subst) (f : String) :
    subst b (Atom.sym f) = Atom.sym f := by
  simp [subst, substN]

@[simp] theorem subst_gnd (b : Subst) (g : Metta.Ground) :
    subst b (Atom.gnd g) = Atom.gnd g := by
  simp [subst, substN]

@[simp] theorem subst_expr (b : Subst) (xs : List Atom) :
    subst b (Atom.expr xs) = Atom.expr (xs.map (subst b)) := by
  simp [subst, substN]

/-- One-pass application is invisible under a runtime substitution that
    realizes every lookup of the applied binding. -/
theorem subst_apply_of_lookupDenotes (runtime binding : Subst)
    (hdenotes : SubstLookupDenotes runtime binding) (atom : Atom) :
    subst runtime (Metta.Subst.apply binding atom) = subst runtime atom := by
  induction atom using machineAtomRecAux with
  | sym symbol => simp [Metta.Subst.apply]
  | gnd ground => simp [Metta.Subst.apply]
  | var name =>
      simp only [Metta.Subst.apply]
      cases hlookup : Metta.Subst.lookup binding name with
      | none => simp
      | some value =>
          simp only [Option.getD_some]
          exact (hdenotes name value hlookup).symm
  | expr atoms atomIH =>
      simp only [Metta.Subst.apply, subst_expr, Atom.expr.injEq,
        List.map_map]
      rw [List.map_congr_left]
      intro child hchild
      exact atomIH child hchild

/-- Repeated application of a denoted substitution is invisible under the
    realizing runtime substitution. -/
private theorem subst_substN_of_lookupDenotes (runtime binding : Subst)
    (hdenotes : SubstLookupDenotes runtime binding)
    (atom : Atom) (fuel : Nat) :
    subst runtime (substN fuel binding atom) = subst runtime atom := by
  induction fuel generalizing atom with
  | zero => simp [substN]
  | succ fuel fuelIH =>
      induction atom using machineAtomRecAux with
      | sym symbol => simp [substN]
      | gnd ground => simp [substN]
      | var name =>
          simp only [substN]
          cases hlookup : Metta.Subst.lookup binding name with
          | none => rfl
          | some value =>
              exact (fuelIH value).trans (hdenotes name value hlookup).symm
      | expr atoms atomIH =>
          simp only [substN, subst_expr, Atom.expr.injEq, List.map_map]
          rw [List.map_congr_left]
          intro child hchild
          exact atomIH child hchild

/-- Deep substitution by a denoted binding is observationally invisible. -/
theorem subst_subst_of_lookupDenotes (runtime binding : Subst)
    (hdenotes : SubstLookupDenotes runtime binding) (atom : Atom) :
    subst runtime (subst binding atom) = subst runtime atom := by
  exact subst_substN_of_lookupDenotes runtime binding hdenotes atom
    (binding.length + 1)

mutual

/-- Lossless Atom encoding of compiled goals for whole-clause α-comparison. -/
private def goalAlphaAtom : Goal → Atom
  | .call f args res =>
      Atom.expr [Atom.sym "goal.call", Atom.sym f, Atom.expr args, res]
  | .bin op args res =>
      Atom.expr [Atom.sym "goal.bin", Atom.sym op, Atom.expr args, res]
  | .callDyn head args res =>
      Atom.expr [Atom.sym "goal.callDyn", head, Atom.expr args, res]
  | .evalg value res => Atom.expr [Atom.sym "goal.evalg", value, res]
  | .catchg tmpl sub res =>
      Atom.expr [Atom.sym "goal.catchg", tmpl, goalsAlphaAtom sub, res]
  | .softcut tmpl sub thn els =>
      Atom.expr [Atom.sym "goal.softcut", tmpl, goalsAlphaAtom sub,
        goalsAlphaAtom thn, goalsAlphaAtom els]
  | .eq a b => Atom.expr [Atom.sym "goal.eq", a, b]
  | .cut => Atom.expr [Atom.sym "goal.cut"]
  | .cutAt n =>
      Atom.expr [Atom.sym "goal.cutAt", Atom.gnd (Metta.Ground.int n)]
  | .findall tmpl sub res =>
      Atom.expr [Atom.sym "goal.findall", tmpl, goalsAlphaAtom sub, res]
  | .onceg tmpl sub res =>
      Atom.expr [Atom.sym "goal.onceg", tmpl, goalsAlphaAtom sub, res]
  | .transactiong tmpl sub =>
      Atom.expr [Atom.sym "goal.transactiong", tmpl, goalsAlphaAtom sub]
  | .amb branches res =>
      Atom.expr [Atom.sym "goal.amb", branchesAlphaAtom branches, res]
  | .spread value res => Atom.expr [Atom.sym "goal.spread", value, res]
  | .ite cond thn els res =>
      Atom.expr [Atom.sym "goal.ite", cond,
        Atom.expr [thn.1, goalsAlphaAtom thn.2],
        Atom.expr [els.1, goalsAlphaAtom els.2], res]
  | .smatch pat => Atom.expr [Atom.sym "goal.smatch", pat]
  | .wact op args res =>
      Atom.expr [Atom.sym "goal.wact", Atom.sym op, Atom.expr args, res]

private def goalsAlphaAtom : List Goal → Atom
  | [] => Atom.expr []
  | goal :: rest =>
      match goalsAlphaAtom rest with
      | Atom.expr encoded => Atom.expr (goalAlphaAtom goal :: encoded)
      | other => Atom.expr [goalAlphaAtom goal, other]

private def branchesAlphaAtom : List (Atom × List Goal) → Atom
  | [] => Atom.expr []
  | (tmpl, goals) :: rest =>
      match branchesAlphaAtom rest with
      | Atom.expr encoded =>
          Atom.expr (Atom.expr [tmpl, goalsAlphaAtom goals] :: encoded)
      | other => Atom.expr [Atom.expr [tmpl, goalsAlphaAtom goals], other]

end

/-- α-canonical clause comparison (retraction matching). -/
def clauseAlphaKey (cl : Clause) : String :=
  let t := Atom.expr (cl.params ++ [cl.result, goalsAlphaAtom cl.body])
  let rec canon (m : List (String × Nat)) (a : Atom) :
      Atom × List (String × Nat) :=
    match a with
    | Atom.var v =>
        (match m.lookup v with
         | some i => (Atom.var s!"α{i}", m)
         | none => (Atom.var s!"α{m.length}", m ++ [(v, m.length)]))
    | Atom.expr es =>
        let (es', m') := es.attach.foldl
          (fun (acc : List Atom × List (String × Nat)) ⟨e, _⟩ =>
            let (e', m2) := canon acc.2 e
            (acc.1 ++ [e'], m2)) ([], m)
        (Atom.expr es', m')
    | x => (x, m)
  Metta.Pretty.atom (canon [] t).1

/-- Total aligned view of live source keys.  Worlds constructed before the
    key field (including compact proof fixtures) receive the ordinary
    compiled key on demand. -/
def PWorld.effectiveProgClauseKeys (w : PWorld) : List String :=
  if w.progClauseKeys.length == w.progClauses.length then w.progClauseKeys
  else w.progClauses.map (fun entry => clauseAlphaKey entry.2)

/-- Remove the first captured clause with the same parent and compiled
    α-shape as a retracted live clause. -/
def PWorld.removeCapturedMeta (w : PWorld) (parent key : String) : PWorld :=
  let kept := (w.metaClauses.foldl
    (fun (acc : List MetaClause × Bool) mc =>
      let capturedKey :=
        if mc.sourceKey.isEmpty then clauseAlphaKey mc.compiled
        else mc.sourceKey
      if !acc.2 && mc.parent == parent && capturedKey == key
      then (acc.1, true)
      else (acc.1 ++ [mc], acc.2)) ([], false)).1
  { w with metaClauses := kept }

theorem PWorld.removeCapturedMeta_coherent (w : PWorld) (parent key : String)
    (coherent : w.ClauseIndexCoherent) :
    (w.removeCapturedMeta parent key).ClauseIndexCoherent := by
  exact coherent

theorem PWorld.removeCapturedMeta_spaceCoherent (w : PWorld)
    (parent key : String) (coherent : w.SpaceIndexCoherent) :
    (w.removeCapturedMeta parent key).SpaceIndexCoherent := by
  exact coherent

/- Atoms whose proof-facing structural equality can be reflected into Lean
    equality.  Host floats are excluded because Lean exposes their bit
    representation computationally but no injectivity theorem for `toBits`;
    such call sites retain the generic path. -/
mutual

/-- One atom belongs to the propositionally checkable profile fragment. -/
def propositionallyCheckableAtom : Atom → Bool
  | .gnd (.float _) => false
  | .expr atoms => propositionallyCheckableAtoms atoms
  | _ => true

/-- Every atom in a list belongs to the propositionally checkable fragment. -/
def propositionallyCheckableAtoms : List Atom → Bool
  | [] => true
  | atom :: rest =>
      propositionallyCheckableAtom atom &&
        propositionallyCheckableAtoms rest

end

/-- Strong call-site support used at the executable specialization boundary.
    It reuses the real runtime unifier, then admits the retarget only when the
    fully resolved tuple is structurally exact in the propositionally
    checkable fragment.  Numeric coercions such as `1` versus `1.0` therefore
    stay on the generic path instead of justifying a different specialized
    body through `Ground.equiv`. -/
def specializationBindingExactlySupported (binding : Subst)
    (formals actuals : List Atom) : Bool :=
  if binding.isEmpty then true
  else if formals.length != actuals.length then false
  else if !binding.all (fun entry =>
      formals.any (specializationVarOccurs entry.1)) then false
  else
    let left := Atom.expr (formals.map (Metta.Subst.apply binding))
    let right := Atom.expr actuals
    match Metta.Unify.unifyTop left right with
    | none => false
    | some unifier =>
        let resolvedLeft := subst unifier left
        let resolvedRight := subst unifier right
        propositionallyCheckableAtom resolvedLeft &&
          propositionallyCheckableAtom resolvedRight &&
          proofAtomEq resolvedLeft resolvedRight

/-- Proof-reflectable equality for complete static call tuples. -/
def propositionallyExactAtoms (left right : List Atom) : Bool :=
  propositionallyCheckableAtoms left &&
    propositionallyCheckableAtoms right &&
    proofAtomsEq left right

mutual

/-- A retargeted child call names the same registered parent and its static
    actuals support every guard binding on every generated child clause.
    Unchanged calls are admitted directly. -/
def PWorld.childCallSiteValid (w : PWorld) (outerBinding : Subst)
    (parent child : String) (args : List Atom) : Bool :=
  let childProvenance := w.specClauseProvenance.filter (fun provenance =>
    provenance.name == child && provenance.parent == parent)
  parent == child ||
    (w.specializations.any (fun record =>
      record.name == child && record.key.parent == parent) &&
    !childProvenance.isEmpty &&
    childProvenance.all (fun provenance =>
      specializationBindingExactlySupported provenance.binding
        provenance.parentClause.params
        (args.map (Metta.Subst.apply outerBinding)) &&
      propositionallyExactAtoms provenance.discoveryActuals
        (args.map (Metta.Subst.apply outerBinding))))

/-- Semantic strengthening of `childCallRewriteValid`: payloads remain exact,
    and recursive retargeting carries the call-site fact needed to discharge
    the target specialization's guards. -/
def PWorld.childCallSitesValid (w : PWorld) (outerBinding : Subst) :
    Goal → Goal → Bool
  | .call parent args res, .call child args' res' =>
      proofAtomsEq args args' && proofAtomEq res res' &&
        w.childCallSiteValid outerBinding parent child args
  | .catchg tmpl sub res, .catchg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        w.childCallSitesValidList outerBinding sub sub'
  | .softcut tmpl sub thn els, .softcut tmpl' sub' thn' els' =>
      proofAtomEq tmpl tmpl' &&
        w.childCallSitesValidList outerBinding sub sub' &&
        w.childCallSitesValidList outerBinding thn thn' &&
        w.childCallSitesValidList outerBinding els els'
  | .findall tmpl sub res, .findall tmpl' sub' res'
  | .onceg tmpl sub res, .onceg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        w.childCallSitesValidList outerBinding sub sub'
  | .transactiong tmpl sub, .transactiong tmpl' sub' =>
      proofAtomEq tmpl tmpl' &&
        w.childCallSitesValidList outerBinding sub sub'
  | .amb branches res, .amb branches' res' =>
      proofAtomEq res res' &&
        w.childCallBranchSitesValid outerBinding branches branches'
  | .ite cond thn els res, .ite cond' thn' els' res' =>
      proofAtomEq cond cond' && proofAtomEq thn.1 thn'.1 &&
        proofAtomEq els.1 els'.1 && proofAtomEq res res' &&
        w.childCallSitesValidList outerBinding thn.2 thn'.2 &&
        w.childCallSitesValidList outerBinding els.2 els'.2
  | original, rewritten => proofGoalEq original rewritten

def PWorld.childCallSitesValidList (w : PWorld) (outerBinding : Subst) :
    List Goal → List Goal → Bool
  | [], [] => true
  | goal :: rest, rewritten :: rewrittenRest =>
      w.childCallSitesValid outerBinding goal rewritten &&
        w.childCallSitesValidList outerBinding rest rewrittenRest
  | _, _ => false

def PWorld.childCallBranchSitesValid (w : PWorld) (outerBinding : Subst) :
    List (Atom × List Goal) → List (Atom × List Goal) → Bool
  | [], [] => true
  | (tmpl, goals) :: rest, (tmpl', rewritten) :: rewrittenRest =>
      proofAtomEq tmpl tmpl' &&
        w.childCallSitesValidList outerBinding goals rewritten &&
        w.childCallBranchSitesValid outerBinding rest rewrittenRest
  | _, _ => false

end

/-- Decidable integrity check for one proof-facing provenance row.  It links
    the exact installed clause and live parent, validates the pure guarded
    envelope, and admits only registered child-specialization retargeting. -/
def PWorld.specClauseProvenanceValid (w : PWorld)
    (provenance : SpecClauseProvenance) : Bool :=
  w.progClauses.any (fun entry =>
      entry.1 == provenance.name &&
        proofClauseEq entry.2 provenance.executableClause) &&
    (w.clausesOf provenance.parent).any (fun clause =>
      proofClauseEq clause provenance.parentClause) &&
    w.specializations.any (fun record =>
      record.name == provenance.name &&
        record.key.parent == provenance.parent) &&
    specializationBindingRuntimeSafe provenance.binding &&
    specializationSourceBindingExact provenance.sourceBinding
      provenance.parentClause.params provenance.discoveryActuals &&
    specializationBindingExactlySupported provenance.binding
      provenance.parentClause.params provenance.discoveryActuals &&
    guardedClauseShapeValid provenance.binding provenance.parentClause
      provenance.guardedClause &&
    proofAtomsEq provenance.executableClause.params
      provenance.guardedClause.params &&
    proofAtomEq provenance.executableClause.result
      provenance.guardedClause.result &&
    childCallsRewriteValid w.specializations provenance.guardedClause.body
      provenance.executableClause.body &&
    w.childCallSitesValidList provenance.binding
      provenance.guardedClause.body provenance.executableClause.body

/-- Every committed generated clause has exact provenance, and every
    provenance row passes the syntactic construction checks above. -/
def PWorld.specializationProvenanceValid (w : PWorld) : Bool :=
  w.specClauseProvenance.all w.specClauseProvenanceValid &&
    w.specializations.all (fun record =>
      let clauses := w.clausesOf record.name
      let provenance := w.specClauseProvenance.filter (fun item =>
        item.name == record.name && item.parent == record.key.parent)
      !clauses.isEmpty &&
        proofClausesEq clauses (provenance.map (·.executableClause)) &&
        proofClausesEq (w.clausesOf record.key.parent)
          (provenance.map (·.parentClause)))

/-- Exact provenance rows belonging to one committed specialization. -/
def PWorld.recordProvenance (w : PWorld) (record : SpecRecord) :
    List SpecClauseProvenance :=
  w.specClauseProvenance.filter (fun provenance =>
    provenance.name == record.name &&
      provenance.parent == record.key.parent)

/-- All provenance rows bearing one generated public name. -/
def PWorld.provenanceNamed (w : PWorld) (name : String) :
    List SpecClauseProvenance :=
  w.specClauseProvenance.filter (fun provenance => provenance.name == name)

/-- Captured clauses use native newest-first metadata order. -/
def PWorld.capturedMetaOf (w : PWorld) (parent : String) : List MetaClause :=
  w.metaClauses.filter (fun captured => captured.parent == parent)

/-- The live executable family is the source-ordered reversal of the complete
    native metadata family.  This is the input invariant used by the
    transactional builder. -/
structure PWorld.CapturedParentOrdered (w : PWorld) (parent : String) : Prop where
  clauses : w.clausesOf parent =
    (w.capturedMetaOf parent).reverse.map (·.compiled)

/-- Constructional ordered correspondence for one registry row.  These are
    propositional equalities carried by the semantic proof, not conclusions
    extracted from the NaN-aware executable Boolean checker. -/
structure PWorld.SpecializationRecordOrdered (w : PWorld)
    (record : SpecRecord) : Prop where
  nonempty : !(w.clausesOf record.name).isEmpty = true
  parentClauses :
    w.clausesOf record.key.parent =
      (w.recordProvenance record).map (·.parentClause)
  executableClauses :
    w.clausesOf record.name =
      (w.recordProvenance record).map (·.executableClause)
  exactHeads : ∀ provenance,
    provenance ∈ w.recordProvenance record →
      provenance.parentClause.params =
          provenance.executableClause.params ∧
        provenance.parentClause.result =
          provenance.executableClause.result

/-- Proposition consumed by the semantic simulation.  The executable check
    protects construction, while `ordered` supplies exact equalities to the
    proof without unsoundly converting bit equality into Lean equality. -/
structure WellSpecializedWorld (w : PWorld) : Prop where
  checked : w.specializationProvenanceValid = true
  ordered : ∀ record, record ∈ w.specializations →
    w.SpecializationRecordOrdered record

/-! ## Transactional compiler-profile specialization -/

/-- Local state for one atomic specialization request.  Provisional records
    make recursive graphs finite, while `directGain` decides whether the
    entire graph commits or rolls back [SPEC specializer.pl:27-55]. -/
structure SpecBuildState where
  world : PWorld
  isBin : String → Bool
  provisional : List SpecRecord := []
  pending : List SpecKey := []
  expanded : List SpecKey := []
  directGain : List SpecKey := []

/-- One clause bundle produced by the transactional specialization builder.
    Public for the constructional preservation proof; installation remains
    mediated by `installBuiltClauses`. -/
structure BuiltSpecClause where
  source : Atom
  sourceClause : Clause
  provenance : SpecClauseProvenance
deriving Repr, Inhabited

/-- Whether a public name is already live or reserved by the current atomic
    specialization transaction.  Public for constructional frame proofs. -/
def SpecBuildState.isDefined (st : SpecBuildState) (f : String) :
    Bool :=
  !(st.world.clausesOf f).isEmpty ||
    st.provisional.any (fun record => record.name == f)

/-- Collision predicate for a newly generated public name.  Unlike callable
    liveness, this includes proof/source metadata and residual declarations:
    overwriting any of them would merge two specialization lifecycles. -/
def SpecBuildState.isNameOccupied (st : SpecBuildState) (f : String) : Bool :=
  st.isDefined f ||
    !(st.world.capturedMetaOf f).isEmpty ||
    !(st.world.provenanceNamed f).isEmpty ||
    st.world.specializations.any (fun record => record.name == f) ||
    st.world.knownHeads.contains f ||
    st.world.typeDecls.any (fun declaration =>
      declaration.1 == Atom.sym f)

def SpecBuildState.isSpecializable (st : SpecBuildState) (f : String) :
    Bool :=
  st.isDefined f || st.isBin f

def SpecBuildState.hasMeta (st : SpecBuildState) (f : String) : Bool :=
  st.world.metaClauses.any (fun mc => mc.parent == f) ||
    st.provisional.any (fun record => record.name == f)

def SpecBuildState.findRecord? (st : SpecBuildState) (key : SpecKey) :
    Option SpecRecord :=
  (st.world.specializations ++ st.provisional).find? (fun record =>
    record.key == key)

def SpecBuildState.markGain (st : SpecBuildState) (key : SpecKey) :
    SpecBuildState :=
  if st.directGain.contains key then st
  else { st with directGain := st.directGain ++ [key] }

def SpecBuildState.commit (st : SpecBuildState) : PWorld :=
  { st.world with specializations :=
      st.world.specializations ++ st.provisional }

/-- Copy all type declarations for a specialized head.  Public for the
    constructional proof; callers still install through `buildSpecRequest`. -/
def installCopiedTypes (w : PWorld) (parent specName : String) :
    PWorld :=
  let copied := w.typeDecls.filter (fun declaration =>
    declaration.1 == Atom.sym parent)
  copied.foldl (fun current declaration =>
    let visible := Atom.expr
      [Atom.sym ":", Atom.sym specName, declaration.2]
    let withAtom := current.addAtom selfSpace (chainify visible)
    { withAtom with typeDecls :=
        withAtom.typeDecls ++ [(Atom.sym specName, declaration.2)] }) w

def installBuiltClauses (w : PWorld) (specName : String)
    (built : List BuiltSpecClause) : PWorld :=
  let sourceOrdered := built.reverse
  let withVisible := sourceOrdered.foldl (fun current item =>
    let withAtom := current.addAtom selfSpace (chainify item.source)
    withAtom.captureMetaWithSourceKey item.source
      item.provenance.executableClause (clauseAlphaKey item.sourceClause)) w
  let arities := sourceOrdered.map (fun item =>
    (specName, item.provenance.executableClause.params.length))
  let entries := sourceOrdered.map (fun item =>
    (specName, item.provenance.executableClause))
  let clauses := w.progClauses ++ entries
  { withVisible with
      progClauses := clauses
      clauseIndex := if withVisible.clauseIndexReady then
        ClauseIndex.build clauses
      else
        withVisible.clauseIndex
      progClauseKeys := w.effectiveProgClauseKeys ++
        sourceOrdered.map (fun item => clauseAlphaKey item.sourceClause)
      specClauseProvenance := w.specClauseProvenance ++
        sourceOrdered.map (fun item => item.provenance)
      knownHeads := (w.knownHeads ++ [specName]).eraseDups
      knownArities := w.knownArities ++ arities }

def specializedSource (specName : String)
    (candidate : SpecClauseCandidate) : Atom :=
  let params := candidate.captured.sourceParams.map
    (Metta.Subst.apply candidate.binding)
  let body := Metta.Subst.apply candidate.binding
    candidate.captured.sourceBody
  Atom.expr [Atom.sym "=", Atom.expr (Atom.sym specName :: params), body]

mutual

def buildSpecRequest : Nat → SpecBuildState → String → List Atom →
    Option (SpecBuildState × Option String)
  | 0, _, _, _ => none
  | fuel + 1, st, parent, actuals =>
      match discoverSpecialization st.isSpecializable st.hasMeta parent actuals
          st.world.metaClauses with
      | none => some (st, none)
      | some candidate =>
          if !candidate.clauses.all SpecClauseCandidate.safe
          then some (st, none)
          else
            match st.findRecord? candidate.key with
            | some record => some (st, some record.name)
            | none =>
                let record : SpecRecord :=
                  { key := candidate.key, name := specializationName candidate.key }
                if st.isNameOccupied record.name then some (st, none)
                else
                  let registered : SpecBuildState :=
                    { st with
                        provisional := st.provisional ++ [record]
                        pending := st.pending ++ [candidate.key]
                        world := installCopiedTypes st.world parent record.name }
                  match buildSpecClauses fuel registered candidate.key record.name
                      candidate.clauses with
                  | none => none
                  | some (expanded, built) =>
                      let installed := installBuiltClauses expanded.world
                        record.name built
                      some
                        ({ expanded with
                            world := installed
                            pending := expanded.pending.filter (· != candidate.key)
                            expanded := expanded.expanded ++ [candidate.key] },
                          some record.name)

def buildSpecClauses : Nat → SpecBuildState → SpecKey → String →
    List SpecClauseCandidate → Option (SpecBuildState × List BuiltSpecClause)
  | _, st, _, _, [] => some (st, [])
  | 0, _, _, _, _ :: _ => none
  | fuel + 1, st, key, specName, candidate :: rest =>
      let instantiated := instantiateGoals candidate.binding
        candidate.captured.compiled.body
      let gained := profileDynamicUseGoals st.isDefined st.isBin instantiated
      let sourceClause := specializeClauseProfile st.isDefined st.isBin
        candidate.binding candidate.captured.compiled
      let base := specializeClauseGuarded st.isDefined st.isBin candidate.binding
        candidate.captured.compiled
      let gainedState := if gained then st.markGain key else st
      match buildProfileGoals fuel gainedState candidate.binding base.body with
      | none => none
      | some (afterBody, body) =>
          let executable := { base with body }
          let available := afterBody.world.specializations ++
            afterBody.provisional
          if !guardedClauseShapeValid candidate.binding
              candidate.captured.compiled base ||
            !childCallsRewriteValid available base.body body
          then none
          else
            let finished : BuiltSpecClause :=
              { source := specializedSource specName candidate
                sourceClause
                provenance :=
                  { name := specName
                    parent := key.parent
                    parentClause := candidate.captured.compiled
                    sourceBinding := candidate.sourceBinding
                    discoveryActuals := candidate.discoveryActuals
                    binding := candidate.binding
                    guardedClause := base
                    executableClause := executable } }
            match buildSpecClauses fuel afterBody key specName rest with
            | none => none
            | some (afterRest, builtRest) =>
                some (afterRest, finished :: builtRest)

def buildProfileGoals : Nat → SpecBuildState → Subst → List Goal →
    Option (SpecBuildState × List Goal)
  | _, st, _, [] => some (st, [])
  | 0, _, _, _ :: _ => none
  | fuel + 1, st, binding, goal :: rest =>
      match buildProfileGoal fuel st binding goal with
      | none => none
      | some (afterGoal, rewritten) =>
          match buildProfileGoals fuel afterGoal binding rest with
          | none => none
          | some (afterRest, rewrittenRest) =>
              some (afterRest, rewritten :: rewrittenRest)

def buildProfileGoal : Nat → SpecBuildState → Subst → Goal →
    Option (SpecBuildState × Goal)
  | 0, _, _, _ => none
  | fuel + 1, st, binding, .call f args res =>
      let actuals := args.map (Metta.Subst.apply binding)
      match buildSpecRequest fuel st f actuals with
      | none => none
      | some (next, some specName) => some (next, .call specName args res)
      | some (next, none) => some (next, .call f args res)
  | fuel + 1, st, binding, .catchg tmpl sub res =>
      (buildProfileGoals fuel st binding sub).map (fun (next, goals) =>
        (next, .catchg tmpl goals res))
  | fuel + 1, st, binding, .softcut tmpl sub thn els =>
      match buildProfileGoals fuel st binding sub with
      | none => none
      | some (afterSub, sub') =>
          match buildProfileGoals fuel afterSub binding thn with
          | none => none
          | some (afterThen, thn') =>
              (buildProfileGoals fuel afterThen binding els).map
                (fun (afterElse, els') =>
                  (afterElse, .softcut tmpl sub' thn' els'))
  | fuel + 1, st, binding, .findall tmpl sub res =>
      (buildProfileGoals fuel st binding sub).map (fun (next, goals) =>
        (next, .findall tmpl goals res))
  | fuel + 1, st, binding, .onceg tmpl sub res =>
      (buildProfileGoals fuel st binding sub).map (fun (next, goals) =>
        (next, .onceg tmpl goals res))
  | fuel + 1, st, binding, .transactiong tmpl sub =>
      (buildProfileGoals fuel st binding sub).map (fun (next, goals) =>
        (next, .transactiong tmpl goals))
  | fuel + 1, st, binding, .amb branches res =>
      (buildProfileBranches fuel st binding branches).map (fun (next, rewritten) =>
        (next, .amb rewritten res))
  | fuel + 1, st, binding, .ite cond thn els res =>
      match buildProfileGoals fuel st binding thn.2 with
      | none => none
      | some (afterThen, thnGoals) =>
          (buildProfileGoals fuel afterThen binding els.2).map
            (fun (afterElse, elsGoals) =>
              (afterElse, .ite cond (thn.1, thnGoals)
                (els.1, elsGoals) res))
  | _, st, _, goal => some (st, goal)

def buildProfileBranches : Nat → SpecBuildState → Subst →
    List (Atom × List Goal) → Option (SpecBuildState × List (Atom × List Goal))
  | _, st, _, [] => some (st, [])
  | 0, _, _, _ :: _ => none
  | fuel + 1, st, binding, (tmpl, goals) :: rest =>
      match buildProfileGoals fuel st binding goals with
      | none => none
      | some (afterGoals, rewritten) =>
          (buildProfileBranches fuel afterGoals binding rest).map
            (fun (afterRest, rewrittenRest) =>
              (afterRest, (tmpl, rewritten) :: rewrittenRest))

end

/-- One explicit finite bound for a transactional specialization graph. -/
def specializationBuildFuel : Nat := 4096

def specializationIsBin (gt : GroundingTable) (name : String) : Bool :=
  (Metta.GroundingTable.lookup gt name).isSome

/-- Attempt one specialization atomically.  Unsupported discovery, exhausted
    build fuel, or a recursive graph with no concrete dynamic-head gain leaves
    both the world and the generic call exactly unchanged. -/
def attemptSpecializeCall (isBin : String → Bool) (buildFuel : Nat)
    (w : PWorld) (f : String) (args : List Atom) (res : Atom) : PWorld × Goal :=
  let generic := Goal.call f args res
  match buildSpecRequest buildFuel { world := w, isBin } f args with
  | some (built, some specName) =>
      let reused := built.provisional.isEmpty
      if !reused && built.directGain.isEmpty then (w, generic)
      else
        let committed := if reused then built.world else built.commit
        if committed.specializationProvenanceValid &&
            committed.childCallSiteValid [] f specName args
        then (committed, Goal.call specName args res)
        else (w, generic)
  | _ => (w, generic)

mutual

/-- Pure profile pass shared by top-level queries and runtime `eval`. -/
def specializeGoals (isBin : String → Bool) (buildFuel : Nat) :
    PWorld → List Goal → PWorld × List Goal
  | w, [] => (w, [])
  | w, goal :: rest =>
      let (afterGoal, rewritten) := specializeGoal isBin buildFuel w goal
      let (afterRest, rewrittenRest) :=
        specializeGoals isBin buildFuel afterGoal rest
      (afterRest, rewritten :: rewrittenRest)

def specializeGoal (isBin : String → Bool) (buildFuel : Nat) (w : PWorld) :
    Goal → PWorld × Goal
  | .call f args res => attemptSpecializeCall isBin buildFuel w f args res
  | .catchg tmpl sub res =>
      let (next, goals) := specializeGoals isBin buildFuel w sub
      (next, .catchg tmpl goals res)
  | .softcut tmpl sub thn els =>
      let (w1, sub') := specializeGoals isBin buildFuel w sub
      let (w2, thn') := specializeGoals isBin buildFuel w1 thn
      let (w3, els') := specializeGoals isBin buildFuel w2 els
      (w3, .softcut tmpl sub' thn' els')
  | .findall tmpl sub res =>
      let (next, goals) := specializeGoals isBin buildFuel w sub
      (next, .findall tmpl goals res)
  | .onceg tmpl sub res =>
      let (next, goals) := specializeGoals isBin buildFuel w sub
      (next, .onceg tmpl goals res)
  | .transactiong tmpl sub =>
      let (next, goals) := specializeGoals isBin buildFuel w sub
      (next, .transactiong tmpl goals)
  | .amb branches res =>
      let (next, rewritten) := specializeBranches isBin buildFuel w branches
      (next, .amb rewritten res)
  | .ite cond thn els res =>
      let (w1, thnGoals) := specializeGoals isBin buildFuel w thn.2
      let (w2, elsGoals) := specializeGoals isBin buildFuel w1 els.2
      (w2, .ite cond (thn.1, thnGoals) (els.1, elsGoals) res)
  | goal => (w, goal)

def specializeBranches (isBin : String → Bool) (buildFuel : Nat) : PWorld →
    List (Atom × List Goal) → PWorld × List (Atom × List Goal)
  | w, [] => (w, [])
  | w, (tmpl, goals) :: rest =>
      let (w1, rewritten) := specializeGoals isBin buildFuel w goals
      let (w2, rewrittenRest) := specializeBranches isBin buildFuel w1 rest
      (w2, (tmpl, rewritten) :: rewrittenRest)

end

/-! ## Transitive specialization invalidation -/

mutual

private def calledGoalHeads : Goal → List String
  | .call f _ _ => [f]
  | .catchg _ sub _ => calledGoalsHeads sub
  | .softcut _ sub thn els =>
      calledGoalsHeads sub ++ calledGoalsHeads thn ++ calledGoalsHeads els
  | .findall _ sub _ => calledGoalsHeads sub
  | .onceg _ sub _ => calledGoalsHeads sub
  | .transactiong _ sub => calledGoalsHeads sub
  | .amb branches _ => calledBranchHeads branches
  | .ite _ thn els _ => calledGoalsHeads thn.2 ++ calledGoalsHeads els.2
  | _ => []

private def calledGoalsHeads : List Goal → List String
  | [] => []
  | goal :: rest => calledGoalHeads goal ++ calledGoalsHeads rest

private def calledBranchHeads : List (Atom × List Goal) → List String
  | [] => []
  | (_, goals) :: rest => calledGoalsHeads goals ++ calledBranchHeads rest

end


/-- Direct generated children of a function family.  The relation is directed:
    records generated from `parent`, plus generated callees named by the
    parent's installed specialized clauses. -/
def PWorld.specializationChildren (w : PWorld) (parent : String) :
    List String :=
  let registered := w.specializations.filterMap (fun record =>
    if record.key.parent == parent then some record.name else none)
  let generatedCalls := (w.clausesOf parent).flatMap (fun clause =>
    calledGoalsHeads clause.body)
  let committedNames := w.specializations.map (·.name)
  (registered ++ generatedCalls.filter committedNames.contains).eraseDups

private def specializationClosure (w : PWorld) : Nat → List String →
    List String → List String
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, parent :: rest, seen =>
      let fresh := (w.specializationChildren parent).filter
        (fun name => !seen.contains name)
      specializationClosure w fuel (rest ++ fresh) (seen ++ fresh)

/-- Every committed specialization generated beneath `parent`.  Invalidation
    follows the native directed parent-to-specialization relation; changing a
    bound callable does not invalidate callers that merely mention it
    [SPEC specializer.pl:104-119, spaces.pl:9-38].  Generated calls supply the
    recursive child edges created within one specialization family. -/
def PWorld.specializationDescendants (w : PWorld) (parent : String) :
    List String :=
  let direct := w.specializationChildren parent
  specializationClosure w (w.specializations.length + 1) direct direct

theorem PWorld.specializationDescendants_eq_nil_of_children_eq_nil
    (w : PWorld) (parent : String)
    (h : w.specializationChildren parent = []) :
    w.specializationDescendants parent = [] := by
  simp [PWorld.specializationDescendants, h, specializationClosure]

private def visibleArtifactHead? (a : Atom) : Option String :=
  match unchainify 10000 a with
  | Atom.expr [Atom.sym ":", Atom.sym name, _] => some name
  | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym name :: _), _] => some name
  | _ => none

private def tableCallHead? : Atom → Option String
  | Atom.expr (Atom.sym name :: _) => some name
  | _ => none

/-- Forget all and only generated artifacts in the transitive specialization
    component rooted at a changed ordinary function.  The ordinary parent's
    newly added/remaining source artifacts are preserved. -/
def PWorld.invalidateSpecializations (w : PWorld) (parent : String) : PWorld :=
  let affected := w.specializationDescendants parent
  if affected.isEmpty then w
  else
    let retainedClauses :=
      (w.progClauses.zip w.effectiveProgClauseKeys).filter (fun entry =>
        !affected.contains entry.1.1)
    let retainedAtoms := w.selfAtoms.filter (fun atom =>
      match visibleArtifactHead? atom with
      | some name => !affected.contains name
      | none => true)
    let retainedBase := w.replaceSelfAtoms retainedAtoms
    let retainedWorld : PWorld := { retainedBase with
      progClauseKeys := retainedClauses.map (fun entry => entry.2)
      metaClauses := w.metaClauses.filter (fun captured =>
        !affected.contains captured.parent)
      specializations := w.specializations.filter (fun record =>
        !affected.contains record.name)
      specClauseProvenance := w.specClauseProvenance.filter (fun record =>
        !affected.contains record.name)
      knownHeads := w.knownHeads.filter (fun name => !affected.contains name)
      knownArities := w.knownArities.filter (fun entry =>
        !affected.contains entry.1)
      tabledArities := w.tabledArities.filter (fun entry =>
        !affected.contains entry.1)
      tableActive := w.tableActive.filter (fun key =>
        match tableCallHead? key with
        | some name => !affected.contains name
        | none => true)
      tableCache := w.tableCache.filter (fun entry =>
        match tableCallHead? entry.1 with
        | some name => !affected.contains name
        | none => true)
      typeDecls := w.typeDecls.filter (fun declaration =>
        match declaration.1 with
        | Atom.sym name => !affected.contains name
        | _ => true) }
    retainedWorld.replaceProgClauses
      (retainedClauses.map (fun entry => entry.1))

private def chainHead? : Atom → Option Atom
  | Atom.expr [Atom.sym "#c", h, _] => some h
  | _ => none

private def shallowRuleChain? : Atom → Bool
  | Atom.expr [Atom.sym "#c", Atom.sym "=", Atom.expr
      [Atom.sym "#c", head, Atom.expr [Atom.sym "#c", _, Atom.sym "#nil"]]] =>
      match chainHead? head with
      | some (Atom.sym _) => true
      | _ => false
  | _ => false

def typeProducts : List (List Atom) → List (List Atom)
  | [] => [[]]
  | ts :: rest =>
      (typeProducts rest).flatMap (fun suffix =>
        ts.map (fun t => t :: suffix))

private def arrowTypeParts? (a : Atom) : Option (List Atom) :=
  match chainListM a with
  | some (Atom.sym "->" :: ts) => some ts
  | _ =>
      match a with
      | Atom.expr (Atom.sym "->" :: ts) => some ts
      | _ => none

/-- `get-type` (probe-pinned petta behaviors): an unbound variable types as
    a FRESH variable; a declared symbol yields EACH of its declarations
    (alternatives); numbers/strings ground-type; a non-application tuple
    types elementwise when every element is typed; anything else is
    `%Undefined%`. Returns the alternatives plus the next fresh counter. -/
def getTypeP (w : PWorld) : Nat → Nat → Atom → List Atom × Nat
  | 0, counter, _ => ([Atom.sym "%Undefined%"], counter)
  | _ + 1, counter, Atom.var _ => ([Atom.var s!"gtv{counter}"], counter + 1)
  | _ + 1, counter, Atom.gnd (Metta.Ground.int _) => ([Atom.sym "Number"], counter)
  | _ + 1, counter, Atom.gnd (Metta.Ground.float _) => ([Atom.sym "Number"], counter)
  | _ + 1, counter, Atom.gnd (Metta.Ground.str _) => ([Atom.sym "String"], counter)
  | _ + 1, counter, Atom.sym "True" => ([Atom.sym "Bool"], counter)
  | _ + 1, counter, Atom.sym "False" => ([Atom.sym "Bool"], counter)
  | _ + 1, counter, Atom.sym s =>
      let ds := w.typeDecls.filterMap (fun (subj, t) =>
        if subj == Atom.sym s then some (chainify t) else none)
      (if ds.isEmpty then [Atom.sym "%Undefined%"] else ds, counter)
  | fuel + 1, counter, a =>
      match chainListM a with
      | some (h :: t) =>
          let headTs := (getTypeP w fuel counter h).1
          if headTs.any (fun ty => (arrowTypeParts? ty).isSome) then
            -- application: each arrow's return type with its type variables
            -- instantiated by unifying declared parameter types against the
            -- argument types (parametric polymorphism)
            let (argTs, c1) := t.foldl
              (fun (acc : List Atom × Nat) e =>
                let (ts, c2) := getTypeP w fuel acc.2 e
                (acc.1 ++ [ts.headD (Atom.sym "%Undefined%")], c2))
              ([], counter)
            ((headTs.filterMap (fun ty =>
              match arrowTypeParts? ty with
              | some ts =>
                  (ts.getLast?).bind (fun ret =>
                    match Metta.Unify.unifyTop
                        (Atom.expr ts.dropLast) (Atom.expr argTs) with
                    | some u => some (Metta.Subst.apply u ret)
                    | none => none)
              | none => none)), c1)
          else
            let (elemTs, c') := (h :: t).foldl
              (fun (acc : List (List Atom) × Nat) e =>
                let (ts, c2) := getTypeP w fuel acc.2 e
                (acc.1 ++ [ts], c2))
              ([], counter)
            if elemTs.any (fun ts => ts.any (· == Atom.sym "%Undefined%")) then
              ([Atom.sym "%Undefined%"], counter)
            else ((typeProducts elemTs).map chainOf, c')
      | _ => ([Atom.sym "%Undefined%"], counter)

/-- Builtins that operate on terms AS TERMS (no groundness requirement). -/
def nonstrictOps : List String :=
  ["==", "!=", "is-var", "=alpha", "#test-results", "repr", "alpha-unique-atom", "is-alpha-member",
   -- Structural list ops act on the list SPINE (access / dedup / filter /
   -- sort by term identity), so they must run on lists whose ELEMENTS carry
   -- free variables — e.g. `(car-atom ((Sentence ($z …) …)))`, which native
   -- PeTTa reduces to the element but the all-ground gate here would drop to
   -- empty. Native compiles these to Prolog list predicates that unify over
   -- variable elements; the all-ground gate is only correct for value ops
   -- (arithmetic/comparison). Verified vs native car-atom/2 on var-element
   -- lists; corpus-checked (0 regressions).
   "car-atom", "cdr-atom", "last", "size-atom", "decons-atom",
   "list_to_set", "exclude-item", "unique-atom", "msort", "sub_string"]

/-- Known arities of partial-eligible builtins (petta checks arity via
    current_predicate; an under-applied registered builtin becomes a partial
    value, [SPEC translator.pl:328-339] applies to builtins too). 0 = don't
    partialize (unknown/variadic). -/
def binArity : String → Nat
  | "=" | "==" | "!=" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">="
  | "min" | "max"
  | "and" | "or" | "cons" | "cons-atom" | "member" | "is-member" | "union-atom"
  | "intersection-atom" | "subtraction-atom" | "exclude-item"
  | "index-atom" | "=alpha" | "is-alpha-member" => 2
  | "#test-results" => 2
  | "not" | "car-atom" | "cdr-atom" | "last" | "size-atom" | "repr" | "parse"
  | "repra" | "unique-atom" | "list_to_set" | "msort" | "println!" | "assert"
  | "add-translator-rule!" | "remove-translator-rule!"
  | "is-ground" | "is-expr" | "is-space" | "argv" => 1
  | _ => 0

/-- Unify under current bindings with PeTTa's exact-ground discipline; the
accepted generated substitution composes with the current binding. -/
def unifyB (b : Subst) (x y : Atom) : Option Subst :=
  match unifyTopExact (subst b x) (subst b y) with
  | some [] => some b
  | some u => some (Metta.Subst.compose u b)
  | none => none

abbrev SubstIndex := Std.HashMap String Atom
abbrev VarSet := Std.HashSet String
def addAtomVars (acc : VarSet) : Atom → VarSet
  | .var x => acc.insert x
  | .expr xs => xs.foldl addAtomVars acc
  | _ => acc

def addFreshAtomVars (state : VarSet × VarSet) : Atom → VarSet × VarSet
  | .var x =>
      if state.1.contains x then state
      else (state.1.insert x, state.2.insert x)
  | .expr xs => xs.foldl addFreshAtomVars state
  | _ => state

mutual
private def goalVarsFuel : Nat → Goal → VarSet → VarSet
  | 0, _, acc => acc
  | _ + 1, .call _ args res, acc =>
      args.foldl addAtomVars (addAtomVars acc res)
  | _ + 1, .bin _ args res, acc =>
      args.foldl addAtomVars (addAtomVars acc res)
  | _ + 1, .callDyn h args res, acc =>
      args.foldl addAtomVars (addAtomVars (addAtomVars acc res) h)
  | _ + 1, .evalg v r, acc => addAtomVars (addAtomVars acc r) v
  | k + 1, .catchg t sub r, acc =>
      goalsVarsFuel k sub (addAtomVars (addAtomVars acc r) t)
  | k + 1, .softcut t sub thn els, acc =>
      goalsVarsFuel k els (goalsVarsFuel k thn
        (goalsVarsFuel k sub (addAtomVars acc t)))
  | _ + 1, .eq a b, acc => addAtomVars (addAtomVars acc a) b
  | _ + 1, .cut, acc => acc
  | _ + 1, .cutAt _, acc => acc
  | k + 1, .findall t sub r, acc =>
      goalsVarsFuel k sub (addAtomVars (addAtomVars acc r) t)
  | k + 1, .onceg t sub r, acc =>
      goalsVarsFuel k sub (addAtomVars (addAtomVars acc r) t)
  | k + 1, .transactiong t sub, acc =>
      goalsVarsFuel k sub (addAtomVars acc t)
  | k + 1, .amb bs r, acc => branchVarsFuel k bs (addAtomVars acc r)
  | k + 1, .ite c t e r, acc =>
      goalsVarsFuel k e.2 (addAtomVars
        (goalsVarsFuel k t.2 (addAtomVars
          (addAtomVars (addAtomVars acc r) c) t.1)) e.1)
  | _ + 1, .spread v r, acc => addAtomVars (addAtomVars acc r) v
  | _ + 1, .smatch p, acc => addAtomVars acc p
  | _ + 1, .wact _ args res, acc =>
      args.foldl addAtomVars (addAtomVars acc res)

private def goalsVarsFuel : Nat → List Goal → VarSet → VarSet
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | k + 1, g :: gs, acc => goalsVarsFuel k gs (goalVarsFuel k g acc)

private def branchVarsFuel : Nat → List (Atom × List Goal) → VarSet → VarSet
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | k + 1, (t, gs) :: rest, acc =>
      branchVarsFuel k rest (goalsVarsFuel k gs (addAtomVars acc t))
end

mutual
private def goalFuel : Goal → Nat
  | .call _ _ _ => 1
  | .bin _ _ _ => 1
  | .callDyn _ _ _ => 1
  | .evalg _ _ => 1
  | .catchg _ sub _ => goalsFuel sub + 1
  | .softcut _ sub thn els =>
      Nat.max (goalsFuel sub) (Nat.max (goalsFuel thn) (goalsFuel els)) + 1
  | .eq _ _ => 1
  | .cut => 1
  | .cutAt _ => 1
  | .findall _ sub _ => goalsFuel sub + 1
  | .onceg _ sub _ => goalsFuel sub + 1
  | .transactiong _ sub => goalsFuel sub + 1
  | .amb bs _ => branchFuel bs + 1
  | .ite _ thn els _ => Nat.max (goalsFuel thn.2) (goalsFuel els.2) + 1
  | .spread _ _ => 1
  | .smatch _ => 1
  | .wact _ _ _ => 1

private def goalsFuel : List Goal → Nat
  | [] => 1
  | g :: gs => Nat.max (goalFuel g) (goalsFuel gs) + 1

private def branchFuel : List (Atom × List Goal) → Nat
  | [] => 1
  | (_, gs) :: rest => Nat.max (goalsFuel gs) (branchFuel rest) + 1
end

def goalsVars (gs : List Goal) : VarSet :=
  goalsVarsFuel (goalsFuel gs + 1) gs (Std.HashSet.emptyWithCapacity 64)

def substIndex (b : Subst) : SubstIndex :=
  b.foldl (fun index (x, a) => index.insertIfNew x a)
    (Std.HashMap.emptyWithCapacity b.length)

private theorem foldl_substIndex_getElem? (entries : Subst)
    (index : SubstIndex) (name : String) :
    (entries.foldl (fun current (x, a) => current.insertIfNew x a)
      index)[name]? =
      match index[name]? with
      | some value => some value
      | none => Metta.Subst.lookup entries name := by
  induction entries generalizing index with
  | nil =>
      cases hget : index[name]? <;> simp [hget, Metta.Subst.lookup]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
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

theorem substIndex_getElem? (b : Subst) (name : String) :
    (substIndex b)[name]? = Metta.Subst.lookup b name := by
  unfold substIndex
  rw [foldl_substIndex_getElem?]
  simp

def closeSubstVars (index : SubstIndex) : Nat → VarSet → VarSet → VarSet
  | 0, live, _ => live
  | k + 1, live, frontier =>
      if frontier.size == 0 then live
      else
        let state := frontier.toList.foldl
          (fun acc x =>
          match index.get? x with
          | some a => addFreshAtomVars acc a
          | none => acc)
          (live, Std.HashSet.emptyWithCapacity frontier.size)
        closeSubstVars index k state.1 state.2

/-- Lookup agreement on the variables observable to a continuation. -/
def SubstAgreeOn (visible : String → Prop) (left right : Subst) : Prop :=
  ∀ name, visible name →
    Metta.Subst.lookup left name = Metta.Subst.lookup right name

/-- A visible set is closed under the variables reached by substitution
    lookup.  This is the semantic content of `closeSubstVars`. -/
def SubstClosedOn (visible : String → Prop) (b : Subst) : Prop :=
  ∀ name value, visible name →
    Metta.Subst.lookup b name = some value →
      ∀ dependency, dependency ∈ value.vars → visible dependency

/-- Every variable occurring in an atom belongs to the visible set. -/
def AtomVarsIn (visible : String → Prop) (a : Atom) : Prop :=
  ∀ name, name ∈ a.vars → visible name

/-- The explicit condition excluding the length-sensitive cyclic behavior of
    raw substitutions: once the machine's ordinary bound is reached, further
    deep-substitution fuel is observationally inert. -/
def DeepSubstStable (b : Subst) : Prop :=
  ∀ a fuel, b.length + 1 ≤ fuel → substN fuel b a = subst b a

/-- Strong, useful base case: every assigned value is variable-free. -/
def SubstClosedRange (b : Subst) : Prop :=
  ∀ name value, Metta.Subst.lookup b name = some value → value.vars = []

private theorem substN_succ_eq_one_of_closedRange (b : Subst)
    (hclosed : SubstClosedRange b) (fuel : Nat) :
    (a : Atom) → substN (fuel + 1) b a = substN 1 b a
  | .sym name => by simp [substN]
  | .gnd ground => by simp [substN]
  | .var name => by
      simp only [substN]
      cases hlookup : Metta.Subst.lookup b name with
      | none => rfl
      | some value =>
          simpa [substN] using
            substN_of_closed fuel b value (hclosed name value hlookup)
  | .expr atoms => by
      simp only [substN, Atom.expr.injEq]
      rw [List.map_congr_left]
      intro child hchild
      exact substN_succ_eq_one_of_closedRange b hclosed fuel child
termination_by a => a.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using
    Nat.lt_add_one_of_le (atomSize_le_sum_of_mem atoms hchild)

/-- Closed-range substitutions reach their deep-substitution fixpoint after
    one lookup and therefore satisfy the runtime stability interface. -/
theorem deepSubstStable_of_closedRange (b : Subst)
    (hclosed : SubstClosedRange b) : DeepSubstStable b := by
  intro a fuel hfuel
  have hfuelPos : 0 < fuel := Nat.lt_of_lt_of_le (by omega) hfuel
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hfuelPos)
  rw [substN_succ_eq_one_of_closedRange b hclosed fuel']
  unfold subst
  exact (substN_succ_eq_one_of_closedRange b hclosed b.length a).symm

/-- A topological certificate for a runtime substitution.  Every bound
    dependency precedes its source in `order`; open variables need not occur
    in the order.  This admits open partial closures while excluding exactly
    the cyclic chains that make length-bounded deep substitution unstable. -/
structure SubstTopological (b : Subst) where
  order : List String
  nodup : order.Nodup
  domain : ∀ name,
    name ∈ order ↔ Metta.Subst.lookup b name ≠ none
  decreases : ∀ source value dependency,
    Metta.Subst.lookup b source = some value →
      dependency ∈ value.vars →
      Metta.Subst.lookup b dependency ≠ none →
      order.idxOf dependency < order.idxOf source

private theorem idxOf_filter_lt_of_idxOf_lt (predicate : String → Bool)
    (items : List String) (earlier later : String)
    (hearlier : earlier ∈ items) (hlater : later ∈ items)
    (hkeepEarlier : predicate earlier = true)
    (hkeepLater : predicate later = true)
    (hbefore : items.idxOf earlier < items.idxOf later) :
    (items.filter predicate).idxOf earlier <
      (items.filter predicate).idxOf later := by
  induction items with
  | nil => simp at hearlier
  | cons head rest ih =>
      have hne : earlier ≠ later := by
        intro heq
        subst later
        omega
      by_cases hheadEarlier : head = earlier
      · subst head
        have hlaterRest : later ∈ rest := by
          rcases List.mem_cons.mp hlater with heq | hmem
          · exact False.elim (hne heq.symm)
          · exact hmem
        have hbeq : (earlier == later) = false := by simp [hne]
        simp only [List.filter_cons, hkeepEarlier, if_true,
          List.idxOf_cons_self]
        rw [List.idxOf_cons, hbeq]
        exact Nat.zero_lt_succ _
      · by_cases hheadLater : head = later
        · subst head
          have hbeq : (later == earlier) = false := by
            simp [Ne.symm hne]
          simp only [List.idxOf_cons_self, List.idxOf_cons, hbeq] at hbefore
          omega
        · have hearlierRest : earlier ∈ rest := by
            rcases List.mem_cons.mp hearlier with heq | hmem
            · exact False.elim (hheadEarlier heq.symm)
            · exact hmem
          have hlaterRest : later ∈ rest := by
            rcases List.mem_cons.mp hlater with heq | hmem
            · exact False.elim (hheadLater heq.symm)
            · exact hmem
          have hbeqEarlier : (head == earlier) = false := by
            simp [hheadEarlier]
          have hbeqLater : (head == later) = false := by
            simp [hheadLater]
          have hbeforeRest : rest.idxOf earlier < rest.idxOf later := by
            simpa [List.idxOf_cons, hbeqEarlier, hbeqLater] using hbefore
          have hrest := ih hearlierRest hlaterRest hbeforeRest
          cases hkeepHead : predicate head with
          | false => simpa [hkeepHead] using hrest
          | true =>
              simpa [List.filter_cons, hkeepHead, List.idxOf_cons,
                hbeqEarlier, hbeqLater] using Nat.add_lt_add_right hrest 1

private theorem mem_subst_keys_of_lookup_ne_none (b : Subst) (name : String)
    (hlookup : Metta.Subst.lookup b name ≠ none) :
    name ∈ b.map Prod.fst := by
  induction b with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases hname : name = key
      · simp [hname]
      · simp only [Metta.Subst.lookup] at hlookup
        have hbeq : (name == key) = false := by simp [hname]
        rw [hbeq] at hlookup
        simp [ih hlookup]

private theorem SubstTopological.order_length_le (b : Subst)
    (topological : SubstTopological b) :
    topological.order.length ≤ b.length := by
  have hsubperm : topological.order.Subperm (b.map Prod.fst) := by
    apply List.subperm_of_subset topological.nodup
    intro name hname
    apply mem_subst_keys_of_lookup_ne_none b name
    exact (topological.domain name).1 hname
  simpa using hsubperm.length_le

private def AtomRankBelow (b : Subst) (order : List String)
    (bound : Nat) (a : Atom) : Prop :=
  ∀ name, name ∈ a.vars → Metta.Subst.lookup b name ≠ none →
    order.idxOf name < bound

private theorem substN_succ_eq_of_rankBelow (b : Subst)
    (topological : SubstTopological b) :
    ∀ bound a, AtomRankBelow b topological.order bound a →
      substN (bound + 1) b a = substN bound b a := by
  intro bound
  induction bound with
  | zero =>
      intro a hrank
      induction a using machineAtomRecAux with
      | sym name => simp [substN]
      | gnd ground => simp [substN]
      | var name =>
          simp only [substN]
          cases hlookup : Metta.Subst.lookup b name with
          | none => rfl
          | some value =>
              have himpossible := hrank name (by simp [Atom.vars]) (by simp [hlookup])
              omega
      | expr atoms atomIH =>
          simp only [substN, Atom.expr.injEq]
          have hchildren : ∀ child ∈ atoms, substN 1 b child = child := by
            intro child hchild
            have hchildStable := atomIH child hchild (by
              intro name hname hlookup
              apply hrank name
              · simp only [Atom.vars]
                rw [List.mem_flatten]
                exact ⟨child.vars, List.mem_map_of_mem hchild, hname⟩
              · exact hlookup)
            simpa [substN] using hchildStable
          rw [List.map_congr_left hchildren]
          simp
  | succ bound boundIH =>
      intro a hrank
      induction a using machineAtomRecAux with
      | sym name => simp [substN]
      | gnd ground => simp [substN]
      | var name =>
          simp only [substN]
          cases hlookup : Metta.Subst.lookup b name with
          | none => rfl
          | some value =>
              apply boundIH value
              intro dependency hdependency hdependencyBound
              have hsource : topological.order.idxOf name < bound + 1 :=
                hrank name (by simp [Atom.vars]) (by simp [hlookup])
              have hdecreases := topological.decreases name value dependency
                hlookup hdependency hdependencyBound
              omega
      | expr atoms atomIH =>
          simp only [substN, Atom.expr.injEq]
          rw [List.map_congr_left]
          intro child hchild
          apply atomIH child hchild
          intro name hname hlookup
          apply hrank name
          · simp only [Atom.vars]
            rw [List.mem_flatten]
            exact ⟨child.vars, List.mem_map_of_mem hchild, hname⟩
          · exact hlookup

private theorem atomRankBelow_orderLength (b : Subst)
    (topological : SubstTopological b) (a : Atom) :
    AtomRankBelow b topological.order topological.order.length a := by
  intro name hname hlookup
  apply List.idxOf_lt_length_of_mem
  exact (topological.domain name).2 hlookup

private theorem substN_eq_orderLength_of_topological (b : Subst)
    (topological : SubstTopological b) (a : Atom) (fuel : Nat)
    (hbound : topological.order.length ≤ fuel) :
    substN fuel b a = substN topological.order.length b a := by
  induction fuel with
  | zero =>
      have hzero : topological.order.length = 0 := by omega
      simp [hzero]
  | succ fuel fuelIH =>
      by_cases hnext : topological.order.length ≤ fuel
      · rw [substN_succ_eq_of_rankBelow b topological fuel a]
        · exact fuelIH hnext
        · intro name hname hlookup
          exact Nat.lt_of_lt_of_le
            (atomRankBelow_orderLength b topological a name hname hlookup)
            hnext
      · have heq : fuel + 1 = topological.order.length := by omega
        rw [heq]

/-- A topological certificate discharges the deep-substitution stability
    interface at the exact machine fuel bound. -/
theorem SubstTopological.deepStable (b : Subst)
    (topological : SubstTopological b) : DeepSubstStable b := by
  intro a fuel hfuel
  unfold subst
  have horderFuel : topological.order.length ≤ fuel :=
    Nat.le_trans (topological.order_length_le b) (by omega)
  have horderMachine : topological.order.length ≤ b.length + 1 := by
    exact Nat.le_trans (topological.order_length_le b)
      (Nat.le_add_right _ _)
  rw [substN_eq_orderLength_of_topological b topological a fuel horderFuel,
    substN_eq_orderLength_of_topological b topological a (b.length + 1)
      horderMachine]

/-- A lookup in a topologically ordered substitution denotes exactly its
    fully resolved target.  This is the semantic meaning of one stored
    binding and avoids exposing the machine's length-bounded `substN` fuel. -/
theorem SubstTopological.subst_var_of_lookup (b : Subst)
    (topological : SubstTopological b) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup b name = some value) :
    subst b (Atom.var name) = subst b value := by
  unfold subst
  simp only [substN, hlookup]
  have horderLength : topological.order.length ≤ b.length :=
    topological.order_length_le b
  rw [substN_eq_orderLength_of_topological b topological value b.length
      horderLength,
    substN_eq_orderLength_of_topological b topological value (b.length + 1)
      (Nat.le_trans horderLength (Nat.le_add_right _ _))]

private theorem substN_resolvesDomain (b : Subst)
    (topological : SubstTopological b) :
    ∀ fuel a, AtomRankBelow b topological.order fuel a →
      ∀ name, name ∈ (substN fuel b a).vars →
        Metta.Subst.lookup b name = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro a hrank name hname
      simp only [substN] at hname
      cases hlookup : Metta.Subst.lookup b name with
      | none => rfl
      | some value =>
          have himpossible := hrank name hname (by simp [hlookup])
          omega
  | succ fuel fuelIH =>
      intro a hrank
      induction a using machineAtomRecAux with
      | sym symbol => simp [substN, Atom.vars]
      | gnd ground => simp [substN, Atom.vars]
      | var source =>
          simp only [substN]
          cases hsource : Metta.Subst.lookup b source with
          | none =>
              intro name hname
              simp only [Atom.vars, List.mem_singleton] at hname
              subst name
              exact hsource
          | some value =>
              apply fuelIH value
              intro dependency hdependency hdependencyBound
              have hsourceRank :
                  topological.order.idxOf source < fuel + 1 :=
                hrank source (by simp [Atom.vars]) (by simp [hsource])
              have hdependencyRank := topological.decreases source value
                dependency hsource hdependency hdependencyBound
              omega
      | expr atoms atomIH =>
          simp only [substN, Atom.vars]
          intro name hname
          rw [List.mem_flatten] at hname
          rcases hname with ⟨variableList, hvariableList, hname⟩
          rcases List.mem_map.mp hvariableList with
            ⟨substitutedChild, hsubstitutedChild, rfl⟩
          rcases List.mem_map.mp hsubstitutedChild with
            ⟨child, hchild, rfl⟩
          apply atomIH child hchild
          · intro dependency hdependency hdependencyBound
            apply hrank dependency
            · simp only [Atom.vars]
              rw [List.mem_flatten]
              exact ⟨child.vars, List.mem_map_of_mem hchild, hdependency⟩
            · exact hdependencyBound
          · exact hname

/-- Deep substitution under a topological substitution eliminates every
    variable in that substitution's domain.  Free variables may remain, but
    no output variable can still be looked up in `b`. -/
theorem SubstTopological.subst_resolvesDomain (b : Subst)
    (topological : SubstTopological b) (a : Atom) (name : String)
    (hname : name ∈ (subst b a).vars) :
    Metta.Subst.lookup b name = none := by
  unfold subst at hname
  apply substN_resolvesDomain b topological (b.length + 1) a
  · intro source hsource hsourceBound
    have hrank : topological.order.idxOf source <
        topological.order.length :=
      List.idxOf_lt_length_of_mem
        ((topological.domain source).2 hsourceBound)
    have hlength := topological.order_length_le b
    omega
  · exact hname

private theorem substN_congr_of_agreeOn (visible : String → Prop)
    (left right : Subst)
    (hagree : SubstAgreeOn visible left right)
    (hclosed : SubstClosedOn visible left) :
    ∀ fuel a, AtomVarsIn visible a →
      substN fuel left a = substN fuel right a := by
  intro fuel
  induction fuel with
  | zero =>
      intro a hvisible
      simp [substN]
  | succ fuel fuelIH =>
      intro a hvisible
      induction a using machineAtomRecAux with
      | sym name => simp [substN]
      | gnd ground => simp [substN]
      | var name =>
          have hname : visible name := by
            apply hvisible name
            simp [Atom.vars]
          have hlookup := hagree name hname
          simp only [substN]
          rw [hlookup]
          cases hright : Metta.Subst.lookup right name with
          | none => rfl
          | some value =>
              apply fuelIH value
              intro dependency hdependency
              apply hclosed name value hname
              · simpa [hlookup] using hright
              · exact hdependency
      | expr atoms atomIH =>
          simp only [substN, Atom.expr.injEq]
          rw [List.map_congr_left]
          intro child hchild
          apply atomIH child hchild
          intro name hname
          apply hvisible name
          simp only [Atom.vars]
          rw [List.mem_flatten]
          exact ⟨child.vars, List.mem_map_of_mem hchild, hname⟩

/-- Stable deep substitutions that agree on a substitution-closed visible
    set denote the same value on every atom supported by that set, even when
    their raw lists have different lengths. -/
theorem subst_congr_of_agreeOn (visible : String → Prop)
    (left right : Subst)
    (hagree : SubstAgreeOn visible left right)
    (hclosed : SubstClosedOn visible left)
    (hleft : DeepSubstStable left) (hright : DeepSubstStable right)
    (a : Atom) (hvars : AtomVarsIn visible a) :
    subst left a = subst right a := by
  let fuel := Nat.max (left.length + 1) (right.length + 1)
  have hleftFuel : left.length + 1 ≤ fuel := Nat.le_max_left _ _
  have hrightFuel : right.length + 1 ≤ fuel := Nat.le_max_right _ _
  calc
    subst left a = substN fuel left a := (hleft a fuel hleftFuel).symm
    _ = substN fuel right a :=
      substN_congr_of_agreeOn visible left right hagree hclosed fuel a hvars
    _ = subst right a := hright a fuel hrightFuel

private theorem addAtomVars_preserves_contains (tracked : String)
    (acc : VarSet) (h : acc.contains tracked = true) (a : Atom) :
    (addAtomVars acc a).contains tracked = true := by
  induction a using machineAtomRecAux generalizing acc with
  | sym _ => simpa [addAtomVars] using h
  | var x => simp [addAtomVars, h]
  | gnd _ => simpa [addAtomVars] using h
  | expr xs ih =>
      simp only [addAtomVars]
      induction xs generalizing acc with
      | nil => exact h
      | cons a rest restIH =>
          simp only [List.foldl_cons]
          apply restIH
          · intro z hz
            exact ih z (by simp [hz])
          · exact ih a (by simp) acc h

private theorem foldl_addAtomVars_preserves_contains (tracked : String)
    (xs : List Atom) (acc : VarSet) (h : acc.contains tracked = true) :
    (xs.foldl addAtomVars acc).contains tracked = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons a rest ih =>
      simp only [List.foldl_cons]
      apply ih
      exact addAtomVars_preserves_contains tracked acc h a

private theorem addAtomVars_contains_of_mem_vars (tracked : String)
    (a : Atom) (acc : VarSet) (hmem : tracked ∈ a.vars) :
    (addAtomVars acc a).contains tracked = true := by
  induction a using machineAtomRecAux generalizing acc with
  | sym name => simp [Atom.vars] at hmem
  | var name =>
      simp only [Atom.vars, List.mem_singleton] at hmem
      subst tracked
      simp [addAtomVars]
  | gnd ground => simp [Atom.vars] at hmem
  | expr xs ih =>
      simp only [Atom.vars] at hmem
      simp only [addAtomVars]
      induction xs generalizing acc with
      | nil => simp at hmem
      | cons atom rest restIH =>
          simp only [List.map_cons, List.flatten_cons,
            List.mem_append] at hmem
          simp only [List.foldl_cons]
          rcases hmem with hhere | hrest
          · apply foldl_addAtomVars_preserves_contains
            exact ih atom (by simp) acc hhere
          · apply restIH
            · intro child hchild
              exact ih child (by simp [hchild])
            · exact hrest

mutual

private theorem goalVarsFuel_preserves_contains (fuel : Nat)
    (tracked : String) (goal : Goal) (acc : VarSet)
    (h : acc.contains tracked = true) :
    (goalVarsFuel fuel goal acc).contains tracked = true := by
  cases fuel with
  | zero => exact h
  | succ fuel =>
      cases goal with
      | call f args res | bin f args res | wact f args res =>
          exact foldl_addAtomVars_preserves_contains tracked args _
            (addAtomVars_preserves_contains tracked acc h res)
      | callDyn head args res =>
          exact foldl_addAtomVars_preserves_contains tracked args _
            (addAtomVars_preserves_contains tracked _
              (addAtomVars_preserves_contains tracked acc h res) head)
      | evalg value res | spread value res =>
          exact addAtomVars_preserves_contains tracked _
            (addAtomVars_preserves_contains tracked acc h res) value
      | catchg tmpl sub res | findall tmpl sub res | onceg tmpl sub res =>
          exact goalsVarsFuel_preserves_contains fuel tracked sub _
            (addAtomVars_preserves_contains tracked _
              (addAtomVars_preserves_contains tracked acc h res) tmpl)
      | softcut tmpl sub thn els =>
          exact goalsVarsFuel_preserves_contains fuel tracked els _
            (goalsVarsFuel_preserves_contains fuel tracked thn _
              (goalsVarsFuel_preserves_contains fuel tracked sub _
                (addAtomVars_preserves_contains tracked acc h tmpl)))
      | eq left right =>
          exact addAtomVars_preserves_contains tracked _
            (addAtomVars_preserves_contains tracked acc h left) right
      | cut | cutAt _ => exact h
      | transactiong tmpl sub =>
          exact goalsVarsFuel_preserves_contains fuel tracked sub _
            (addAtomVars_preserves_contains tracked acc h tmpl)
      | amb branches res =>
          exact branchVarsFuel_preserves_contains fuel tracked branches _
            (addAtomVars_preserves_contains tracked acc h res)
      | ite cond thn els res =>
          exact goalsVarsFuel_preserves_contains fuel tracked els.2 _
            (addAtomVars_preserves_contains tracked _
              (goalsVarsFuel_preserves_contains fuel tracked thn.2 _
                (addAtomVars_preserves_contains tracked _
                  (addAtomVars_preserves_contains tracked _
                    (addAtomVars_preserves_contains tracked acc h res) cond)
                  thn.1))
              els.1)
      | smatch pat =>
          exact addAtomVars_preserves_contains tracked acc h pat

private theorem goalsVarsFuel_preserves_contains (fuel : Nat)
    (tracked : String) (goals : List Goal) (acc : VarSet)
    (h : acc.contains tracked = true) :
    (goalsVarsFuel fuel goals acc).contains tracked = true := by
  cases fuel with
  | zero => exact h
  | succ fuel =>
      cases goals with
      | nil => exact h
      | cons goal rest =>
          exact goalsVarsFuel_preserves_contains fuel tracked rest _
            (goalVarsFuel_preserves_contains fuel tracked goal acc h)

private theorem branchVarsFuel_preserves_contains (fuel : Nat)
    (tracked : String) (branches : List (Atom × List Goal)) (acc : VarSet)
    (h : acc.contains tracked = true) :
    (branchVarsFuel fuel branches acc).contains tracked = true := by
  cases fuel with
  | zero => exact h
  | succ fuel =>
      cases branches with
      | nil => exact h
      | cons branch rest =>
          exact branchVarsFuel_preserves_contains fuel tracked rest _
            (goalsVarsFuel_preserves_contains fuel tracked branch.2 _
              (addAtomVars_preserves_contains tracked acc h branch.1))

end

private theorem goalsVarsFuel_eq_left_mem (tracked : String) :
    ∀ fuel goals acc rhs,
      goalsFuel goals + 1 ≤ fuel →
      Goal.eq (Atom.var tracked) rhs ∈ goals →
      (goalsVarsFuel fuel goals acc).contains tracked = true := by
  intro fuel goals
  induction goals generalizing fuel with
  | nil => simp
  | cons goal rest ih =>
      intro acc rhs hfuel hmem
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [goalsVarsFuel]
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst goal
            have hfuelPos : 0 < fuel := by
              simp only [goalsFuel, goalFuel] at hfuel
              omega
            obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hfuelPos)
            apply goalsVarsFuel_preserves_contains
            simp only [goalVarsFuel]
            apply addAtomVars_preserves_contains
            simp [addAtomVars]
          · apply ih fuel (goalVarsFuel fuel goal acc) rhs
            · simp only [goalsFuel] at hfuel
              have hrestLe : goalsFuel rest ≤
                  Nat.max (goalFuel goal) (goalsFuel rest) :=
                Nat.le_max_right _ _
              omega
            · exact htail

private theorem goalsVarsFuel_eq_left_atom_mem (tracked : String) :
    ∀ fuel goals acc left rhs,
      goalsFuel goals + 1 ≤ fuel →
      Goal.eq left rhs ∈ goals →
      tracked ∈ left.vars →
      (goalsVarsFuel fuel goals acc).contains tracked = true := by
  intro fuel goals
  induction goals generalizing fuel with
  | nil => simp
  | cons goal rest ih =>
      intro acc left rhs hfuel hmem htracked
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [goalsVarsFuel]
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst goal
            have hfuelPos : 0 < fuel := by
              simp only [goalsFuel, goalFuel] at hfuel
              omega
            obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hfuelPos)
            apply goalsVarsFuel_preserves_contains
            simp only [goalVarsFuel]
            apply addAtomVars_preserves_contains
            exact addAtomVars_contains_of_mem_vars tracked left _ htracked
          · apply ih fuel (goalVarsFuel fuel goal acc) left rhs
            · simp only [goalsFuel] at hfuel
              have hrestLe : goalsFuel rest ≤
                  Nat.max (goalFuel goal) (goalsFuel rest) :=
                Nat.le_max_right _ _
              omega
            · exact htail
            · exact htracked

private theorem goalsVarsFuel_eq_right_mem (tracked : String) :
    ∀ fuel goals acc left rhs,
      goalsFuel goals + 1 ≤ fuel →
      Goal.eq left rhs ∈ goals →
      tracked ∈ rhs.vars →
      (goalsVarsFuel fuel goals acc).contains tracked = true := by
  intro fuel goals
  induction goals generalizing fuel with
  | nil => simp
  | cons goal rest ih =>
      intro acc left rhs hfuel hmem htracked
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [goalsVarsFuel]
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst goal
            have hfuelPos : 0 < fuel := by
              simp only [goalsFuel, goalFuel] at hfuel
              omega
            obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hfuelPos)
            apply goalsVarsFuel_preserves_contains
            simp only [goalVarsFuel]
            exact addAtomVars_contains_of_mem_vars tracked rhs _ htracked
          · apply ih fuel (goalVarsFuel fuel goal acc) left rhs
            · simp only [goalsFuel] at hfuel
              have hrestLe : goalsFuel rest ≤
                  Nat.max (goalFuel goal) (goalsFuel rest) :=
                Nat.le_max_right _ _
              omega
            · exact htail
            · exact htracked

private theorem addFreshAtomVars_preserves_contains (tracked : String)
    (state : VarSet × VarSet) (h : state.1.contains tracked = true)
    (a : Atom) :
    (addFreshAtomVars state a).1.contains tracked = true := by
  induction a using machineAtomRecAux generalizing state with
  | sym _ => simpa [addFreshAtomVars] using h
  | var x =>
      simp only [addFreshAtomVars]
      split
      · exact h
      · simp [h]
  | gnd _ => simpa [addFreshAtomVars] using h
  | expr xs ih =>
      simp only [addFreshAtomVars]
      induction xs generalizing state with
      | nil => exact h
      | cons a rest restIH =>
          simp only [List.foldl_cons]
          apply restIH
          · intro z hz
            exact ih z (by simp [hz])
          · exact ih a (by simp) state h

private theorem addFreshAtomVars_membership (tracked : String)
    (state : VarSet × VarSet) (a : Atom) :
    (tracked ∈ (addFreshAtomVars state a).1 ↔
        tracked ∈ state.1 ∨ tracked ∈ a.vars) ∧
      (tracked ∈ (addFreshAtomVars state a).2 ↔
        tracked ∈ state.2 ∨
          (tracked ∈ a.vars ∧ tracked ∉ state.1)) := by
  induction a using machineAtomRecAux generalizing state with
  | sym name => simp [addFreshAtomVars, Atom.vars]
  | gnd ground => simp [addFreshAtomVars, Atom.vars]
  | var name =>
      simp only [addFreshAtomVars, Atom.vars, List.mem_singleton]
      split
      next halready =>
        have hmem : name ∈ state.1 :=
          Std.HashSet.mem_iff_contains.mpr halready
        constructor
        · constructor
          · exact Or.inl
          · intro htracked
            rcases htracked with htracked | htracked
            · exact htracked
            · subst tracked
              exact hmem
        · constructor
          · exact Or.inl
          · intro htracked
            rcases htracked with htracked | ⟨htracked, hnotmem⟩
            · exact htracked
            · subst tracked
              exact (hnotmem hmem).elim
      next hnew =>
        have hnotmem : name ∉ state.1 := by
          intro hmem
          exact hnew (Std.HashSet.mem_iff_contains.mp hmem)
        simp only [Std.HashSet.mem_insert, beq_iff_eq]
        constructor
        · constructor
          · intro htracked
            rcases htracked with htracked | htracked
            · exact Or.inr htracked.symm
            · exact Or.inl htracked
          · intro htracked
            rcases htracked with htracked | htracked
            · exact Or.inr htracked
            · exact Or.inl htracked.symm
        · constructor
          · intro htracked
            rcases htracked with htracked | htracked
            · subst tracked
              exact Or.inr ⟨rfl, hnotmem⟩
            · exact Or.inl htracked
          · intro htracked
            rcases htracked with htracked | ⟨htracked, _⟩
            · exact Or.inr htracked
            · exact Or.inl htracked.symm
  | expr atoms atomIH =>
      simp only [addFreshAtomVars, Atom.vars]
      induction atoms generalizing state with
      | nil => simp
      | cons atom rest restIH =>
          simp only [List.foldl_cons, List.map_cons, List.flatten_cons,
            List.mem_append]
          have hatom := atomIH atom (by simp) state
          have hrest := restIH
            (fun child hchild => atomIH child (by simp [hchild]))
            (addFreshAtomVars state atom)
          rw [hrest.1, hrest.2, hatom.1, hatom.2]
          constructor
          · constructor
            · intro htracked
              rcases htracked with (htracked | htracked) | htracked
              · exact Or.inl htracked
              · exact Or.inr (Or.inl htracked)
              · exact Or.inr (Or.inr htracked)
            · intro htracked
              rcases htracked with htracked | (htracked | htracked)
              · exact Or.inl (Or.inl htracked)
              · exact Or.inl (Or.inr htracked)
              · exact Or.inr htracked
          · constructor
            · intro htracked
              rcases htracked with (htracked | ⟨htracked, hnotmem⟩) |
                  ⟨htracked, hnotmem⟩
              · exact Or.inl htracked
              · exact Or.inr ⟨Or.inl htracked, hnotmem⟩
              · exact Or.inr ⟨Or.inr htracked, fun hmem =>
                  hnotmem (Or.inl hmem)⟩
            · intro htracked
              rcases htracked with htracked | ⟨htracked, hnotmem⟩
              · exact Or.inl (Or.inl htracked)
              · rcases htracked with htracked | htracked
                · exact Or.inl (Or.inr ⟨htracked, hnotmem⟩)
                · by_cases hinAtom : tracked ∈ atom.vars
                  · exact Or.inl (Or.inr ⟨hinAtom, hnotmem⟩)
                  · exact Or.inr ⟨htracked, fun hmem => by
                      rcases hmem with hmem | hmem
                      · exact hnotmem hmem
                      · exact hinAtom hmem⟩

private theorem foldl_lookup_preserves_contains (index : SubstIndex)
    (tracked : String) (xs : List String) (state : VarSet × VarSet)
    (h : state.1.contains tracked = true) :
    (xs.foldl
      (fun acc x =>
        match index.get? x with
        | some a => addFreshAtomVars acc a
        | none => acc)
      state).1.contains tracked = true := by
  induction xs generalizing state with
  | nil => exact h
  | cons x rest ih =>
      simp only [List.foldl_cons]
      apply ih
      cases hx : index.get? x with
      | none => exact h
      | some a => exact addFreshAtomVars_preserves_contains tracked state h a

private theorem foldl_lookup_membership (index : SubstIndex)
    (tracked : String) (xs : List String) (state : VarSet × VarSet) :
    let expanded := xs.foldl
      (fun acc source =>
        match index[source]? with
        | some value => addFreshAtomVars acc value
        | none => acc)
      state
    let discovered := ∃ source ∈ xs, ∃ value,
      index[source]? = some value ∧ tracked ∈ value.vars
    (tracked ∈ expanded.1 ↔ tracked ∈ state.1 ∨ discovered) ∧
      (tracked ∈ expanded.2 ↔
        tracked ∈ state.2 ∨ (discovered ∧ tracked ∉ state.1)) := by
  dsimp only
  induction xs generalizing state with
  | nil => simp
  | cons source rest ih =>
      simp only [List.foldl_cons, List.mem_cons]
      cases hlookup : index[source]? with
      | none =>
          have hrest := ih state
          rw [hrest.1, hrest.2]
          simp [hlookup]
      | some value =>
          have hadded := addFreshAtomVars_membership tracked state value
          have hrest := ih (addFreshAtomVars state value)
          rw [hrest.1, hrest.2, hadded.1, hadded.2]
          grind

private structure CloseSubstInvariant (b : Subst)
    (topological : SubstTopological b) (fuel : Nat)
    (live frontier : VarSet) : Prop where
  frontier_live : ∀ name, name ∈ frontier → name ∈ live
  processed : ∀ source value, source ∈ live → source ∉ frontier →
    Metta.Subst.lookup b source = some value →
      ∀ dependency, dependency ∈ value.vars → dependency ∈ live
  frontier_rank : ∀ source, source ∈ frontier →
    Metta.Subst.lookup b source ≠ none →
      topological.order.idxOf source < fuel

private theorem closeSubstInvariant_step (b : Subst)
    (topological : SubstTopological b) (fuel : Nat)
    (live frontier : VarSet)
    (invariant : CloseSubstInvariant b topological (fuel + 1)
      live frontier) :
    let next := frontier.toList.foldl
      (fun state source =>
        match (substIndex b)[source]? with
        | some value => addFreshAtomVars state value
        | none => state)
      (live, Std.HashSet.emptyWithCapacity frontier.size)
    CloseSubstInvariant b topological fuel next.1 next.2 := by
  dsimp only
  let next := frontier.toList.foldl
    (fun state source =>
      match (substIndex b)[source]? with
      | some value => addFreshAtomVars state value
      | none => state)
    (live, Std.HashSet.emptyWithCapacity frontier.size)
  have membership (tracked : String) :=
    foldl_lookup_membership (substIndex b) tracked frontier.toList
      (live, Std.HashSet.emptyWithCapacity frontier.size)
  change CloseSubstInvariant b topological fuel next.1 next.2
  refine
    { frontier_live := ?_
      processed := ?_
      frontier_rank := ?_ }
  · intro tracked hfrontier
    have hfrontier' := (membership tracked).2.mp hfrontier
    have hdiscovered : ∃ source ∈ frontier.toList, ∃ value,
        (substIndex b)[source]? = some value ∧ tracked ∈ value.vars := by
      have hpair :
          (∃ source ∈ frontier.toList, ∃ value,
            (substIndex b)[source]? = some value ∧ tracked ∈ value.vars) ∧
            tracked ∉ live := by
        simpa using hfrontier'
      exact hpair.1
    exact (membership tracked).1.mpr (Or.inr hdiscovered)
  · intro source value hsource hnotFrontier hlookup dependency hdependency
    have hsource' := (membership source).1.mp hsource
    have hsourceOld : source ∈ live := by
      rcases hsource' with hsourceOld | hdiscovered
      · exact hsourceOld
      · by_cases hsourceOld : source ∈ live
        · exact hsourceOld
        · exact False.elim (hnotFrontier
            ((membership source).2.mpr (Or.inr
              ⟨hdiscovered, hsourceOld⟩)))
    apply (membership dependency).1.mpr
    by_cases hsourceFrontier : source ∈ frontier
    · apply Or.inr
      refine ⟨source, ?_, value, ?_, hdependency⟩
      · simpa using hsourceFrontier
      · rw [substIndex_getElem?]
        exact hlookup
    · exact Or.inl
        (invariant.processed source value hsourceOld hsourceFrontier hlookup
          dependency hdependency)
  · intro source hsourceFrontier hsourceBound
    have hsourceFrontier' := (membership source).2.mp hsourceFrontier
    have hdiscovered : ∃ parent ∈ frontier.toList, ∃ value,
        (substIndex b)[parent]? = some value ∧ source ∈ value.vars := by
      have hpair :
          (∃ parent ∈ frontier.toList, ∃ value,
            (substIndex b)[parent]? = some value ∧ source ∈ value.vars) ∧
            source ∉ live := by
        simpa using hsourceFrontier'
      exact hpair.1
    rcases hdiscovered with ⟨parent, hparentFrontier, value,
      hparentLookup, hsourceDependency⟩
    have hparentFrontier' : parent ∈ frontier := by
      simpa using hparentFrontier
    have hparentLookup' :
        Metta.Subst.lookup b parent = some value := by
      simpa [substIndex_getElem?] using hparentLookup
    have hparentRank : topological.order.idxOf parent < fuel + 1 :=
      invariant.frontier_rank parent hparentFrontier' (by
        simp [hparentLookup'])
    have hdecreases : topological.order.idxOf source <
        topological.order.idxOf parent :=
      topological.decreases parent value source hparentLookup'
        hsourceDependency hsourceBound
    omega

theorem closeSubstVars_preserves_contains (index : SubstIndex)
    (fuel : Nat) (live frontier : VarSet) (tracked : String)
    (h : live.contains tracked = true) :
    (closeSubstVars index fuel live frontier).contains tracked = true := by
  induction fuel generalizing live frontier with
  | zero => exact h
  | succ fuel ih =>
      simp only [closeSubstVars]
      split
      · exact h
      · apply ih
        exact foldl_lookup_preserves_contains index tracked frontier.toList
          (live, Std.HashSet.emptyWithCapacity frontier.size) h

private theorem closeSubstVars_closed_of_invariant (b : Subst)
    (topological : SubstTopological b) :
    ∀ fuel live frontier,
      CloseSubstInvariant b topological fuel live frontier →
        SubstClosedOn
          (fun name => name ∈
            closeSubstVars (substIndex b) fuel live frontier)
          b := by
  intro fuel
  induction fuel with
  | zero =>
      intro live frontier invariant
      simp only [closeSubstVars]
      intro source value hsource hlookup dependency hdependency
      by_cases hfrontier : source ∈ frontier
      · have hrank := invariant.frontier_rank source hfrontier (by
          simp [hlookup])
        omega
      · exact invariant.processed source value hsource hfrontier hlookup
          dependency hdependency
  | succ fuel ih =>
      intro live frontier invariant
      simp only [closeSubstVars]
      split
      next hempty =>
        change SubstClosedOn (fun name => name ∈ live) b
        have hisEmpty : frontier.isEmpty = true := by
          rw [Std.HashSet.isEmpty_eq_size_eq_zero]
          exact hempty
        have hnotFrontier : ∀ name, name ∉ frontier :=
          Std.HashSet.isEmpty_iff_forall_not_mem.mp hisEmpty
        intro source value hsource hlookup dependency hdependency
        exact invariant.processed source value hsource
          (hnotFrontier source) hlookup dependency hdependency
      next hnonempty =>
        apply ih
        exact closeSubstInvariant_step b topological fuel live frontier
          invariant

private theorem closeSubstVars_closed_of_topological (b : Subst)
    (topological : SubstTopological b) (roots : VarSet) :
    SubstClosedOn
      (fun name => name ∈ closeSubstVars (substIndex b) (b.length + 1)
        roots roots)
      b := by
  apply closeSubstVars_closed_of_invariant b topological
  refine
    { frontier_live := fun _ hmem => hmem
      processed := ?_
      frontier_rank := ?_ }
  · intro source value hsource hnotFrontier
    exact False.elim (hnotFrontier hsource)
  · intro source _ hlookup
    have horder : source ∈ topological.order :=
      (topological.domain source).2 hlookup
    have hrank : topological.order.idxOf source <
        topological.order.length :=
      List.idxOf_lt_length_of_mem horder
    have hlength := topological.order_length_le b
    omega

private theorem foldl_lookup_eq_self_of_stable (index : SubstIndex)
    (stable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state)
    (xs : List String) (state : VarSet × VarSet) :
    xs.foldl
      (fun acc x =>
        match index.get? x with
        | some a => addFreshAtomVars acc a
        | none => acc)
      state = state := by
  induction xs generalizing state with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.foldl_cons]
      cases hx : index.get? x with
      | none => exact ih state
      | some a =>
          change rest.foldl
            (fun acc x =>
              match index.get? x with
              | some a => addFreshAtomVars acc a
              | none => acc)
            (addFreshAtomVars state a) = state
          rw [stable x a state hx]
          exact ih state

private theorem foldl_lookup_eq_fixed_state (index : SubstIndex)
    (state : VarSet × VarSet)
    (stable : ∀ x a, index.get? x = some a →
      addFreshAtomVars state a = state)
    (xs : List String) :
    xs.foldl
      (fun acc x =>
        match index.get? x with
        | some a => addFreshAtomVars acc a
        | none => acc)
      state = state := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.foldl_cons]
      cases hx : index.get? x with
      | none => exact ih
      | some a =>
          change rest.foldl
            (fun acc x =>
              match index.get? x with
              | some a => addFreshAtomVars acc a
              | none => acc)
            (addFreshAtomVars state a) = state
          rw [stable x a hx]
          exact ih

private theorem closeSubstVars_empty_frontier (index : SubstIndex)
    (fuel : Nat) (live : VarSet) :
    closeSubstVars index fuel live (Std.HashSet.emptyWithCapacity live.size) =
      live := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [closeSubstVars]

private theorem closeSubstVars_eq_live_of_initial_stable
    (index : SubstIndex) (fuel : Nat) (live : VarSet)
    (stable : ∀ x a, index.get? x = some a →
      addFreshAtomVars
        (live, Std.HashSet.emptyWithCapacity live.size) a =
      (live, Std.HashSet.emptyWithCapacity live.size)) :
    closeSubstVars index (fuel + 1) live live = live := by
  simp only [closeSubstVars]
  split
  · rfl
  · rw [foldl_lookup_eq_fixed_state index _ stable]
    exact closeSubstVars_empty_frontier index fuel live

private theorem closeSubstVars_eq_live_of_stable (index : SubstIndex)
    (stable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state)
    (fuel : Nat) (live frontier : VarSet) :
    closeSubstVars index fuel live frontier = live := by
  induction fuel generalizing live frontier with
  | zero => rfl
  | succ fuel ih =>
      simp only [closeSubstVars]
      split
      · rfl
      · rw [foldl_lookup_eq_self_of_stable index stable]
        exact ih live (Std.HashSet.emptyWithCapacity frontier.size)

def filterLiveSubst (live : VarSet) : VarSet → Subst → Subst
  | _, [] => []
  | seen, (x, a) :: rest =>
      if live.contains x && !seen.contains x then
        (x, a) :: filterLiveSubst live (seen.insert x) rest
      else
        filterLiveSubst live seen rest

theorem filterLiveSubst_sublist (live seen : VarSet) (b : Subst) :
    List.Sublist (filterLiveSubst live seen b) b := by
  induction b generalizing seen with
  | nil => exact List.Sublist.slnil
  | cons binding rest ih =>
      simp only [filterLiveSubst]
      split
      · exact List.Sublist.cons_cons binding (ih (seen.insert binding.1))
      · exact List.Sublist.cons binding (ih seen)

theorem filterLiveSubst_eq_self_of_length_eq (live seen : VarSet)
    (b : Subst)
    (lengthEq : (filterLiveSubst live seen b).length = b.length) :
    filterLiveSubst live seen b = b :=
  (filterLiveSubst_sublist live seen b).eq_of_length lengthEq

private theorem filterLiveSubst_eq_self (live seen : VarSet) (b : Subst)
    (hlive : ∀ x a, (x, a) ∈ b → live.contains x = true)
    (hunseen : ∀ x a, (x, a) ∈ b → seen.contains x = false)
    (hnodup : (b.map Prod.fst).Nodup) :
    filterLiveSubst live seen b = b := by
  induction b generalizing seen with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨x, a⟩
      have hxLive : live.contains x = true := hlive x a (by simp)
      have hxUnseen : seen.contains x = false := hunseen x a (by simp)
      have hxRest : x ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hnodup).1
      simp only [filterLiveSubst, hxLive, hxUnseen, Bool.not_false,
        Bool.and_true, if_true, List.cons.injEq, true_and]
      apply ih
      · intro y value hy
        exact hlive y value (by simp [hy])
      · intro y value hy
        have hxy : x ≠ y := by
          intro hEq
          subst y
          exact hxRest (List.mem_map_of_mem hy)
        simp [Std.HashSet.contains_insert, hxy, hunseen y value (by simp [hy])]
      · exact (List.nodup_cons.mp hnodup).2

theorem filterLiveSubst_lookup_of_live (live seen : VarSet)
    (b : Subst) (x : String)
    (hlive : live.contains x = true)
    (hunseen : seen.contains x = false) :
    Metta.Subst.lookup (filterLiveSubst live seen b) x =
      Metta.Subst.lookup b x := by
  induction b generalizing seen with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨y, value⟩
      by_cases hxy : x = y
      · subst y
        simp [filterLiveSubst, Metta.Subst.lookup, hlive, hunseen]
      · simp only [filterLiveSubst, Metta.Subst.lookup]
        have hbeq : (x == y) = false := by simp [hxy]
        have hyx : y ≠ x := Ne.symm hxy
        rw [hbeq]
        split
        next hkeep =>
          simp only [Metta.Subst.lookup, hbeq, Bool.false_eq_true, if_false]
          apply ih (seen.insert y)
          simp [Std.HashSet.contains_insert, hyx, hunseen]
        next hskip => exact ih seen hunseen

theorem filterLiveSubst_keys_live (live seen : VarSet) (b : Subst) :
    ∀ name, name ∈ (filterLiveSubst live seen b).map Prod.fst →
      live.contains name = true := by
  induction b generalizing seen with
  | nil => simp [filterLiveSubst]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [filterLiveSubst]
      split
      next hkeep =>
        have hkeyLive : live.contains key = true := by
          have hparts := hkeep
          simp only [Bool.and_eq_true] at hparts
          exact hparts.1
        intro name hmem
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hrest
        · exact hkeyLive
        · exact ih (seen.insert key) name hrest
      next hskip => exact ih seen

theorem filterLiveSubst_keys_unseen (live seen : VarSet) (b : Subst) :
    ∀ name, name ∈ (filterLiveSubst live seen b).map Prod.fst →
      seen.contains name = false := by
  induction b generalizing seen with
  | nil => simp [filterLiveSubst]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [filterLiveSubst]
      split
      next hkeep =>
        have hparts := hkeep
        simp only [Bool.and_eq_true] at hparts
        intro name hmem
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hrest
        · cases hseen : seen.contains name with
          | false => rfl
          | true => simp [hseen] at hparts
        · have hnext := ih (seen.insert key) name hrest
          by_cases hname : key = name
          · subst name
            simp [Std.HashSet.contains_insert] at hnext
          · simpa [Std.HashSet.contains_insert, hname] using hnext
      next hskip => exact ih seen

theorem filterLiveSubst_keys_nodup (live seen : VarSet) (b : Subst) :
    ((filterLiveSubst live seen b).map Prod.fst).Nodup := by
  induction b generalizing seen with
  | nil => simp [filterLiveSubst]
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [filterLiveSubst]
      split
      next hkeep =>
        simp only [List.map_cons, List.nodup_cons]
        constructor
        · intro hmem
          have hunseen := filterLiveSubst_keys_unseen live
            (seen.insert key) rest key hmem
          simp [Std.HashSet.contains_insert] at hunseen
        · exact ih (seen.insert key)
      next hskip => exact ih seen

theorem filterLiveSubst_lookup_of_not_live (live seen : VarSet)
    (b : Subst) (name : String) (hnotlive : live.contains name = false) :
    Metta.Subst.lookup (filterLiveSubst live seen b) name = none := by
  induction b generalizing seen with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [filterLiveSubst]
      split
      next hkeep =>
        have hparts := hkeep
        simp only [Bool.and_eq_true] at hparts
        have hkey : name ≠ key := by
          intro heq
          subst key
          simp [hnotlive] at hkeep
        simp only [Metta.Subst.lookup]
        have hbeq : (name == key) = false := by simp [hkey]
        rw [hbeq]
        exact ih (seen.insert key)
      next hskip => exact ih seen

theorem filterLiveSubst_lookup_empty (live : VarSet) (b : Subst)
    (name : String) :
    Metta.Subst.lookup
        (filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b)
        name =
      if live.contains name then Metta.Subst.lookup b name else none := by
  cases hlive : live.contains name
  · simpa [hlive] using filterLiveSubst_lookup_of_not_live live
      (Std.HashSet.emptyWithCapacity b.length) b name hlive
  · simpa [hlive] using filterLiveSubst_lookup_of_live live
      (Std.HashSet.emptyWithCapacity b.length) b name hlive (by simp)

private theorem filterLiveSubst_lookup_eq_original_of_some
    (live : VarSet) (b : Subst) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup
      (filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b)
        name = some value) :
    Metta.Subst.lookup b name = some value := by
  have hkey : name ∈
      (filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b).map
        Prod.fst :=
    mem_subst_keys_of_lookup_ne_none _ name (by simp [hlookup])
  have hlive := filterLiveSubst_keys_live live
    (Std.HashSet.emptyWithCapacity b.length) b name hkey
  have hagree := filterLiveSubst_lookup_of_live live
    (Std.HashSet.emptyWithCapacity b.length) b name hlive (by simp)
  rw [hlookup] at hagree
  exact hagree.symm

def trimSubst (b : Subst) (roots : VarSet) : Subst :=
  let live := closeSubstVars (substIndex b) (b.length + 1) roots roots
  filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b

def trimFor (goals : List Goal) (qterm : Atom) (b : Subst) : Subst :=
  trimSubst b (addAtomVars (goalsVars goals) qterm)

def trimRoots (goals : List Goal) (qterm : Atom) : VarSet :=
  addAtomVars (goalsVars goals) qterm

/-- Execute a translated conditional branch in PeTTa's `build_branch/4`
order. A translation-time output alias needs no runtime equality; every
other branch unifies its value before running its conjunction.
[SPEC translator.pl:387-390] -/
def iteBranchGoals (res : Atom) (branch : Atom × List Goal) : List Goal :=
  if branch.1 == res then branch.2
  else Goal.eq branch.1 res :: branch.2

def PersistentSubst.Scoped.trimFor (state : PersistentSubst.Scoped)
    (goals : List Goal) (qterm : Atom) : PersistentSubst.Scoped :=
  state.trimWith (trimRoots goals qterm) (PLeaTTa.trimFor goals qterm)

/-- Proof-reflectable exact equality, excluding host values whose executable
    equality cannot be reflected into Lean equality. -/
def propositionallyExactAtom (left right : Atom) : Bool :=
  propositionallyCheckableAtom left &&
    propositionallyCheckableAtom right && proofAtomEq left right

/-- Execute and validate the exact guard prefix that a specialized clause
    will run after head narrowing.  Returning `some final` records the same
    ordered `unifyB` and `trimFor` states as the machine, while requiring both
    exact guard equality and preservation of the observable query after each
    step. -/
def exactBindingGuardsRun? (qterm : Atom) (rest : List Goal) :
    Subst → Subst → Option Subst
  | [], b => some b
  | (name, value) :: tail, b =>
      match unifyB b value (Atom.var name) with
      | none => none
      | some next =>
          if propositionallyExactAtom
                (subst next (subst b value))
                (subst next (subst b (Atom.var name))) &&
              propositionallyExactAtom (subst next qterm) (subst b qterm)
          then
            exactBindingGuardsRun? qterm rest tail
              (trimFor (specializationGuards tail ++ rest) qterm next)
          else none

/-- Every binding retained by trimming is the original first binding for
    that key; trimming never changes a target. -/
theorem trimFor_lookup_eq_original_of_some (goals : List Goal) (qterm : Atom)
    (b : Subst) (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup (trimFor goals qterm b) name = some value) :
    Metta.Subst.lookup b name = some value := by
  exact filterLiveSubst_lookup_eq_original_of_some
    (closeSubstVars (substIndex b) (b.length + 1)
      (addAtomVars (goalsVars goals) qterm)
      (addAtomVars (goalsVars goals) qterm))
    b name value hlookup

/-- Is `x` directly referenced by the remaining goals or query term?  This is
    the proof-facing interface to the optimized hash-set liveness scan. -/
def isTrimRoot (goals : List Goal) (qterm : Atom) (x : String) : Bool :=
  (addAtomVars (goalsVars goals) qterm).contains x

/-- The left variable of a pending equality is directly live.  Keeping this
    fact at the optimized liveness boundary lets semantic proofs reason about
    guard execution without unfolding hash-table traversal. -/
theorem isTrimRoot_eq_left_var (x : String) (rhs qterm : Atom)
    (rest : List Goal) :
    isTrimRoot (Goal.eq (Atom.var x) rhs :: rest) qterm x = true := by
  simp only [isTrimRoot, goalsVars, goalsFuel, goalFuel, goalsVarsFuel,
    goalVarsFuel]
  apply addAtomVars_preserves_contains
  apply goalsVarsFuel_preserves_contains
  apply addAtomVars_preserves_contains
  simp [addAtomVars]

/-- Every variable occurring in the right side of a pending equality is
    directly live. -/
theorem isTrimRoot_eq_right_mem (left rhs qterm : Atom)
    (name : String) (rest : List Goal) (hmem : name ∈ rhs.vars) :
    isTrimRoot (Goal.eq left rhs :: rest) qterm name = true := by
  simp only [isTrimRoot, goalsVars, goalsFuel, goalFuel, goalsVarsFuel,
    goalVarsFuel]
  apply addAtomVars_preserves_contains
  apply goalsVarsFuel_preserves_contains
  exact addAtomVars_contains_of_mem_vars name rhs _ hmem

/-- The left variable of any pending top-level equality is live, not only the
    head equality.  This is the list-level interface needed to execute a whole
    specialization-guard prefix through repeated trimming. -/
theorem isTrimRoot_eq_left_of_mem (goals : List Goal) (qterm rhs : Atom)
    (name : String)
    (hmem : Goal.eq (Atom.var name) rhs ∈ goals) :
    isTrimRoot goals qterm name = true := by
  unfold isTrimRoot goalsVars
  apply addAtomVars_preserves_contains
  apply goalsVarsFuel_eq_left_mem name (goalsFuel goals + 1) goals
    (Std.HashSet.emptyWithCapacity 64) rhs
  · omega
  · exact hmem

/-- Every variable occurring in the left side of a pending equality is
    directly live. -/
theorem isTrimRoot_eq_left_atom_of_mem (goals : List Goal) (qterm left rhs : Atom)
    (name : String) (heq : Goal.eq left rhs ∈ goals)
    (hname : name ∈ left.vars) :
    isTrimRoot goals qterm name = true := by
  unfold isTrimRoot goalsVars
  apply addAtomVars_preserves_contains
  apply goalsVarsFuel_eq_left_atom_mem name (goalsFuel goals + 1) goals
    (Std.HashSet.emptyWithCapacity 64) left rhs
  · omega
  · exact heq
  · exact hname

/-- Every variable on the right of any pending top-level equality is live. -/
theorem isTrimRoot_eq_right_of_mem (goals : List Goal) (qterm left rhs : Atom)
    (name : String) (heq : Goal.eq left rhs ∈ goals)
    (hname : name ∈ rhs.vars) :
    isTrimRoot goals qterm name = true := by
  unfold isTrimRoot goalsVars
  apply addAtomVars_preserves_contains
  apply goalsVarsFuel_eq_right_mem name (goalsFuel goals + 1) goals
    (Std.HashSet.emptyWithCapacity 64) left rhs
  · omega
  · exact heq
  · exact hname

/-- Every query-term variable is directly live for every continuation. -/
theorem isTrimRoot_qterm_mem (goals : List Goal) (qterm : Atom)
    (name : String) (hmem : name ∈ qterm.vars) :
    isTrimRoot goals qterm name = true := by
  exact addAtomVars_contains_of_mem_vars name qterm _ hmem

/-- Liveness trimming preserves acyclicity constructionally: filter the
    original topological order to exactly the retained domain.  Relative
    dependency order is preserved, so the shorter substitution receives a
    correspondingly shorter valid fuel bound. -/
def SubstTopological.trimFor (goals : List Goal) (qterm : Atom)
    (b : Subst) (topological : SubstTopological b) :
    SubstTopological (PLeaTTa.trimFor goals qterm b) := by
  let trimmed := PLeaTTa.trimFor goals qterm b
  let keep := fun name => (Metta.Subst.lookup trimmed name).isSome
  refine
    { order := topological.order.filter keep
      nodup := topological.nodup.filter keep
      domain := ?_
      decreases := ?_ }
  · intro name
    cases hlookup : Metta.Subst.lookup trimmed name with
    | none => simp [keep, hlookup]
    | some value =>
        have horiginal : Metta.Subst.lookup b name = some value :=
          trimFor_lookup_eq_original_of_some goals qterm b name value hlookup
        have horder : name ∈ topological.order :=
          (topological.domain name).2 (by simp [horiginal])
        simp [keep, hlookup, horder]
  · intro source value dependency hsource hdependency hdependencyBound
    have hsourceOriginal : Metta.Subst.lookup b source = some value :=
      trimFor_lookup_eq_original_of_some goals qterm b source value hsource
    cases hdependencyLookup : Metta.Subst.lookup trimmed dependency with
    | none => exact False.elim (hdependencyBound hdependencyLookup)
    | some dependencyValue =>
        have hdependencyOriginal :
            Metta.Subst.lookup b dependency = some dependencyValue :=
          trimFor_lookup_eq_original_of_some goals qterm b dependency
            dependencyValue hdependencyLookup
        apply idxOf_filter_lt_of_idxOf_lt keep topological.order dependency
          source
        · exact (topological.domain dependency).2 (by
            simp [hdependencyOriginal])
        · exact (topological.domain source).2 (by simp [hsourceOriginal])
        · simp [keep, hdependencyLookup]
        · simp [keep, trimmed, hsource]
        · apply topological.decreases source value dependency
            hsourceOriginal hdependency
          simp [hdependencyOriginal]

/-- Trimming is observationally invisible at every variable referenced by the
    remaining goals or the query term.  Unlike `trimFor_eq_self_of_root_keys`,
    this permits dead bindings to be removed and duplicate keys to be
    canonicalized. -/
theorem trimFor_lookup_of_root (goals : List Goal) (qterm : Atom)
    (b : Subst) (x : String)
    (hroot : isTrimRoot goals qterm x = true) :
    Metta.Subst.lookup (trimFor goals qterm b) x =
      Metta.Subst.lookup b x := by
  let roots := addAtomVars (goalsVars goals) qterm
  let live := closeSubstVars (substIndex b) (b.length + 1) roots roots
  have hlive : live.contains x = true := by
    apply closeSubstVars_preserves_contains
    exact hroot
  change Metta.Subst.lookup
      (filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b) x =
    Metta.Subst.lookup b x
  apply filterLiveSubst_lookup_of_live live _ b x hlive
  simp

/-- Liveness trimming preserves the full deep-substitution denotation of an
    atom whose variables are directly observable.  The proof covers both
    halves hidden by the optimized implementation: the computed live set is
    closed under lookup dependencies, and filtering preserves a topological
    certificate despite shortening the machine's substitution-fuel bound. -/
theorem subst_trimFor_eq_of_topological (goals : List Goal) (qterm : Atom)
    (b : Subst) (topological : SubstTopological b) (a : Atom)
    (hroot : ∀ name, name ∈ a.vars →
      isTrimRoot goals qterm name = true) :
    subst (trimFor goals qterm b) a = subst b a := by
  let roots := addAtomVars (goalsVars goals) qterm
  let live := closeSubstVars (substIndex b) (b.length + 1) roots roots
  have hagree : SubstAgreeOn (fun name => name ∈ live) b
      (trimFor goals qterm b) := by
    intro name hlive
    symm
    change Metta.Subst.lookup
        (filterLiveSubst live
          (Std.HashSet.emptyWithCapacity b.length) b) name =
      Metta.Subst.lookup b name
    apply filterLiveSubst_lookup_of_live live _ b name
    · exact Std.HashSet.mem_iff_contains.mp hlive
    · simp
  have hclosed : SubstClosedOn (fun name => name ∈ live) b := by
    exact closeSubstVars_closed_of_topological b topological roots
  have hvars : AtomVarsIn (fun name => name ∈ live) a := by
    intro name hname
    apply Std.HashSet.mem_iff_contains.mpr
    apply closeSubstVars_preserves_contains
    exact hroot name hname
  have horiginalStable : DeepSubstStable b := topological.deepStable
  have htrimmedStable : DeepSubstStable (trimFor goals qterm b) :=
    (topological.trimFor goals qterm b).deepStable
  exact (subst_congr_of_agreeOn (fun name => name ∈ live) b
    (trimFor goals qterm b) hagree hclosed horiginalStable htrimmedStable
    a hvars).symm

/-- A binding actually retained by liveness trimming keeps its complete deep
    denotation, even when the key is live only through dependency closure
    rather than as a direct goal/query root. -/
theorem subst_trimFor_var_eq_of_lookup_some (goals : List Goal) (qterm : Atom)
    (b : Subst) (topological : SubstTopological b)
    (name : String) (value : Atom)
    (hlookup : Metta.Subst.lookup (trimFor goals qterm b) name = some value) :
    subst (trimFor goals qterm b) (Atom.var name) =
      subst b (Atom.var name) := by
  let roots := addAtomVars (goalsVars goals) qterm
  let live := closeSubstVars (substIndex b) (b.length + 1) roots roots
  have hkey : name ∈ (trimFor goals qterm b).map Prod.fst :=
    mem_subst_keys_of_lookup_ne_none _ name (by simp [hlookup])
  have hliveContains : live.contains name = true := by
    exact filterLiveSubst_keys_live live
      (Std.HashSet.emptyWithCapacity b.length) b name (by
        simpa [trimFor, trimSubst, roots, live] using hkey)
  have hlive : name ∈ live := Std.HashSet.mem_iff_contains.mpr hliveContains
  have hagree : SubstAgreeOn (fun item => item ∈ live) b
      (trimFor goals qterm b) := by
    intro item hitem
    symm
    change Metta.Subst.lookup
        (filterLiveSubst live
          (Std.HashSet.emptyWithCapacity b.length) b) item =
      Metta.Subst.lookup b item
    apply filterLiveSubst_lookup_of_live live _ b item
    · exact Std.HashSet.mem_iff_contains.mp hitem
    · simp
  have hclosed : SubstClosedOn (fun item => item ∈ live) b :=
    closeSubstVars_closed_of_topological b topological roots
  have hvars : AtomVarsIn (fun item => item ∈ live) (Atom.var name) := by
    intro item hitem
    simp only [Atom.vars, List.mem_singleton] at hitem
    subst item
    exact hlive
  exact (subst_congr_of_agreeOn (fun item => item ∈ live) b
    (trimFor goals qterm b) hagree hclosed topological.deepStable
    (topological.trimFor goals qterm b).deepStable (Atom.var name) hvars).symm

/-- If every substitution key is directly live and keys are unique, trimming
    is the identity.  This frames proofs against the optimized implementation
    without exposing hash-table traversal order. -/
theorem trimFor_eq_self_of_root_keys (goals : List Goal) (qterm : Atom)
    (b : Subst)
    (hlive : ∀ x a, (x, a) ∈ b → isTrimRoot goals qterm x = true)
    (hnodup : (b.map Prod.fst).Nodup) :
    trimFor goals qterm b = b := by
  let roots := addAtomVars (goalsVars goals) qterm
  let live := closeSubstVars (substIndex b) (b.length + 1) roots roots
  have hlive' : ∀ x a, (x, a) ∈ b → live.contains x = true := by
    intro x a hmem
    apply closeSubstVars_preserves_contains
    exact hlive x a hmem
  change filterLiveSubst live (Std.HashSet.emptyWithCapacity b.length) b = b
  apply filterLiveSubst_eq_self live _ b hlive'
  · intro x a hmem
    simp
  · exact hnodup

@[simp] theorem isTrimRoot_qterm_var (goals : List Goal) (q : String) :
    isTrimRoot goals (Atom.var q) q = true := by
  simp [isTrimRoot, addAtomVars]

@[simp] theorem isTrimRoot_guard_head (h q f x : String) (rhs res : Atom) :
    isTrimRoot
      [Goal.eq rhs (Atom.var h), Goal.call f [Atom.var x] res]
      (Atom.var q) h = true := by
  exact isTrimRoot_eq_right_of_mem
    [Goal.eq rhs (Atom.var h), Goal.call f [Atom.var x] res]
    (Atom.var q) rhs (Atom.var h) h (by simp) (by simp [Atom.vars])

@[simp] theorem isTrimRoot_guard_call_arg (h q f x : String)
    (rhs res : Atom) :
    isTrimRoot
      [Goal.eq rhs (Atom.var h), Goal.call f [Atom.var x] res]
      (Atom.var q) x = true := by
  simp [isTrimRoot, goalsVars, goalsVarsFuel, goalVarsFuel, goalsFuel, goalFuel,
    addAtomVars]

@[simp] theorem isTrimRoot_callDyn_head (h q : String) (args : List Atom)
    (res : Atom) :
    isTrimRoot [Goal.callDyn (Atom.var h) args res] (Atom.var q) h = true := by
  have hhead :
      (args.foldl addAtomVars
        (addAtomVars
          (addAtomVars (Std.HashSet.emptyWithCapacity 64) res)
          (Atom.var h))).contains h = true :=
    foldl_addAtomVars_preserves_contains h args _ (by simp [addAtomVars])
  have hhead' :
      (args.foldl addAtomVars
        ((addAtomVars (Std.HashSet.emptyWithCapacity 64) res).insert h)).contains h =
        true := by
    simpa [addAtomVars] using hhead
  have hmem : h ∈ args.foldl addAtomVars
      ((addAtomVars (Std.HashSet.emptyWithCapacity 64) res).insert h) := by
    exact Std.HashSet.mem_iff_contains.mpr (by simpa using hhead')
  simp [isTrimRoot, goalsVars, goalsVarsFuel, goalVarsFuel, goalsFuel, goalFuel,
    addAtomVars, hmem]

@[simp] theorem isTrimRoot_call_arg (f q x : String) (res : Atom) :
    isTrimRoot [Goal.call f [Atom.var x] res] (Atom.var q) x = true := by
  simp [isTrimRoot, goalsVars, goalsVarsFuel, goalVarsFuel, goalsFuel, goalFuel,
    addAtomVars]

@[simp] theorem isTrimRoot_callDyn_arg (h q x : String) (res : Atom) :
    isTrimRoot [Goal.callDyn (Atom.var h) [Atom.var x] res] (Atom.var q) x =
      true := by
  simp [isTrimRoot, goalsVars, goalsVarsFuel, goalVarsFuel, goalsFuel, goalFuel,
    addAtomVars]

theorem trimFor_target_effect_generic (g input answer marker : String) :
    trimFor
      [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")]
      (Atom.var "answer")
      [("answer", Atom.sym answer),
       ("x#r10", Atom.sym input),
       ("hof#r10", Atom.sym g),
       ("result#r10", Atom.sym answer),
       ("targetArg#r11", Atom.sym input)] =
      [("answer", Atom.sym answer)] := by
  let roots := addAtomVars
    (goalsVars
      [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")])
    (Atom.var "answer")
  let bindings : Subst :=
    [("answer", Atom.sym answer),
     ("x#r10", Atom.sym input),
     ("hof#r10", Atom.sym g),
     ("result#r10", Atom.sym answer),
     ("targetArg#r11", Atom.sym input)]
  let index := substIndex bindings
  have hstable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state := by
    intro x a state hget
    simp [index, bindings, substIndex, Std.HashMap.getElem?_insertIfNew] at hget
    by_cases hTarget : "targetArg#r11" = x
    · simp [hTarget] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hResult : "result#r10" = x
    · simp [hTarget, hResult] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hHof : "hof#r10" = x
    · simp [hTarget, hResult, hHof] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hX : "x#r10" = x
    · simp [hTarget, hResult, hHof, hX] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hAnswer : "answer" = x
    · simp [hTarget, hResult, hHof, hX, hAnswer] at hget
      cases hget
      simp [addFreshAtomVars]
    simp [hTarget, hResult, hHof, hX, hAnswer] at hget
  have hclose : closeSubstVars index (bindings.length + 1) roots roots = roots :=
    closeSubstVars_eq_live_of_stable index hstable _ _ _
  change filterLiveSubst
      (closeSubstVars index (bindings.length + 1) roots roots)
      (Std.HashSet.emptyWithCapacity bindings.length) bindings = _
  rw [hclose]
  simp [bindings, roots, filterLiveSubst, goalsVars, goalsVarsFuel,
    goalVarsFuel, goalsFuel, goalFuel, addAtomVars]

theorem trimFor_target_effect_specialized (input answer marker : String) :
    trimFor
      [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")]
      (Atom.var "answer")
      [("answer", Atom.sym answer),
       ("x#r10", Atom.sym input),
       ("result#r10", Atom.sym answer),
       ("targetArg#r11", Atom.sym input)] =
      [("answer", Atom.sym answer)] := by
  let roots := addAtomVars
    (goalsVars
      [Goal.wact "add-atom" [Atom.sym marker] (Atom.var "effectResult#r11")])
    (Atom.var "answer")
  let bindings : Subst :=
    [("answer", Atom.sym answer),
     ("x#r10", Atom.sym input),
     ("result#r10", Atom.sym answer),
     ("targetArg#r11", Atom.sym input)]
  let index := substIndex bindings
  have hstable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state := by
    intro x a state hget
    simp [index, bindings, substIndex, Std.HashMap.getElem?_insertIfNew] at hget
    by_cases hTarget : "targetArg#r11" = x
    · simp [hTarget] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hResult : "result#r10" = x
    · simp [hTarget, hResult] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hX : "x#r10" = x
    · simp [hTarget, hResult, hX] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hAnswer : "answer" = x
    · simp [hTarget, hResult, hX, hAnswer] at hget
      cases hget
      simp [addFreshAtomVars]
    simp [hTarget, hResult, hX, hAnswer] at hget
  have hclose : closeSubstVars index (bindings.length + 1) roots roots = roots :=
    closeSubstVars_eq_live_of_stable index hstable _ _ _
  change filterLiveSubst
      (closeSubstVars index (bindings.length + 1) roots roots)
      (Std.HashSet.emptyWithCapacity bindings.length) bindings = _
  rw [hclose]
  simp [bindings, roots, filterLiveSubst, goalsVars, goalsVarsFuel,
    goalVarsFuel, goalsFuel, goalFuel, addAtomVars]

/-- Executing the strict specialization guard removes only its now-dead
    higher-order binding; the query and direct-call argument bindings remain
    live. -/
theorem trimFor_specialization_guard_direct (g input : String) :
    trimFor
      [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")]
      (Atom.var "answer")
      [("answer", Atom.var "result#r10"),
       ("x#r10", Atom.sym input),
       ("hof#r10", Atom.sym g)] =
      [("answer", Atom.var "result#r10"),
       ("x#r10", Atom.sym input)] := by
  let roots := addAtomVars
    (goalsVars [Goal.call g [Atom.var "x#r10"] (Atom.var "result#r10")])
    (Atom.var "answer")
  let bindings : Subst :=
    [("answer", Atom.var "result#r10"),
     ("x#r10", Atom.sym input),
     ("hof#r10", Atom.sym g)]
  let index := substIndex bindings
  have hstable : ∀ x a, index.get? x = some a →
      addFreshAtomVars
        (roots, Std.HashSet.emptyWithCapacity roots.size) a =
      (roots, Std.HashSet.emptyWithCapacity roots.size) := by
    intro x a hget
    simp [index, bindings, substIndex,
      Std.HashMap.getElem?_insertIfNew] at hget
    by_cases hHof : "hof#r10" = x
    · simp [hHof] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hX : "x#r10" = x
    · simp [hHof, hX] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hAnswer : "answer" = x
    · simp [hHof, hX, hAnswer] at hget
      cases hget
      simp [addFreshAtomVars, roots, goalsVars, goalsVarsFuel, goalVarsFuel,
        goalsFuel, goalFuel, addAtomVars]
    simp [hHof, hX, hAnswer] at hget
  have hclose :
      closeSubstVars index (bindings.length + 1) roots roots = roots := by
    exact closeSubstVars_eq_live_of_initial_stable index bindings.length roots
      hstable
  change filterLiveSubst
      (closeSubstVars index (bindings.length + 1) roots roots)
      (Std.HashSet.emptyWithCapacity bindings.length) bindings = _
  rw [hclose]
  simp [bindings, roots, filterLiveSubst, goalsVars, goalsVarsFuel,
    goalVarsFuel, goalsFuel, goalFuel, addAtomVars]

theorem trimFor_ordered_target_generic (g input answer : String) :
    trimFor [] (Atom.var "answer")
      [("answer", Atom.sym answer),
       ("x#r10", Atom.sym input),
       ("hof#r10", Atom.sym g),
       ("result#r10", Atom.sym answer)] =
      [("answer", Atom.sym answer)] := by
  let roots := addAtomVars (goalsVars []) (Atom.var "answer")
  let bindings : Subst :=
    [("answer", Atom.sym answer),
     ("x#r10", Atom.sym input),
     ("hof#r10", Atom.sym g),
     ("result#r10", Atom.sym answer)]
  let index := substIndex bindings
  have hstable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state := by
    intro x a state hget
    simp [index, bindings, substIndex, Std.HashMap.getElem?_insertIfNew] at hget
    by_cases hResult : "result#r10" = x
    · simp [hResult] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hHof : "hof#r10" = x
    · simp [hResult, hHof] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hX : "x#r10" = x
    · simp [hResult, hHof, hX] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hAnswer : "answer" = x
    · simp [hResult, hHof, hX, hAnswer] at hget
      cases hget
      simp [addFreshAtomVars]
    simp [hResult, hHof, hX, hAnswer] at hget
  have hclose : closeSubstVars index (bindings.length + 1) roots roots = roots :=
    closeSubstVars_eq_live_of_stable index hstable _ _ _
  change filterLiveSubst
      (closeSubstVars index (bindings.length + 1) roots roots)
      (Std.HashSet.emptyWithCapacity bindings.length) bindings = _
  rw [hclose]
  simp [bindings, roots, filterLiveSubst, goalsVars, goalsVarsFuel,
    addAtomVars]

theorem trimFor_ordered_target_specialized (input answer : String) :
    trimFor [] (Atom.var "answer")
      [("answer", Atom.sym answer),
       ("x#r10", Atom.sym input),
       ("result#r10", Atom.sym answer)] =
      [("answer", Atom.sym answer)] := by
  let roots := addAtomVars (goalsVars []) (Atom.var "answer")
  let bindings : Subst :=
    [("answer", Atom.sym answer),
     ("x#r10", Atom.sym input),
     ("result#r10", Atom.sym answer)]
  let index := substIndex bindings
  have hstable : ∀ x a state, index.get? x = some a →
      addFreshAtomVars state a = state := by
    intro x a state hget
    simp [index, bindings, substIndex, Std.HashMap.getElem?_insertIfNew] at hget
    by_cases hResult : "result#r10" = x
    · simp [hResult] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hX : "x#r10" = x
    · simp [hResult, hX] at hget
      cases hget
      simp [addFreshAtomVars]
    by_cases hAnswer : "answer" = x
    · simp [hResult, hX, hAnswer] at hget
      cases hget
      simp [addFreshAtomVars]
    simp [hResult, hX, hAnswer] at hget
  have hclose : closeSubstVars index (bindings.length + 1) roots roots = roots :=
    closeSubstVars_eq_live_of_stable index hstable _ _ _
  change filterLiveSubst
      (closeSubstVars index (bindings.length + 1) roots roots)
      (Std.HashSet.emptyWithCapacity bindings.length) bindings = _
  rw [hclose]
  simp [bindings, roots, filterLiveSubst, goalsVars, goalsVarsFuel,
    addAtomVars]

/-- Numeric atom renaming retained for trace reconstruction.  Executable
    clause resolution and space matching use `renameAtomSuffix` below, whose
    suffix is proved disjoint from the caller. -/
def renameAtom (k : Nat) : Atom → Atom
  | Atom.var v => Atom.var s!"{v}#{k}"
  | Atom.expr es => Atom.expr (es.attach.map (fun ⟨e, _⟩ => renameAtom k e))
  | a => a

mutual
/-- Tag cuts in goals compiled by runtime `eval` without renaming caller
    variables: `reduce([grandfather, X, c], _)` must bind `X` in the caller,
    just as native Prolog `reduce/2` does. Fresh compiler temporaries are
    allocated from the global counter instead. -/
def tagCutsGoal (bc : Nat) : Goal → Goal
  | .call f args res => .call f args res
  | .bin op args res => .bin op args res
  | .callDyn h args res => .callDyn h args res
  | .evalg v r => .evalg v r
  | .catchg t sub r => .catchg t (tagCutsGoals bc sub) r
  | .softcut t sub thn els =>
      .softcut t (tagCutsGoals bc sub) (tagCutsGoals bc thn) (tagCutsGoals bc els)
  | .eq a b => .eq a b
  | .cut => .cutAt bc
  | .cutAt n => .cutAt n
  | .findall t sub r => .findall t (tagCutsGoals bc sub) r
  | .onceg t sub r => .onceg t (tagCutsGoals bc sub) r
  | .transactiong t sub => .transactiong t (tagCutsGoals bc sub)
  | .amb bs r => .amb (tagCutsBranches bc bs) r
  | .ite c t e r =>
      .ite c (t.1, tagCutsGoals bc t.2) (e.1, tagCutsGoals bc e.2) r
  | .spread v r => .spread v r
  | .smatch p => .smatch p
  | .wact op args res => .wact op args res

def tagCutsGoals (bc : Nat) : List Goal → List Goal
  | [] => []
  | g :: gs => tagCutsGoal bc g :: tagCutsGoals bc gs

def tagCutsBranches (bc : Nat) : List (Atom × List Goal) →
    List (Atom × List Goal)
  | [] => []
  | (t, gs) :: bs => (t, tagCutsGoals bc gs) :: tagCutsBranches bc bs
end

/-- Every caller variable whose identity is live at a clause-copy boundary.
    `argsv` are the substituted arguments; variables removed from raw `args`
    by substitution remain present among the substitution keys.  The query
    term is explicit because answer variables can remain observable after
    disappearing from the current continuation. -/
def resolutionOccupiedVars (argsv : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) : List String :=
  (argsv.flatMap Atom.vars ++ res.vars ++
    specializationGoalsVars rest ++
    b.flatMap (fun entry => entry.1 :: entry.2.vars) ++
    qterm.vars)

/-- The length-based resolution suffix is a simple, unconditional freshness
    fallback.  It is deliberately not the normal choice for long-running
    derivations: repeatedly appending a suffix whose size exceeds every live
    name makes variable names grow without bound. -/
def resolutionLongSuffix (occupied : List String) : String :=
  let maxLength := occupied.foldl
    (fun current name => max current name.length) 0
  "#" ++ residualFreshName (maxLength + 1)

/-- Whether a suffix can be appended to a clause-local variable without the
    result equalling any live caller variable.  If `source ++ suffix = caller`,
    then `suffix` must be a suffix of `caller`, so rejecting all such suffixes
    is a source-independent freshness test. -/
def resolutionSuffixFresh (occupied : List String) (suffix : String) : Bool :=
  occupied.all fun caller =>
    !(suffix.toList.isSuffixOf caller.toList)

/-- A short suffix derived from the machine's monotone branch counter. -/
def resolutionCompactSuffix (seed : Nat) : String :=
  "#r" ++ toString seed

/-- A common suffix for standardizing a clause apart. CLI execution seeds the
    monotone resolution counter above every source/host terminal `#r<n>` token;
    each allocation consumes a distinct counter value. -/
def resolutionFreshSuffix (_argsv : List Atom) (_res : Atom)
    (_rest : List Goal) (_b : Subst) (_qterm : Atom) (seed : Nat) : String :=
  resolutionCompactSuffix seed

/-- Build the same resolution suffix from a compact summary of all occupied
variable names. Persistent substitution states cache their part of this
summary, so clause copying need only inspect the current goals and query. -/
def resolutionFreshSuffixSummary
    (_summary : PersistentSubst.FreshSummary) (seed : Nat) : String :=
  resolutionCompactSuffix seed

/-- Combine the persistent binding index with the small, ephemeral variable
surface of the current call. Dynamic names are inspected directly instead of
being copied into a throwaway trie at every resolution step. -/
def resolutionFreshSuffixCached
    (_binding : PersistentSubst.FreshSummary) (_dynamic : List String)
    (seed : Nat) : String :=
  resolutionCompactSuffix seed

def resolutionDynamicVars (argsv : List Atom) (res : Atom)
    (rest : List Goal) (qterm : Atom) : List String :=
  argsv.flatMap Atom.vars ++ res.vars ++
    specializationGoalsVars rest ++ qterm.vars

/-- Add the small, per-call live-variable surface to the cached substitution
summary. `merge` extends the cached hash set only with dynamic names. -/
def resolutionOccupiedSummary
    (binding : PersistentSubst.FreshSummary) (argsv : List Atom)
    (res : Atom) (rest : List Goal) (qterm : Atom) :
    PersistentSubst.FreshSummary :=
  binding.merge (PersistentSubst.FreshSummary.ofNames
    (resolutionDynamicVars argsv res rest qterm))

/-- Injective variable renaming by a common nonempty suffix. -/
def renameAtomSuffix (suffix : String) : Atom → Atom
  | Atom.var v => Atom.var (v ++ suffix)
  | Atom.expr es =>
      Atom.expr (es.attach.map (fun ⟨e, _⟩ => renameAtomSuffix suffix e))
  | atom => atom

theorem renameAtomSuffix_var (suffix v : String) :
    renameAtomSuffix suffix (Atom.var v) = Atom.var (v ++ suffix) :=
  renameAtomSuffix.eq_1 suffix v

theorem renameAtomSuffix_sym (suffix name : String) :
    renameAtomSuffix suffix (Atom.sym name) = Atom.sym name := by
  exact renameAtomSuffix.eq_3 suffix (Atom.sym name)
    (by intro v h; cases h) (by intro es h; cases h)

theorem renameAtomSuffix_gnd (suffix : String)
    (ground : Metta.Ground) :
    renameAtomSuffix suffix (Atom.gnd ground) = Atom.gnd ground := by
  exact renameAtomSuffix.eq_3 suffix (Atom.gnd ground)
    (by intro v h; cases h) (by intro es h; cases h)

theorem renameAtomSuffix_expr (suffix : String) (atoms : List Atom) :
    renameAtomSuffix suffix (Atom.expr atoms) =
      Atom.expr (atoms.map (renameAtomSuffix suffix)) := by
  rw [renameAtomSuffix.eq_2]
  congr 1
  exact List.attach_map_val

/- Allocation-free closedness for the resolution renamer. Mutable-space
atoms are commonly ground; recognizing that fact lets standardization apart
reuse the stored term instead of rebuilding it. -/
def resolutionAtomClosed : Atom → Bool := PersistentSubst.atomClosed

def resolutionAtomsClosed : List Atom → Bool := PersistentSubst.atomsClosed

private theorem resolutionAtomClosed_of_mem :
    ∀ (atoms : List Atom), PersistentSubst.atomsClosed atoms = true →
      ∀ atom ∈ atoms, PersistentSubst.atomClosed atom = true
  | [], _, atom, member => by simp at member
  | head :: tail, closed, atom, member => by
      simp only [PersistentSubst.atomsClosed, Bool.and_eq_true] at closed
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact closed.1
      · exact resolutionAtomClosed_of_mem tail closed.2 atom member

theorem renameAtomSuffix_eq_self_of_resolutionAtomClosed (suffix : String) :
    ∀ atom, resolutionAtomClosed atom = true →
      renameAtomSuffix suffix atom = atom := by
  intro atom
  induction atom using machineAtomRecAux with
  | sym name =>
      simp [resolutionAtomClosed, PersistentSubst.atomClosed,
        renameAtomSuffix_sym]
  | var name => simp [resolutionAtomClosed, PersistentSubst.atomClosed]
  | gnd ground =>
      simp [resolutionAtomClosed, PersistentSubst.atomClosed,
        renameAtomSuffix_gnd]
  | expr atoms ih =>
      intro closed
      simp only [resolutionAtomClosed, PersistentSubst.atomClosed] at closed
      rw [renameAtomSuffix_expr]
      have hmap : atoms.map (renameAtomSuffix suffix) = atoms.map id :=
        List.map_congr_left fun child member =>
          ih child member (resolutionAtomClosed_of_mem atoms closed child member)
      rw [hmap, List.map_id]

/-- Standardization apart with maximal safe structural sharing. -/
def renameAtomSuffixShared (suffix : String) (atom : Atom) : Atom :=
  if resolutionAtomClosed atom then atom else renameAtomSuffix suffix atom

theorem renameAtomSuffixShared_eq (suffix : String) (atom : Atom) :
    renameAtomSuffixShared suffix atom = renameAtomSuffix suffix atom := by
  cases closed : resolutionAtomClosed atom with
  | false => simp [renameAtomSuffixShared, closed]
  | true =>
      simp [renameAtomSuffixShared, closed,
        renameAtomSuffix_eq_self_of_resolutionAtomClosed suffix atom closed]

mutual

/-- Apply one suffix renaming throughout a goal and tag its cuts. -/
def renameGoalSuffix (suffix : String) (bc : Nat) : Goal → Goal
  | .call f args res =>
      .call f (args.map (renameAtomSuffix suffix)) (renameAtomSuffix suffix res)
  | .bin op args res =>
      .bin op (args.map (renameAtomSuffix suffix)) (renameAtomSuffix suffix res)
  | .callDyn head args res =>
      .callDyn (renameAtomSuffix suffix head)
        (args.map (renameAtomSuffix suffix)) (renameAtomSuffix suffix res)
  | .evalg value res =>
      .evalg (renameAtomSuffix suffix value) (renameAtomSuffix suffix res)
  | .catchg tmpl sub res =>
      .catchg (renameAtomSuffix suffix tmpl) (renameGoalsSuffix suffix bc sub)
        (renameAtomSuffix suffix res)
  | .softcut tmpl sub thn els =>
      .softcut (renameAtomSuffix suffix tmpl)
        (renameGoalsSuffix suffix bc sub) (renameGoalsSuffix suffix bc thn)
        (renameGoalsSuffix suffix bc els)
  | .eq left right =>
      .eq (renameAtomSuffix suffix left) (renameAtomSuffix suffix right)
  | .cut => .cutAt bc
  | .cutAt n => .cutAt n
  | .findall tmpl sub res =>
      .findall (renameAtomSuffix suffix tmpl) (renameGoalsSuffix suffix bc sub)
        (renameAtomSuffix suffix res)
  | .onceg tmpl sub res =>
      .onceg (renameAtomSuffix suffix tmpl) (renameGoalsSuffix suffix bc sub)
        (renameAtomSuffix suffix res)
  | .transactiong tmpl sub =>
      .transactiong (renameAtomSuffix suffix tmpl)
        (renameGoalsSuffix suffix bc sub)
  | .amb branches res =>
      .amb (renameBranchesSuffix suffix bc branches)
        (renameAtomSuffix suffix res)
  | .ite cond thn els res =>
      .ite (renameAtomSuffix suffix cond)
        (renameAtomSuffix suffix thn.1, renameGoalsSuffix suffix bc thn.2)
        (renameAtomSuffix suffix els.1, renameGoalsSuffix suffix bc els.2)
        (renameAtomSuffix suffix res)
  | .spread value res =>
      .spread (renameAtomSuffix suffix value) (renameAtomSuffix suffix res)
  | .smatch pat => .smatch (renameAtomSuffix suffix pat)
  | .wact op args res =>
      .wact op (args.map (renameAtomSuffix suffix))
        (renameAtomSuffix suffix res)

def renameGoalsSuffix (suffix : String) (bc : Nat) : List Goal → List Goal
  | [] => []
  | goal :: rest =>
      renameGoalSuffix suffix bc goal :: renameGoalsSuffix suffix bc rest

def renameBranchesSuffix (suffix : String) (bc : Nat) :
    List (Atom × List Goal) → List (Atom × List Goal)
  | [] => []
  | (tmpl, goals) :: rest =>
      (renameAtomSuffix suffix tmpl, renameGoalsSuffix suffix bc goals) ::
        renameBranchesSuffix suffix bc rest

end

/-- PeTTa's per-resolution `copy_term` boundary, followed by the existing cut
    barrier tagging.  Head and body use exactly the same alpha-substitution. -/
def freshenResolutionClause (argsv _args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (qterm : Atom) (seed bc : Nat)
    (clause : Clause) : Clause :=
  let suffix := resolutionFreshSuffix argsv res rest b qterm seed
  { params := clause.params.map (renameAtomSuffix suffix)
    result := renameAtomSuffix suffix clause.result
    body := clause.body.map (renameGoalSuffix suffix bc) }

mutual
/-- Conservative match pruning for `match`: false only when syntactic
    unification is impossible. This mirrors Prolog's indexed predicate call
    for `match/4` [SPEC spaces.pl:60-63], without changing the branch body. -/
def matchCompat : Atom → Atom → Bool
  | Atom.var _, _ => true
  | _, Atom.var _ => true
  | Atom.sym a, Atom.sym b => a == b
  | Atom.gnd a, Atom.gnd b => Metta.Ground.equiv a b
  | Atom.expr xs, Atom.expr ys => matchCompatList xs ys
  | _, _ => false

def matchCompatList : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => matchCompat x y && matchCompatList xs ys
  | _, _ => false
end

mutual

/-- Standardizing a stored atom apart changes variable names only, so the
    conservative match discriminator is invariant. -/
theorem matchCompat_renameAtomSuffix_right (suffix : String) :
    ∀ left right : Atom,
      matchCompat left (renameAtomSuffix suffix right) =
        matchCompat left right
  | .var _, .var v => by rw [renameAtomSuffix_var]; rfl
  | .var _, .sym name => by rw [renameAtomSuffix_sym]
  | .var _, .gnd ground => by rw [renameAtomSuffix_gnd]
  | .var _, .expr atoms => by rw [renameAtomSuffix_expr]; rfl
  | .sym _, .var v => by rw [renameAtomSuffix_var]; rfl
  | .sym _, .sym name => by rw [renameAtomSuffix_sym]
  | .sym _, .gnd ground => by rw [renameAtomSuffix_gnd]
  | .sym _, .expr atoms => by rw [renameAtomSuffix_expr]; rfl
  | .gnd _, .var v => by rw [renameAtomSuffix_var]; rfl
  | .gnd _, .sym name => by rw [renameAtomSuffix_sym]
  | .gnd _, .gnd ground => by rw [renameAtomSuffix_gnd]
  | .gnd _, .expr atoms => by rw [renameAtomSuffix_expr]; rfl
  | .expr _, .var v => by rw [renameAtomSuffix_var]; rfl
  | .expr _, .sym name => by rw [renameAtomSuffix_sym]
  | .expr _, .gnd ground => by rw [renameAtomSuffix_gnd]
  | .expr left, .expr right => by
      rw [renameAtomSuffix_expr]
      exact matchCompatList_map_renameAtomSuffix_right suffix left right

/-- List counterpart of `matchCompat_renameAtomSuffix_right`. -/
theorem matchCompatList_map_renameAtomSuffix_right (suffix : String) :
    ∀ left right : List Atom,
      matchCompatList left (right.map (renameAtomSuffix suffix)) =
        matchCompatList left right
  | [], [] => by rfl
  | [], _ :: _ => by rfl
  | _ :: _, [] => by rfl
  | left :: leftRest, right :: rightRest => by
      rw [List.map_cons]
      simp only [matchCompatList]
      rw [matchCompat_renameAtomSuffix_right suffix left right,
        matchCompatList_map_renameAtomSuffix_right suffix leftRest rightRest]

end

mutual

theorem matchCompat_eq_spaceCompatible (left right : Atom) :
    matchCompat left right = SpaceIndex.compatible left right := by
  cases left <;> cases right <;>
    simp [matchCompat, SpaceIndex.compatible,
      matchCompatList_eq_spaceCompatibleList]

theorem matchCompatList_eq_spaceCompatibleList (left right : List Atom) :
    matchCompatList left right = SpaceIndex.compatibleList left right := by
  cases left with
  | nil => cases right <;> rfl
  | cons leftHead leftRest =>
      cases right with
      | nil => rfl
      | cons rightHead rightRest =>
          simp [matchCompatList, SpaceIndex.compatibleList,
            matchCompat_eq_spaceCompatible,
            matchCompatList_eq_spaceCompatibleList]

end

theorem PWorld.atomCandidates_filter_matchCompat (w : PWorld)
    (space query : Atom) (coherent : w.SpaceIndexCoherent) :
    (w.atomCandidates space query).filter (matchCompat query) =
      (w.atomsOf space).filter (matchCompat query) := by
  have hpredicate : matchCompat query = SpaceIndex.compatible query := by
    funext atom
    exact matchCompat_eq_spaceCompatible query atom
  rw [hpredicate]
  exact w.atomCandidates_filter_compatible space query coherent

/-- Candidate pruning remains exact after PeTTa's per-branch variable
    standardization-apart step. -/
theorem PWorld.atomCandidates_filter_matchCompat_renamed (w : PWorld)
    (space query : Atom) (suffix : String)
    (coherent : w.SpaceIndexCoherent) :
    (w.atomCandidates space query).filter
        (fun atom => matchCompat query (renameAtomSuffixShared suffix atom)) =
      (w.atomsOf space).filter
        (fun atom => matchCompat query (renameAtomSuffixShared suffix atom)) := by
  have hpredicate :
      (fun atom => matchCompat query (renameAtomSuffixShared suffix atom)) =
        matchCompat query := by
    funext atom
    rw [renameAtomSuffixShared_eq]
    exact matchCompat_renameAtomSuffix_right suffix query atom
  rw [hpredicate]
  exact w.atomCandidates_filter_matchCompat space query coherent

def smatchAlts (w : PWorld) (counter : Nat) (b : Subst) (pat : Atom)
    (rest : List Goal) (qterm : Atom) : List Alt × Nat :=
  match spacePatView pat with
  | (sp, q) =>
      let query := subst b q
      let space := subst b sp
      let suffix := resolutionFreshSuffix [query] q rest b qterm counter
      let revAlts := (w.atomCandidates space query).foldl
        (fun (acc : List Alt) a =>
          let a' := renameAtomSuffixShared suffix a
          if matchCompat query a' then
            Alt.br (Goal.eq q a' :: rest) b :: acc
          else
            acc)
        []
      (revAlts.reverse,
        counter + max (w.atomsOf space).length
          (w.atomCandidates space query).length)

/-- Independent canonical-scan reference for mutable-space matching.  It is
    intentionally not used by either the executable machine or `Step`. -/
def smatchAltsNaive (w : PWorld) (counter : Nat) (b : Subst) (pat : Atom)
    (rest : List Goal) (qterm : Atom) : List Alt × Nat :=
  match spacePatView pat with
  | (sp, q) =>
      let query := subst b q
      let space := subst b sp
      let suffix := resolutionFreshSuffix [query] q rest b qterm counter
      let revAlts := (w.atomsOf space).foldl
        (fun (acc : List Alt) atom =>
          let renamed := renameAtomSuffixShared suffix atom
          if matchCompat query renamed then
            Alt.br (Goal.eq q renamed :: rest) b :: acc
          else
            acc)
        []
      (revAlts.reverse, counter + (w.atomsOf space).length)

/-- The indexed executable match produces exactly the canonical scan's
    alternatives, order, duplicate multiplicity, snapshot, and counter. -/
theorem smatchAlts_eq_naive (w : PWorld) (counter : Nat) (b : Subst)
    (pat : Atom) (rest : List Goal) (qterm : Atom)
    (coherent : w.SpaceIndexCoherent) :
    smatchAlts w counter b pat rest qterm =
      smatchAltsNaive w counter b pat rest qterm := by
  unfold smatchAlts smatchAltsNaive
  rcases hview : spacePatView pat with ⟨spacePattern, queryPattern⟩
  simp only
  let query := subst b queryPattern
  let space := subst b spacePattern
  let suffix := resolutionFreshSuffix [query] queryPattern rest b qterm counter
  have hfilter := w.atomCandidates_filter_matchCompat_renamed
    space query suffix coherent
  have hlength := w.atomCandidates_length_le space query coherent
  have hmax :
      max (w.atomsOf space).length (w.atomCandidates space query).length =
        (w.atomsOf space).length :=
    Nat.max_eq_left hlength
  rw [hmax]
  congr 2
  rw [← List.foldl_filter, ← List.foldl_filter, hfilter]

def chainSplits : List Atom → List (List Atom × List Atom)
  | [] => [([], [])]
  | x :: xs =>
      ([], x :: xs) :: (chainSplits xs).map (fun (l, r) => (x :: l, r))

def unionReverseAlts (args : List Atom) (res : Atom) (rest : List Goal)
    (b : Subst) : Option (List Alt) :=
  match args, chainListM (subst b res) with
  | [x, y], some zs =>
      some ((chainSplits zs).map (fun (l, r) =>
        Alt.br (Goal.eq x (chainOf l) :: Goal.eq y (chainOf r) :: rest) b))
  | _, _ => none

/-- Reverse-union branch construction is relevant only to `union-atom`.
Keeping that guard outside the denotation-dependent helper prevents every
ordinary builtin from evaluating work that its dispatch branch discards. -/
def unionReverseAltsForOp (op : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) : Option (List Alt) :=
  if op == "union-atom" then unionReverseAlts args res rest b else none

@[simp] def barrierCountStep {Binding : Type} (count : Nat) : Alt Binding → Nat
  | .barrier => count + 1
  | _ => count

def barrierCount {Binding : Type} (alts : List (Alt Binding)) : Nat :=
  alts.foldl barrierCountStep 0

/-- Barrier depth used to tag cuts. The uncached lane is definitionally the
reference list semantics; the executable lane carries `some depth`. -/
def barrierDepth {Binding : Type} (c : Conf Binding) : Nat :=
  c.barriers.getD (barrierCount c.alts)

@[simp] def pushBarrierCache : Option Nat → Option Nat
  | none => none
  | some depth => some (depth + 1)

@[simp] def popBarrierCache : Option Nat → Option Nat
  | none => none
  | some depth => some (depth - 1)

@[simp] def resetBarrierCache : Option Nat → Option Nat
  | none => none
  | some _ => some 0

/-- Cut: pop alternatives until fewer than `k` barriers remain (removes the
    cut's own clause barrier and everything above it). -/
def cutTo {Binding : Type} (k : Nat) :
    List (Alt Binding) → List (Alt Binding)
  | [] => []
  | a :: rest =>
      if barrierCount (a :: rest) ≥ k then cutTo k rest else a :: rest

/-- Linear cut over a stack whose barrier count is already known. The second
component is the exact count for the returned suffix. -/
def cutToCached {Binding : Type} (k : Nat) :
    Nat → List (Alt Binding) → List (Alt Binding) × Nat
  | _, [] => ([], 0)
  | barriers, alt :: rest =>
      if barriers ≥ k then
        let next := match alt with
          | .barrier => barriers - 1
          | .br _ _ => barriers
        cutToCached k next rest
      else
        (alt :: rest, barriers)

/-- Use the cached cut only when a cache is present. The `none` branch remains
the original `cutTo` semantics and therefore cannot trust stale metadata. -/
def cutToTracked {Binding : Type} (k : Nat) :
    Option Nat → List (Alt Binding) → List (Alt Binding) × Option Nat
  | none, alts => (cutTo k alts, none)
  | some barriers, alts =>
      let result := cutToCached k barriers alts
      (result.1, some result.2)

def pullAux {Binding : Type} :
    List (Alt Binding) →
      Option ((List Goal × Binding) × List (Alt Binding))
  | [] => none
  | .barrier :: rest => pullAux rest
  | .br gs b :: rest => some ((gs, b), rest)

/-- Pull while decrementing the cached barrier depth for each skipped
marker. Branch alternatives do not change the depth. -/
def pullAuxCached {Binding : Type} : Nat → List (Alt Binding) →
    Option ((List Goal × Binding) × List (Alt Binding)) × Nat
  | _, [] => (none, 0)
  | barriers, .barrier :: rest =>
      pullAuxCached (barriers - 1) rest
  | barriers, .br gs b :: rest =>
      (some ((gs, b), rest), barriers)

theorem pullAuxCached_fst {Binding : Type} :
    ∀ (depth : Nat) (alts : List (Alt Binding)),
      (pullAuxCached depth alts).1 = pullAux alts
  | _, [] => rfl
  | depth, .barrier :: rest => pullAuxCached_fst (depth - 1) rest
  | _, .br _ _ :: _ => rfl

def pullAuxTracked {Binding : Type} : Option Nat → List (Alt Binding) →
    Option ((List Goal × Binding) × List (Alt Binding)) × Option Nat
  | none, alts => (pullAux alts, none)
  | some barriers, alts =>
      let result := pullAuxCached barriers alts
      (result.1, some result.2)

@[simp] theorem pullAuxTracked_fst {Binding : Type}
    (cache : Option Nat) (alts : List (Alt Binding)) :
    (pullAuxTracked cache alts).1 = pullAux alts := by
  cases cache with
  | none => rfl
  | some depth => exact pullAuxCached_fst depth alts

/-- Pull the next alternative into `cur`. -/
def pull {Binding : Type} (c : Conf Binding) : Conf Binding :=
  let result := pullAuxTracked c.barriers c.alts
  match result.1 with
  | none => { c with cur := none, alts := [], barriers := result.2 }
  | some (br, rest) =>
      { c with cur := some br, alts := rest, barriers := result.2 }

@[simp] theorem pull_barrier {Binding : Type} (c : Conf Binding)
    (rest : List (Alt Binding)) :
    pull { c with
      cur := none
      alts := Alt.barrier :: rest
      barriers := pushBarrierCache c.barriers } =
      pull { c with cur := none, alts := rest } := by
  cases c.barriers <;> rfl

@[simp] theorem pull_branch {Binding : Type} (c : Conf Binding)
    (gs : List Goal) (b : Binding) (rest : List (Alt Binding)) :
    pull { c with cur := none, alts := Alt.br gs b :: rest } =
      { c with cur := some (gs, b), alts := rest } := by
  cases c.barriers <;> rfl

@[simp] theorem pull_two_barriers {Binding : Type} (c : Conf Binding) :
    pull { c with
      cur := none
      alts := [(Alt.barrier : Alt Binding), (Alt.barrier : Alt Binding)]
      barriers := some 2 } =
      { c with cur := none, alts := [], barriers := some 0 } := by
  rfl

theorem pull_of_alts_branch {Binding : Type} (c : Conf Binding)
    (gs : List Goal) (b : Binding) (rest : List (Alt Binding))
    (h : c.alts = Alt.br gs b :: rest) :
    pull c = { c with cur := some (gs, b), alts := rest } := by
  unfold pull
  rw [h]
  cases c.barriers <;> rfl

theorem pull_of_two_barriers {Binding : Type} (c : Conf Binding)
    (h : c.alts = [(Alt.barrier : Alt Binding),
      (Alt.barrier : Alt Binding)]) (hb : c.barriers = none) :
    pull c = { c with cur := none, alts := [], barriers := none } := by
  unfold pull
  rw [h, hb]
  rfl

/-- Recognize a Prolog call into a named MeTTa space. `Predicate/2` in pinned
    PeTTa constructs exactly such a callable term from an expression whose
    head is a space name. -/
private def prologSpaceCall? : PrologTerm → Option (Atom × Atom)
  | .compound "Predicate" [.compound space args] =>
      if space.startsWith "&" then
        some (.sym space, chainOf (args.map PrologTerm.toAtom))
      else none
  | .compound "Predicate" [.list (.atom space :: args)] =>
      if space.startsWith "&" then
        some (.sym space, chainOf (args.map PrologTerm.toAtom))
      else none
  | _ => none

/-- Extract the local space relation represented by a direct Prolog goal or
    by the `catch(Predicate(...), _, fail)` idiom emitted by `lib_spaces`.
    The latter catches only exceptions; ordinary space-match failure remains
    ordinary failure. -/
private def localSpaceCall? (functor : String) (args : List PrologTerm) :
    Option (Atom × Atom) :=
  match functor, args with
  | "catch", [predicate, _, .atom "fail"] => prologSpaceCall? predicate
  | space, args =>
      if space.startsWith "&" then
        some (.sym space, chainOf (args.map PrologTerm.toAtom))
      else none

/-- Resolve a typed Prolog call that is owned by the pure PLeaTTa world.
    Named-space relations become `smatch`; asserted/compiled predicates become
    ordinary certified `call` goals. Calls not owned by the world remain at
    the explicit host boundary. -/
def localPrologGoals? (world : PWorld) (gt : GroundingTable) (functor : String)
    (ptArgs : List PrologTerm) (res : Atom) (rest : List Goal) :
    Option (List Goal) :=
  match localSpaceCall? functor ptArgs with
  | some (space, pattern) =>
      some (Goal.smatch (spacePat space pattern) ::
        Goal.eq res trueA :: rest)
  | none =>
      match ptArgs.reverse with
      | [] => none
      | output :: reversedInputs =>
          let inputs := reversedInputs.reverse.map PrologTerm.toAtom
          if !importedPrologHostBacked functor &&
              (Metta.GroundingTable.lookup gt functor).isSome then
            some (Goal.bin functor inputs output.toAtom ::
              Goal.eq res trueA :: rest)
          else if (world.clauseCandidates functor inputs.length).isEmpty then
            none
          else
            some (Goal.call functor inputs output.toAtom ::
              Goal.eq res trueA :: rest)

/-- Decode a `translatePredicate` builtin invocation only when its target is
    owned by the pure world. Returning `none` is deliberate: the host-aware
    driver may service an imported SWI predicate, while host-disabled core
    execution retains its ordinary unavailable-builtin behavior. -/
def localTranslatePredicateGoals? (world : PWorld) (gt : GroundingTable)
    (op : String)
    (args : List Atom) (res : Atom) (rest : List Goal) : Option (List Goal) :=
  if op != "translatePredicate" then none
  else
    match args with
    | [innerExpr] =>
        match buildPrologCall innerExpr with
        | some (functor, ptArgs, _) =>
            localPrologGoals? world gt functor ptArgs res rest
        | none => none
    | _ => none

/-- Builtin dispatch after arguments and the result position have been
substituted. The reference and persistent machines share this entire control
tree; only the binding representation and precomputed reverse-union branches
differ. -/
def binResolvedStep {Binding : Type} (gt : GroundingTable)
    (c : Conf Binding) (op : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Binding) (av : List Atom) (rv : Atom)
    (allGround : Bool)
    (advanceResults : List Atom → Nat)
    (grounded : Unit → ReduceResult)
    (unionAlts : Option (List (Alt Binding))) : Conf Binding :=
  match localTranslatePredicateGoals? c.world gt op av res rest with
  | some goals => { c with cur := some (goals, binding) }
  | none => if op == "get-type" then
    let (types, counter') := getTypeP c.world 100 c.counter
      (av.headD (Atom.sym "?"))
    pull { c with
      cur := none
      counter := advanceCounterPastAtoms (max c.counter counter') types
      alts := types.map (fun type =>
        Alt.br (Goal.eq res type :: rest) binding) ++ c.alts }
  else if op == "get-metatype" then
    let metatype := match av.headD (Atom.sym "?") with
      | Atom.var _ => "Variable"
      | Atom.gnd _ => "Grounded"
      | Atom.sym name =>
          if (Metta.GroundingTable.lookup gt name).isSome then "Grounded"
          else "Symbol"
      | Atom.expr _ => "Expression"
    { c with
      cur := some (Goal.eq res (Atom.sym metatype) :: rest, binding) }
  else if nonstrictOps.contains op then
    match grounded () with
    | ReduceResult.ok results =>
        pull { c with
          cur := none
          counter := advanceResults results
          alts := results.map (fun result =>
            Alt.br (Goal.eq res (canonBool result) :: rest) binding) ++
            c.alts }
    | _ => pull { c with cur := none }
  else if ["+", "-", "*"].contains op && !allGround &&
      Metta.isGround rv then
    match op, av with
    | "+", [x, y] =>
        { c with cur := some ((if Metta.isGround x then
            Goal.bin "-" [rv, x] y
          else Goal.bin "-" [rv, y] x) :: rest, binding) }
    | "-", [x, y] =>
        { c with cur := some ((if Metta.isGround x then
            Goal.bin "-" [x, rv] y
          else Goal.bin "+" [rv, y] x) :: rest, binding) }
    | "*", [x, y] =>
        { c with cur := some ((if Metta.isGround x then
            Goal.bin "/" [rv, x] y
          else Goal.bin "/" [rv, y] x) :: rest, binding) }
    | _, _ => pull { c with cur := none }
  else if allGround then
    match grounded () with
    | ReduceResult.ok results =>
        let branches := results.map (fun result =>
          Alt.br (Goal.eq res (canonBool result) :: rest) binding)
        pull { c with
          cur := none
          counter := advanceResults results
          alts := branches ++ c.alts }
    | _ => pull { c with cur := none }
  else if op == "union-atom" then
    match unionAlts with
    | some alts => pull { c with cur := none, alts := alts ++ c.alts }
    | none =>
        match rest with
        | [] => pull { c with cur := none }
        | _ =>
            { c with
              cur := some (rest ++ [Goal.bin op args res], binding) }
    else
      match rest with
      | [] => pull { c with cur := none }
      | _ =>
          { c with cur := some (rest ++ [Goal.bin op args res], binding) }

/-- World effects (sequenced, never undone). Returns the result atom. -/
def wactRun (w : PWorld) (op : String) (args : List Atom) :
    Option (Atom × PWorld) :=
  match op, args with
  | "add-atom", [a] => some (trueA, w.addAtom selfSpace a)
  | "add-atom", [sp, a] => some (trueA, w.addAtom sp a)
  | "remove-atom", [a] => some (trueA, w.removeAtom selfSpace a)
  | "remove-atom", [sp, a] => some (trueA, w.removeAtom sp a)
  | "change-state!", [name, v] =>
      -- [SPEC metta.pl:241] nb_setval: answers true
      some (trueA, { w with store := (name, v) ::
          (w.store.filter (fun p => p.1 != name)) })
  | "get-state", [name] =>
      -- [SPEC metta.pl:242] nb_getval: the stored value (fails if unset)
      (w.store.lookup name).map (fun v => (v, w))
  | _, _ => none

/-- Remove one source-level `Predicate` wrapper. -/
private def unwrapPredicate : Atom → Atom
  | .expr [.sym "Predicate", body] => body
  | other => other

/-- Read the function-convention shape `p(inputs..., output)` used by PeTTa's
    Prolog interoperability layer. -/
private def predicateCallParts? (atom : Atom) :
    Option (String × List Atom × Atom) :=
  match unwrapPredicate atom with
  | .expr (.sym functor :: args) =>
      match args.reverse with
      | [] => none
      | output :: reversedInputs =>
          some (functor, reversedInputs.reverse, output)
  | _ => none

private def predicateRelationGoal (gt : GroundingTable) (functor : String)
    (inputs : List Atom) (output : Atom) : Goal :=
  if (Metta.GroundingTable.lookup gt functor).isSome then
    .bin functor inputs output
  else
    .call functor inputs output

/-- Translate the right-hand value of Prolog `is/2` into the same relation IR
    used by compiled MeTTa expressions. -/
private def predicateValueGoals? (gt : GroundingTable) (target : Atom) :
    Atom → Option (List Goal)
  | .expr [.sym "Predicate", value] => predicateValueGoals? gt target value
  | .expr (.sym functor :: inputs) =>
      some [predicateRelationGoal gt functor inputs target]
  | value => some [.eq target value]

/-- Translate the supported definite-clause body: ordered conjunction,
    `is/2`, and function-convention predicate calls.  Unsupported syntax is
    rejected instead of being silently reinterpreted. -/
private def predicateBodyGoals? (gt : GroundingTable) :
    Atom → Option (List Goal)
  | .expr [.sym "Predicate", body] => predicateBodyGoals? gt body
  | .expr [.sym ",", left, right] => do
      let leftGoals ← predicateBodyGoals? gt left
      let rightGoals ← predicateBodyGoals? gt right
      pure (leftGoals ++ rightGoals)
  | .expr [.sym "is", target, value] =>
      predicateValueGoals? gt target value
  | call => do
      let (functor, inputs, output) ← predicateCallParts? call
      pure [predicateRelationGoal gt functor inputs output]

/-- Decode a quoted Prolog fact or definite clause into PLeaTTa's canonical
    clause representation.  This is a general function-convention mapping;
    no corpus name or test value participates in dispatch. -/
private def predicateClause? (gt : GroundingTable) (value : Atom) :
    Option (String × Clause) :=
  match unchainify 10000 value with
  | .expr [.sym "Predicate", .expr [.sym ":-", head, body]] => do
      let (functor, inputs, output) ← predicateCallParts? head
      let goals ← predicateBodyGoals? gt body
      pure (functor, { params := inputs, result := output, body := goals })
  | .expr [.sym "Predicate", fact] => do
      let (functor, inputs, output) ← predicateCallParts? fact
      pure (functor, { params := inputs, result := output, body := [] })
  | _ => none

/-- Install a dynamic predicate at the requested Prolog clause-order edge,
    maintaining the canonical key list and the executable clause index. -/
private def installPredicateClause (w : PWorld) (front : Bool)
    (functor : String) (clause : Clause) : PWorld :=
  let base := w.invalidateSpecializations functor
  let entry := (functor, clause)
  let clauses := if front then entry :: base.progClauses
    else base.progClauses ++ [entry]
  let key := clauseAlphaKey clause
  let keys := if front then key :: base.effectiveProgClauseKeys
    else base.effectiveProgClauseKeys ++ [key]
  let installed := base.replaceProgClauses clauses
  { installed with
      progClauseKeys := keys
      knownHeads := (functor :: installed.knownHeads).eraseDups
      knownArities := ((functor, clause.params.length) ::
        installed.knownArities.filter (fun entry =>
          !(entry.1 == functor && entry.2 == clause.params.length))) }

/-- Retract the first alpha-equivalent clause of the named predicate. -/
private def retractPredicateClause (w : PWorld) (functor : String)
    (clause : Clause) : Option PWorld :=
  let key := clauseAlphaKey clause
  let base := w.invalidateSpecializations functor
  let dropped := (base.progClauses.zip base.effectiveProgClauseKeys).foldl
    (fun (acc : List ((String × Clause) × String) × Bool) entry =>
      if !acc.2 && entry.1.1 == functor && entry.2 == key then
        (acc.1, true)
      else
        (acc.1 ++ [entry], acc.2)) ([], false)
  if !dropped.2 then none
  else
    let clauses := dropped.1.map (fun entry => entry.1)
    let keys := dropped.1.map (fun entry => entry.2)
    some { base.replaceProgClauses clauses with progClauseKeys := keys }

private def dynamicRuleSource? : Atom →
    Option (String × List Atom × Atom)
  | .expr [.sym "=", .expr (.sym functor :: params), rhs] =>
      some (functor, params, rhs)
  | _ => none

private def compileDynamicRules (env : CEnv) : Nat → List Atom →
    Option (List (Atom × String × Clause) × Nat)
  | counter, [] => some ([], counter)
  | counter, source :: rest =>
      match dynamicRuleSource? source with
      | none => compileDynamicRules env counter rest
      | some (functor, params, rhs) => do
          let (clause, next) ← (compileRule env counter params rhs).toOption
          let (compiled, finalCounter) ← compileDynamicRules env next rest
          pure ((source, functor, clause) :: compiled, finalCounter)

/-- Install parsed runtime source in source order.  Queries and split bang
    markers are deliberately rejected here: installing definitions is a world
    transition, while executing nested top-level queries requires its own
    continuation semantics. -/
private def installDynamicSource (w : PWorld) : List Atom →
    List (Atom × String × Clause) → Option PWorld
  | [], [] => some w
  | [], _ :: _ => none
  | source :: rest, compiled =>
      match source with
      | .sym "!" | .expr (.sym "!" :: _) => none
      | .expr [.sym "=", .expr (.sym functor :: _), _] =>
          match compiled with
          | (compiledSource, compiledFunctor, clause) :: compiledRest =>
              if source != compiledSource || functor != compiledFunctor then none
              else
                let installed := installPredicateClause w false functor clause
                let visible := installed.addAtom selfSpace (chainify source)
                installDynamicSource (visible.captureMeta source clause) rest
                  compiledRest
          | [] => none
      | .expr [.sym ":", subject, ty] =>
          let visible := w.addAtom selfSpace (chainify source)
          installDynamicSource
            { visible with typeDecls := visible.typeDecls ++ [(subject, ty)] }
            rest compiled
      | fact =>
          installDynamicSource (w.addAtom selfSpace (chainify fact)) rest compiled

/-- Parse and install a definition-only MeTTa source string into the live
    program.  Compilation sees both the new source heads and the existing
    world, so recursion and references to prior definitions use the ordinary
    compiler rather than a second evaluator. -/
private def processMettaString? (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (source : String) : Option (PWorld × Nat) := do
  let atoms ← (Metta.Runtime.parseFile source).toOption
  let newRules := atoms.filterMap dynamicRuleSource?
  let newHeads := newRules.map (fun (functor, _, _) => functor)
  let newArities := newRules.map
    (fun (functor, params, _) => (functor, params.length))
  let newDecls := atoms.filterMap fun atom => match atom with
    | .expr [.sym ":", subject, ty] => some (subject, ty)
    | _ => none
  let env := { mkEnv
      (fun name => (Metta.GroundingTable.lookup gt name).isSome)
      (newHeads ++ w.compileHeads).eraseDups
      (newArities ++ w.compileArities)
      (w.typeDecls ++ newDecls) with
    prologFunctions := w.prologFunctions }
  let (compiled, nextCounter) ←
    compileDynamicRules env (counter * 1000 + 500000) atoms
  let world ← installDynamicSource w atoms compiled
  pure (world, max counter nextCounter)

/-- The COMPLETE world-effect dispatch, SHARED verbatim by the executable
    and the Step relation (the same by-construction gate as `resolveAlts`).
    Rule-form add/remove-atom assert/retract compiled clauses (Prolog
    discipline); other ops go through `wactRun`; `none` = branch failure.
    Returns (result atom, new world, new counter). -/
private def wactDispatchRaw (w : PWorld) (gt : GroundingTable) (counter : Nat)
    (op : String) (av : List Atom) : Option (Atom × PWorld × Nat) :=
  let predicateAction : Option (Atom × PWorld × Nat) :=
    match op, av with
    | "assertaPredicate", [value] => do
        let (functor, clause) ← predicateClause? gt value
        pure (trueA, installPredicateClause w true functor clause, counter + 1)
    | "assertzPredicate", [value] => do
        let (functor, clause) ← predicateClause? gt value
        pure (trueA, installPredicateClause w false functor clause, counter + 1)
    | "retractPredicate", [value] => do
        let (functor, clause) ← predicateClause? gt value
        let world ← retractPredicateClause w functor clause
        pure (trueA, world, counter)
    | "process_metta_string", [.gnd (.str source)] => do
        let (world, nextCounter) ← processMettaString? w gt counter source
        pure (nilA, world, nextCounter)
    | _, _ => none
  let ruleForm : Option (Bool × Atom × Atom) := match op, av with
    | "add-atom", [a] =>
        if shallowRuleChain? a then
          let s := unchainify 1000 a
          match s with
          | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym _ :: _), _] =>
              some (true, selfSpace, s)
          | _ => none
        else none
    | "add-atom", [sp, a] =>
        if shallowRuleChain? a then
          let s := unchainify 1000 a
          match s with
          | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym _ :: _), _] =>
              some (true, sp, s)
          | _ => none
        else none
    | "remove-atom", [a] =>
        if shallowRuleChain? a then
          let s := unchainify 1000 a
          match s with
          | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym _ :: _), _] =>
              some (false, selfSpace, s)
          | _ => none
        else none
    | "remove-atom", [sp, a] =>
        if shallowRuleChain? a then
          let s := unchainify 1000 a
          match s with
          | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym _ :: _), _] =>
              some (false, sp, s)
          | _ => none
        else none
    | _, _ => none
  match predicateAction with
  | some result => some result
  | none => match ruleForm with
  | some (isAdd, sp, Atom.expr [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs]) =>
      if isAdd then
        let env : CEnv :=
          { defined := (f :: w.compileHeads).eraseDups,
            arities := fun name =>
              ((f, ps.length) :: w.compileArities).filterMap (fun (g, n) =>
                  if g == name then some n else none),
            isBin := fun n => (Metta.GroundingTable.lookup gt n).isSome,
            atomTyped := fun _ _ => false }
        match compileRule env (counter * 1000 + 500000) ps rhs with
        | .ok (cl, _) =>
            let source := Atom.expr
              [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs]
            let captured :=
              (w.addAtom sp (chainify source)).captureMeta source cl
            let withClause := captured.appendProgClause (f, cl)
            let updated :=
              { withClause with
                progClauseKeys := captured.effectiveProgClauseKeys ++
                  [clauseAlphaKey cl] }
            some (Atom.sym "True",
              updated.invalidateSpecializations f,
              counter + 1)
        | .error _ => none
      else
        -- retract the first clause α-matching the given rule form
        let env : CEnv :=
          { defined := (f :: w.compileHeads).eraseDups,
            arities := fun name =>
              ((f, ps.length) :: w.compileArities).filterMap (fun (g, n) =>
                  if g == name then some n else none),
            isBin := fun n => (Metta.GroundingTable.lookup gt n).isSome,
            atomTyped := fun _ _ => false }
        match compileRule env 900000 ps rhs with
        | .ok (pat, _) =>
            let key := clauseAlphaKey pat
            let dropped := (w.progClauses.zip w.effectiveProgClauseKeys).foldl
              (fun (acc : List ((String × Clause) × String) × Bool) e =>
                if !acc.2 && e.1.1 == f && e.2 == key
                then (acc.1, true)
                else (acc.1 ++ [e], acc.2)) ([], false)
            let source := Atom.expr
              [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs]
            let uncaptured :=
              (w.removeAtom sp (chainify source)).removeCapturedMeta f key
            let withoutClause := uncaptured.replaceProgClauses
              (dropped.1.map
                (fun (entry : (String × Clause) × String) => entry.1))
            let updated :=
              { withoutClause with
                progClauseKeys := dropped.1.map
                  (fun (entry : (String × Clause) × String) => entry.2) }
            some (Atom.sym "True",
              updated.invalidateSpecializations f, counter)
        | .error _ => none
  | _ =>
      (wactRun w op av).map (fun (r, w') =>
        (r, w', advanceCounterPastAtoms counter [r]))

/-- Publish a world-action result through one explicit freshness boundary.
The returned counter is at least the incoming and raw-operation counters and
strictly beyond every terminal resolution token in the published value. -/
def wactDispatch (w : PWorld) (gt : GroundingTable) (counter : Nat)
    (op : String) (args : List Atom) : Option (Atom × PWorld × Nat) :=
  (wactDispatchRaw w gt counter op args).map fun (result, world, rawCounter) =>
    (result, world,
      advanceCounterPastAtoms (max counter rawCounter) [result])

/-- Prepared fast path for ordinary `add-atom`.  Rule-shaped atoms retain the
full compiler dispatch; data atoms reuse insertion metadata while producing
the same result, world, and freshness counter as `wactDispatch`. -/
def wactDispatchAddIndexed (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (space : Option Atom)
    (prepared : SpaceIndex.IndexedAtom) : Option (Atom × PWorld × Nat) :=
  let args := match space with
    | none => [prepared.atom]
    | some sp => [sp, prepared.atom]
  if shallowRuleChain? prepared.atom then
    wactDispatch w gt counter "add-atom" args
  else
    let targetSpace := space.getD selfSpace
    let result := trueA
    let rawCounter := advanceCounterPastAtoms counter [result]
    some (result, w.addIndexedAtom targetSpace prepared,
      advanceCounterPastAtoms (max counter rawCounter) [result])

theorem wactDispatchAddIndexed_eq (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (space : Option Atom)
    (prepared : SpaceIndex.IndexedAtom) :
    wactDispatchAddIndexed w gt counter space prepared =
      wactDispatch w gt counter "add-atom"
        (match space with
        | none => [prepared.atom]
        | some sp => [sp, prepared.atom]) := by
  cases space with
  | none =>
      unfold wactDispatchAddIndexed
      by_cases rule : shallowRuleChain? prepared.atom = true
      · simp [rule]
      · simp only [rule, Option.getD_none]
        rw [w.addIndexedAtom_eq_addAtom]
        unfold wactDispatch wactDispatchRaw wactRun
        simp [rule]
  | some sp =>
      unfold wactDispatchAddIndexed
      by_cases rule : shallowRuleChain? prepared.atom = true
      · simp [rule]
      · simp only [rule, Option.getD_some]
        rw [w.addIndexedAtom_eq_addAtom]
        unfold wactDispatch wactDispatchRaw wactRun
        simp [rule]

theorem wactDispatch_counter_mono (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (op : String) (args : List Atom) (result : Atom)
    (world : PWorld) (counter' : Nat)
    (dispatch : wactDispatch w gt counter op args =
      some (result, world, counter')) :
    counter ≤ counter' := by
  unfold wactDispatch at dispatch
  cases raw : wactDispatchRaw w gt counter op args with
  | none => simp [raw] at dispatch
  | some value =>
      rcases value with ⟨result', world', rawCounter⟩
      simp only [raw, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at dispatch
      rcases dispatch with ⟨rfl, rfl, rfl⟩
      exact Nat.le_trans (Nat.le_max_left _ _)
        (by unfold advanceCounterPastAtoms; exact Nat.le_max_left _ _)

@[simp] theorem max_counter_eq_of_wactDispatch (w : PWorld)
    (gt : GroundingTable) (counter : Nat) (op : String) (args : List Atom)
    (result : Atom) (world : PWorld) (counter' : Nat)
    (dispatch : wactDispatch w gt counter op args =
      some (result, world, counter')) :
    max counter counter' = counter' :=
  Nat.max_eq_right
    (wactDispatch_counter_mono w gt counter op args result world counter'
      dispatch)

theorem wactDispatch_result_below (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (op : String) (args : List Atom) (result : Atom)
    (world : PWorld) (counter' : Nat)
    (dispatch : wactDispatch w gt counter op args =
      some (result, world, counter')) :
    resolutionSeedHighWaterNames result.vars ≤ counter' := by
  unfold wactDispatch at dispatch
  cases raw : wactDispatchRaw w gt counter op args with
  | none => simp [raw] at dispatch
  | some value =>
      rcases value with ⟨result', world', rawCounter⟩
      simp only [raw, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at dispatch
      rcases dispatch with ⟨rfl, rfl, rfl⟩
      unfold advanceCounterPastAtoms
      change resolutionSeedHighWaterAtom result' ≤
        max (max counter rawCounter) (resolutionSeedHighWaterAtoms [result'])
      simp only [resolutionSeedHighWaterAtoms]
      omega

theorem wactDispatch_result_counter (w : PWorld) (gt : GroundingTable)
    (counter : Nat) (op : String) (args : List Atom) (result : Atom)
    (world : PWorld) (counter' : Nat)
    (dispatch : wactDispatch w gt counter op args =
      some (result, world, counter')) :
    advanceCounterPastAtoms counter' [result] = counter' := by
  unfold advanceCounterPastAtoms
  rw [show resolutionSeedHighWaterAtoms [result] =
      resolutionSeedHighWaterNames result.vars by
    simp [resolutionSeedHighWaterAtoms, resolutionSeedHighWaterAtom]]
  exact Nat.max_eq_left
    (wactDispatch_result_below w gt counter op args result world counter'
      dispatch)

/-- Reconstruct a compile environment from the live world + grounding table,
    for meta-circular `eval` [SPEC metta.pl:245]: `eval(C,Out) :-
    translate_expr(C,Goals,Out), call_goals(Goals)` — the runtime VALUE is
    re-run through the full translator against the current definitions. -/
def runtimeEnv (w : PWorld) (gt : GroundingTable) : CEnv :=
  { defined := w.compileHeads,
    prologFunctions := w.prologFunctions,
    arities := fun f =>
      w.compileArities.filterMap (fun (g, n) =>
        if g == f then some n else none),
    isBin := fun n => (Metta.GroundingTable.lookup gt n).isSome,
    atomTyped := fun f i =>
      w.typeDecls.any (fun (subj, t) => subj == Atom.sym f &&
        match t with
        | Atom.expr (Atom.sym "->" :: tys) =>
            (tys.getD i (Atom.sym "?")) == Atom.sym "Expression"
        | _ => false),
    typeChains := fun f =>
      w.typeDecls.filterMap (fun (subj, t) =>
        if subj == Atom.sym f then
          match t with
          | Atom.expr (Atom.sym "->" :: tys) => some tys
          | _ => none
        else none) }

/-- The clause-resolution construction, SHARED verbatim by the executable
    and the Step relation (Semantics.lean cites this definition — the
    correspondence gate holds by construction here). `argsv` are the
    substituted call arguments (for indexing); `args` the raw ones (for the
    head-unification goal, substituted at unify time). -/
def resolveAlts (cs : List Clause) (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (b : Metta.Subst) (qterm : Atom) (bc counter : Nat) :
    List Alt × Nat :=
  let resv := subst b res
  let (revAlts, counter') := cs.foldl
    (fun (acc : List Alt × Nat) cl =>
      -- All predicate-head positions participate in Prolog indexing,
      -- including the output slot. Definite clashes build no branch.
      if cl.params.length != argsv.length then acc
      else if !matchCompatList argsv cl.params then acc
      else if !matchCompat resv cl.result then acc
      else
        let k := acc.2
        let copied := freshenResolutionClause argsv args res rest b qterm k bc cl
        let ps := copied.params
        let rt := copied.result
        let body := copied.body
        -- A PeTTa function clause is a Prolog predicate whose output slot is
        -- part of the predicate head. Narrow inputs and output together
        -- before the body, so reverse calls constrain recursive bodies just
        -- as native `f(args..., Out) :- Body` does.
        let gs := Goal.eq (Atom.expr (args ++ [res]))
                    (Atom.expr (ps ++ [rt])) :: body ++ rest
        (Alt.br gs b :: acc.1, k + 1))
    ([], counter)
  (revAlts.reverse, counter')

private def catchErrorAtom (kind msg : String) : Atom :=
  chainOf [Atom.sym "Error", Atom.sym kind, Atom.gnd (Metta.Ground.str msg)]

/-- SWI arithmetic exceptions reified by PeTTa's one-argument `catch`.
    The final context variable is intentionally free, matching Prolog's
    implementation-supplied context message modulo alpha-renaming. -/
private def zeroDivisorErrorAtom (predicate : String) : Atom :=
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "evaluation_error", Atom.sym "zero_divisor"],
    chainOf [Atom.sym "context",
      chainOf [Atom.sym "/", Atom.sym predicate, Atom.gnd (.int 2)],
      Atom.var "_errorContext"]]

/-- SWI's error term for an undefined arithmetic result such as
    `sqrt(-1.0)`, reified by PeTTa's one-argument `catch`. -/
private def undefinedEvaluationErrorAtom : Atom :=
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "evaluation_error", Atom.sym "undefined"],
    chainOf [Atom.sym "context",
      chainOf [Atom.sym ":", Atom.sym "system",
        chainOf [Atom.sym "/", Atom.sym "is", Atom.gnd (.int 2)]],
      Atom.var "_errorContext"]]

/-- PeTTa `sread/2` and its `parse/2` alias raise
    `error(syntax_error('Parse error in form: ...'), none)` when their
    whole-input grammar rejects the source. -/
private def syntaxErrorAtom (source : String) : Atom :=
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "syntax_error",
      Atom.sym s!"Parse error in form: {source}"],
    Atom.sym "none"]

private def runtimeErrorAtom (op msg : String) : Atom :=
  if op == "sread" || op == "parse" then
    syntaxErrorAtom msg
  else if msg == "undefined" then
    undefinedEvaluationErrorAtom
  else if op == "/" && msg == "division by zero" then
    zeroDivisorErrorAtom "/"
  else if op == "%" && msg == "mod zero" then
    zeroDivisorErrorAtom "mod"
  else catchErrorAtom "runtime_error" msg

#guard runtimeErrorAtom "sread" "foo bar" ==
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "syntax_error", Atom.sym "Parse error in form: foo bar"],
    Atom.sym "none"]

inductive CatchResult where
  | answers (xs : List Atom)
  | error (err : Atom)
deriving Repr, Inhabited

private def caughtBin? (gt : GroundingTable) (b : Subst) (tmpl : Atom) :
    String → List Atom → Atom → Option CatchResult
  | op, args, r =>
      let av := args.map (subst b)
      if binArity op != 0 && av.length < binArity op then none
      else if op == "get-type" || op == "get-metatype" then none
      else if ["+", "-", "*"].contains op && !(av.all Metta.isGround) then none
      else if nonstrictOps.contains op || av.all Metta.isGround then
        match callGrounded gt op av with
        | .ok rs =>
            some (.answers (rs.filterMap (fun rv =>
              (unifyB b r (canonBool rv)).map (fun b' => subst b' tmpl))))
        | .incorrectArgument msg => some (.error (catchErrorAtom "type_error" msg))
        | .runtimeError msg => some (.error (runtimeErrorAtom op msg))
        | .noReduce => none
      else none

def catchDirect? (gt : GroundingTable) (b : Subst) (tmpl : Atom) :
    List Goal → Option CatchResult
  | [Goal.bin op args r] => caughtBin? gt b tmpl op args r
  | _ => none

/-- Error-only builtin preflight after argument substitution. Clean execution
uses this before the ordinary machine step; successful answers are still
handled by `binResolvedStep`. -/
def caughtBinErrorResolved? (gt : GroundingTable) (op : String)
    (args : List Atom) : Option Atom :=
  if binArity op != 0 && args.length < binArity op then none
  else if op == "get-type" || op == "get-metatype" then none
  else if ["+", "-", "*"].contains op && !(args.all Metta.isGround) then none
  else if nonstrictOps.contains op || args.all Metta.isGround then
    match callGrounded gt op args with
    | .incorrectArgument msg => some (catchErrorAtom "type_error" msg)
    | .runtimeError msg => some (runtimeErrorAtom op msg)
    | _ => none
  else none

/-- Error preflight with groundness supplied by a certified representation.
The ordinary helper remains the denotational reference. -/
def caughtBinErrorResolvedWithGround? (gt : GroundingTable) (op : String)
    (args : List Atom) (allGround : Bool) : Option Atom :=
  if binArity op != 0 && args.length < binArity op then none
  else if op == "get-type" || op == "get-metatype" then none
  else if ["+", "-", "*"].contains op && !allGround then none
  else if nonstrictOps.contains op || allGround then
    match callGrounded gt op args with
    | .incorrectArgument msg => some (catchErrorAtom "type_error" msg)
    | .runtimeError msg => some (runtimeErrorAtom op msg)
    | _ => none
  else none

theorem caughtBinErrorResolvedWithGround_eq (gt : GroundingTable)
    (op : String) (args : List Atom) (allGround : Bool)
    (ground : allGround = args.all Metta.isGround) :
    caughtBinErrorResolvedWithGround? gt op args allGround =
      caughtBinErrorResolved? gt op args := by
  simp [caughtBinErrorResolvedWithGround?, caughtBinErrorResolved?, ground]

theorem caughtBinErrorResolved_some_iff (gt : GroundingTable) (b : Subst)
    (op : String) (args : List Atom) (res err : Atom) :
    caughtBinErrorResolved? gt op (args.map (subst b)) = some err ↔
      catchDirect? gt b res [Goal.bin op args res] = some (.error err) := by
  simp [caughtBinErrorResolved?, catchDirect?, caughtBin?]
  intro _ _ _ _ _
  cases callGrounded gt op (args.map (subst b)) <;> simp

def tableFresh {Binding : Type} (c : Conf Binding) : Atom :=
  Atom.var s!"_tbl{c.counter}"

/-- SWI `transaction/1` commits to its first solution. Reusing the machine's
    scoped `onceg` gives a terminal nested run with at most one answer, which
    keeps the transaction step inside the existing StepStar proof boundary. -/
def transactionSub (tmpl : Atom) (sub : List Goal) : List Goal :=
  [Goal.onceg tmpl sub tmpl]

mutual

/-- One machine step. `gt` is the grounded-builtin oracle table. -/
def step (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf) : Conf :=
  match c.cur with
  | none => pull c
  | some ([], b) =>
      let answer := subst b c.qterm
      pull { c with
        cur := none
        answers := answer :: c.answers
        answerKeys := PersistentSubst.atomExactKey answer :: c.answerKeys
        answerKeys_sound := by
          simp only [List.map_cons]
          rw [c.answerKeys_sound] }
  | some (g :: rest, b) =>
    match g with
    | .eq x y =>
        match unifyB b x y with
        | some b' => { c with cur := some (rest, trimFor rest c.qterm b') }
        | none => pull { c with cur := none }
    | .cut => pull { c with cur := none }         -- untagged: compile artifact
    | .cutAt k =>
        let cut := cutToTracked k c.barriers c.alts
        { c with
          cur := some (rest, b)
          alts := cut.1
          barriers := cut.2 }
    | .callDyn hd args res =>
        -- apply-or-data: a symbol naming a defined function applies; a
        -- builtin dispatches; anything else is an ordinary data tuple
        -- (var-headed tuples are usually data in MeTTa)
        (match subst b hd with
         | Atom.sym f =>
             if !(c.world.clauseHeadCandidates f).isEmpty then
               { c with cur := some (Goal.call f args res :: rest, b) }
             else if (Metta.GroundingTable.lookup gt f).isSome then
               { c with cur := some (Goal.bin f args res :: rest, b) }
             else
               let g := Goal.eq res (chainOf (Atom.sym f :: args))
               { c with cur := some (g :: rest, b) }
         | other =>
             -- [SPEC translator.pl:59-61] applying a partial(base, bound)
             -- appends the new args to bound and re-dispatches; anything
             -- else is data (:62-64)
             match chainListM other with
             | some [Atom.sym "partial", Atom.sym base, boundList] =>
                 let bound := (chainListM boundList).getD []
                 let g := Goal.callDyn (Atom.sym base) (bound ++ args) res
                 { c with cur := some (g :: rest, b) }
             | _ =>
                 let g := Goal.eq res (chainOf (other :: args))
                 { c with cur := some (g :: rest, b) })
    | .evalg v res =>
        -- meta-circular eval [SPEC metta.pl:245]: resolve the value, unchain
        -- to surface form, re-run the translator against the CURRENT
        -- definitions, splice the compiled goals. Caller variables are kept
        -- shared; compiler temporaries are fresh because compilation starts
        -- from the global counter and returns the next counter.
        let vv := unchainify 10000 (subst b v)
        (match compileExpr (runtimeEnv c.world gt) (c.counter + 1) vv with
         | .ok (t, gs, m) =>
             let (profileWorld, profileGoals) :=
               specializeGoals (specializationIsBin gt)
                 specializationBuildFuel c.world gs
             let bc := barrierDepth c + 1
             let gs' := tagCutsGoals bc profileGoals
             let newgoals := gs' ++ [Goal.eq res t] ++ rest
             { c with cur := some (newgoals, b),
                      world := profileWorld,
                      counter := advanceCounterPastGoals (max c.counter m)
                        (profileGoals ++ [Goal.eq res t] ++ rest) }
         | .error _ =>
             -- untranslatable value: eval is the identity (data)
             let data := chainify vv
             { c with cur := some (Goal.eq res data :: rest, b),
                      counter := advanceCounterPastAtoms c.counter [data] })
    | .catchg tmpl sub res =>
        match catchDirect? gt b tmpl sub with
        | some (.error err) =>
            { c with cur := some (Goal.eq res err :: rest, b),
                     world := c.world,
                     counter := advanceCounterPastAtoms c.counter [err] }
        | some (.answers answers) =>
            if answers.isEmpty then
              pull { c with cur := none }
            else
              pull { c with
                cur := none
                counter := advanceCounterPastAtoms c.counter answers
                alts := answers.map (fun inst =>
                  Alt.br (Goal.eq res inst :: rest) b) ++ c.alts }
        | none =>
            let subConf : Conf :=
              { cur := some (sub, b), alts := [], world := c.world,
                counter := c.counter, qterm := tmpl,
                barriers := resetBarrierCache c.barriers }
            let d := run prog gt fuel subConf none
            if d.answers.isEmpty then
              pull { c with cur := none, world := d.world,
                            counter := d.counter }
            else
              pull { c with cur := none, world := d.world,
                            counter := d.counter,
                            alts := d.answerValues.map (fun inst =>
                              Alt.br (Goal.eq res inst :: rest) b) ++ c.alts }
    | .transactiong tmpl sub =>
        let txSub := transactionSub tmpl sub
        let subConf : Conf :=
          { cur := some (txSub, b), alts := [], world := c.world,
            counter := c.counter, qterm := tmpl,
            barriers := resetBarrierCache c.barriers }
        let d := run prog gt fuel subConf none
        if d.answers.isEmpty then
          pull { c with cur := none, world := c.world, counter := d.counter }
        else
          pull { c with cur := none, world := d.world, counter := d.counter,
                        alts := d.answerValues.map (fun inst =>
                          Alt.br (Goal.eq tmpl inst :: rest) b) ++ c.alts }
    | .softcut tmpl sub thn els =>
        -- (sub *-> thn ; els): thn runs once PER solution of sub (bindings
        -- re-imported via `tmpl ≐ instance`); els runs iff sub has none.
        -- Unification subs have ≤1 solution (plain soft-cut); nondet
        -- scrutinees (case) enumerate per solution. Fuel-bounded sub-run.
        let subConf : Conf :=
          { cur := some (sub, b), alts := [], world := c.world,
            counter := c.counter, qterm := tmpl,
            barriers := resetBarrierCache c.barriers }
        let d := run prog gt fuel subConf none
        (if d.answers.isEmpty then
           { c with cur := some (els ++ rest, b),
                    world := d.world, counter := d.counter }
         else
           pull { c with cur := none,
                         world := d.world, counter := d.counter,
                         alts := d.answerValues.map (fun inst =>
                           Alt.br (Goal.eq tmpl inst :: thn ++ rest) b)
                           ++ c.alts })
    | .call f args res =>
        let argsv := args.map (subst b)
        let key := tableKey f argsv
        if c.world.canTableCall f argsv then
          match c.world.tableLookup key with
          | some answers =>
              pull { c with cur := none,
                            counter := advanceCounterPastAtoms c.counter answers,
                            alts := answers.map (fun ans =>
                              Alt.br (Goal.eq res ans :: rest) b) ++ c.alts }
          | none =>
              -- [SPEC lib_tabling.metta:7-11] `(tabled (f ...))` injects
              -- SWI's `:- table f/n.` directive. For ground calls, compute
              -- the tabled variant once, cache its answers, then replay them.
              let tres := tableFresh c
              let subWorld := { c.world with tableActive := key :: c.world.tableActive }
              let subConf : Conf :=
                { cur := some ([Goal.call f argsv tres], []), alts := [],
                  world := subWorld,
                  counter := advanceCounterPastAtoms (c.counter + 1) [tres],
                  qterm := tres,
                  barriers := resetBarrierCache c.barriers }
              let d := run prog gt fuel subConf none
              let answerValues := d.answerValues
              let w' := (d.world.deactivateTable key).tableInsert key answerValues
              if d.answers.isEmpty then
                pull { c with cur := none, world := w', counter := d.counter }
              else
                pull { c with cur := none, world := w', counter := d.counter,
                              alts := answerValues.map (fun ans =>
                                Alt.br (Goal.eq res ans :: rest) b) ++ c.alts }
        else
        let headCs := c.world.clauseHeadCandidates f
        -- [SPEC translator.pl:62-64] a head with NO clauses reduces to data
        -- (f args) — e.g. after all clauses are remove-atom'd
        if headCs.isEmpty then
          let g := Goal.eq res (chainOf (Atom.sym f :: args))
          { c with cur := some (g :: rest, b) }
        -- [SPEC translator.pl:328-339] under-application (clauses exist but
        -- none of the call's arity) yields partial(f, args); a right-arity
        -- call with no matching clause fails (goal failure) as usual
        else
        let cs := c.world.resolutionCandidates f args.length
        if !(cs.any (fun cl => cl.params.length == args.length)) then
          let pv := chainOf [Atom.sym "partial", Atom.sym f, chainOf args]
          { c with cur := some (Goal.eq res pv :: rest, b) }
        else
          let bc := barrierDepth c + 1
          let (branches, counter') :=
            resolveAlts cs argsv args res rest b c.qterm bc c.counter
          pull { c with cur := none, counter := counter',
                        alts := branches ++ (Alt.barrier :: c.alts),
                        barriers := pushBarrierCache c.barriers }
    | .bin op args res =>
        let av := args.map (subst b)
        -- under-applied builtin -> partial value (same root as .call)
        if binArity op != 0 && av.length < binArity op then
          let pv := chainOf [Atom.sym "partial", Atom.sym op, chainOf av]
          { c with cur := some (Goal.eq res pv :: rest, b) }
        else
          binResolvedStep gt c op args res rest b av (subst b res)
            (av.all Metta.isGround)
            (advanceCounterPastAtoms c.counter)
            (fun _ => callGrounded gt op av)
            (unionReverseAltsForOp op args res rest b)
    | .ite cond thn els res =>
        -- [SPEC translator.pl:156-162] `Cv == true -> Then ; Else`: the else
        -- branch fires on ANY non-True condition (identity check, not a
        -- boolean match); no delay — the let goal order (unify-first)
        -- resolves pattern-position conditions before they are tested
        let cv := subst b cond
        if cv == trueA then
          { c with cur := some (iteBranchGoals res thn ++ rest, b) }
        else
          { c with cur := some (iteBranchGoals res els ++ rest, b) }
    | .amb branches res =>
        let alts := branches.map (fun (t, gs) =>
          Alt.br (gs ++ [Goal.eq res t] ++ rest) b)
        pull { c with cur := none, alts := alts ++ c.alts }
    | .spread v res =>
        let vv := subst b v
        let elems := (chainListM vv).getD [vv]
        pull { c with cur := none,
                      alts := elems.map (fun e =>
                        Alt.br (Goal.eq res e :: rest) b) ++ c.alts }
    | .smatch pat =>
        let (alts, counter') := smatchAlts c.world c.counter b pat rest c.qterm
        pull { c with cur := none,
                      counter := counter',
                      alts := alts ++ c.alts }
    | .wact op args res =>
        -- the complete dispatch is the SHARED wactDispatch (correspondence
        -- by construction, like resolveAlts)
        (match wactDispatch c.world gt c.counter op (args.map (subst b)) with
         | some (r, w', k') =>
             { c with cur := some (Goal.eq res r :: rest, b),
                      world := w', counter := max c.counter k' }
         | none => pull { c with cur := none })
    | .findall tmpl sub res =>
        let subConf : Conf :=
          { cur := some (sub, b), alts := [], world := c.world,
            counter := c.counter, qterm := tmpl,
            barriers := resetBarrierCache c.barriers }
        let subDone := run prog gt fuel subConf none
        let items := chainOf subDone.answerValues
        { c with cur := some (Goal.eq res items :: rest, b),
                 world := subDone.world, counter := subDone.counter }
    | .onceg tmpl sub res =>
        -- once(G) ≡ (G, !) under its own barrier: bindings RETAINED in the
        -- caller (unlike findall, which copies), first solution committed.
        let bc := barrierDepth c + 1
        let gs := sub ++ [Goal.cutAt bc, Goal.eq res tmpl] ++ rest
        pull { c with cur := none,
                      alts := Alt.br gs b :: (Alt.barrier :: c.alts),
                      barriers := pushBarrierCache c.barriers }

/-- Run to completion or fuel exhaustion; `limit` stops early at that many
    answers (for `once`). -/
def run (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
    (limit : Option Nat) : Conf :=
  match fuel with
  | 0 => c
  | fuel + 1 =>
      if c.cur.isNone && c.alts.isEmpty then c
      else if limit.any (fun l => c.answers.length ≥ l) then c
      else run prog gt fuel (step prog gt fuel c) limit

end

/-!
## Clean executable lane

The historical `step` above is total by fuel, but its nested heads (`findall`,
`softcut`, `catchg`, and uncached tabled calls) can construct an outer
successor even when the internal sub-run merely exhausted fuel.  That is useful
for profiling, but it is not a semantics-licensed result.  The clean lane makes
fuel exhaustion explicit so the CLI can fail honestly instead of printing a
partial answer.
-/

inductive StepOutcome where
  | progressed (c : Conf)
  | exhausted (c : Conf)
  | errored (c : Conf) (err : Atom)
deriving Repr, Inhabited

inductive RunOutcome where
  | done (c : Conf)
  | limited (c : Conf)
  | exhausted (c : Conf)
  | errored (c : Conf) (err : Atom)
deriving Repr, Inhabited

def Conf.isTerminalB (c : Conf) : Bool :=
  c.cur.isNone && c.alts.isEmpty

def Conf.limitReachedB (c : Conf) (limit : Option Nat) : Bool :=
  limit.any (fun l => c.answers.length ≥ l)

def runOutcomeConf : RunOutcome → Conf
  | .done c => c
  | .limited c => c
  | .exhausted c => c
  | .errored c _ => c

def subConfOf (c : Conf) (sub : List Goal) (b : Subst)
    (tmpl : Atom) : Conf :=
  { cur := some (sub, b), alts := [], world := c.world,
    counter := c.counter, qterm := tmpl,
    barriers := resetBarrierCache c.barriers }

def tableSubConfOf (c : Conf) (f : String) (argsv : List Atom)
    (tres key : Atom) : Conf :=
  let subWorld := { c.world with tableActive := key :: c.world.tableActive }
  { cur := some ([Goal.call f argsv tres], []), alts := [],
    world := subWorld,
    counter := advanceCounterPastAtoms (c.counter + 1) [tres],
    qterm := tres,
    barriers := resetBarrierCache c.barriers }

/-- Rejoin a clean nested `catch` run without duplicating its outcome
handling in the executable and representation-polymorphic machines. -/
def finishCatchClean (c : Conf) (rest : List Goal) (res : Atom)
    (b : Subst) : RunOutcome → StepOutcome
  | .done d =>
      if d.answers.isEmpty then
        .progressed (pull { c with cur := none,
                                   world := d.world,
                                   counter := d.counter })
      else
        .progressed
          (pull { c with cur := none,
                         world := d.world,
                         counter := d.counter,
                         alts := d.answerValues.map (fun inst =>
                           Alt.br (Goal.eq res inst :: rest) b) ++ c.alts })
  | .limited d => .exhausted d
  | .exhausted d => .exhausted d
  | .errored d err =>
      .progressed { c with
        cur := some (Goal.eq res err :: rest, b),
        world := d.world,
        counter := advanceCounterPastAtoms d.counter [err] }

/-- Rejoin a clean nested transaction. -/
def finishTransactionClean (c : Conf) (rest : List Goal) (tmpl : Atom)
    (b : Subst) : RunOutcome → StepOutcome
  | .done d =>
      if d.answers.isEmpty then
        .progressed
          (pull { c with cur := none, world := c.world,
                           counter := d.counter })
      else
        .progressed
          (pull { c with cur := none, world := d.world,
                           counter := d.counter,
                           alts := d.answerValues.map (fun inst =>
                             Alt.br (Goal.eq tmpl inst :: rest) b)
                             ++ c.alts })
  | .limited d => .exhausted d
  | .exhausted d => .exhausted d
  | .errored d err => .errored d err

/-- Rejoin a clean nested soft cut. -/
def finishSoftcutClean (c : Conf) (rest thn els : List Goal)
    (tmpl : Atom) (b : Subst) : RunOutcome → StepOutcome
  | .done d =>
      if d.answers.isEmpty then
        .progressed { c with cur := some (els ++ rest, b),
                             world := d.world,
                             counter := d.counter }
      else
        .progressed
          (pull { c with cur := none,
                         world := d.world,
                         counter := d.counter,
                         alts := d.answerValues.map (fun inst =>
                           Alt.br (Goal.eq tmpl inst :: thn ++ rest) b)
                           ++ c.alts })
  | .limited d => .exhausted d
  | .exhausted d => .exhausted d
  | .errored d err => .errored d err

/-- Rejoin a clean nested `findall`. -/
def finishFindallClean (c : Conf) (rest : List Goal) (res : Atom)
    (b : Subst) : RunOutcome → StepOutcome
  | .done d =>
      .progressed { c with
        cur := some (Goal.eq res (chainOf d.answerValues) :: rest, b),
        world := d.world, counter := d.counter }
  | .limited d => .exhausted d
  | .exhausted d => .exhausted d
  | .errored d err => .errored d err

/-- Rejoin a clean uncached table evaluation. -/
def finishTableClean (c : Conf) (key : Atom) (rest : List Goal)
    (res : Atom) (b : Subst) : RunOutcome → StepOutcome
  | .done d =>
      let answerValues := d.answerValues
      let world := (d.world.deactivateTable key).tableInsert key answerValues
      if d.answers.isEmpty then
        .progressed (pull { c with cur := none,
                                   world,
                                   counter := d.counter })
      else
        .progressed
          (pull { c with cur := none,
                         world,
                         counter := d.counter,
                         alts := answerValues.map (fun answer =>
                           Alt.br (Goal.eq res answer :: rest) b) ++ c.alts })
  | .limited d => .exhausted d
  | .exhausted d => .exhausted d
  | .errored d err => .errored d err

mutual

def stepClean (prog : Prog) (gt : GroundingTable) :
    Nat → Conf → StepOutcome
  | 0, c => .exhausted c
  | fuel + 1, c =>
      match c.cur with
      | some (Goal.catchg tmpl sub res :: rest, b) =>
          match catchDirect? gt b tmpl sub with
          | some (.error err) =>
              .progressed { c with cur := some (Goal.eq res err :: rest, b),
                                   world := c.world,
                                   counter :=
                                     advanceCounterPastAtoms c.counter [err] }
          | some (.answers answers) =>
              if answers.isEmpty then
                .progressed (pull { c with cur := none })
              else
                .progressed
                  (pull { c with
                    cur := none
                    counter := advanceCounterPastAtoms c.counter answers
                    alts := answers.map (fun inst =>
                      Alt.br (Goal.eq res inst :: rest) b) ++ c.alts })
          | none =>
              finishCatchClean c rest res b
                (runClean prog gt fuel (subConfOf c sub b tmpl) none)
      | some (Goal.transactiong tmpl sub :: rest, b) =>
          let txSub := transactionSub tmpl sub
          finishTransactionClean c rest tmpl b
            (runClean prog gt fuel (subConfOf c txSub b tmpl) none)
      | some (Goal.softcut tmpl sub thn els :: rest, b) =>
          finishSoftcutClean c rest thn els tmpl b
            (runClean prog gt fuel (subConfOf c sub b tmpl) none)
      | some (Goal.findall tmpl sub res :: rest, b) =>
          finishFindallClean c rest res b
            (runClean prog gt fuel (subConfOf c sub b tmpl) none)
      | some (Goal.call f args res :: rest, b) =>
          let argsv := args.map (subst b)
          let key := tableKey f argsv
          if c.world.canTableCall f argsv then
            match c.world.tableLookup key with
            | some _ => .progressed (step prog gt fuel c)
            | none =>
                let tres := tableFresh c
                finishTableClean c key rest res b
                  (runClean prog gt fuel
                    (tableSubConfOf c f argsv tres key) none)
          else
            .progressed (step prog gt fuel c)
      | some (Goal.bin op args res :: rest, b) =>
          let values := args.map (subst b)
          match localTranslatePredicateGoals? c.world gt op values res rest with
          | some _ => .progressed (step prog gt fuel c)
          | none =>
              match caughtBinErrorResolved? gt op values with
              | some err => .errored c err
              | none => .progressed (step prog gt fuel c)
      | _ => .progressed (step prog gt fuel c)

def runClean (prog : Prog) (gt : GroundingTable) :
    Nat → Conf → Option Nat → RunOutcome
  | 0, c, limit =>
      if c.isTerminalB then .done c
      else if c.limitReachedB limit then .limited c
      else .exhausted c
  | fuel + 1, c, limit =>
      if c.isTerminalB then .done c
      else if c.limitReachedB limit then .limited c
      else
        match stepClean prog gt fuel c with
        | .progressed c' => runClean prog gt fuel c' limit
        | .exhausted d => .exhausted d
        | .errored d err => .errored d err

end

def runClean? (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
    (limit : Option Nat) : Option Conf :=
  match runClean prog gt fuel c limit with
  | .done d => some d
  | .limited d => some d
  | .exhausted _ => none
  | .errored _ _ => none

end PLeaTTa
