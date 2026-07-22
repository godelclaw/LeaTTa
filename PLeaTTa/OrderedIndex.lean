-- SPDX-License-Identifier: Apache-2.0

/-
Insertion-order-preserving derived indices for PLeaTTa's mutable world.

The canonical lists remain the semantic reference.  Buckets are stored in
reverse order so appending a live clause updates its bucket in O(1); candidate
lookup reverses only the selected bucket and therefore returns exactly the
same order as naive filtering of the canonical clause list.
-/
import PLeaTTa.Types
import PLeaTTa.Chain
import PLeaTTa.PersistentSubstCore
import Std.Data.HashMap.Lemmas

namespace PLeaTTa

/-- A live-clause bucket key: function head and compiled parameter arity. -/
abbrev ClauseKey := String × Nat

/-- A live-clause index.  Both head-only and head-and-arity buckets are stored
    newest-first.  Head-only lookup preserves the previous `clausesOf`
    interface; head-and-arity lookup removes candidates resolution would
    immediately reject. -/
structure ClauseIndex where
  byHead : Std.HashMap String (List Clause) :=
    Std.HashMap.emptyWithCapacity
  byHeadArity : Std.HashMap ClauseKey (List Clause) :=
    Std.HashMap.emptyWithCapacity
deriving Repr, Inhabited

namespace ClauseIndex

def empty : ClauseIndex := {}

def key (entry : String × Clause) : ClauseKey :=
  (entry.1, entry.2.params.length)

/-- Add one canonical `(head, clause)` entry to the derived index. -/
def push (index : ClauseIndex) (entry : String × Clause) : ClauseIndex :=
  { byHead := index.byHead.alter entry.1 fun current =>
      some (entry.2 :: current.getD [])
    byHeadArity := index.byHeadArity.alter (key entry) fun current =>
      some (entry.2 :: current.getD []) }

/-- Build the derived index in one left-to-right pass. -/
def build (clauses : List (String × Clause)) : ClauseIndex :=
  clauses.foldl push empty

/-- Read one head-and-arity bucket in canonical insertion order. -/
def candidates (index : ClauseIndex) (head : String) (arity : Nat) :
    List Clause :=
  (index.byHeadArity.getD (head, arity) []).reverse

/-- Read every clause for a head in canonical insertion order. -/
def headCandidates (index : ClauseIndex) (head : String) : List Clause :=
  (index.byHead.getD head []).reverse

/-- The independent, unindexed meaning of live-clause lookup. -/
def naiveCandidates (clauses : List (String × Clause))
    (head : String) (arity : Nat) : List Clause :=
  clauses.filterMap fun entry =>
    if key entry == (head, arity) then some entry.2 else none

/-- The old live-clause lookup before arity discrimination. -/
def naiveHeadCandidates (clauses : List (String × Clause))
    (head : String) : List Clause :=
  clauses.filterMap fun entry =>
    if entry.1 == head then some entry.2 else none

/-- The reverse bucket accumulated by `push` consists exactly of the matching
    processed clauses, reversed, followed by the seed bucket. -/
theorem foldl_getD (wanted : ClauseKey)
    (clauses : List (String × Clause)) :
    ∀ seed : ClauseIndex,
      (clauses.foldl push seed).byHeadArity.getD wanted [] =
        (clauses.filterMap (fun entry =>
          if key entry == wanted then some entry.2 else none)).reverse ++
          seed.byHeadArity.getD wanted [] := by
  induction clauses with
  | nil =>
      intro seed
      simp
  | cons entry rest ih =>
      intro seed
      rw [List.foldl_cons, ih]
      by_cases heq : key entry = wanted
      · simp [push, heq, Std.HashMap.getD_eq_getD_getElem?,
          List.append_assoc]
      · simp [push, heq, Std.HashMap.getD_alter]

/-- The reverse head-only bucket contains exactly the matching processed
    clauses, reversed, followed by the seed bucket. -/
theorem foldl_head_getD (wanted : String)
    (clauses : List (String × Clause)) :
    ∀ seed : ClauseIndex,
      (clauses.foldl push seed).byHead.getD wanted [] =
        (naiveHeadCandidates clauses wanted).reverse ++
          seed.byHead.getD wanted [] := by
  induction clauses with
  | nil =>
      intro seed
      simp [naiveHeadCandidates]
  | cons entry rest ih =>
      intro seed
      rcases entry with ⟨entryHead, clause⟩
      rw [List.foldl_cons, ih]
      by_cases heq : entryHead = wanted
      · subst entryHead
        simp [push, naiveHeadCandidates,
          Std.HashMap.getD_eq_getD_getElem?, List.append_assoc]
      · simp [push, naiveHeadCandidates, heq, Std.HashMap.getD_alter]

/-- Building an index and selecting a bucket is exactly naive ordered
    filtering, not merely a permutation or set equality. -/
theorem build_candidates (clauses : List (String × Clause)) (head : String)
    (arity : Nat) :
    candidates (build clauses) head arity =
      naiveCandidates clauses head arity := by
  simp [build, candidates, foldl_getD, empty,
    naiveCandidates, Std.HashMap.getD_emptyWithCapacity]

/-- Building an index and selecting a head is exactly the old ordered
    `clausesOf` filter. -/
theorem build_headCandidates (clauses : List (String × Clause))
    (head : String) :
    headCandidates (build clauses) head =
      naiveHeadCandidates clauses head := by
  simp [build, headCandidates, foldl_head_getD, empty,
    Std.HashMap.getD_emptyWithCapacity]

/-- Arity-indexed filtering is the old head-only candidate list followed by
    the structural arity check that resolution already performs. -/
theorem naiveCandidates_eq_head_filter (clauses : List (String × Clause))
    (head : String) (arity : Nat) :
    naiveCandidates clauses head arity =
      (naiveHeadCandidates clauses head).filter fun clause =>
        clause.params.length == arity := by
  induction clauses with
  | nil => simp [naiveCandidates, naiveHeadCandidates]
  | cons entry rest ih =>
      rcases entry with ⟨entryHead, clause⟩
      simp only [naiveCandidates, naiveHeadCandidates] at ih ⊢
      simp only [List.filterMap_cons]
      rw [ih]
      by_cases hhead : entryHead = head
      · subst entryHead
        by_cases harity : clause.params.length = arity
        · simp [key, harity]
        · simp [key, harity]
      · simp [key, hhead]

/-- The derived index is exactly the one built from the canonical clause
    list.  Candidate correctness follows from the independent build theorems
    above rather than from Machine and Step sharing an implementation. -/
def Valid (index : ClauseIndex) (clauses : List (String × Clause)) : Prop :=
  index = build clauses

theorem build_valid (clauses : List (String × Clause)) :
    Valid (build clauses) clauses := rfl

theorem Valid.headCandidates {index : ClauseIndex}
    {clauses : List (String × Clause)} (valid : Valid index clauses)
    (head : String) :
    headCandidates index head = naiveHeadCandidates clauses head := by
  rw [valid]
  exact build_headCandidates clauses head

theorem Valid.candidates {index : ClauseIndex}
    {clauses : List (String × Clause)} (valid : Valid index clauses)
    (head : String) (arity : Nat) :
    candidates index head arity = naiveCandidates clauses head arity := by
  rw [valid]
  exact build_candidates clauses head arity

/-- Updating the selected bucket appends the new clause in observable order. -/
theorem candidates_push_self (index : ClauseIndex) (head : String)
    (clause : Clause) :
    candidates (push index (head, clause)) head clause.params.length =
      candidates index head clause.params.length ++ [clause] := by
  simp [candidates, push, key, Std.HashMap.getD_eq_getD_getElem?]

/-- Updating another bucket cannot affect this head's candidates. -/
theorem candidates_push_other (index : ClauseIndex) (entryHead head : String)
    (clause : Clause) (arity : Nat)
    (hne : (entryHead, clause.params.length) ≠ (head, arity)) :
    candidates (push index (entryHead, clause)) head arity =
      candidates index head arity := by
  simp [candidates, push, key, Std.HashMap.getD_alter, hne]

theorem headCandidates_push_self (index : ClauseIndex) (head : String)
    (clause : Clause) :
    headCandidates (push index (head, clause)) head =
      headCandidates index head ++ [clause] := by
  simp [headCandidates, push, Std.HashMap.getD_eq_getD_getElem?]

theorem headCandidates_push_other (index : ClauseIndex)
    (entryHead head : String) (clause : Clause) (hne : entryHead ≠ head) :
    headCandidates (push index (entryHead, clause)) head =
      headCandidates index head := by
  simp [headCandidates, push, Std.HashMap.getD_alter, hne]

/-- Appending one canonical clause and pushing the same clause into a valid
    index preserves the exact ordered-filter invariant. -/
theorem Valid.push {index : ClauseIndex} {clauses : List (String × Clause)}
    (valid : Valid index clauses) (entry : String × Clause) :
    Valid (push index entry) (clauses ++ [entry]) := by
  rw [valid]
  simp [Valid, build, List.foldl_append]

end ClauseIndex

/-! ## Mutable-space atom index -/

/-- A conservative outer discriminator for stored atoms.  A chain whose
    first element is a fixed symbol is the common representation of a MeTTa
    application/fact.  Returning `none` means that selecting one bucket is
    not known safe, so lookup falls back to the canonical snapshot. -/
inductive SpaceOuterKey where
  | symbol (name : String)
  | grounded
  | expressionHeads (first second : String)
deriving Repr, BEq, ReflBEq, LawfulBEq, Hashable

/-- Constant-size digest for exact structural indexing. Hash collisions are
    harmless: buckets are conservative candidate supersets and the unchanged
    compatibility check remains the semantic filter. -/
abbrev SpaceExactKey := UInt64

namespace SpaceIndex

open Metta (Atom Ground)

def outerKey : Atom → Option SpaceOuterKey
  | .sym name => some (.symbol name)
  | .gnd _ => some .grounded
  | .expr (.sym first :: .sym second :: _) =>
      some (.expressionHeads first second)
  | _ => none

mutual
  def exactKey : Atom → Option SpaceExactKey
    | .sym name => some (mixHash 1 (hash name))
    | .var _ => none
    | .gnd ground => match ground with
      | .int value => some (mixHash 2 (hash value))
      | .float _ => none
      | .str value => some (mixHash 3 (hash value))
      | .bool value => some (mixHash 4 (hash value))
      | .unit => some 5
      | .error message => some (mixHash 6 (hash message))
      | .external tag payload =>
          some (mixHash 7 (mixHash (hash tag) (hash payload)))
    | .expr items => (exactKeyList items).map fun keys =>
        mixHash 8 keys

  def exactKeyList : List Atom → Option SpaceExactKey
    | [] => some 9
    | atom :: rest => do
        let head ← exactKey atom
        let tail ← exactKeyList rest
        pure (mixHash (mixHash 10 head) tail)
end

mutual
  theorem exactKey_eq_atomExactKey : ∀ atom : Atom,
      exactKey atom = PersistentSubst.atomExactKey atom
    | .sym _ => rfl
    | .var _ => rfl
    | .gnd ground => by cases ground <;> rfl
    | .expr items => by
        simp only [exactKey, PersistentSubst.atomExactKey]
        rw [exactKeyList_eq_atomExactKeyList items]

  theorem exactKeyList_eq_atomExactKeyList : ∀ atoms : List Atom,
      exactKeyList atoms = PersistentSubst.atomExactKeyList atoms
    | [] => rfl
    | atom :: rest => by
        simp only [exactKeyList, PersistentSubst.atomExactKeyList]
        rw [exactKey_eq_atomExactKey atom,
          exactKeyList_eq_atomExactKeyList rest]
end

/-- Cached metadata for one immediate child of an indexed expression.  The
    fields are uniquely determined by `atom`, so optimized construction can
    reuse prepared substitution results without changing index validity. -/
structure IndexedChild where
  atom : Atom
  closed : Bool
  exact : Option SpaceExactKey
  closed_eq : closed = PersistentSubst.atomClosed atom
  exact_eq : exact = exactKey atom
deriving Repr

def prepareChild (atom : Atom) : IndexedChild :=
  { atom
    closed := PersistentSubst.atomClosed atom
    exact := exactKey atom
    closed_eq := rfl
    exact_eq := rfl }

@[simp] theorem prepareChild_atom (atom : Atom) :
    (prepareChild atom).atom = atom := rfl

@[simp] theorem prepareChild_atom_eq (prepared : IndexedChild) :
    prepareChild prepared.atom = prepared := by
  rcases prepared with ⟨atom, closed, exact, closedEq, exactEq⟩
  subst closed
  subst exact
  rfl

def prepareChildren : Atom → List IndexedChild
  | .expr atoms => atoms.map prepareChild
  | _ => []

/-- Canonical metadata for the logical elements of an internal PeTTa chain.
    This flattens only the `#c` spine; element subtrees remain shared. -/
def prepareItems (atom : Atom) : List IndexedChild :=
  (chainListM atom).getD [] |>.map prepareChild

/-- An indexed atom paired with metadata computed once when it enters a
    mutable space.  `SpaceIndex.Valid` below requires every executable index
    to be the result of `build`, so these fields cannot drift from `atom`. -/
structure IndexedAtom where
  atom : Atom
  closed : Bool
  exact : Option SpaceExactKey
  children : List IndexedChild
  items : List IndexedChild
  closed_eq : closed = PersistentSubst.atomClosed atom
  exact_eq : exact = exactKey atom
  children_eq : children = prepareChildren atom
  items_eq : items = prepareItems atom
deriving Repr

def prepareAtom (atom : Atom) : IndexedAtom :=
  { atom
    closed := PersistentSubst.atomClosed atom
    exact := exactKey atom
    children := prepareChildren atom
    items := prepareItems atom
    closed_eq := rfl
    exact_eq := rfl
    children_eq := rfl
    items_eq := rfl }

@[simp] theorem prepareAtom_atom (atom : Atom) :
    (prepareAtom atom).atom = atom := rfl

@[simp] theorem prepareAtom_atom_eq (prepared : IndexedAtom) :
    prepareAtom prepared.atom = prepared := by
  rcases prepared with
    ⟨atom, closed, exact, children, items, closedEq, exactEq, childrenEq,
      itemsEq⟩
  subst closed
  subst exact
  subst children
  subst items
  rfl

@[simp] theorem map_prepareAtom_map_atom (prepared : List IndexedAtom) :
    (prepared.map IndexedAtom.atom).map prepareAtom = prepared := by
  rw [List.map_map]
  simp [Function.comp_def]

/- Syntactic compatibility used by space matching before full unification.
   It is false only on a constructor/head/arity clash. -/
mutual
  def compatible : Atom → Atom → Bool
    | .var _, _ => true
    | _, .var _ => true
    | .sym left, .sym right => left == right
    | .gnd left, .gnd right => Metta.Ground.equiv left right
    | .expr left, .expr right => compatibleList left right
    | _, _ => false

  def compatibleList : List Atom → List Atom → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        compatible left right && compatibleList leftRest rightRest
    | _, _ => false
end

mutual

/-- Exact-keyable compatible atoms receive the same bucket key.  Unsupported
    values have no exact key and therefore take a conservative fallback. -/
theorem exactKey_eq_of_compatible (left right : Atom)
    (leftKey rightKey : SpaceExactKey)
    (hcompat : compatible left right = true)
    (hleft : exactKey left = some leftKey)
    (hright : exactKey right = some rightKey) :
    leftKey = rightKey := by
  cases left with
  | sym leftName =>
      cases right with
      | sym rightName =>
          have hname : leftName = rightName := by
            simpa [compatible] using hcompat
          subst rightName
          cases hleft
          cases hright
          rfl
      | var rightName => simp [exactKey] at hright
      | gnd rightGround => simp [compatible] at hcompat
      | expr rightItems => simp [compatible] at hcompat
  | var leftName =>
      simp [exactKey] at hleft
  | gnd leftGround =>
      cases right with
      | sym rightName => simp [compatible] at hcompat
      | var rightName => simp [exactKey] at hright
      | expr rightItems => simp [compatible] at hcompat
      | gnd rightGround =>
          cases leftGround <;> cases rightGround <;>
            simp [exactKey, compatible, Metta.Ground.equiv, BEq.beq,
              Metta.instBEqGround.beq]
              at hcompat hleft hright ⊢
          all_goals
            simp_all
  | expr leftItems =>
      cases right with
      | sym rightName => simp [compatible] at hcompat
      | var rightName => simp [exactKey] at hright
      | gnd rightGround => simp [compatible] at hcompat
      | expr rightItems =>
          cases hleftKeys : exactKeyList leftItems with
          | none => simp [exactKey, hleftKeys] at hleft
          | some leftKeys =>
              cases hrightKeys : exactKeyList rightItems with
              | none => simp [exactKey, hrightKeys] at hright
              | some rightKeys =>
                  have hkeys := exactKeyList_eq_of_compatibleList
                    leftItems rightItems leftKeys rightKeys hcompat
                    hleftKeys hrightKeys
                  subst rightKeys
                  simp [exactKey, hleftKeys, hrightKeys] at hleft hright
                  exact hleft.symm.trans hright

/-- Pointwise counterpart of `exactKey_eq_of_compatible`. -/
theorem exactKeyList_eq_of_compatibleList (left right : List Atom)
    (leftKeys rightKeys : SpaceExactKey)
    (hcompat : compatibleList left right = true)
    (hleft : exactKeyList left = some leftKeys)
    (hright : exactKeyList right = some rightKeys) :
    leftKeys = rightKeys := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          cases hleft
          cases hright
          rfl
      | cons rightHead rightRest => simp [compatibleList] at hcompat
  | cons leftHead leftRest =>
      cases right with
      | nil => simp [compatibleList] at hcompat
      | cons rightHead rightRest =>
          simp only [compatibleList, Bool.and_eq_true] at hcompat
          rcases hcompat with ⟨hheadCompat, hrestCompat⟩
          cases hleftHead : exactKey leftHead with
          | none => simp [exactKeyList, hleftHead] at hleft
          | some leftHeadKey =>
              cases hrightHead : exactKey rightHead with
              | none => simp [exactKeyList, hrightHead] at hright
              | some rightHeadKey =>
                  cases hleftRest : exactKeyList leftRest with
                  | none => simp [exactKeyList, hleftHead, hleftRest] at hleft
                  | some leftRestKeys =>
                      cases hrightRest : exactKeyList rightRest with
                      | none =>
                          simp [exactKeyList, hrightHead, hrightRest] at hright
                      | some rightRestKeys =>
                          have hheadKey := exactKey_eq_of_compatible
                            leftHead rightHead leftHeadKey rightHeadKey
                            hheadCompat hleftHead hrightHead
                          have hrestKey := exactKeyList_eq_of_compatibleList
                            leftRest rightRest leftRestKeys rightRestKeys
                            hrestCompat hleftRest hrightRest
                          subst rightHeadKey
                          subst rightRestKeys
                          simp [exactKeyList, hleftHead, hleftRest] at hleft
                          simp [exactKeyList, hrightHead, hrightRest] at hright
                          exact hleft.symm.trans hright

end

/-- Outer-keyable compatible atoms receive the same bucket key. -/
theorem outerKey_eq_of_compatible (left right : Atom)
    (leftKey rightKey : SpaceOuterKey)
    (hcompat : compatible left right = true)
    (hleft : outerKey left = some leftKey)
    (hright : outerKey right = some rightKey) :
    leftKey = rightKey := by
  cases left with
  | sym leftName =>
      cases right with
      | sym rightName =>
          have hname : leftName = rightName := by
            simpa [compatible] using hcompat
          subst rightName
          cases hleft
          cases hright
          rfl
      | var rightName => simp [outerKey] at hright
      | gnd rightGround => simp [compatible] at hcompat
      | expr rightItems => simp [compatible] at hcompat
  | var leftName => simp [outerKey] at hleft
  | gnd leftGround =>
      cases right with
      | sym rightName => simp [compatible] at hcompat
      | var rightName => simp [outerKey] at hright
      | gnd rightGround =>
          cases hleft
          cases hright
          rfl
      | expr rightItems => simp [compatible] at hcompat
  | expr leftItems =>
      cases right with
      | sym rightName => simp [compatible] at hcompat
      | var rightName => simp [outerKey] at hright
      | gnd rightGround => simp [compatible] at hcompat
      | expr rightItems =>
          cases leftItems with
          | nil => simp [outerKey] at hleft
          | cons leftFirst leftRest =>
              cases leftRest with
              | nil => simp [outerKey] at hleft
              | cons leftSecond leftTail =>
                  cases leftFirst with
                  | sym leftFirstName =>
                      cases leftSecond with
                      | sym leftSecondName =>
                          cases rightItems with
                          | nil => simp [outerKey] at hright
                          | cons rightFirst rightRest =>
                              cases rightRest with
                              | nil => simp [outerKey] at hright
                              | cons rightSecond rightTail =>
                                  cases rightFirst with
                                  | sym rightFirstName =>
                                      cases rightSecond with
                                      | sym rightSecondName =>
                                          simp [compatible, compatibleList]
                                            at hcompat
                                          rcases hcompat with
                                            ⟨hfirst, hsecond, _⟩
                                          subst rightFirstName
                                          subst rightSecondName
                                          cases hleft
                                          cases hright
                                          rfl
                                      | var name =>
                                          simp [outerKey] at hright
                                      | gnd ground =>
                                          simp [outerKey] at hright
                                      | expr items =>
                                          simp [outerKey] at hright
                                  | var name => simp [outerKey] at hright
                                  | gnd ground => simp [outerKey] at hright
                                  | expr items => simp [outerKey] at hright
                      | var name => simp [outerKey] at hleft
                      | gnd ground => simp [outerKey] at hleft
                      | expr items => simp [outerKey] at hleft
                  | var name => simp [outerKey] at hleft
                  | gnd ground => simp [outerKey] at hleft
                  | expr items => simp [outerKey] at hleft

/-- Derived buckets are stored newest-first, matching `PWorld`'s canonical
    representation.  Every bucket also contains the previously inserted
    unkeyable atoms, which are the wildcard/cross-numeric fallback candidates
    for that discriminator. -/
structure State where
  byOuter : Std.HashMap SpaceOuterKey (List IndexedAtom) :=
    Std.HashMap.emptyWithCapacity
  outerFallback : List IndexedAtom := []
  byExact : Std.HashMap SpaceExactKey (List IndexedAtom) :=
    Std.HashMap.emptyWithCapacity
  exactFallback : List IndexedAtom := []
  newest : List IndexedAtom := []
deriving Repr, Inhabited

def empty : State := {}

/-- Insert prepared atom metadata into every safe derived bucket. -/
def pushPrepared (index : State) (prepared : IndexedAtom) : State :=
  { byOuter := match outerKey prepared.atom with
      | some key => index.byOuter.alter key fun current =>
          some (prepared :: current.getD index.outerFallback)
      | none => index.byOuter.map fun _ bucket => prepared :: bucket
    outerFallback := match outerKey prepared.atom with
      | some _ => index.outerFallback
      | none => prepared :: index.outerFallback
    byExact := match prepared.exact with
      | some key => index.byExact.alter key fun current =>
          some (prepared :: current.getD index.exactFallback)
      | none => index.byExact.map fun _ bucket => prepared :: bucket
    exactFallback := match prepared.exact with
      | some _ => index.exactFallback
      | none => prepared :: index.exactFallback
    newest := prepared :: index.newest }

/-- Insert one new canonical atom into every safe derived bucket. -/
def push (index : State) (atom : Atom) : State :=
  pushPrepared index (prepareAtom atom)

/-- Build from a newest-first canonical list.  Recursing over the tail first
    processes atoms in insertion order, while `push` restores newest-first
    buckets. -/
def build : List Atom → State
  | [] => empty
  | atom :: rest => push (build rest) atom

def outerSelect (key : SpaceOuterKey) (atom : Atom) : Bool :=
  match outerKey atom with
  | some atomKey => atomKey == key
  | none => true

def exactSelect (key : SpaceExactKey) (atom : Atom) : Bool :=
  match exactKey atom with
  | some atomKey => atomKey == key
  | none => true

def preparedOuterBucket (index : State) (key : SpaceOuterKey) :
    List IndexedAtom :=
  index.byOuter.getD key index.outerFallback

def preparedExactBucket (index : State) (key : SpaceExactKey) :
    List IndexedAtom :=
  index.byExact.getD key index.exactFallback

def outerBucket (index : State) (key : SpaceOuterKey) : List Atom :=
  (preparedOuterBucket index key).map IndexedAtom.atom

def exactBucket (index : State) (key : SpaceExactKey) : List Atom :=
  (preparedExactBucket index key).map IndexedAtom.atom

def outerCandidates (index : State) (key : SpaceOuterKey) : List Atom :=
  (outerBucket index key).reverse

def exactCandidates (index : State) (key : SpaceExactKey) : List Atom :=
  (exactBucket index key).reverse

def preparedOuterCandidates (index : State) (key : SpaceOuterKey) :
    List IndexedAtom :=
  (preparedOuterBucket index key).reverse

def preparedExactCandidates (index : State) (key : SpaceExactKey) :
    List IndexedAtom :=
  (preparedExactBucket index key).reverse

/-- Candidate selection with insertion-time atom metadata. -/
def preparedCandidates (index : State) (query : Atom) : List IndexedAtom :=
  match exactKey query with
  | some key => preparedExactCandidates index key
  | none =>
      match outerKey query with
      | some key => preparedOuterCandidates index key
      | none => index.newest.reverse

/-- Candidate selection using a prepared query cache.  An unknown cache
falls back to the raw exact-key computation; a computed negative result skips
that traversal and uses the outer discriminator directly. -/
def preparedCandidatesCached (index : State) (query : Atom)
    (cache : PersistentSubst.AtomExactCache) : List IndexedAtom :=
  match cache with
  | some (some key) => preparedExactCandidates index key
  | some none =>
      match outerKey query with
      | some key => preparedOuterCandidates index key
      | none => index.newest.reverse
  | none => preparedCandidates index query

def outerCandidatesOrAll (index : State) (_atomsNewest : List Atom)
    (query : Atom) : List Atom :=
  match outerKey query with
  | some key => outerCandidates index key
  | none => index.newest.reverse.map IndexedAtom.atom

/-- Select an order-preserving candidate snapshot.  Wildcard and unsafe
    stored atoms are already interleaved into each bucket at insertion time. -/
def candidates (index : State) (_atomsNewest : List Atom)
    (query : Atom) : List Atom :=
  (preparedCandidates index query).map IndexedAtom.atom

/-- Independent ordered-filter meaning of `candidates`, stated only from the
    canonical list. -/
def naiveCandidates (atomsNewest : List Atom) (query : Atom) : List Atom :=
  match exactKey query with
  | some key => atomsNewest.reverse.filter (exactSelect key)
  | none =>
      match outerKey query with
      | some key => atomsNewest.reverse.filter (outerSelect key)
      | none => atomsNewest.reverse

theorem naiveCandidates_length_le (atomsNewest : List Atom) (query : Atom) :
    (naiveCandidates atomsNewest query).length ≤ atomsNewest.length := by
  unfold naiveCandidates
  cases exactKey query with
  | some key =>
      simpa using List.length_filter_le (exactSelect key) atomsNewest.reverse
  | none =>
      cases outerKey query with
      | some key =>
          simpa using List.length_filter_le (outerSelect key)
            atomsNewest.reverse
      | none => simp

private theorem getD_map_cons {Key Value : Type} [BEq Key] [Hashable Key]
    [LawfulBEq Key] (table : Std.HashMap Key (List Value)) (value : Value)
    (key : Key) (fallback : List Value) :
    (table.map fun _ bucket => value :: bucket).getD key
        (value :: fallback) =
      value :: table.getD key fallback := by
  rw [Std.HashMap.getD_map]
  cases hlookup : table[key]? <;>
    simp [hlookup, Std.HashMap.getD_eq_getD_getElem?]

theorem push_outerBucket (index : State) (atom : Atom)
    (wanted : SpaceOuterKey) :
    outerBucket (push index atom) wanted =
      if outerSelect wanted atom then atom :: outerBucket index wanted
      else outerBucket index wanted := by
  cases hkey : outerKey atom with
  | none =>
      simp [outerBucket, preparedOuterBucket, outerSelect, prepareAtom,
        push, pushPrepared, hkey, getD_map_cons]
  | some key =>
      by_cases heq : key = wanted
      · subst key
        simp [outerBucket, preparedOuterBucket, outerSelect, prepareAtom,
          push, pushPrepared, hkey,
          Std.HashMap.getD_eq_getD_getElem?]
      · simp [outerBucket, preparedOuterBucket, outerSelect, prepareAtom,
          push, pushPrepared, hkey, heq,
          Std.HashMap.getD_alter]

theorem push_exactBucket (index : State) (atom : Atom)
    (wanted : SpaceExactKey) :
    exactBucket (push index atom) wanted =
      if exactSelect wanted atom then atom :: exactBucket index wanted
      else exactBucket index wanted := by
  cases hkey : exactKey atom with
  | none =>
      simp [exactBucket, preparedExactBucket, exactSelect, prepareAtom,
        push, pushPrepared, hkey,
        getD_map_cons]
  | some key =>
      by_cases heq : key = wanted
      · subst key
        simp [exactBucket, preparedExactBucket, exactSelect, prepareAtom,
          push, pushPrepared, hkey,
          Std.HashMap.getD_eq_getD_getElem?]
      · simp [exactBucket, preparedExactBucket, exactSelect, prepareAtom,
          push, pushPrepared, hkey, heq,
          Std.HashMap.getD_alter]

theorem push_preparedOuterBucket (index : State) (atom : Atom)
    (wanted : SpaceOuterKey) :
    preparedOuterBucket (push index atom) wanted =
      if outerSelect wanted atom then
        prepareAtom atom :: preparedOuterBucket index wanted
      else preparedOuterBucket index wanted := by
  cases hkey : outerKey atom with
  | none =>
      simp [preparedOuterBucket, outerSelect, push, pushPrepared, hkey,
        getD_map_cons]
  | some key =>
      by_cases heq : key = wanted
      · subst key
        simp [preparedOuterBucket, outerSelect, push, pushPrepared, hkey,
          Std.HashMap.getD_eq_getD_getElem?]
      · simp [preparedOuterBucket, outerSelect, push, pushPrepared, hkey, heq,
          Std.HashMap.getD_alter]

theorem push_preparedExactBucket (index : State) (atom : Atom)
    (wanted : SpaceExactKey) :
    preparedExactBucket (push index atom) wanted =
      if exactSelect wanted atom then
        prepareAtom atom :: preparedExactBucket index wanted
      else preparedExactBucket index wanted := by
  cases hkey : exactKey atom with
  | none =>
      simp [preparedExactBucket, exactSelect, prepareAtom, push, pushPrepared,
        hkey,
        getD_map_cons]
  | some key =>
      by_cases heq : key = wanted
      · subst key
        simp [preparedExactBucket, exactSelect, prepareAtom, push,
          pushPrepared, hkey,
          Std.HashMap.getD_eq_getD_getElem?]
      · simp [preparedExactBucket, exactSelect, prepareAtom, push,
          pushPrepared, hkey,
          heq, Std.HashMap.getD_alter]

theorem build_outerBucket (atoms : List Atom) (key : SpaceOuterKey) :
    outerBucket (build atoms) key = atoms.filter (outerSelect key) := by
  induction atoms with
  | nil => simp [build, empty, outerBucket, preparedOuterBucket,
      Std.HashMap.getD_emptyWithCapacity]
  | cons atom rest ih =>
      rw [build, push_outerBucket, ih]
      cases hselect : outerSelect key atom <;> simp [hselect]

theorem build_exactBucket (atoms : List Atom) (key : SpaceExactKey) :
    exactBucket (build atoms) key = atoms.filter (exactSelect key) := by
  induction atoms with
  | nil => simp [build, empty, exactBucket, preparedExactBucket,
      Std.HashMap.getD_emptyWithCapacity]
  | cons atom rest ih =>
      rw [build, push_exactBucket, ih]
      cases hselect : exactSelect key atom <;> simp [hselect]

theorem build_preparedOuterBucket (atoms : List Atom)
    (key : SpaceOuterKey) :
    preparedOuterBucket (build atoms) key =
      (atoms.filter (outerSelect key)).map prepareAtom := by
  induction atoms with
  | nil => simp [build, empty, preparedOuterBucket,
      Std.HashMap.getD_emptyWithCapacity]
  | cons atom rest ih =>
      rw [build, push_preparedOuterBucket, ih]
      cases hselect : outerSelect key atom <;> simp [hselect]

theorem build_preparedExactBucket (atoms : List Atom)
    (key : SpaceExactKey) :
    preparedExactBucket (build atoms) key =
      (atoms.filter (exactSelect key)).map prepareAtom := by
  induction atoms with
  | nil => simp [build, empty, preparedExactBucket,
      Std.HashMap.getD_emptyWithCapacity]
  | cons atom rest ih =>
      rw [build, push_preparedExactBucket, ih]
      cases hselect : exactSelect key atom <;> simp [hselect]

theorem build_preparedNewest (atoms : List Atom) :
    (build atoms).newest = atoms.map prepareAtom := by
  induction atoms with
  | nil => rfl
  | cons atom rest => simp [build, push, pushPrepared, *]

theorem build_outerCandidates (atoms : List Atom) (key : SpaceOuterKey) :
    outerCandidates (build atoms) key =
      atoms.reverse.filter (outerSelect key) := by
  simp [outerCandidates, build_outerBucket, List.filter_reverse]

theorem build_exactCandidates (atoms : List Atom) (key : SpaceExactKey) :
    exactCandidates (build atoms) key =
      atoms.reverse.filter (exactSelect key) := by
  simp [exactCandidates, build_exactBucket, List.filter_reverse]

/-- The executable selector is exactly its independent canonical-list
    denotation, including every conservative fallback. -/
theorem build_candidates (atoms : List Atom) (query : Atom) :
    candidates (build atoms) atoms query = naiveCandidates atoms query := by
  unfold candidates preparedCandidates naiveCandidates
  cases exactKey query with
  | some key =>
      simp [preparedExactCandidates, build_preparedExactBucket,
        List.filter_reverse, Function.comp_def]
  | none =>
      cases outerKey query with
      | some key =>
          simp [preparedOuterCandidates, build_preparedOuterBucket,
            List.filter_reverse, Function.comp_def]
      | none => simp [build_preparedNewest, Function.comp_def]

theorem build_preparedCandidates (atoms : List Atom) (query : Atom) :
    preparedCandidates (build atoms) query =
      (naiveCandidates atoms query).map prepareAtom := by
  unfold preparedCandidates naiveCandidates
  cases exactKey query with
  | some key =>
      simp [preparedExactCandidates, build_preparedExactBucket,
        List.filter_reverse]
  | none =>
      cases outerKey query with
      | some key =>
          simp [preparedOuterCandidates, build_preparedOuterBucket,
            List.filter_reverse]
      | none => simp [build_preparedNewest]

private theorem filter_filter_eq_of_imp_mem {α : Type}
    (items : List α) (keep select : α → Bool)
    (h : ∀ item ∈ items, keep item = true → select item = true) :
    (items.filter select).filter keep = items.filter keep := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have hrest : ∀ candidate ∈ rest,
          keep candidate = true → select candidate = true := by
        intro candidate hmem
        exact h candidate (by simp [hmem])
      cases hselect : select item <;> cases hkeep : keep item
      · simp [hselect, hkeep, ih hrest]
      · have himpossible := h item (by simp) hkeep
        simp [hselect] at himpossible
      · simp [hselect, hkeep, ih hrest]
      · simp [hselect, hkeep, ih hrest]

/-- Index pruning followed by the unchanged syntactic matcher is exactly a
    full canonical scan followed by that matcher, in the same order and with
    duplicate multiplicity preserved. -/
theorem naiveCandidates_filter_compatible (atoms : List Atom) (query : Atom) :
    (naiveCandidates atoms query).filter (compatible query) =
      atoms.reverse.filter (compatible query) := by
  unfold naiveCandidates
  cases hqueryExact : exactKey query with
  | some queryExact =>
      apply filter_filter_eq_of_imp_mem
      intro atom _ hcompat
      unfold exactSelect
      cases hatomExact : exactKey atom with
      | none => rfl
      | some atomExact =>
          have hkeys := exactKey_eq_of_compatible query atom
            queryExact atomExact hcompat hqueryExact hatomExact
          subst atomExact
          simp
  | none =>
      cases hqueryOuter : outerKey query with
      | none => rfl
      | some queryOuter =>
          apply filter_filter_eq_of_imp_mem
          intro atom _ hcompat
          unfold outerSelect
          cases hatomOuter : outerKey atom with
          | none => rfl
          | some atomOuter =>
              have hkeys := outerKey_eq_of_compatible query atom
                queryOuter atomOuter hcompat hqueryOuter hatomOuter
              subst atomOuter
              simp

def Valid (index : State) (atomsNewest : List Atom) : Prop :=
  index = build atomsNewest

theorem build_valid (atomsNewest : List Atom) :
    Valid (build atomsNewest) atomsNewest := rfl

theorem Valid.candidates {index : State} {atomsNewest : List Atom}
    (valid : Valid index atomsNewest) (query : Atom) :
    candidates index atomsNewest query = naiveCandidates atomsNewest query := by
  rw [valid]
  exact build_candidates atomsNewest query

theorem Valid.preparedCandidates {index : State} {atomsNewest : List Atom}
    (valid : Valid index atomsNewest) (query : Atom) :
    preparedCandidates index query =
      (SpaceIndex.candidates index atomsNewest query).map prepareAtom := by
  rw [valid, build_candidates, build_preparedCandidates]

theorem Valid.candidates_length_le {index : State} {atomsNewest : List Atom}
    (valid : Valid index atomsNewest) (query : Atom) :
    (SpaceIndex.candidates index atomsNewest query).length ≤ atomsNewest.length := by
  rw [valid, build_candidates]
  exact naiveCandidates_length_le atomsNewest query

theorem Valid.filteredCandidates {index : State} {atomsNewest : List Atom}
    (valid : Valid index atomsNewest) (query : Atom) :
    (SpaceIndex.candidates index atomsNewest query).filter
        (compatible query) =
      atomsNewest.reverse.filter (compatible query) := by
  rw [Valid.candidates valid query]
  exact naiveCandidates_filter_compatible atomsNewest query

theorem Valid.push {index : State} {atomsNewest : List Atom}
    (valid : Valid index atomsNewest) (atom : Atom) :
    Valid (push index atom) (atom :: atomsNewest) := by
  rw [valid]
  rfl

end SpaceIndex

end PLeaTTa
