import MettaHyperonFull.Core.Unification
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.String.ToNat
import Std.Data.TreeMap.Basic

namespace PLeaTTa

open Metta (Atom)

/-- Scan a reversed name, accumulating the terminal decimal payload in its
    original order. -/
def terminalResolutionSeedRev : List Char → List Char → Option Nat
  | [], _ => none
  | char :: rest, digits =>
      if char.isDigit then terminalResolutionSeedRev rest (char :: digits)
      else if char == 'r' then
        match rest with
        | '#' :: _ => (String.ofList digits).toNat?
        | _ => none
      else none

/-- Recover the numeric payload of a terminal internal resolution suffix. -/
def terminalResolutionSeed? (name : String) : Option Nat :=
  terminalResolutionSeedRev name.toList.reverse []

/-- Exclusive upper bound for every terminal `#r<n>` token in one name. -/
def resolutionSeedHighWaterName (name : String) : Nat :=
  match terminalResolutionSeed? name with
  | some seed => seed + 1
  | none => 0

def resolutionSeedHighWaterNames : List String → Nat
  | [] => 0
  | name :: rest =>
      max (resolutionSeedHighWaterName name)
        (resolutionSeedHighWaterNames rest)

def resolutionSeedHighWaterAtom (atom : Atom) : Nat :=
  resolutionSeedHighWaterNames atom.vars

def resolutionSeedHighWaterAtoms : List Atom → Nat
  | [] => 0
  | atom :: rest =>
      max (resolutionSeedHighWaterAtom atom)
        (resolutionSeedHighWaterAtoms rest)

/-- Advance a name supply past arbitrary atoms crossing a host boundary. -/
def advanceCounterPastAtoms (counter : Nat) (atoms : List Atom) : Nat :=
  max counter (resolutionSeedHighWaterAtoms atoms)

namespace PersistentSubst

open Metta (Atom Subst)

/- Allocation-free closedness test used by the executable substitution
engine.  Unlike `Atom.vars`, it does not construct a list of occurrences. -/
mutual
/-- True exactly when an atom contains no variables. -/
def atomClosed : Atom → Bool
  | .sym _ => true
  | .var _ => false
  | .gnd _ => true
  | .expr atoms => atomsClosed atoms
termination_by atom => 2 * atom.size
decreasing_by
  simp [Atom.size]
  omega

def atomsClosed : List Atom → Bool
  | [] => true
  | atom :: rest => atomClosed atom && atomsClosed rest
termination_by atoms => 2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals
    simp only [List.map_cons, List.sum_cons]
    have hsize : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega
end

/-- Structural key shared with the mutable-space exact index.  Variables and
floating-point values deliberately have no exact key. -/
abbrev AtomExactKey := UInt64

mutual
def atomExactKey : Atom → Option AtomExactKey
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
  | .expr items => (atomExactKeyList items).map fun keys =>
      mixHash 8 keys

def atomExactKeyList : List Atom → Option AtomExactKey
  | [] => some 9
  | atom :: rest => do
      let head ← atomExactKey atom
      let tail ← atomExactKeyList rest
      pure (mixHash (mixHash 10 head) tail)
end

/-- Reflexive, injective equality on the exact-key fragment.  Floating-point
atoms are deliberately excluded, matching `atomExactKey`; this avoids turning
host floating-point non-reflexivity into a cache assumption. -/
def groundExactEq : Metta.Ground → Metta.Ground → Bool
  | .int left, .int right => left == right
  | .float _, .float _ => false
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .unit, .unit => true
  | .error left, .error right => left == right
  | .external leftTag leftPayload, .external rightTag rightPayload =>
      leftTag == rightTag && leftPayload == rightPayload
  | _, _ => false

mutual
def atomExactEq : Atom → Atom → Bool
  | .sym left, .sym right => left == right
  | .var _, .var _ => false
  | .gnd left, .gnd right => groundExactEq left right
  | .expr left, .expr right => atomExactEqList left right
  | _, _ => false

def atomExactEqList : List Atom → List Atom → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      atomExactEq left right && atomExactEqList leftRest rightRest
  | _, _ => false
end

mutual
theorem atomExactEq_sound : ∀ left right,
    atomExactEq left right = true → left = right := by
  intro left right
  cases left <;> cases right
  all_goals simp only [atomExactEq, Bool.false_eq_true]
  all_goals try { intro impossible; contradiction }
  · intro equal
    simp only [beq_iff_eq] at equal
    exact congrArg Atom.sym equal
  · rename_i left right
    intro equal
    cases left <;> cases right <;>
      simp [groundExactEq, Bool.and_eq_true] at equal ⊢ <;> assumption
  · intro equal
    exact congrArg Atom.expr (atomExactEqList_sound _ _ equal)
termination_by left _ => 2 * left.size
decreasing_by
  simp [Atom.size]
  omega

theorem atomExactEqList_sound : ∀ left right,
    atomExactEqList left right = true → left = right := by
  intro left right
  cases left with
  | nil => cases right <;> simp [atomExactEqList]
  | cons head tail =>
      cases right with
      | nil => simp [atomExactEqList]
      | cons other rest =>
          intro equal
          simp only [atomExactEqList, Bool.and_eq_true] at equal
          rw [atomExactEq_sound head other equal.1,
            atomExactEqList_sound tail rest equal.2]
termination_by left _ => 2 * (left.map Atom.size).sum + 1
decreasing_by
  all_goals subst left
  all_goals simp only [List.map_cons, List.sum_cons]
  all_goals
    have hsize : 0 < head.size := by
      cases head <;> simp [Atom.size] <;> omega
    omega
end

mutual
theorem atomExactEq_self_of_key : ∀ atom key,
    atomExactKey atom = some key → atomExactEq atom atom = true := by
  intro atom key found
  cases atom with
  | sym name => simp [atomExactEq]
  | var name => simp [atomExactKey] at found
  | gnd ground =>
      cases ground <;> simp [atomExactKey, atomExactEq, groundExactEq] at found ⊢
  | expr atoms =>
      simp only [atomExactKey] at found
      cases listKey : atomExactKeyList atoms with
      | none => simp [listKey] at found
      | some listKeyValue =>
          exact atomExactEqList_self_of_key atoms listKeyValue listKey
termination_by atom _ _ => 2 * atom.size
decreasing_by
  all_goals simp_all [Atom.size] <;> omega

theorem atomExactEqList_self_of_key : ∀ atoms key,
    atomExactKeyList atoms = some key →
      atomExactEqList atoms atoms = true := by
  intro atoms key found
  cases atoms with
  | nil => simp [atomExactEqList]
  | cons atom rest =>
      simp only [atomExactKeyList] at found
      cases atomKey : atomExactKey atom with
      | none => simp [atomKey] at found
      | some head =>
          cases restKey : atomExactKeyList rest with
          | none => simp [atomKey, restKey] at found
          | some tail =>
              simp [atomExactEqList,
                atomExactEq_self_of_key atom head atomKey,
                atomExactEqList_self_of_key rest tail restKey]
termination_by atoms _ _ => 2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals subst atoms
  all_goals simp only [List.map_cons, List.sum_cons]
  all_goals
    have hsize : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega
end

mutual
/-- Exact-key availability certifies variable-freedom without a second tree
walk.  Floating-point atoms have no exact key and therefore stay on the
ordinary closedness path. -/
theorem atomExactKey_some_atomClosed : ∀ atom key,
    atomExactKey atom = some key → atomClosed atom = true := by
  intro atom key found
  cases atom with
  | sym name => simp [atomClosed]
  | var name => simp [atomExactKey] at found
  | gnd ground =>
      cases ground <;> simp [atomExactKey, atomClosed] at found ⊢
  | expr atoms =>
      simp only [atomExactKey] at found
      cases listKey : atomExactKeyList atoms with
      | none => simp [listKey] at found
      | some listKeyValue =>
          simpa [atomClosed] using
            atomExactKeyList_some_atomsClosed atoms listKeyValue listKey
termination_by atom _ _ => 2 * atom.size
decreasing_by
  all_goals simp_all [Atom.size] <;> omega

/-- List counterpart of `atomExactKey_some_atomClosed`. -/
theorem atomExactKeyList_some_atomsClosed : ∀ atoms key,
    atomExactKeyList atoms = some key → atomsClosed atoms = true := by
  intro atoms key found
  cases atoms with
  | nil => simp [atomsClosed]
  | cons atom rest =>
      simp only [atomExactKeyList] at found
      cases atomKey : atomExactKey atom with
      | none => simp [atomKey] at found
      | some head =>
          cases restKey : atomExactKeyList rest with
          | none => simp [atomKey, restKey] at found
          | some tail =>
              simp [atomsClosed,
                atomExactKey_some_atomClosed atom head atomKey,
                atomExactKeyList_some_atomsClosed rest tail restKey]
termination_by atoms _ _ => 2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals subst atoms
  all_goals simp only [List.map_cons, List.sum_cons]
  all_goals
    have hsize : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega
end

mutual
/-- Exact-key availability also gives the proof-facing variable-freedom
fact directly, avoiding a second traversal through `Atom.vars`. -/
theorem atomExactKey_some_vars_nil : ∀ atom key,
    atomExactKey atom = some key → atom.vars = [] := by
  intro atom key found
  cases atom with
  | sym name => simp [Atom.vars]
  | var name => simp [atomExactKey] at found
  | gnd ground => simp [Atom.vars]
  | expr atoms =>
      simp only [atomExactKey] at found
      cases listKey : atomExactKeyList atoms with
      | none => simp [listKey] at found
      | some listKeyValue =>
          simpa [Atom.vars] using
            atomExactKeyList_some_vars_nil atoms listKeyValue listKey
termination_by atom _ _ => 2 * atom.size
decreasing_by
  all_goals simp_all [Atom.size] <;> omega

/-- List counterpart of `atomExactKey_some_vars_nil`. -/
theorem atomExactKeyList_some_vars_nil : ∀ atoms key,
    atomExactKeyList atoms = some key →
      (atoms.map Atom.vars).flatten = [] := by
  intro atoms key found
  cases atoms with
  | nil => simp
  | cons atom rest =>
      simp only [atomExactKeyList] at found
      cases atomKey : atomExactKey atom with
      | none => simp [atomKey] at found
      | some head =>
          cases restKey : atomExactKeyList rest with
          | none => simp [atomKey, restKey] at found
          | some tail =>
              simp [atomExactKey_some_vars_nil atom head atomKey,
                atomExactKeyList_some_vars_nil rest tail restKey]
termination_by atoms _ _ => 2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals subst atoms
  all_goals simp only [List.map_cons, List.sum_cons]
  all_goals
    have hsize : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega
end

/-- `none` means that no exact-key result has been computed for this root;
`some none` is a computed negative result; `some (some key)` is a computed
exact key.  Expression summaries deliberately start unknown so creating a
prepared view never rescans an existing tree. -/
abbrev AtomExactCache := Option (Option AtomExactKey)

def atomExactCache : Atom → AtomExactCache
  | .expr _ => none
  | atom => some (atomExactKey atom)

theorem atomExactCache_sound (atom : Atom) :
    ∀ result, atomExactCache atom = some result →
      result = atomExactKey atom := by
  intro result found
  cases atom <;> simp [atomExactCache] at found ⊢
  all_goals exact found.symm

/-- Variable dependencies with a no-allocation path for closed terms. -/
def atomDependencies (atom : Atom) : List String :=
  if atomClosed atom then [] else atom.vars

/-- A raw atom paired with cached variable metadata and, for atoms assembled
    incrementally by substitution, prepared immediate children.  The cached
    `atom` remains the O(1) erasure; `Valid` below is the proof-facing
    denotation contract. -/
inductive PreparedAtom where
  | summary (atom : Atom) (variables : List String)
      (exact : AtomExactCache)
      (exactSound : ∀ result, exact = some result →
        result = atomExactKey atom)
  | expr (atom : Atom) (children : List PreparedAtom)
      (variables : List String) (exact : AtomExactCache)
      (exactSound : ∀ result, exact = some result →
        result = atomExactKey atom)

namespace PreparedAtom

def atom : PreparedAtom → Atom
  | .summary atom _ _ _ => atom
  | .expr atom _ _ _ _ => atom

def variables : PreparedAtom → List String
  | .summary _ variables _ _ => variables
  | .expr _ _ variables _ _ => variables

def children : PreparedAtom → List PreparedAtom
  | .summary _ _ _ _ => []
  | .expr _ children _ _ _ => children

def exact : PreparedAtom → AtomExactCache
  | .summary _ _ exact _ => exact
  | .expr _ _ _ exact _ => exact

theorem exact_sound (prepared : PreparedAtom) :
    ∀ result, prepared.exact = some result →
      result = atomExactKey prepared.atom := by
  cases prepared with
  | summary atom variables exact sound => exact sound
  | expr atom children variables exact sound => exact sound

/-- Read a cached exact-key result, computing it only when the prepared root
has no cached result. -/
def exactValue (prepared : PreparedAtom) : Option AtomExactKey :=
  match prepared.exact with
  | some result => result
  | none => atomExactKey prepared.atom

@[simp] theorem exactValue_eq (prepared : PreparedAtom) :
    prepared.exactValue = atomExactKey prepared.atom := by
  unfold exactValue
  cases found : prepared.exact with
  | none => rfl
  | some result => exact prepared.exact_sound result found

def ofAtom (atom : Atom) : PreparedAtom :=
  .summary atom atom.vars (atomExactCache atom) (atomExactCache_sound atom)

def ofClosed (atom : Atom) : PreparedAtom :=
  .summary atom [] (atomExactCache atom) (atomExactCache_sound atom)

def exactList : List PreparedAtom → AtomExactCache
  | [] => some (some 9)
  | prepared :: rest =>
      match prepared.exact with
      | none => none
      | some none => some none
      | some (some head) =>
          match exactList rest with
          | none => none
          | some none => some none
          | some (some tail) =>
              some (some (mixHash (mixHash 10 head) tail))

theorem exactList_sound : ∀ (children : List PreparedAtom) result,
    exactList children = some result →
      result = atomExactKeyList (children.map PreparedAtom.atom)
  | [], result, found => by
      simpa [exactList, atomExactKeyList] using found.symm
  | child :: rest, result, found => by
      cases childFound : child.exact with
      | none => simp [exactList, childFound] at found
      | some childResult =>
          cases childResult with
          | none =>
              simp [exactList, childFound] at found
              have childKey := child.exact_sound none childFound
              calc
                result = none := found.symm
                _ = atomExactKeyList ((child :: rest).map atom) := by
                  simp [atomExactKeyList, ← childKey]
          | some head =>
              cases restFound : exactList rest with
              | none => simp [exactList, childFound, restFound] at found
              | some restResult =>
                  have childKey := child.exact_sound (some head) childFound
                  have restKey := exactList_sound rest restResult restFound
                  cases restResult with
                  | none =>
                      simp [exactList, childFound, restFound] at found
                      calc
                        result = none := found.symm
                        _ = atomExactKeyList ((child :: rest).map atom) := by
                          simp [atomExactKeyList, ← childKey, ← restKey]
                  | some tail =>
                      simp [exactList, childFound, restFound] at found
                      calc
                        result = some (mixHash (mixHash 10 head) tail) :=
                          found.symm
                        _ = atomExactKeyList ((child :: rest).map atom) := by
                          simp [atomExactKeyList, ← childKey, ← restKey]

def exprExactCache (children : List PreparedAtom) : AtomExactCache :=
  (exactList children).map (Option.map fun keys => mixHash 8 keys)

theorem exprExactCache_sound (children : List PreparedAtom) :
    ∀ result, exprExactCache children = some result →
      result = atomExactKey (Atom.expr (children.map PreparedAtom.atom)) := by
  intro result found
  cases listFound : exactList children with
  | none => simp [exprExactCache, listFound] at found
  | some listResult =>
      have listKey := exactList_sound children listResult listFound
      simp [exprExactCache, listFound] at found
      subst result
      simp [atomExactKey, listKey]

def mkExpr (children : List PreparedAtom) : PreparedAtom :=
  .expr (Atom.expr (children.map PreparedAtom.atom)) children
    (children.flatMap PreparedAtom.variables)
    (exprExactCache children) (exprExactCache_sound children)

/-- Runtime pointer identity is only a shortcut for the ordinary structural
equality checked by the kernel definition of `withPtrEq`. -/
def sameAtom (prepared : PreparedAtom) (target : Atom) : Bool :=
  match cache : prepared.exact with
  | some (some key) =>
      withPtrEq prepared.atom target
        (fun _ => atomExactEq prepared.atom target) (by
          intro equal
          subst target
          exact atomExactEq_self_of_key prepared.atom key
            (prepared.exact_sound (some key) cache).symm)
  | _ => false

/-- A successful prepared comparison is ordinary structural equality.
Pointer identity only short-circuits this kernel-visible comparison at
runtime. -/
theorem sameAtom_eq_true {prepared : PreparedAtom} {target : Atom}
    (equal : prepared.sameAtom target = true) :
    prepared.atom = target := by
  unfold sameAtom at equal
  split at equal
  · exact atomExactEq_sound _ _ equal
  · contradiction

/-- Compare the immediate raw children of an existing expression with a
prepared child list.  Shared children take the pointer-fast path; the pure
meaning remains exact structural equality. -/
def sameAtoms : List PreparedAtom → List Atom → Bool
  | [], [] => true
  | prepared :: rest, atom :: atoms =>
      prepared.sameAtom atom && sameAtoms rest atoms
  | _, _ => false

theorem sameAtoms_eq_true : ∀ {children : List PreparedAtom}
    {atoms : List Atom}, sameAtoms children atoms = true →
      children.map PreparedAtom.atom = atoms
  | [], [], _ => rfl
  | prepared :: rest, atom :: atoms, equal => by
      simp only [sameAtoms, Bool.and_eq_true] at equal
      simp [sameAtom_eq_true equal.1, sameAtoms_eq_true equal.2]

/-- Build prepared expression metadata while retaining the existing raw root
when all immediate children are unchanged.  The explicit `root` argument is
load-bearing: rebuilding `Atom.expr atoms` would allocate a fresh wrapper and
destroy pointer sharing with the parent even though its children are shared. -/
def mkExprFromExpr (root : Atom) (atoms : List Atom)
    (root_eq : root = Atom.expr atoms) (children : List PreparedAtom) :
    PreparedAtom :=
  if equal : sameAtoms children atoms then
    .expr root children
      (children.flatMap PreparedAtom.variables)
      (exprExactCache children) (by
        intro result found
        rw [root_eq, ← sameAtoms_eq_true equal]
        exact exprExactCache_sound children result found)
  else
    mkExpr children

theorem mkExprFromExpr_eq_mkExpr (root : Atom) (atoms : List Atom)
    (root_eq : root = Atom.expr atoms) (children : List PreparedAtom) :
    mkExprFromExpr root atoms root_eq children = mkExpr children := by
  subst root
  unfold mkExprFromExpr
  split
  · rename_i equal
    have atomsEqual : atoms = children.map PreparedAtom.atom :=
      (sameAtoms_eq_true equal).symm
    subst atoms
    rfl
  · rfl

def mkExprFrom (root : Atom) (children : List PreparedAtom) : PreparedAtom :=
  match root_eq : root with
  | .expr atoms => mkExprFromExpr root atoms root_eq children
  | _ => ofAtom root

theorem mkExprFrom_eq_mkExpr (atoms : List Atom)
    (children : List PreparedAtom) :
    mkExprFrom (Atom.expr atoms) children = mkExpr children := by
  simp only [mkExprFrom]
  exact mkExprFromExpr_eq_mkExpr (Atom.expr atoms) atoms rfl children

/-- Recover metadata for a recently erased closed root.  Closedness makes the
cached atom stable under every later substitution; `sameAtom` makes pointer
identity an optimization rather than a semantic assumption. -/
def findRecentClosed (target : Atom) : List PreparedAtom → Option PreparedAtom
  | [] => none
  | prepared :: rest =>
      if prepared.variables.isEmpty && prepared.sameAtom target then
        some prepared
      else
        findRecentClosed target rest

/-- Retain the most recent prepared batch for the immediately following
machine operation.  Older batches are not searched linearly: expression
reconstruction preserves their raw structural sharing instead. -/
def refreshRecent (fresh _previous : List PreparedAtom) : List PreparedAtom :=
  fresh

inductive Valid : PreparedAtom → Prop where
  | summary (atom : Atom) :
      Valid (.summary atom atom.vars (atomExactCache atom)
        (atomExactCache_sound atom))
  | cached (atom : Atom) (variables : List String)
      (exact : AtomExactCache)
      (exactSound : ∀ result, exact = some result →
        result = atomExactKey atom)
      (variablesSound : variables = atom.vars) :
      Valid (.summary atom variables exact exactSound)
  | expr (children : List PreparedAtom)
      (valid : ∀ child ∈ children, Valid child) :
      Valid (mkExpr children)

abbrev PreparedSubst := List (String × PreparedAtom)

def PreparedSubst.Valid (entries : PreparedSubst) : Prop :=
  ∀ entry : String × PreparedAtom, entry ∈ entries → entry.2.Valid

def eraseSubst (entries : PreparedSubst) : Subst :=
  entries.map fun entry => (entry.1, entry.2.atom)

end PreparedAtom

/-- A closed atom whose exact key was already computed by the mutable-space
    index.  The proof fields are erased at runtime; they let the substitution
    engine reuse the raw root without rescanning it for variables. -/
structure ClosedRoot where
  atom : Atom
  key : AtomExactKey
  closed : atom.vars = []
  exact : atomExactKey atom = some key
  prepared : PreparedAtom
  prepared_valid : prepared.Valid
  prepared_atom : prepared.atom = atom

namespace ClosedRoot

/-- Pointer identity is the expected fast path.  Exact structural equality
    remains the kernel-visible fallback. -/
def sameAtom (root : ClosedRoot) (target : Atom) : Bool :=
  withPtrEq root.atom target
    (fun _ => atomExactEq root.atom target) (by
      intro equal
      subst target
      exact atomExactEq_self_of_key root.atom root.key root.exact)

theorem sameAtom_eq_true {root : ClosedRoot} {target : Atom}
    (equal : root.sameAtom target = true) : root.atom = target := by
  unfold sameAtom at equal
  exact atomExactEq_sound _ _ equal

end ClosedRoot

def findClosedRoot (target : Atom) : List ClosedRoot → Option ClosedRoot
  | [] => none
  | root :: rest =>
      if root.sameAtom target then some root else findClosedRoot target rest

/-- Package a valid prepared value as a reusable closed root whenever its
    cached exact key proves that it contains no variables. -/
def closedRootOfPrepared (prepared : PreparedAtom)
    (valid : prepared.Valid) : Option ClosedRoot :=
  match found : prepared.exact with
  | some (some key) =>
      let exact : atomExactKey prepared.atom = some key :=
        (prepared.exact_sound (some key) found).symm
      some
        { atom := prepared.atom
          key := key
          closed := atomExactKey_some_vars_nil prepared.atom key exact
          exact := exact
          prepared := prepared
          prepared_valid := valid
          prepared_atom := rfl }
  | _ => none

structure MemoEntry where
  value : Atom
  version : Nat
  prepared : Option { prepared : PreparedAtom //
    prepared.Valid ∧ prepared.atom = value } := none

def MemoEntry.ofPrepared (prepared : PreparedAtom)
    (valid : prepared.Valid) (version : Nat) : MemoEntry :=
  { value := prepared.atom
    version
    prepared := some ⟨prepared, valid, rfl⟩ }

abbrev MemoIndex := Std.TreeMap String MemoEntry
abbrev VarSet := Std.HashSet String
abbrev ForwardDependencyIndex := Std.HashMap String (List String)
abbrev ReverseDependencyIndex := Std.HashMap String VarSet
abbrev ClosedPreparedCache := Std.HashMap AtomExactKey ClosedRoot

/-- Cached facts retained as an exact proof/reference view of live variable
names. Resolution allocation itself uses the globally seeded counter. -/
structure FreshSummary where
  maxLength : Nat
  names : List String

def FreshSummary.empty : FreshSummary :=
  { maxLength := 0
    names := [] }

instance : Inhabited FreshSummary := ⟨FreshSummary.empty⟩

def FreshSummary.addName (summary : FreshSummary) (name : String) :
    FreshSummary :=
  { maxLength := max summary.maxLength name.length
    names := name :: summary.names }

def FreshSummary.addAtom (summary : FreshSummary) (atom : Atom) :
    FreshSummary :=
  atom.vars.foldl FreshSummary.addName summary

def FreshSummary.addBinding (summary : FreshSummary)
    (binding : String × Atom) : FreshSummary :=
  (summary.addName binding.1).addAtom binding.2

def bindingNames (entries : Subst) : List String :=
  entries.flatMap fun binding => binding.1 :: binding.2.vars

def FreshSummary.ofNames (names : List String) : FreshSummary :=
  names.foldl FreshSummary.addName FreshSummary.empty

def FreshSummary.ofSubst (entries : Subst) : FreshSummary :=
  FreshSummary.ofNames (bindingNames entries)

/-- Extend a persistent summary by a small set of newly introduced names. -/
def FreshSummary.merge (summary added : FreshSummary) : FreshSummary :=
  { maxLength := max summary.maxLength added.maxLength
    names := added.names ++ summary.names }

def FreshSummary.containsSuffix (summary : FreshSummary) (suffix : String) :
    Bool :=
  summary.names.any fun name => suffix.toList.isSuffixOf name.toList

def buildMemoIndex (entries : Subst) (version : Nat) : MemoIndex :=
  entries.foldl
    (fun index entry => index.insertIfNew entry.1
      { value := entry.2, version })
    Std.TreeMap.empty

/-- Erase bindings that just left the logical domain. Iterating the previous
active set makes trimming proportional to the bindings that were live, not to
the historical cache size. -/
def eraseInactiveEntries (entries : MemoIndex) (retained : VarSet) :
    List String → MemoIndex
  | [] => entries
  | name :: rest =>
      let next :=
        if retained.contains name then entries else entries.erase name
      eraseInactiveEntries next retained rest

def retainMemoEntries (entries : MemoIndex) (active retained : VarSet) :
    MemoIndex :=
  eraseInactiveEntries entries retained active.toList

/-- Versioned persistent substitution. `layers` are newest-first. A cached
entry records the eager lookup value at `entry.version`; reading it applies
only the layers added since then and refreshes that one path. -/
structure Memo where
  /-- Proof-facing denotation thunk. Composition and trimming extend this
  thunk in O(1). Lean's runtime memoizes `Thunk.get`, so an unavoidable
  denotation read materializes a shared history at most once. -/
  semantic : Thunk Subst
  base : Subst
  layers : List Subst
  version : Nat
  depth : Nat
  entries : MemoIndex

def Memo.ofList (entries : Subst) : Memo :=
  { semantic := .pure entries
    base := entries
    layers := []
    version := 0
    depth := entries.length
    entries := buildMemoIndex entries 0 }

def Memo.empty : Memo := Memo.ofList []

instance : Inhabited Memo := ⟨Memo.empty⟩

def Memo.advance (layers : List Subst) (count : Nat) (value : Atom) : Atom :=
  (layers.take count).foldr Metta.Subst.apply value

def Memo.denote (state : Memo) : Subst :=
  state.semantic.get

def Memo.peek (state : Memo) (name : String) : Option Atom :=
  state.entries[name]?.map fun entry =>
    Memo.advance state.layers (state.version - entry.version) entry.value

/-- Return cached prepared metadata only when it denotes the entry at the
current composition version.  Stale entries must first be advanced through
newer substitution layers, so their old prepared tree cannot be reused. -/
def Memo.currentPrepared (state : Memo) (name : String) :
    Option PreparedAtom :=
  match state.entries[name]? with
  | some entry =>
      if entry.version == state.version then
        entry.prepared.map Subtype.val
      else none
  | none => none

/-- Return retained prepared metadata without requiring the cache entry to
be stamped at the current composition version.  This view is used only after
`Scoped.cachedClosedPrepared` establishes that the retained atom is closed,
so every intervening substitution layer fixes it. -/
def Memo.cachedPrepared (state : Memo) (name : String) :
    Option PreparedAtom :=
  match state.entries[name]? with
  | some entry => entry.prepared.map Subtype.val
  | none => none

def Memo.compose (state : Memo) (generated : Subst) : Memo :=
  let nextVersion := state.version + 1
  { semantic := Thunk.mk fun _ => Metta.Subst.compose generated state.denote
    base := state.base
    layers := generated :: state.layers
    version := nextVersion
    depth := state.depth + generated.length
    entries := generated.foldl
      (fun index entry => index.insertIfNew entry.1
        { value := entry.2, version := nextVersion })
      state.entries }

/-- Refresh one cache path at the current version. This is persistent: other
branches retain the old map and every semantic field is unchanged. -/
def Memo.refresh (state : Memo) (name : String) (value : Atom) : Memo :=
  let refreshed : MemoEntry := { value := value, version := state.version }
  { state with entries := state.entries.insert name refreshed }

/-- A state-threaded lookup: advance only the queried cached value through
new composition layers, then stamp that path at the current version. -/
def Memo.lookup (state : Memo) (name : String) : Option Atom × Memo :=
  match state.peek name with
  | none => (none, state)
  | some value => (some value, state.refresh name value)

/-- Deep substitution with a persistent, state-threaded lookup cache. The
fuel and atom recursion are identical to PLeaTTa's list reference; only
variable lookup is memoized. -/
def Memo.substN : Nat → Atom → StateM Memo Atom
  | 0, atom => pure atom
  | fuel + 1, Atom.var name => do
      let state ← get
      let result := state.lookup name
      set result.2
      match result.1 with
      | some value => Memo.substN fuel value
      | none => pure (Atom.var name)
  | fuel + 1, Atom.expr atoms => do
      return Atom.expr (← atoms.mapM (Memo.substN (fuel + 1)))
  | _ + 1, atom => pure atom

def Memo.subst (state : Memo) (atom : Atom) : Atom × Memo :=
  Id.run ((Memo.substN (state.depth + 1) atom).run state)

/-- Unification over the persistent representation. Cache refreshes from
substituting the two inputs are retained, while a nonempty unifier is added
as one shared composition layer. -/
def Memo.unifyB (state : Memo) (left right : Atom) : Option Memo :=
  let leftResult := state.subst left
  let rightResult := leftResult.2.subst right
  match Metta.Unify.unifyTop leftResult.1 rightResult.1 with
  | none => none
  | some [] => some rightResult.2
  | some generated => some (rightResult.2.compose generated)

def addFreshAtomVars (state : VarSet × VarSet) : Atom → VarSet × VarSet
  | .var name =>
      if state.1.contains name then state
      else (state.1.insert name, state.2.insert name)
  | .expr atoms => atoms.foldl addFreshAtomVars state
  | _ => state

/-- Exact first-lookup dependency relation for the eager list denotation.
`forward[source]` is the set of variables in that source's current target;
`reverse[dependency]` is the set of sources containing that variable. -/
structure DependencyGraph where
  forward : ForwardDependencyIndex
  reverse : ReverseDependencyIndex

def DependencyGraph.empty : DependencyGraph :=
  { forward := Std.HashMap.emptyWithCapacity
    reverse := Std.HashMap.emptyWithCapacity }

instance : Inhabited DependencyGraph := ⟨DependencyGraph.empty⟩

def DependencyGraph.reverseContains (graph : DependencyGraph)
    (dependency source : String) : Bool :=
  match graph.reverse[dependency]? with
  | none => false
  | some users => users.contains source

/-- Constant-time closed-range query for a bound source.  Coherence relates
this cached empty dependency list to the source value's exact variables. -/
def DependencyGraph.targetClosed (graph : DependencyGraph)
    (source : String) : Bool :=
  match graph.forward[source]? with
  | some [] => true
  | _ => false

def DependencyGraph.addReverse (reverse : ReverseDependencyIndex)
    (dependency source : String) : ReverseDependencyIndex :=
  let users := reverse[dependency]?.getD
    (Std.HashSet.emptyWithCapacity 1)
  reverse.insert dependency (users.insert source)

def DependencyGraph.removeReverse (reverse : ReverseDependencyIndex)
    (dependency source : String) : ReverseDependencyIndex :=
  match reverse[dependency]? with
  | none => reverse
  | some users =>
      let remaining := users.erase source
      if remaining.size == 0 then reverse.erase dependency
      else reverse.insert dependency remaining

def DependencyGraph.bindSource (graph : DependencyGraph)
    (source : String) (dependencies : List String) : DependencyGraph :=
  { forward := graph.forward.insert source dependencies
    reverse := dependencies.foldl
      (fun reverse dependency =>
        DependencyGraph.addReverse reverse dependency source)
      graph.reverse }

def DependencyGraph.unbindSource (graph : DependencyGraph)
    (source : String) : DependencyGraph :=
  match graph.forward[source]? with
  | none => graph
  | some dependencies =>
      { forward := graph.forward.erase source
        reverse := dependencies.foldl
          (fun reverse dependency =>
            DependencyGraph.removeReverse reverse dependency source)
          graph.reverse }

def DependencyGraph.replaceSource (graph : DependencyGraph)
    (source : String) (dependencies : List String) : DependencyGraph :=
  (graph.unbindSource source).bindSource source dependencies

def DependencyGraph.ofList : Subst → DependencyGraph
  | [] => DependencyGraph.empty
  | (source, value) :: rest =>
      (DependencyGraph.ofList rest).replaceSource source
        (atomDependencies value)

def transformDependencies (generated : Subst)
    (dependencies : List String) : List String :=
  dependencies.flatMap
    (fun dependency =>
      match Metta.Subst.lookup generated dependency with
      | none => [dependency]
      | some value => atomDependencies value)

def PreparedAtom.lookup : PreparedAtom.PreparedSubst → String →
    Option PreparedAtom
  | [], _ => none
  | binding :: rest, source =>
      if source == binding.1 then some binding.2
      else PreparedAtom.lookup rest source

/-- Dependency transformation using summaries already assembled by
substitution.  No target atom is traversed. -/
def transformDependenciesPrepared (generated : PreparedAtom.PreparedSubst)
    (dependencies : List String) : List String :=
  dependencies.flatMap fun dependency =>
    match PreparedAtom.lookup generated dependency with
    | none => [dependency]
    | some value => value.variables

def dependenciesTouched (generated : Subst)
    (dependencies : List String) : Bool :=
  generated.any fun binding => dependencies.contains binding.1

def insertAll (target source : VarSet) : VarSet :=
  source.toList.foldl (fun names name => names.insert name) target

def DependencyGraph.affectedSources (graph : DependencyGraph) :
    Subst → VarSet
  | [] => Std.HashSet.emptyWithCapacity
  | binding :: rest =>
      let affected := graph.affectedSources rest
      match graph.reverse[binding.1]? with
      | none => affected
      | some users => insertAll affected users

def DependencyGraph.transformSources (generated : Subst) :
    DependencyGraph → List String → DependencyGraph
  | graph, [] => graph
  | graph, source :: rest =>
      let next :=
        match graph.forward[source]? with
        | none => graph
        | some dependencies =>
            graph.replaceSource source
              (transformDependencies generated dependencies)
      next.transformSources generated rest

def DependencyGraph.transformSourcesPrepared
    (generated : PreparedAtom.PreparedSubst) :
    DependencyGraph → List String → DependencyGraph
  | graph, [] => graph
  | graph, source :: rest =>
      let next :=
        match graph.forward[source]? with
        | none => graph
        | some dependencies =>
            graph.replaceSource source
              (transformDependenciesPrepared generated dependencies)
      next.transformSourcesPrepared generated rest

def DependencyGraph.addGenerated : DependencyGraph → Subst → DependencyGraph
  | graph, [] => graph
  | graph, binding :: rest =>
      let next :=
        if graph.forward.contains binding.1 then graph
        else graph.bindSource binding.1 (atomDependencies binding.2)
      next.addGenerated rest

def DependencyGraph.addGeneratedPrepared :
    DependencyGraph → PreparedAtom.PreparedSubst → DependencyGraph
  | graph, [] => graph
  | graph, binding :: rest =>
      let next :=
        if graph.forward.contains binding.1 then graph
        else graph.bindSource binding.1 binding.2.variables
      next.addGeneratedPrepared rest

/-- Incrementally realize the dependency relation of eager composition.
Only old targets mentioning a generated key can change; all other graph
nodes remain physically shared. -/
def DependencyGraph.compose (graph : DependencyGraph)
    (generated : Subst) : DependencyGraph :=
  let affected := graph.affectedSources generated
  let updated := graph.transformSources generated affected.toList
  updated.addGenerated generated

/-- Incremental eager-composition metadata update.  Prepared target
summaries replace all whole-atom dependency scans. -/
def DependencyGraph.composePrepared (graph : DependencyGraph)
    (generated : PreparedAtom.PreparedSubst) : DependencyGraph :=
  let erased := PreparedAtom.eraseSubst generated
  let affected := graph.affectedSources erased
  let updated := graph.transformSourcesPrepared generated affected.toList
  updated.addGeneratedPrepared generated

def DependencyGraph.retainList (retained : VarSet) :
    DependencyGraph → List String → DependencyGraph
  | graph, [] => graph
  | graph, source :: rest =>
      let next :=
        if retained.contains source then graph
        else graph.unbindSource source
      next.retainList retained rest

def DependencyGraph.retainSources (graph : DependencyGraph)
    (active retained : VarSet) : DependencyGraph :=
  graph.retainList retained active.toList

structure CandidateClosure where
  live : VarSet
  frontier : VarSet

def splitDirectCandidates (active roots : VarSet) : VarSet × VarSet :=
  active.toList.foldl
    (fun split source =>
      if roots.contains source then (split.1.insert source, split.2)
      else (split.1, split.2.insert source))
    (Std.HashSet.emptyWithCapacity active.size,
      Std.HashSet.emptyWithCapacity 4)

def DependencyGraph.seedCandidates (graph : DependencyGraph)
    (direct candidates : VarSet) : VarSet :=
  candidates.toList.foldl
    (fun live candidate =>
      match graph.reverse[candidate]? with
      | none => live
      | some users =>
          if users.toList.any direct.contains then live.insert candidate
          else live)
    (Std.HashSet.emptyWithCapacity candidates.size)

def DependencyGraph.candidateStep (graph : DependencyGraph)
    (candidates : VarSet) (state : CandidateClosure)
    (source : String) : CandidateClosure :=
  match graph.forward[source]? with
  | none => state
  | some dependencies =>
      dependencies.foldl
        (fun current dependency =>
          if candidates.contains dependency &&
              !(current.live.contains dependency) then
            { live := current.live.insert dependency
              frontier := current.frontier.insert dependency }
          else current)
        state

def DependencyGraph.closeCandidates (graph : DependencyGraph)
    (candidates : VarSet) : Nat → CandidateClosure → CandidateClosure
  | 0, state => state
  | fuel + 1, state =>
      if state.frontier.size == 0 then state
      else
        let next := state.frontier.toList.foldl
          (graph.candidateStep candidates)
          { state with
            frontier := Std.HashSet.emptyWithCapacity state.frontier.size }
        graph.closeCandidates candidates fuel next

/-- Reachability restricted to the complement of direct bound roots. Every
direct bound root is live; reverse edges seed the usually tiny candidate
set, and forward edges propagate only within that complement. -/
def DependencyGraph.retainedFromRoots (graph : DependencyGraph)
    (active roots : VarSet) : VarSet :=
  let split := splitDirectCandidates active roots
  let seeded := graph.seedCandidates split.1 split.2
  let closed := graph.closeCandidates split.2 (split.2.size + 1)
    { live := seeded, frontier := seeded }
  closed.live.toList.foldl (fun live name => live.insert name) split.1

def DependencyGraph.namesForList (graph : DependencyGraph) :
    List String → List String
  | [] => []
  | source :: rest =>
      source :: graph.forward[source]?.getD [] ++ graph.namesForList rest

def DependencyGraph.namesFor (graph : DependencyGraph)
    (retained : VarSet) : List String :=
  graph.namesForList retained.toList

def DependencyGraph.freshFor (graph : DependencyGraph)
    (retained : VarSet) : FreshSummary :=
  FreshSummary.ofNames (graph.namesFor retained)

def varSetEquivalent (left right : VarSet) : Bool :=
  left.size == right.size && left.toList.all right.contains

def addFreshName (state : VarSet × VarSet) (name : String) :
    VarSet × VarSet :=
  if state.1.contains name then state
  else (state.1.insert name, state.2.insert name)

def addFreshNames (state : VarSet × VarSet) (names : List String) :
    VarSet × VarSet :=
  names.foldl addFreshName state

structure DependencyClosure where
  live : VarSet
  frontier : VarSet

def DependencyGraph.closureStep (graph : DependencyGraph)
    (state : DependencyClosure) (source : String) : DependencyClosure :=
  match graph.forward[source]? with
  | none => state
  | some dependencies =>
      let discovered := addFreshNames (state.live, state.frontier) dependencies
      { live := discovered.1, frontier := discovered.2 }

def DependencyGraph.close : DependencyGraph → Nat →
    DependencyClosure → DependencyClosure
  | _, 0, state => state
  | graph, fuel + 1, state =>
      if state.frontier.size == 0 then state
      else
        let next := state.frontier.toList.foldl graph.closureStep
          { state with
            frontier := Std.HashSet.emptyWithCapacity state.frontier.size }
        graph.close fuel next

/-- A logical liveness view over a persistent memo. Inactive cache entries
remain physically shared but are invisible to lookup and may be overwritten
if a later scope reuses their name. -/
structure Scoped where
  memo : Memo
  active : VarSet
  /-- Variables whose identities remain live at alpha-copy boundaries.
  This includes unbound dependencies, unlike `active`, which is the exact
  bound lookup domain. -/
  visible : VarSet
  dependencies : DependencyGraph
  /-- Prepared roots most recently erased by a batch substitution.  The
  executable reuses only closed entries whose atoms match structurally. -/
  recent : List PreparedAtom := []
  /-- Closed roots supplied by a space index for the next equality step.
  Each entry intrinsically carries the facts needed for O(1) reuse. -/
  closedRoots : List ClosedRoot := []
  /-- The most recently inserted closed prepared value.  Exact-key lookup
  narrows the candidate; atom identity/equality rejects hash collisions.
  Keeping this cache bounded prevents persistent search branches from
  retaining an ever-growing copy-on-write hash table. -/
  closedPrepared : ClosedPreparedCache := Std.HashMap.emptyWithCapacity

def activeOfList (entries : Subst) : VarSet :=
  entries.foldl (fun active entry => active.insert entry.1)
    (Std.HashSet.emptyWithCapacity entries.length)

def addVisibleAtom (visible : VarSet) (atom : Atom) : VarSet :=
  if atomClosed atom then visible
  else
    (addFreshAtomVars
      (visible, Std.HashSet.emptyWithCapacity atom.vars.length) atom).1

def addVisibleBinding (visible : VarSet) (binding : String × Atom) : VarSet :=
  addVisibleAtom (visible.insert binding.1) binding.2

def addVisiblePreparedBinding (visible : VarSet)
    (binding : String × PreparedAtom) : VarSet :=
  (addFreshNames
    (visible.insert binding.1,
      Std.HashSet.emptyWithCapacity binding.2.variables.length)
    binding.2.variables).1

def visibleOfList (entries : Subst) : VarSet :=
  entries.foldl addVisibleBinding
    (Std.HashSet.emptyWithCapacity (entries.length * 2))

def Scoped.ofList (entries : Subst) : Scoped :=
  { memo := Memo.ofList entries
    active := activeOfList entries
    visible := visibleOfList entries
    dependencies := DependencyGraph.ofList entries
    recent := []
    closedRoots := []
    closedPrepared := Std.HashMap.emptyWithCapacity }

def Scoped.empty : Scoped := Scoped.ofList []

instance : Inhabited Scoped := ⟨Scoped.empty⟩

def Scoped.denote (state : Scoped) : Subst := state.memo.denote

def Scoped.peek (state : Scoped) (name : String) : Option Atom :=
  if state.active.contains name then state.memo.peek name else none

def Scoped.lookup (state : Scoped) (name : String) : Option Atom × Scoped :=
  if state.active.contains name then
    let result := state.memo.lookup name
    (result.1, { state with memo := result.2 })
  else (none, state)

/-- Reuse a retained prepared tree across later composition versions exactly
when both the dependency graph and the retained metadata certify that its
target is closed.  The active-domain check prevents stale entries left by
scope trimming from becoming visible again. -/
def Scoped.cachedClosedPrepared (state : Scoped) (name : String) :
    Option PreparedAtom :=
  if state.active.contains name then
    match state.memo.cachedPrepared name with
    | some prepared =>
        if prepared.variables.isEmpty then some prepared else none
    | none => none
  else none

/-- Retain one certified prepared tree for the immediately following machine
operation without changing substitution denotation.  This transient path is
constant-time even when the prepared tree is large. -/
def Scoped.rememberRecent (state : Scoped) (prepared : PreparedAtom)
    (_valid : prepared.Valid) : Scoped :=
  { state with recent := [prepared] }

/-- Retain one certified prepared tree at a durable insertion boundary.
The most recent exact closed value is additionally installed in a bounded
cache so a following space lookup can recover the same prepared metadata. -/
def Scoped.rememberPrepared (state : Scoped) (prepared : PreparedAtom)
    (valid : prepared.Valid) : Scoped :=
  let remembered := state.rememberRecent prepared valid
  match closedRootOfPrepared prepared valid with
  | none => remembered
  | some root =>
      { remembered with
        closedPrepared :=
          (Std.HashMap.emptyWithCapacity : ClosedPreparedCache).insert
            root.key root }

/-- Select the structurally shared root retained when an atom entered a
    mutable space.  A key collision falls back to the intrinsically valid
    root supplied by the space index. -/
def Scoped.selectClosedRoot (state : Scoped) (root : ClosedRoot) : Scoped :=
  let selected :=
    match state.closedPrepared[root.key]? with
    | some cached => if cached.sameAtom root.atom then cached else root
    | none => root
  { state with closedRoots := [selected] }

def Scoped.bindingsFor (state : Scoped) (active : VarSet) : Subst :=
  active.toList.filterMap fun name =>
    (state.peek name).map fun value => (name, value)

def Scoped.freshFor (state : Scoped) (active : VarSet) : FreshSummary :=
  FreshSummary.ofNames (bindingNames (state.bindingsFor active))

def extendGenerated (entries : MemoIndex) (active : VarSet)
    (version : Nat) (generated : Subst) : MemoIndex × VarSet :=
  generated.foldl
    (fun current entry =>
      let cached : MemoEntry :=
        { value := entry.2, version }
      let entries :=
        if current.2.contains entry.1 then
          current.1.insertIfNew entry.1 cached
        else current.1.insert entry.1 cached
      (entries, current.2.insert entry.1))
    (entries, active)

/-- Prepared counterpart of `extendGenerated`.  The raw value and version are
identical; a newly visible binding additionally retains its proved prepared
tree so later closed substitutions can reuse structural metadata in O(1). -/
def extendGeneratedPrepared (entries : MemoIndex) (active : VarSet)
    (version : Nat) :
    (generated : PreparedAtom.PreparedSubst) → generated.Valid →
      MemoIndex × VarSet
  | [], _ => (entries, active)
  | binding :: rest, valid =>
      let targetValid : binding.2.Valid := valid binding (by simp)
      let restValid : PreparedAtom.PreparedSubst.Valid rest :=
        fun entry member =>
        valid entry (by simp [member])
      let cached := MemoEntry.ofPrepared binding.2 targetValid version
      let nextEntries :=
        if active.contains binding.1 then
          entries.insertIfNew binding.1 cached
        else entries.insert binding.1 cached
      extendGeneratedPrepared nextEntries (active.insert binding.1)
        version rest restValid

/-- Add one generated unifier layer. Active old bindings retain first-lookup
priority; a key absent from the current logical domain overwrites any stale
cache entry left by an earlier trim. -/
def Scoped.compose (state : Scoped) (generated : Subst) : Scoped :=
  let nextVersion := state.memo.version + 1
  let extended := extendGenerated state.memo.entries state.active
    nextVersion generated
  { memo :=
      { semantic := Thunk.mk fun _ =>
          Metta.Subst.compose generated state.memo.denote
        base := state.memo.base
        layers := generated :: state.memo.layers
        version := nextVersion
        depth := state.memo.depth + generated.length
        entries := extended.1 }
    active := extended.2
    visible := generated.foldl addVisibleBinding state.visible
    dependencies := state.dependencies.compose generated
    recent := state.recent
    closedRoots := state.closedRoots
    closedPrepared := state.closedPrepared }

/-- Compose a prepared unifier without rediscovering target variables.
The proof-facing denotation remains the unchanged raw eager composition. -/
def Scoped.composePrepared (state : Scoped)
    (generated : PreparedAtom.PreparedSubst) (valid : generated.Valid) :
    Scoped :=
  let erased := PreparedAtom.eraseSubst generated
  let nextVersion := state.memo.version + 1
  let extended := extendGeneratedPrepared state.memo.entries state.active
    nextVersion generated valid
  { memo :=
      { semantic := Thunk.mk fun _ =>
          Metta.Subst.compose erased state.memo.denote
        base := state.memo.base
        layers := erased :: state.memo.layers
        version := nextVersion
        depth := state.memo.depth + erased.length
        entries := extended.1 }
    active := extended.2
    visible := generated.foldl addVisiblePreparedBinding state.visible
    dependencies := state.dependencies.composePrepared generated
    recent := state.recent
    closedRoots := state.closedRoots
    closedPrepared := state.closedPrepared }

def Scoped.substN : Nat → Atom → StateM Scoped Atom
  | 0, atom => pure atom
  | fuel + 1, Atom.var name => do
      let state ← get
      match state.cachedClosedPrepared name with
      | some prepared => pure prepared.atom
      | none =>
          let result := state.lookup name
          set result.2
          match result.1 with
          | some value =>
              if result.2.dependencies.targetClosed name then pure value
              else if atomClosed value then pure value
              else Scoped.substN fuel value
          | none => pure (Atom.var name)
  | fuel + 1, Atom.expr atoms => do
      return Atom.expr (← atoms.mapM (Scoped.substN (fuel + 1)))
  | _ + 1, atom => pure atom

/-- Avoid rebuilding a variable-free root.  This check is performed once per
machine substitution request, rather than recursively at every expression
node. -/
def Scoped.substRootN (fuel : Nat) (atom : Atom) : StateM Scoped Atom :=
  if atomClosed atom then pure atom else Scoped.substN fuel atom

def Scoped.subst (state : Scoped) (atom : Atom) : Atom × Scoped :=
  if state.memo.depth == 0 then (atom, state)
  else Id.run ((Scoped.substRootN (state.memo.depth + 1) atom).run state)

/-- Prepared substitution follows the same lookup order as `substN`, but it
    builds expression metadata from prepared children.  A graph-certified
    closed lookup is wrapped in O(1), so a large shared target is not walked
    merely to rediscover that it has no variables. -/
def Scoped.substPreparedN : Nat → Atom → StateM Scoped PreparedAtom
  | 0, atom => pure (PreparedAtom.ofAtom atom)
  | fuel + 1, Atom.var name => do
      let state ← get
      match state.cachedClosedPrepared name with
      | some prepared => pure prepared
      | none =>
          let result := state.lookup name
          set result.2
          match result.1 with
          | some value =>
              if result.2.dependencies.targetClosed name then
                pure (PreparedAtom.ofClosed value)
              else
                Scoped.substPreparedN fuel value
          | none => pure (PreparedAtom.ofAtom (Atom.var name))
  | fuel + 1, atom@(.expr atoms) => do
      return PreparedAtom.mkExprFrom atom
        (← atoms.mapM (Scoped.substPreparedN (fuel + 1)))
  | _ + 1, atom => pure (PreparedAtom.ofAtom atom)

def Scoped.substPrepared (state : Scoped) (atom : Atom) :
    PreparedAtom × Scoped :=
  match findClosedRoot atom state.closedRoots with
  | some root => (root.prepared, state)
  | none =>
      match PreparedAtom.findRecentClosed atom state.recent with
      | some prepared => (prepared, state)
      | none =>
          if state.memo.depth == 0 then (PreparedAtom.ofAtom atom, state)
          else
            Id.run ((Scoped.substPreparedN (state.memo.depth + 1) atom).run state)

/-- State-monad view of `substPrepared`.  Batch substitution uses this entry
point so roots prepared by the preceding machine operation remain reusable;
descending directly through `substPreparedN` would bypass both the transient
closed-root cache and indexed closed roots. -/
def Scoped.substPreparedRoot (atom : Atom) : StateM Scoped PreparedAtom :=
  fun state => state.substPrepared atom

/-- Exact key of an already prepared value.  Prefer the prepared cache so a
    child inherited from indexed expression metadata does not compare itself
    against an unrelated whole-root cache.  A transient indexed closed root
    remains the fallback before an ordinary structural-key computation. -/
def Scoped.preparedExactKey (state : Scoped) (prepared : PreparedAtom) :
    Option AtomExactKey :=
  match prepared.exact with
  | some result => result
  | none =>
      match findClosedRoot prepared.atom state.closedRoots with
      | some root => some root.key
      | none => prepared.exactValue

def Scoped.substManyPrepared (state : Scoped) (atoms : List Atom) :
    List PreparedAtom × Scoped :=
  let result :=
    if state.memo.depth == 0 then
      (atoms.map PreparedAtom.ofAtom, state)
    else
      Id.run ((atoms.mapM Scoped.substPreparedRoot).run state)
  (result.1, { result.2 with
    recent := PreparedAtom.refreshRecent result.1 result.2.recent })

/-- Batch substitution erases the prepared roots in O(1) while retaining
their certified metadata in the resulting scoped state. -/
def Scoped.substMany (state : Scoped) (atoms : List Atom) : List Atom × Scoped :=
  let result := state.substManyPrepared atoms
  (result.1.map PreparedAtom.atom, result.2)

def Scoped.unifyB (state : Scoped) (left right : Atom) : Option Scoped :=
  let leftResult := state.subst left
  let rightResult := leftResult.2.subst right
  match Metta.Unify.unifyTop leftResult.1 rightResult.1 with
  | none => none
  | some [] => some rightResult.2
  | some generated => some (rightResult.2.compose generated)

structure ClosureState where
  subst : Scoped
  live : VarSet
  frontier : VarSet

def closureStep (state : ClosureState) (name : String) : ClosureState :=
  let result := state.subst.lookup name
  match result.1 with
  | none => { state with subst := result.2 }
  | some value =>
      let discovered := addFreshAtomVars (state.live, state.frontier) value
      { subst := result.2
        live := discovered.1
        frontier := discovered.2 }

def closeScoped : Nat → ClosureState → ClosureState
  | 0, state => state
  | fuel + 1, state =>
      if state.frontier.size == 0 then state
      else
        let next := state.frontier.toList.foldl closureStep
          { state with
            frontier := Std.HashSet.emptyWithCapacity state.frontier.size }
        closeScoped fuel next

/-- Cheap sufficient condition for exact no-op trimming: every current
logical binding is a direct root, and the logical domain has no duplicate
list entries. -/
def Scoped.trimIsIdentity (state : Scoped) (roots : VarSet) : Bool :=
  state.active.size == state.memo.depth &&
    state.active.toList.all roots.contains

/-- Full exact liveness closure used when the identity guard does not apply. -/
def Scoped.trimWithSlow (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) : Scoped :=
  let closed := closeScoped (state.memo.depth + 1)
    { subst := state, live := roots, frontier := roots }
  let retained := closed.subst.active.filter closed.live.contains
  { memo :=
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
    closedPrepared := state.closedPrepared }

/-- Exact graph-backed liveness closure. Unlike `trimWithSlow`, this never
reconstructs target atoms or refreshes substitution cache paths merely to
read their variable dependencies. -/
def Scoped.trimWithGraph (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) : Scoped :=
  let closed := state.dependencies.close (state.memo.depth + 1)
    { live := roots, frontier := roots }
  let retained := state.active.filter closed.live.contains
  { memo :=
      { state.memo with
        semantic := Thunk.mk fun _ => referenceTrim state.denote
        depth := retained.size
        entries := retainMemoEntries state.memo.entries
          state.active retained }
    active := retained
    visible := closed.live
    dependencies := state.dependencies.retainSources state.active retained
    recent := state.recent
    closedRoots := state.closedRoots
    closedPrepared := state.closedPrepared }

/-- Logical trimming without rebuilding the substitution map. `referenceTrim`
is captured in the proof-facing denotation thunk and is never forced by the
executable lookup path. -/
def Scoped.trimWith (state : Scoped) (roots : VarSet)
    (referenceTrim : Subst → Subst) : Scoped :=
  if state.trimIsIdentity roots then
    { state with
      memo :=
        { state.memo with
          semantic := Thunk.mk fun _ => referenceTrim state.denote } }
  else
    state.trimWithGraph roots referenceTrim

end PLeaTTa.PersistentSubst
