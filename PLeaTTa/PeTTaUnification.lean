import PLeaTTa.Types
import PLeaTTa.PrologFloat
import MettaHyperonFull.Core.Unification

namespace PLeaTTa

open Metta (Atom Subst)

def substN : Nat → Subst → Atom → Atom
  | 0, _, atom => atom
  | fuel + 1, binding, .var name =>
      match Metta.Subst.lookup binding name with
      | some atom => substN fuel binding atom
      | none => .var name
  | fuel + 1, binding, .expr atoms =>
      .expr (atoms.map (substN (fuel + 1) binding))
  | _ + 1, _, atom => atom

/-- Deep substitution (to fixpoint): one-step `apply` leaves stale reads when
a single unifier contains internal variable chains; iterating to the fixpoint
(bounded by the substitution's length) resolves every chain. -/
def subst (binding : Subst) (atom : Atom) : Atom :=
  substN (binding.length + 1) binding atom

/- Candidate compatibility at the PeTTa boundary.  The shared Hyperon
unifier deliberately identifies integer and floating-point grounds by numeric
value, while SWI-Prolog keeps those term constructors distinct.  This filter
is applied only after the shared unifier succeeds, so it checks exactly that
extra distinction without repeating host-ground equality (which need not be
reflexive for values such as NaN). -/
mutual
def pettaUnifyCompatible : Atom → Atom → Bool
  | .sym _, .sym _ => true
  | .var _, .var _ => true
  | .gnd (.int _), .gnd (.float _) => false
  | .gnd (.float _), .gnd (.int _) => false
  | .gnd _, .gnd _ => true
  | .expr left, .expr right => pettaUnifyCompatibleList left right
  | _, _ => false

def pettaUnifyCompatibleList : List Atom → List Atom → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      pettaUnifyCompatible left right &&
        pettaUnifyCompatibleList leftRest rightRest
  | _, _ => false
end

mutual

/-- Conservative clause-indexing discriminator for the PeTTa/Prolog
dialect.  Variables remain wildcards, while every ground-ground comparison
uses exact Prolog term identity.  `false` therefore means that Prolog
unification is structurally impossible; in particular, equal NaN terms are
not discarded before the resolver can unify them. -/
def prologMatchCompat : Atom → Atom → Bool
  | .var _, _ => true
  | _, .var _ => true
  | .sym left, .sym right => left == right
  | .gnd left, .gnd right => prologGroundIdentical left right
  | .expr left, .expr right => prologMatchCompatList left right
  | _, _ => false

/-- List counterpart of `prologMatchCompat`. -/
def prologMatchCompatList : List Atom → List Atom → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      prologMatchCompat left right &&
        prologMatchCompatList leftRest rightRest
  | _, _ => false

end

mutual

  /-- Structural runtime-term equivalence parameterized only at grounded
  leaves.  Symbols and variable names remain exact, expression children
  remain ordered, and the ground comparator is the sole non-propositional
  seam.  This is the relation that comparator-parametric unification actually
  decides; plain `Atom` equality is too strong for identities such as
  distinct IEEE NaN payloads that SWI-Prolog treats as one term. -/
  inductive AtomEquivalentWith
      (groundEq : Metta.Ground → Metta.Ground → Bool) :
      Atom → Atom → Prop where
    | symbol (name : String) :
        AtomEquivalentWith groundEq (.sym name) (.sym name)
    | variable (name : String) :
        AtomEquivalentWith groundEq (.var name) (.var name)
    | ground {left right : Metta.Ground}
        (identical : groundEq left right = true) :
        AtomEquivalentWith groundEq (.gnd left) (.gnd right)
    | expression {left right : List Atom}
        (children : AtomsEquivalentWith groundEq left right) :
        AtomEquivalentWith groundEq (.expr left) (.expr right)

  /-- Ordered-list counterpart of `AtomEquivalentWith`. -/
  inductive AtomsEquivalentWith
      (groundEq : Metta.Ground → Metta.Ground → Bool) :
      List Atom → List Atom → Prop where
    | nil : AtomsEquivalentWith groundEq [] []
    | cons {leftHead rightHead : Atom} {leftTail rightTail : List Atom}
        (head : AtomEquivalentWith groundEq leftHead rightHead)
        (tail : AtomsEquivalentWith groundEq leftTail rightTail) :
        AtomsEquivalentWith groundEq
          (leftHead :: leftTail) (rightHead :: rightTail)

end

mutual

  /-- A reflexive ground comparator induces reflexive structural term
  equivalence. -/
  theorem AtomEquivalentWith.refl
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundReflexive : ∀ ground, groundEq ground ground = true) :
      ∀ atom, AtomEquivalentWith groundEq atom atom
    | .sym name => .symbol name
    | .var name => .variable name
    | .gnd ground => .ground (groundReflexive ground)
    | .expr atoms => .expression
        (AtomsEquivalentWith.refl groundReflexive atoms)

  /-- Ordered-list reflexivity. -/
  theorem AtomsEquivalentWith.refl
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundReflexive : ∀ ground, groundEq ground ground = true) :
      ∀ atoms, AtomsEquivalentWith groundEq atoms atoms
    | [] => .nil
    | atom :: atoms => .cons
        (AtomEquivalentWith.refl groundReflexive atom)
        (AtomsEquivalentWith.refl groundReflexive atoms)

end

mutual

  /-- Symmetry lifts structurally from grounded leaves to complete terms. -/
  theorem AtomEquivalentWith.symm
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundSymmetric :
        ∀ {left right : Metta.Ground}, groundEq left right = true →
          groundEq right left = true) :
      ∀ {left right}, AtomEquivalentWith groundEq left right →
        AtomEquivalentWith groundEq right left
    | _, _, .symbol name => .symbol name
    | _, _, .variable name => .variable name
    | _, _, .ground identical => .ground (groundSymmetric identical)
    | _, _, .expression children => .expression
        (AtomsEquivalentWith.symm (groundEq := groundEq)
          groundSymmetric children)

  /-- Ordered-list symmetry. -/
  theorem AtomsEquivalentWith.symm
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundSymmetric :
        ∀ {left right : Metta.Ground}, groundEq left right = true →
          groundEq right left = true) :
      ∀ {left right}, AtomsEquivalentWith groundEq left right →
        AtomsEquivalentWith groundEq right left
    | _, _, .nil => .nil
    | _, _, .cons head tail => .cons
        (AtomEquivalentWith.symm (groundEq := groundEq)
          groundSymmetric head)
        (AtomsEquivalentWith.symm (groundEq := groundEq)
          groundSymmetric tail)

end

mutual

  /-- Transitivity lifts structurally from grounded leaves to complete
  terms. -/
  theorem AtomEquivalentWith.trans
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundTransitive :
        ∀ {first second third : Metta.Ground},
          groundEq first second = true →
          groundEq second third = true →
          groundEq first third = true) :
      ∀ {first second third},
        AtomEquivalentWith groundEq first second →
        AtomEquivalentWith groundEq second third →
        AtomEquivalentWith groundEq first third
    | _, _, _, .symbol name, .symbol _ => .symbol name
    | _, _, _, .variable name, .variable _ => .variable name
    | _, _, _, .ground firstSecond, .ground secondThird =>
        .ground (groundTransitive firstSecond secondThird)
    | _, _, _, .expression firstSecond, .expression secondThird =>
        .expression
          (AtomsEquivalentWith.trans (groundEq := groundEq) groundTransitive
            firstSecond secondThird)

  /-- Ordered-list transitivity. -/
  theorem AtomsEquivalentWith.trans
      {groundEq : Metta.Ground → Metta.Ground → Bool}
      (groundTransitive :
        ∀ {first second third : Metta.Ground},
          groundEq first second = true →
          groundEq second third = true →
          groundEq first third = true) :
      ∀ {first second third},
        AtomsEquivalentWith groundEq first second →
        AtomsEquivalentWith groundEq second third →
        AtomsEquivalentWith groundEq first third
    | _, _, _, .nil, .nil => .nil
    | _, _, _, .cons firstHead firstTail, .cons secondHead secondTail =>
        .cons
          (AtomEquivalentWith.trans (groundEq := groundEq)
            groundTransitive firstHead secondHead)
          (AtomsEquivalentWith.trans (groundEq := groundEq)
            groundTransitive firstTail secondTail)

end

mutual

  /-- Structurally equivalent runtime terms have the same finite size. -/
  theorem AtomEquivalentWith.size_eq
      {groundEq : Metta.Ground → Metta.Ground → Bool} :
      ∀ {left right}, AtomEquivalentWith groundEq left right →
        left.size = right.size
    | _, _, .symbol _ => rfl
    | _, _, .variable _ => rfl
    | _, _, .ground _ => by simp only [Atom.size]
    | _, _, .expression children => by
        simp only [Atom.size]
        rw [AtomsEquivalentWith.size_sum_eq children]

  /-- Ordered equivalent children have equal summed structural size. -/
  theorem AtomsEquivalentWith.size_sum_eq
      {groundEq : Metta.Ground → Metta.Ground → Bool} :
      ∀ {left right}, AtomsEquivalentWith groundEq left right →
        (left.map Atom.size).sum = (right.map Atom.size).sum
    | _, _, .nil => rfl
    | _, _, .cons head tail => by
        simp only [List.map_cons, List.sum_cons]
        rw [AtomEquivalentWith.size_eq head,
          AtomsEquivalentWith.size_sum_eq tail]

end

/-- Propositional equality is a special case of structural equivalence under
a reflexive ground comparator. -/
theorem AtomEquivalentWith.of_eq
    {groundEq : Metta.Ground → Metta.Ground → Bool}
    (groundReflexive : ∀ ground, groundEq ground ground = true)
    {left right : Atom} (equal : left = right) :
    AtomEquivalentWith groundEq left right := by
  subst right
  exact AtomEquivalentWith.refl groundReflexive left

/-- PeTTa/SWI first-order unification with exact Prolog ground identity at
every decomposition round.  Comparator-parametric decomposition is
load-bearing: substitution may expose a ground-ground equation only after an
earlier variable-elimination round. -/
def unifyTopExact (x y : Atom) : Option Subst :=
  Metta.Unify.unifyTopWith prologGroundIdentical x y

end PLeaTTa
