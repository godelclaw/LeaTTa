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

/-- PeTTa/SWI first-order unification with exact Prolog ground identity at
every decomposition round.  Comparator-parametric decomposition is
load-bearing: substitution may expose a ground-ground equation only after an
earlier variable-elimination round. -/
def unifyTopExact (x y : Atom) : Option Subst :=
  Metta.Unify.unifyTopWith prologGroundIdentical x y

end PLeaTTa
