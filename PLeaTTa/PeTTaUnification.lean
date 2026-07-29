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

/-- Current PeTTa/SWI exact-ground wrapper.  The comparator-parametric core is
available for the full Prolog-identity migration; until its metatheory is
ported, this wrapper retains the existing candidate filter. -/
def unifyTopExact (x y : Atom) : Option Subst :=
  match Metta.Unify.unifyTop x y with
  | some generated =>
      if pettaUnifyCompatible (subst generated x) (subst generated y) then
        some generated
      else none
  | none => none

end PLeaTTa
