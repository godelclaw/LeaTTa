-- SPDX-License-Identifier: Apache-2.0

/-
Value representation (the load-bearing choice): PeTTa runs on Prolog, and
MeTTa tuples ARE Prolog lists there — `[H|T]`. PLeaTTa therefore represents
tuple VALUES as cons-chains internally, so `(cons $a $rest)` and friends
narrow STRUCTURALLY through ordinary unification (no moded builtins).
Surface tuples chainify at compile/world boundaries and unchainify at print.

Encoding: nil = one source-unforgeable tag, cons = `(#c h t)`.
-/
import MettaHyperonFull.Core.Atom

namespace PLeaTTa

open Metta (Atom)

/-- Source-unforgeable tag for pinned PeTTa's empty Prolog list.

The source atom `#nil` is an ordinary atom in pinned PeTTa and is distinct
from `()`.  Using that spelling as the internal empty-list sentinel aliases
the two source values during unification.  The external payload is erased by
`unchainify` before any user observation. -/
def nilA : Atom :=
  Atom.gnd (.external "PLeaTTa.internal" "nil")

/-- One boolean representation everywhere: the symbols `True`/`False`
    (the parser produces `Ground.bool`; builtins may too). -/
def canonBool : Atom → Atom
  | Atom.gnd (Metta.Ground.bool true) => Atom.sym "True"
  | Atom.gnd (Metta.Ground.bool false) => Atom.sym "False"
  | Atom.sym "true" => Atom.sym "True"     -- PeTTa's lowercase aliases
  | Atom.sym "false" => Atom.sym "False"
  | a => a

def consC (h t : Atom) : Atom := Atom.expr [Atom.sym "#c", h, t]

/-- Chainify one tuple level into the private nil/cons representation. -/
def chainOf (es : List Atom) : Atom := es.foldr consC nilA

theorem chainOf_nil : chainOf [] = nilA := by
  rfl

theorem chainOf_cons (head : Atom) (tail : List Atom) :
    chainOf (head :: tail) = consC head (chainOf tail) := by
  rfl

/-- Source-unforgeable tag for an ordinary Prolog compound constructed by
pinned `Predicate/2` through `=../2` [SPEC metta.pl:275].

An ordinary MeTTa expression is represented by a cons-chain, so neither a
source expression headed by `Predicate` nor a quoted list may double as a
Prolog compound.  Keeping the provenance in an external tag makes that
distinction structural; `unchainify` erases it only at observation time.

This tag is deliberately distinct from `reservedSyntaxTagA`: ordinary
Prolog data may use functor spellings such as `$clause` and `$goal.call`, but
it must never become executable retract syntax merely because the spelling
matches. -/
def prologCompoundTagA : Atom :=
  Atom.gnd (.external "PLeaTTa.internal" "prolog-compound")

/-- Internal representation of one positive-arity Prolog compound.  The
argument spine is an ordinary private proper-list encoding.  Prolog atoms
(the zero-arity `=../2` case) remain ordinary `Atom.sym` values and therefore
do not use this constructor. -/
def prologCompoundC (functor : String) (encodedArgs : Atom) : Atom :=
  Atom.expr [prologCompoundTagA, Atom.sym functor, encodedArgs]

/-- Source-unforgeable tag for executable syntax used only by the internal
`retract/1` matcher.

Pinned Prolog uses ordinary compounds for both data and syntax, but the
executable bridge must remember which terms came from its certified clause
encoder: otherwise `Predicate/2` could construct a value named `$clause` or
`$goal.call` and forge an internal syntax node.  Keeping a second private tag
makes that provenance distinction structural without restricting the
ordinary Prolog functor namespace. -/
def reservedSyntaxTagA : Atom :=
  Atom.gnd (.external "PLeaTTa.internal" "reserved-syntax")

/-- Internal representation of one certified retract-syntax constructor. -/
def reservedSyntaxC (functor : String) (encodedArgs : Atom) : Atom :=
  Atom.expr [reservedSyntaxTagA, Atom.sym functor, encodedArgs]

/-- Compatibility name for the former dedicated partial tag.

Pinned PeTTa gives compiler-produced partial applications and Predicate/2's
`partial(Fun, Args)` the same Prolog term identity.  Partial values therefore
use `prologCompoundTagA`; this name remains only so downstream proofs can
remove their old shape assumptions incrementally. -/
def partialTagA : Atom := prologCompoundTagA

/-- Exact runtime representation of pinned PeTTa's `partial(Fun, Args)`.

The outer value is the same private positive-arity compound produced by
Predicate/2.  Its argument spine has exactly two fields: the callable
functor atom and the already-encoded bound-argument list.  An ordinary MeTTa
list headed by the source symbol `partial` remains a distinct cons-chain. -/
def partialC (functor : String) (encodedArgs : Atom) : Atom :=
  prologCompoundC "partial" (chainOf [.sym functor, encodedArgs])

/-- Decode one complete internal cons-chain.  Compilation, specialization,
    and execution share this exact inverse view of `chainOf`. -/
def chainListM : Atom → Option (List Atom)
  | Atom.gnd (.external "PLeaTTa.internal" "nil") => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainListM t).map (h :: ·)
  | _ => none

/-- Decoding the canonical proper-list representation is a left inverse.
This foundational equation lives beside the representation rather than in a
downstream specialization proof, so runtime and adequacy layers can reuse it
without importing the compiler specialization stack. -/
@[simp] theorem chainListM_chainOf_exact (atoms : List Atom) :
    chainListM (chainOf atoms) = some atoms := by
  induction atoms with
  | nil =>
      rw [chainOf_nil]
      rfl
  | cons head tail inductionHypothesis =>
      rw [chainOf_cons]
      simp [chainListM, consC, inductionHypothesis]

/-- The internal empty-list sentinel cannot alias the forgeable source atom
`#nil`.  This is the discriminator that the previous representation lacked. -/
theorem nilA_ne_source_nil : nilA ≠ Atom.sym "#nil" := by
  simp [nilA]

/-- A literal source `#nil` is not decoded as an empty proper list. -/
@[simp] theorem chainListM_source_nil :
    chainListM (Atom.sym "#nil") = none := by
  rfl

/-- Recognize only the source-unforgeable positive-arity Prolog-compound
encoding. -/
def prologCompoundView? : Atom → Option (String × Atom)
  | Atom.expr [Atom.gnd (.external "PLeaTTa.internal" "prolog-compound"),
      Atom.sym functor, encodedArgs] => some (functor, encodedArgs)
  | _ => none

/-- Recognize only certified retract-syntax constructors. -/
def reservedSyntaxView? : Atom → Option (String × Atom)
  | Atom.expr [Atom.gnd (.external "PLeaTTa.internal" "reserved-syntax"),
      Atom.sym functor, encodedArgs] => some (functor, encodedArgs)
  | _ => none

/-- Recognize only the exact callable `partial/2` compound shape.

The two nested cons cells and private nil terminator make the arity check
structural.  Predicate/2's `partial/3` therefore remains ordinary data,
while Predicate/2 and the compiler agree on every exact `partial/2` value. -/
def partialView? : Atom → Option (String × Atom)
  | Atom.expr
      [Atom.gnd (.external "PLeaTTa.internal" "prolog-compound"),
       Atom.sym "partial",
       Atom.expr
         [Atom.sym "#c", Atom.sym functor,
          Atom.expr
            [Atom.sym "#c", encodedArgs,
             Atom.gnd (.external "PLeaTTa.internal" "nil")]]] =>
      some (functor, encodedArgs)
  | _ => none

@[simp] theorem chainListM_partialC (functor : String)
    (encodedArgs : Atom) :
    chainListM (partialC functor encodedArgs) = none := by
  simp [partialC, prologCompoundC, prologCompoundTagA, chainListM]

@[simp] theorem partialView?_partialC (functor : String)
    (encodedArgs : Atom) :
    partialView? (partialC functor encodedArgs) =
      some (functor, encodedArgs) := by
  simp [partialView?, partialC, prologCompoundC, prologCompoundTagA,
    chainOf, consC, nilA]

/-- Successful partial decoding exposes the exact internal compound. -/
theorem partialView?_sound {atom : Atom} {functor : String}
    {encodedArgs : Atom}
    (view : partialView? atom = some (functor, encodedArgs)) :
    atom = partialC functor encodedArgs := by
  unfold partialView? at view
  split at view
  next parsedFunctor parsedArgs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at view
    rcases view with ⟨rfl, rfl⟩
    rfl
  next => contradiction

@[simp] theorem chainListM_prologCompoundC (functor : String)
    (encodedArgs : Atom) :
    chainListM (prologCompoundC functor encodedArgs) = none := by
  simp [prologCompoundC, prologCompoundTagA, chainListM]

@[simp] theorem prologCompoundView?_prologCompoundC (functor : String)
    (encodedArgs : Atom) :
    prologCompoundView? (prologCompoundC functor encodedArgs) =
      some (functor, encodedArgs) := by
  simp [prologCompoundView?, prologCompoundC, prologCompoundTagA]

/-- Successful compound decoding exposes the exact internal constructor. -/
theorem prologCompoundView?_sound {atom : Atom} {functor : String}
    {encodedArgs : Atom}
    (view : prologCompoundView? atom = some (functor, encodedArgs)) :
    atom = prologCompoundC functor encodedArgs := by
  unfold prologCompoundView? at view
  split at view
  next parsedFunctor parsedArgs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at view
    rcases view with ⟨rfl, rfl⟩
    rfl
  next => contradiction

/-- The internal compound representation is injective in both the functor
and the encoded argument spine. -/
theorem prologCompoundC_injective {leftFunctor rightFunctor : String}
    {leftArgs rightArgs : Atom}
    (equal : prologCompoundC leftFunctor leftArgs =
      prologCompoundC rightFunctor rightArgs) :
    leftFunctor = rightFunctor ∧ leftArgs = rightArgs := by
  simpa [prologCompoundC, prologCompoundTagA] using equal

@[simp] theorem chainListM_reservedSyntaxC (functor : String)
    (encodedArgs : Atom) :
    chainListM (reservedSyntaxC functor encodedArgs) = none := by
  simp [reservedSyntaxC, reservedSyntaxTagA, chainListM]

@[simp] theorem reservedSyntaxView?_reservedSyntaxC (functor : String)
    (encodedArgs : Atom) :
    reservedSyntaxView? (reservedSyntaxC functor encodedArgs) =
      some (functor, encodedArgs) := by
  simp [reservedSyntaxView?, reservedSyntaxC, reservedSyntaxTagA]

/-- Successful reserved-syntax decoding exposes the exact constructor. -/
theorem reservedSyntaxView?_sound {atom : Atom} {functor : String}
    {encodedArgs : Atom}
    (view : reservedSyntaxView? atom = some (functor, encodedArgs)) :
    atom = reservedSyntaxC functor encodedArgs := by
  unfold reservedSyntaxView? at view
  split at view
  next parsedFunctor parsedArgs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at view
    rcases view with ⟨rfl, rfl⟩
    rfl
  next => contradiction

/-- Certified syntax is injective in its functor and argument spine. -/
theorem reservedSyntaxC_injective {leftFunctor rightFunctor : String}
    {leftArgs rightArgs : Atom}
    (equal : reservedSyntaxC leftFunctor leftArgs =
      reservedSyntaxC rightFunctor rightArgs) :
    leftFunctor = rightFunctor ∧ leftArgs = rightArgs := by
  simpa [reservedSyntaxC, reservedSyntaxTagA] using equal

/-- An ordinary Prolog value cannot forge certified retract syntax, even
when both use the same visible functor and argument spine. -/
@[simp] theorem prologCompoundC_ne_reservedSyntaxC
    (valueFunctor syntaxFunctor : String) (valueArgs syntaxArgs : Atom) :
    prologCompoundC valueFunctor valueArgs ≠
      reservedSyntaxC syntaxFunctor syntaxArgs := by
  simp [prologCompoundC, prologCompoundTagA,
    reservedSyntaxC, reservedSyntaxTagA]

@[simp] theorem reservedSyntaxC_ne_prologCompoundC
    (syntaxFunctor valueFunctor : String) (syntaxArgs valueArgs : Atom) :
    reservedSyntaxC syntaxFunctor syntaxArgs ≠
      prologCompoundC valueFunctor valueArgs := by
  exact Ne.symm
    (prologCompoundC_ne_reservedSyntaxC valueFunctor syntaxFunctor
      valueArgs syntaxArgs)

/-- Deep chainify a surface atom (quoted data, facts). -/
def chainify : Atom → Atom
  | Atom.expr es => chainOf (es.attach.map (fun ⟨e, _⟩ => chainify e))
  | a => canonBool a

/-- A surface expression chainifies pointwise before the outer proper-list
encoding.  Naming this equation avoids reopening `List.attach` in recursive
representation proofs. -/
@[simp] theorem chainify_expr (atoms : List Atom) :
    chainify (.expr atoms) = chainOf (atoms.map chainify) := by
  simp [chainify]

/-- Deep unchainify for printing: chains back to tuples; non-chain exprs
    (e.g. partially instantiated) render elementwise. -/
def unchainify (fuel : Nat) (a : Atom) : Atom :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
    match prologCompoundView? a with
    | some (functor, encodedArgs) =>
        match chainListM encodedArgs with
        | some arguments =>
            Atom.expr (Atom.sym functor :: arguments.map (unchainify fuel))
        | none =>
            -- This malformed internal value is unreachable from Predicate;
            -- retain its argument rather than silently dropping information.
            Atom.expr [Atom.sym functor, unchainify fuel encodedArgs]
    | none =>
        match partialView? a with
        | some (functor, encodedArgs) =>
            Atom.expr
              [Atom.sym "partial", Atom.sym functor,
                unchainify fuel encodedArgs]
        | none =>
            match a with
            | Atom.expr [Atom.sym "#c", h, t] =>
                let rec walk (fu : Nat) (x : Atom)
                    (acc : List Atom) : List Atom × Option Atom :=
                  match fu, x with
                  | 0, x => (acc, some x)
                  | _, Atom.gnd
                      (.external "PLeaTTa.internal" "nil") => (acc, none)
                  | fu + 1, Atom.expr [Atom.sym "#c", h', t'] =>
                      walk fu t' (acc ++ [unchainify fu h'])
                  | _, other => (acc, some other)
                let (items, tail?) := walk fuel t [unchainify fuel h]
                match tail? with
                | none => Atom.expr items
                | some tl =>
                    Atom.expr (items ++ [Atom.sym ".", unchainify fuel tl])
            | Atom.gnd (.external "PLeaTTa.internal" "nil") => Atom.expr []
            | Atom.expr es => Atom.expr (es.map (unchainify fuel))
            | a => a

/-- Shared depth bound for reconstructing source syntax at runtime `eval/2`.

`unchainify` is information-preserving when this bound is exhausted: it
retains the residual internal representation rather than fabricating or
dropping syntax. Naming the bound keeps the specification and both executors
on exactly the same classifier. -/
def runtimeEvalUnchainifyFuel : Nat := 10000

/-- Prepare one resolved runtime value for pinned `eval/2`.

Pinned `translate_expr/3` accepts variables, atomic values, proper lists, and
exact `partial/2` compounds.  Internal proper lists must therefore be
unchainified back to source syntax, while a tagged `partial/2` must retain its
compound identity and variable sharing.  Every other tagged Prolog compound
is rejected: it is neither a literal accepted by the first source clause nor
a proper list accepted by the recursive clause.

Certified retract syntax is rejected as well.  It is a PLeaTTa-only internal
provenance carrier, not runtime MeTTa code.
[SPEC translator.pl:96-97; metta.pl:251-253] -/
def prepareEvalInput? (fuel : Nat) (a : Atom) : Option Atom :=
  match partialView? a with
  | some _ => some a
  | none =>
      match prologCompoundView? a with
      | some _ => none
      | none =>
          match reservedSyntaxView? a with
          | some _ => none
          | none => some (unchainify fuel a)

/-- Exact `partial/2` values pass through runtime eval preparation unchanged. -/
@[simp] theorem prepareEvalInput?_partialC (fuel : Nat) (functor : String)
    (encodedArgs : Atom) :
    prepareEvalInput? fuel (partialC functor encodedArgs) =
      some (partialC functor encodedArgs) := by
  simp [prepareEvalInput?]

/-- A tagged Prolog compound that is not exact `partial/2` is rejected. -/
theorem prepareEvalInput?_prologCompound_of_not_partial (fuel : Nat)
    (functor : String) (encodedArgs : Atom)
    (notPartial : partialView? (prologCompoundC functor encodedArgs) = none) :
    prepareEvalInput? fuel (prologCompoundC functor encodedArgs) = none := by
  simp [prepareEvalInput?, notPartial]

/-- Certified internal syntax is never reinterpreted as runtime MeTTa code. -/
@[simp] theorem prepareEvalInput?_reservedSyntaxC (fuel : Nat)
    (functor : String) (encodedArgs : Atom) :
    prepareEvalInput? fuel (reservedSyntaxC functor encodedArgs) = none := by
  simp [prepareEvalInput?, reservedSyntaxC, reservedSyntaxTagA,
    partialView?, prologCompoundView?, reservedSyntaxView?]

/-- Proper-list provenance, including a source list spelled `partial`, cannot
forge the live Prolog-compound path. -/
theorem prepareEvalInput?_chainOf (fuel : Nat) (atoms : List Atom) :
    prepareEvalInput? fuel (chainOf atoms) =
      some (unchainify fuel (chainOf atoms)) := by
  cases atoms with
  | nil =>
      simp [prepareEvalInput?, chainOf, nilA, partialView?,
        prologCompoundView?, reservedSyntaxView?]
  | cons head tail =>
      simp [prepareEvalInput?, chainOf, consC, partialView?,
        prologCompoundView?, reservedSyntaxView?]

@[simp] theorem unchainify_sym (fuel : Nat) (name : String) :
    unchainify fuel (.sym name) = .sym name := by
  cases fuel <;> rfl

@[simp] theorem unchainify_var (fuel : Nat) (name : String) :
    unchainify fuel (.var name) = .var name := by
  cases fuel <;> rfl

@[simp] theorem unchainify_ordinary_ground (fuel : Nat) (ground : Metta.Ground)
    (notNil : ground ≠ .external "PLeaTTa.internal" "nil") :
    unchainify fuel (.gnd ground) = .gnd ground := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [unchainify]
      split <;> simp_all [prologCompoundView?, partialView?]

end PLeaTTa
