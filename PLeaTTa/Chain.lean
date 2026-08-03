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

/-- Source-unforgeable tag for pinned PeTTa's `partial(Fun, Args)` compound.

Using the source symbol `partial` here would alias the ordinary source list
`[partial, Fun, Args]`.  The external payload is an internal representation
tag only; `unchainify` below erases it before any user observation. -/
def partialTagA : Atom :=
  Atom.gnd (.external "PLeaTTa.internal" "partial")

/-- Internal representation of one pinned PeTTa `partial(Fun, Args)`
compound, where `encodedArgs` is the ordinary internal list encoding.

This is deliberately a direct expression rather than a `#c` chain.  Pinned
PeTTa's `partial/2` is a Prolog compound, not a list: representing it as a
chain would let generic list operations observe the private tag and would
give partial values the wrong list semantics. -/
def partialC (functor : String) (encodedArgs : Atom) : Atom :=
  Atom.expr [partialTagA, Atom.sym functor, encodedArgs]

/-- Source-unforgeable tag for a Prolog compound constructed by pinned
`Predicate/2` through `=../2` [SPEC metta.pl:275].

An ordinary MeTTa expression is represented by a cons-chain, so neither a
source expression headed by `Predicate` nor a quoted list may double as a
Prolog compound.  Keeping the provenance in an external tag makes that
distinction structural; `unchainify` erases it only at observation time. -/
def prologCompoundTagA : Atom :=
  Atom.gnd (.external "PLeaTTa.internal" "prolog-compound")

/-- Internal representation of one positive-arity Prolog compound.  The
argument spine is an ordinary private proper-list encoding.  Prolog atoms
(the zero-arity `=../2` case) remain ordinary `Atom.sym` values and therefore
do not use this constructor. -/
def prologCompoundC (functor : String) (encodedArgs : Atom) : Atom :=
  Atom.expr [prologCompoundTagA, Atom.sym functor, encodedArgs]

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

/-- Recognize only the source-unforgeable partial compound encoding. -/
def partialView? : Atom → Option (String × Atom)
  | Atom.expr [Atom.gnd (.external "PLeaTTa.internal" "partial"),
      Atom.sym functor, encodedArgs] => some (functor, encodedArgs)
  | _ => none

/-- Recognize only the source-unforgeable positive-arity Prolog-compound
encoding. -/
def prologCompoundView? : Atom → Option (String × Atom)
  | Atom.expr [Atom.gnd (.external "PLeaTTa.internal" "prolog-compound"),
      Atom.sym functor, encodedArgs] => some (functor, encodedArgs)
  | _ => none

@[simp] theorem chainListM_partialC (functor : String)
    (encodedArgs : Atom) :
    chainListM (partialC functor encodedArgs) = none := by
  simp [partialC, partialTagA, chainListM]

@[simp] theorem partialView?_partialC (functor : String)
    (encodedArgs : Atom) :
    partialView? (partialC functor encodedArgs) =
      some (functor, encodedArgs) := by
  simp [partialView?, partialC, partialTagA]

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
