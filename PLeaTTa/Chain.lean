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

/-- Decode one complete internal cons-chain.  Compilation, specialization,
    and execution share this exact inverse view of `chainOf`. -/
def chainListM : Atom → Option (List Atom)
  | Atom.gnd (.external "PLeaTTa.internal" "nil") => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainListM t).map (h :: ·)
  | _ => none

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

end PLeaTTa
