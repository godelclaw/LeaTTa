-- SPDX-License-Identifier: Apache-2.0

/-
Value representation (the load-bearing choice): PeTTa runs on Prolog, and
MeTTa tuples ARE Prolog lists there — `[H|T]`. PLeaTTa therefore represents
tuple VALUES as cons-chains internally, so `(cons $a $rest)` and friends
narrow STRUCTURALLY through ordinary unification (no moded builtins).
Surface tuples chainify at compile/world boundaries and unchainify at print.

Encoding: nil = `#nil`, cons = `(#c h t)`.
-/
import MettaHyperonFull.Core.Atom

namespace PLeaTTa

open Metta (Atom)

def nilA : Atom := Atom.sym "#nil"

/-- One boolean representation everywhere: the symbols `True`/`False`
    (the parser produces `Ground.bool`; builtins may too). -/
def canonBool : Atom → Atom
  | Atom.gnd (Metta.Ground.bool true) => Atom.sym "True"
  | Atom.gnd (Metta.Ground.bool false) => Atom.sym "False"
  | Atom.sym "true" => Atom.sym "True"     -- PeTTa's lowercase aliases
  | Atom.sym "false" => Atom.sym "False"
  | a => a

def consC (h t : Atom) : Atom := Atom.expr [Atom.sym "#c", h, t]

/-- Chainify one tuple level: `(a b c)` → `(#c a (#c b (#c c #nil)))`. -/
def chainOf (es : List Atom) : Atom := es.foldr consC nilA

/-- Decode one complete internal cons-chain.  Compilation, specialization,
    and execution share this exact inverse view of `chainOf`. -/
def chainListM : Atom → Option (List Atom)
  | Atom.sym "#nil" => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainListM t).map (h :: ·)
  | _ => none

/-- Deep chainify a surface atom (quoted data, facts). -/
def chainify : Atom → Atom
  | Atom.expr es => chainOf (es.attach.map (fun ⟨e, _⟩ => chainify e))
  | a => canonBool a

/-- Deep unchainify for printing: chains back to tuples; non-chain exprs
    (e.g. partially instantiated) render elementwise. -/
def unchainify (fuel : Nat) (a : Atom) : Atom :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
    match a with
    | Atom.expr [Atom.sym "#c", h, t] =>
        let rec walk (fu : Nat) (x : Atom) (acc : List Atom) : List Atom × Option Atom :=
          match fu, x with
          | 0, x => (acc, some x)
          | _, Atom.sym "#nil" => (acc, none)
          | fu + 1, Atom.expr [Atom.sym "#c", h', t'] =>
              walk fu t' (acc ++ [unchainify fu h'])
          | _, other => (acc, some other)
        let (items, tail?) := walk fuel t [unchainify fuel h]
        match tail? with
        | none => Atom.expr items
        | some tl => Atom.expr (items ++ [Atom.sym ".", unchainify fuel tl])
    | Atom.sym "#nil" => Atom.expr []
    | Atom.expr es => Atom.expr (es.map (unchainify fuel))
    | a => a

end PLeaTTa
