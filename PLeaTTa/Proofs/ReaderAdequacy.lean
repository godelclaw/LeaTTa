/-
Module: PLeaTTa.Proofs.ReaderAdequacy
Purpose: Soundness and completeness of the executable PeTTa readers against
  the independent relational specification in PLeaTTa.PeTTaSpec.Reader.
Trusted boundary: none
-/
import MettaHyperonFull.Runtime.Parser
import PLeaTTa.PeTTaSpec.Reader

namespace PLeaTTa.ReaderAdequacy

open PLeaTTa.PeTTaSpec.Reader

def modeOfComments : Bool → ReaderMode
  | true => .source
  | false => .sread

def stateOfRuntime : Metta.Runtime.TokState → LexState
  | .sym chars => .symbol chars.reverse
  | .str chars escaped => .string chars.reverse escaped
  | .comment => .comment

theorem runtime_isSpace_iff (c : Char) :
    Metta.Runtime.isSpace c = true ↔ IsBlank c := by
  simp [Metta.Runtime.isSpace, IsBlank, Bool.or_eq_true, or_assoc]

theorem runtime_isSpace_eq_false_iff (c : Char) :
    Metta.Runtime.isSpace c = false ↔ ¬ IsBlank c := by
  rw [Bool.eq_false_iff]
  exact not_congr (runtime_isSpace_iff c)

theorem runtime_decodeStringEscape_eq (c : Char) :
    Metta.Runtime.decodeStringEscape c = decodeEscape c := by
  simp [Metta.Runtime.decodeStringEscape, decodeEscape]

theorem emitSymbol_reverse (chars : List Char) :
    emitSymbol chars.reverse =
      match chars with
      | [] => []
      | _ :: _ => [String.ofList chars.reverse] := by
  cases chars with
  | nil => rfl
  | cons c cs =>
      simp [emitSymbol, List.reverse_cons]

theorem reverse_flushSym (chars : List Char) (tokens : List String) :
    (Metta.Runtime.flushSym chars tokens).reverse =
      tokens.reverse ++ emitSymbol chars.reverse := by
  cases chars with
  | nil => simp [Metta.Runtime.flushSym, emitSymbol]
  | cons c cs =>
      rw [emitSymbol_reverse]
      simp [Metta.Runtime.flushSym]

end PLeaTTa.ReaderAdequacy
