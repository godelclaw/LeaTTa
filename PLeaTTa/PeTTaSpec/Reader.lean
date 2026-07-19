/-
Module: PLeaTTa.PeTTaSpec.Reader
Purpose: An independent relational specification of PeTTa's source and runtime
  lexical readers.  The rules are anchored to parser.pl and filereader.pl;
  they deliberately do not call the executable Lean tokenizer.
Trusted boundary: none
Main exports: ReaderMode, LexState, Lexes, RuntimeLexes, SourceLexes
-/
import MettaHyperonFull.Core.Atom

namespace PLeaTTa.PeTTaSpec.Reader

/-- PeTTa has two distinct reader modes.  Source loading removes semicolon
comments before reading forms; runtime `sread/2` admits semicolons inside atom
tokens. -/
inductive ReaderMode where
  | source
  | sread
deriving Repr, DecidableEq

/-- The lexical state is intentionally separate from the executable
`Metta.Runtime.TokState`.  Character accumulators are in source order. -/
inductive LexState where
  | symbol (chars : List Char)
  | string (chars : List Char) (escaped : Bool)
  | comment
deriving Repr, DecidableEq

/-- Whitespace accepted by PeTTa's `blanks//0`. -/
def IsBlank (c : Char) : Prop :=
  c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r'

instance (c : Char) : Decidable (IsBlank c) := by
  unfold IsBlank
  infer_instance

/-- PeTTa string escape decoding (`parser.pl:string_chars//1`). -/
def decodeEscape (c : Char) : Char :=
  if c = 'n' then '\n'
  else if c = 't' then '\t'
  else if c = 'r' then '\r'
  else c

/-- Emit a pending symbol, if any. -/
def emitSymbol : List Char → List String
  | [] => []
  | chars => [String.ofList chars]

/-- Encode a completed string as the token representation consumed by the
existing atom parser.  Escape decoding has already happened. -/
def stringToken (chars : List Char) : String :=
  "\"" ++ String.ofList chars ++ "\""

/-- A standalone `!` is recognized only at a token boundary and only before
`(`, whitespace, or end of input. -/
def BangBoundary : Option Char → Prop
  | none => True
  | some c => c = '(' ∨ IsBlank c

instance (next : Option Char) : Decidable (BangBoundary next) := by
  cases next with
  | none => exact isTrue True.intro
  | some _ =>
      unfold BangBoundary
      infer_instance

/-- Big-step lexical relation for the pinned PeTTa reader.  Its constructors
are mutually exclusive and follow the character cases in `parser.pl` and
`filereader.pl`, but this is a proposition rather than an executable parser. -/
inductive Lexes : ReaderMode → LexState → List Char → List String → Prop where
  | doneSymbol (mode : ReaderMode) (chars : List Char) :
      Lexes mode (.symbol chars) [] (emitSymbol chars)
  | doneComment (mode : ReaderMode) :
      Lexes mode .comment [] []
  | commentNewline {mode : ReaderMode} {input : List Char} {tokens : List String}
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode .comment ('\n' :: input) tokens
  | commentChar {mode : ReaderMode} {c : Char} {input : List Char} {tokens : List String}
      (notNewline : c ≠ '\n')
      (tail : Lexes mode .comment input tokens) :
      Lexes mode .comment (c :: input) tokens
  | escapedChar {mode : ReaderMode} {chars : List Char} {c : Char}
      {input : List Char} {tokens : List String}
      (tail : Lexes mode (.string (chars ++ [decodeEscape c]) false) input tokens) :
      Lexes mode (.string chars true) (c :: input) tokens
  | beginEscape {mode : ReaderMode} {chars : List Char}
      {input : List Char} {tokens : List String}
      (tail : Lexes mode (.string chars true) input tokens) :
      Lexes mode (.string chars false) ('\\' :: input) tokens
  | closeString {mode : ReaderMode} {chars : List Char}
      {input : List Char} {tokens : List String}
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode (.string chars false) ('"' :: input)
        (stringToken chars :: tokens)
  | stringChar {mode : ReaderMode} {chars : List Char} {c : Char}
      {input : List Char} {tokens : List String}
      (notSlash : c ≠ '\\') (notQuote : c ≠ '"')
      (tail : Lexes mode (.string (chars ++ [c]) false) input tokens) :
      Lexes mode (.string chars false) (c :: input) tokens
  | symbolBlank {mode : ReaderMode} {chars : List Char} {c : Char}
      {input : List Char} {tokens : List String}
      (blank : IsBlank c)
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode (.symbol chars) (c :: input) (emitSymbol chars ++ tokens)
  | sourceComment {chars : List Char} {input : List Char}
      {tokens : List String}
      (tail : Lexes .source .comment input tokens) :
      Lexes .source (.symbol chars) (';' :: input) (emitSymbol chars ++ tokens)
  | openString {mode : ReaderMode} {input : List Char}
      {tokens : List String}
      (tail : Lexes mode (.string [] false) input tokens) :
      Lexes mode (.symbol []) ('"' :: input) tokens
  | leftParen {mode : ReaderMode} {chars : List Char}
      {input : List Char} {tokens : List String}
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode (.symbol chars) ('(' :: input)
        (emitSymbol chars ++ "(" :: tokens)
  | rightParen {mode : ReaderMode} {chars : List Char}
      {input : List Char} {tokens : List String}
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode (.symbol chars) (')' :: input)
        (emitSymbol chars ++ ")" :: tokens)
  | standaloneBang {mode : ReaderMode} {input : List Char}
      {tokens : List String}
      (boundary : BangBoundary input.head?)
      (tail : Lexes mode (.symbol []) input tokens) :
      Lexes mode (.symbol []) ('!' :: input) ("!" :: tokens)
  | symbolChar {mode : ReaderMode} {chars : List Char} {c : Char}
      {input : List Char} {tokens : List String}
      (notBlank : ¬ IsBlank c)
      (notSourceComment : mode ≠ .source ∨ c ≠ ';')
      (notOpenString : chars ≠ [] ∨ c ≠ '"')
      (notLeftParen : c ≠ '(')
      (notRightParen : c ≠ ')')
      (notStandaloneBang : chars ≠ [] ∨ c ≠ '!' ∨ ¬ BangBoundary input.head?)
      (tail : Lexes mode (.symbol (chars ++ [c])) input tokens) :
      Lexes mode (.symbol chars) (c :: input) tokens

/-- Runtime `sread` lexical judgment. -/
def RuntimeLexes (input : String) (tokens : List String) : Prop :=
  Lexes .sread (.symbol []) input.toList tokens

/-- Source-file lexical judgment. -/
def SourceLexes (input : String) (tokens : List String) : Prop :=
  Lexes .source (.symbol []) input.toList tokens

end PLeaTTa.PeTTaSpec.Reader
