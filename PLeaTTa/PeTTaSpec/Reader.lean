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

open Metta

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

/-- Nonempty base-ten digits.  This deliberately excludes Lean numeric
separators such as `_`, matching the decimal fragment accepted by PeTTa's
`number//1` and supported by PLeaTTa. -/
def DigitString (text : String) : Prop :=
  text ≠ "" ∧ ∀ char ∈ text.toList, Char.isDigit char = true

/-- Meaning of a signed decimal integer token.  This is a proposition over
standard string operations, not a call to the executable integer parser. -/
def DecimalInteger (token : String) (value : Int) : Prop :=
  let negative := token.startsWith "-"
  let positive := token.startsWith "+"
  let body := if negative || positive then (token.drop 1).toString else token
  DigitString body ∧ ∃ magnitude,
    body.toNat? = some magnitude ∧
    value = if negative then -Int.ofNat magnitude else Int.ofNat magnitude

/-- Meaning of a decimal mantissa before an optional exponent is applied. -/
def DecimalMantissa (token : String) (negative : Bool)
    (magnitude fractionalDigits : Nat) : Prop :=
  let isNegative := token.startsWith "-"
  let isPositive := token.startsWith "+"
  let body :=
    if isNegative || isPositive then (token.drop 1).toString else token
  negative = isNegative ∧
    match body.splitOn "." with
    | [digits] =>
        DigitString digits ∧ digits.toNat? = some magnitude ∧
          fractionalDigits = 0
    | [integerPart, fractionalPart] =>
        DigitString integerPart ∧ DigitString fractionalPart ∧
          (integerPart ++ fractionalPart).toNat? = some magnitude ∧
          fractionalDigits = fractionalPart.length
    | _ => False

/-- Pinned reader convention for selecting lower- or upper-case exponent
separators.  Lower-case `e` has priority when present. -/
def exponentParts (token : String) : List String :=
  if token.contains "e" then token.splitOn "e" else token.splitOn "E"

def signedScientific (negative : Bool) (magnitude fractionalDigits : Nat) : Float :=
  let value := Float.ofScientific magnitude true fractionalDigits
  if negative then -value else value

def signedExponentScientific (negative : Bool) (magnitude fractionalDigits : Nat)
    (exponent : Int) : Float :=
  let scale := Int.ofNat fractionalDigits - exponent
  let value := if scale >= 0 then
    Float.ofScientific magnitude true scale.toNat
  else
    Float.ofScientific magnitude false (-scale).toNat
  if negative then -value else value

/-- Independent relation for the supported decimal-float fragment. -/
inductive DecimalFloat : String → Float → Prop where
  | fixed {token mantissa : String} {negative : Bool}
      {magnitude fractionalDigits : Nat}
      (parts : exponentParts token = [mantissa])
      (hasPoint : mantissa.contains "." = true)
      (mantissaMeaning :
        DecimalMantissa mantissa negative magnitude fractionalDigits) :
      DecimalFloat token
        (signedScientific negative magnitude fractionalDigits)
  | exponent {token mantissa exponentToken : String} {negative : Bool}
      {magnitude fractionalDigits : Nat} {exponentValue : Int}
      (parts : exponentParts token = [mantissa, exponentToken])
      (mantissaMeaning :
        DecimalMantissa mantissa negative magnitude fractionalDigits)
      (exponentMeaning : DecimalInteger exponentToken exponentValue) :
      DecimalFloat token
        (signedExponentScientific negative magnitude fractionalDigits exponentValue)

/-- Earlier `parseAtomToken` cases are false, so numeric/symbol fallback is
reachable. -/
def BeforeNumber (token : String) : Prop :=
  token.startsWith "$" = false ∧ token ≠ "True" ∧ token ≠ "False" ∧
    token ≠ "()" ∧ token.startsWith "\"" = false

/-- Independent meaning relation for a non-parenthesis token.  Constructor
order records `parser.pl`'s variable/string/number/atom priority. -/
inductive TokenDenotes : Nat → String → Atom → Prop where
  | anonymous (position : Nat) :
      TokenDenotes position "$_" (Atom.var s!"_ anonymous {position}")
  | namedVariable {position : Nat} {token : String}
      (notAnonymous : token ≠ "$_")
      (startsDollar : token.startsWith "$" = true) :
      TokenDenotes position token (Atom.var (token.drop 1).toString)
  | trueLiteral (position : Nat) :
      TokenDenotes position "True" (Atom.gnd (Ground.bool true))
  | falseLiteral (position : Nat) :
      TokenDenotes position "False" (Atom.gnd (Ground.bool false))
  | emptyExpression (position : Nat) :
      TokenDenotes position "()" (Atom.expr [])
  | string {position : Nat} {token : String}
      (before : token.startsWith "$" = false ∧ token ≠ "True" ∧
        token ≠ "False" ∧ token ≠ "()")
      (startsQuote : token.startsWith "\"" = true) :
      TokenDenotes position token
        (Atom.gnd (Ground.str ((token.drop 1).dropEnd 1).toString))
  | integer {position : Nat} {token : String} {value : Int}
      (before : BeforeNumber token)
      (meaning : DecimalInteger token value) :
      TokenDenotes position token (Atom.gnd (Ground.int value))
  | float {position : Nat} {token : String} {value : Float}
      (before : BeforeNumber token)
      (notInteger : ¬ ∃ integer, DecimalInteger token integer)
      (meaning : DecimalFloat token value) :
      TokenDenotes position token (Atom.gnd (Ground.float value))
  | symbol {position : Nat} {token : String}
      (before : BeforeNumber token)
      (notInteger : ¬ ∃ integer, DecimalInteger token integer)
      (notFloat : ¬ ∃ value, DecimalFloat token value) :
      TokenDenotes position token (Atom.sym token)

/-- Independent stack-machine judgment for balanced token streams. `Leaf`
supplies token meaning separately, so structural reader adequacy cannot hide a
claim about numbers, strings, or variables. Positions count the tokens still
to the right, matching PeTTa's per-read freshness convention for `$_`. -/
inductive ParsesTokens (Leaf : Nat → String → Atom → Prop) :
    List (List Atom) → List String → List Atom → Prop where
  | done (top : List Atom) :
      ParsesTokens Leaf [top] [] top.reverse
  | push {stack : List (List Atom)} {rest : List String} {output : List Atom}
      (tail : ParsesTokens Leaf ([] :: stack) rest output) :
      ParsesTokens Leaf stack ("(" :: rest) output
  | pop {inner outer : List Atom} {more : List (List Atom)}
      {rest : List String} {output : List Atom}
      (tail : ParsesTokens Leaf
        ((Atom.expr inner.reverse :: outer) :: more) rest output) :
      ParsesTokens Leaf (inner :: outer :: more) (")" :: rest) output
  | leaf {top : List Atom} {more : List (List Atom)} {token : String}
      {rest : List String} {atom : Atom} {output : List Atom}
      (notOpen : token ≠ "(") (notClose : token ≠ ")")
      (denotes : Leaf rest.length token atom)
      (tail : ParsesTokens Leaf ((atom :: top) :: more) rest output) :
      ParsesTokens Leaf (top :: more) (token :: rest) output

def ReadsProgram (Leaf : Nat → String → Atom → Prop)
    (source : String) (output : List Atom) : Prop :=
  ∃ tokens, SourceLexes source tokens ∧ ParsesTokens Leaf [[]] tokens output

def ReadsSExpr (Leaf : Nat → String → Atom → Prop)
    (source : String) (output : Atom) : Prop :=
  ∃ tokens, RuntimeLexes source tokens ∧
    ParsesTokens Leaf [[]] tokens [output]

/-- Independent state for pinned `filereader.pl:strip/3`.  It is deliberately
not the executable `Metta.Runtime.FileStripState`.

Source anchor: PeTTa revision `6b7f52f`, `src/filereader.pl:72-78`. -/
inductive StripState where
  | text (inString : Bool)
  | comment
deriving Repr, DecidableEq

/-- Relational specification of pinned source-comment stripping.  The pinned
revision toggles at every quote, does not recognize escapes at this pass, and
drops the newline which terminates a comment.

Constructor crosswalk at revision `6b7f52f`: `done` is line 73; `quote` is
lines 74-75; emitted newlines are covered by `textChar` from line 76;
`commentStart`, `commentChar`, and `commentNewline` relationally expand the
search-and-resume clause at line 77; all other emitted characters are
`textChar` from line 78. -/
inductive FileStrips : StripState → List Char → List Char → Prop where
  | done (state : StripState) : FileStrips state [] []
  | commentNewline {input output : List Char}
      (tail : FileStrips (.text false) input output) :
      FileStrips .comment ('\n' :: input) output
  | commentChar {char : Char} {input output : List Char}
      (notNewline : char ≠ '\n')
      (tail : FileStrips .comment input output) :
      FileStrips .comment (char :: input) output
  | quote {inString : Bool} {input output : List Char}
      (tail : FileStrips (.text (!inString)) input output) :
      FileStrips (.text inString) ('"' :: input) ('"' :: output)
  | commentStart {input output : List Char}
      (tail : FileStrips .comment input output) :
      FileStrips (.text false) (';' :: input) output
  | textChar {inString : Bool} {char : Char} {input output : List Char}
      (notQuote : char ≠ '"')
      (notComment : inString = true ∨ char ≠ ';')
      (tail : FileStrips (.text inString) input output) :
      FileStrips (.text inString) (char :: input) (char :: output)

/-- Independent form-collection state.  Unlike the executable collector,
completed characters are stored in source order. -/
inductive FileFormState where
  | between
  | afterBang
  | form (runnable : Bool) (depth : Nat) (inString : Bool)
      (chars : List Char)
deriving Repr, DecidableEq

/-- Pinned `grab_until_balanced/6` quote transition.

Source anchor: PeTTa revision `6b7f52f`, `src/filereader.pl:51-60`. -/
def nextFileString (inString : Bool) (char : Char) : Bool :=
  if char = '"' then !inString else inString

/-- Pinned `grab_until_balanced/6` parenthesis-depth transition. -/
def nextFileDepth (inString : Bool) (depth : Nat) (char : Char) : Nat :=
  if inString then depth
  else if char = '(' then depth + 1
  else if char = ')' then depth - 1
  else depth

/-- Append one parsed top-level form in source order.  A runnable contributes
the marker and its expression, matching the existing source-form convention. -/
def appendFileForm (runnable : Bool) (atoms : List Atom) (atom : Atom) :
    List Atom :=
  if runnable then atoms ++ [Atom.sym "!", atom] else atoms ++ [atom]

/-- Independent successful judgment for pinned `top_forms//2` and
`grab_until_balanced/6`.  Invalid prefixes, unfinished forms, and forms which
have no independent `ReadsSExpr` derivation have no constructor.

Constructor crosswalk at revision `6b7f52f`: `done` and `blank` are line 63;
`bang`, `open`, and `runnableOpen` are lines 64-67; `finish` and `continue`
expand the character/depth/string transitions at lines 51-60; `finish`'s
`ReadsSExpr` premise is the `parse_form`/`sread` call at lines 20-24; recursive
form order is line 70. -/
inductive SourceForms (Leaf : Nat → String → Atom → Prop) :
    FileFormState → List Atom → List Char → List Atom → Prop where
  | done (atoms : List Atom) :
      SourceForms Leaf .between atoms [] atoms
  | blank {atoms : List Atom} {char : Char} {input : List Char}
      {output : List Atom}
      (isBlank : IsBlank char)
      (tail : SourceForms Leaf .between atoms input output) :
      SourceForms Leaf .between atoms (char :: input) output
  | bang {atoms : List Atom} {input : List Char} {output : List Atom}
      (tail : SourceForms Leaf .afterBang atoms input output) :
      SourceForms Leaf .between atoms ('!' :: input) output
  | open {atoms : List Atom} {input : List Char} {output : List Atom}
      (tail : SourceForms Leaf (.form false 1 false ['(']) atoms input output) :
      SourceForms Leaf .between atoms ('(' :: input) output
  | runnableOpen {atoms : List Atom} {input : List Char}
      {output : List Atom}
      (tail : SourceForms Leaf (.form true 1 false ['(']) atoms input output) :
      SourceForms Leaf .afterBang atoms ('(' :: input) output
  | finish {runnable inString : Bool} {depth : Nat}
      {chars : List Char} {atoms : List Atom} {char : Char}
      {input : List Char} {atom : Atom} {output : List Atom}
      (depthDone : nextFileDepth inString depth char = 0)
      (stringDone : nextFileString inString char = false)
      (read : ReadsSExpr Leaf (String.ofList (chars ++ [char])) atom)
      (tail : SourceForms Leaf .between
        (appendFileForm runnable atoms atom) input output) :
      SourceForms Leaf (.form runnable depth inString chars) atoms
        (char :: input) output
  | continue {runnable inString : Bool} {depth : Nat}
      {chars : List Char} {atoms : List Atom} {char : Char}
      {input : List Char} {output : List Atom}
      (notDone : ¬ (nextFileDepth inString depth char = 0 ∧
        nextFileString inString char = false))
      (tail : SourceForms Leaf
        (.form runnable (nextFileDepth inString depth char)
          (nextFileString inString char) (chars ++ [char]))
        atoms input output) :
      SourceForms Leaf (.form runnable depth inString chars) atoms
        (char :: input) output

/-- Independent pinned-file success judgment: comment stripping followed by
top-level form extraction and independent runtime reading of each form. -/
def ReadsFile (Leaf : Nat → String → Atom → Prop)
    (source : String) (output : List Atom) : Prop :=
  ∃ stripped, FileStrips (.text false) source.toList stripped ∧
    SourceForms Leaf .between [] stripped output

end PLeaTTa.PeTTaSpec.Reader
