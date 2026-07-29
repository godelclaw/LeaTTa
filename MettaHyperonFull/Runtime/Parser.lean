-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Runtime.Parser
Layer: Runtime
Purpose: Parsers for PeTTa source programs and runtime `sread`. The tokenizer is a structural state
  machine that recognises parentheses, the `!` query prefix, `"`-strings, and whitespace-separated
  symbols. Source mode additionally strips `;`-comments and accepts multiple top-level forms;
  `sread` mode treats `;` as token content and requires exactly one complete expression.
Imports: MettaHyperonFull.Core.Atom
Trusted boundary: none
Main exports: tokenize, tokenizeSExpr, parseFloat?, parseAtomToken, parseTokens,
  parseProgram, parseSExpr, parseFile
Open obligations: float literals are IEEE 64-bit doubles, so values like `0.1` carry the usual binary
  rounding.
-/
import MettaHyperonFull.Core.Atom

namespace Metta.Runtime
open Metta

def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- Tokenizer state: accumulating a symbol (`sym`, chars reversed; `[]` means "between tokens"),
    inside a `"`-string literal (`str`, content chars reversed), or inside a `;`-comment. -/
inductive TokState where
  | sym (acc : List Char)
  | str (acc : List Char) (escaped : Bool)
  | comment

/-- Emit the pending symbol token (its chars are reversed in `acc`) onto `toks`, if non-empty. -/
def flushSym (acc : List Char) (toks : List String) : List String :=
  match acc with
  | [] => toks
  | _ => String.ofList acc.reverse :: toks

/-- PeTTa string-literal escape decoding.  Newline, tab, and carriage return
    have their control-character meanings; every other escaped character is
    taken literally (including `\"` and `\\`).  [SPEC parser.pl:56-59] -/
def decodeStringEscape (c : Char) : Char :=
  if c == 'n' then '\n'
  else if c == 't' then '\t'
  else if c == 'r' then '\r'
  else c

/-- Tokenize a character list as a state machine, recursing structurally on the input.
    `semicolonComments` distinguishes source-file stripping (`true`) from PeTTa `sread`, whose
    token grammar admits semicolons (`false`). `toks` accumulates completed tokens in reverse. -/
def tokenizeAux (semicolonComments : Bool) (state : TokState)
    (toks : List String) : List Char → Except String (List String)
  | [] =>
      match state with
      | TokState.sym acc => .ok (flushSym acc toks).reverse
      | TokState.str _ _ => .error "unterminated string literal"
      | TokState.comment => .ok toks.reverse
  | c :: cs =>
      match state with
      | TokState.comment =>
          tokenizeAux semicolonComments
            (if c == '\n' then TokState.sym [] else TokState.comment) toks cs
      | TokState.str acc escaped =>
          if escaped then
            tokenizeAux semicolonComments
              (TokState.str (decodeStringEscape c :: acc) false) toks cs
          else if c == '\\' then
            tokenizeAux semicolonComments (TokState.str acc true) toks cs
          else if c == '"' then
            tokenizeAux semicolonComments (TokState.sym [])
              (("\"" ++ String.ofList acc.reverse ++ "\"") :: toks) cs
          else
            tokenizeAux semicolonComments (TokState.str (c :: acc) false) toks cs
      | TokState.sym acc =>
          if isSpace c then
            tokenizeAux semicolonComments (TokState.sym []) (flushSym acc toks) cs
          else if semicolonComments && c == ';' then
            tokenizeAux semicolonComments TokState.comment (flushSym acc toks) cs
          else if c == '"' && acc.isEmpty then
            tokenizeAux semicolonComments (TokState.str [] false) (flushSym acc toks) cs
          else if c == '(' || c == ')' then
            tokenizeAux semicolonComments (TokState.sym [])
              (String.singleton c :: flushSym acc toks) cs
          else if c == '!' && acc.isEmpty && (cs.head?).elim true (fun d => d == '(' || isSpace d) then
            -- a leading `!` before `(`, whitespace, or end-of-input is the query/exec marker; a `!`
            -- inside a symbol (`bind!`, `change-state!`, `!=`, `println!`) is an ordinary symbol char
            tokenizeAux semicolonComments (TokState.sym []) ("!" :: toks) cs
          else tokenizeAux semicolonComments (TokState.sym (c :: acc)) toks cs

/-- Source-program tokenizer: semicolons outside strings begin comments. -/
def tokenize (s : String) : Except String (List String) :=
  tokenizeAux true (TokState.sym []) [] s.toList

/-- Runtime `sread` tokenizer: PeTTa's token grammar treats semicolons as ordinary content. -/
def tokenizeSExpr (s : String) : Except String (List String) :=
  tokenizeAux false (TokState.sym []) [] s.toList

/-- True when the string is non-empty and contains only decimal digits. Lean's own numeric parsers
    accept separators such as `_`, while MeTTa's lexer treats those tokens as symbols. -/
def allDigits (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit

/-- Parse a signed integer with only decimal digits after an optional sign. -/
def parseInt? (s : String) : Option Int :=
  let neg := s.startsWith "-"
  let pos := s.startsWith "+"
  let body := if neg || pos then (s.drop 1).toString else s
  if allDigits body then
    body.toNat?.map fun n => if neg then -Int.ofNat n else Int.ofNat n
  else none

/-- Split a mantissa into `(sign, digits, fractional_digits)`. A decimal mantissa must have at least
    one digit before and after `.`, so `.5` stays a symbol. -/
def parseMantissa? (s : String) : Option (Bool × Nat × Nat) :=
  let neg := s.startsWith "-"
  let pos := s.startsWith "+"
  let body := if neg || pos then (s.drop 1).toString else s
  match body.splitOn "." with
  | [digits] =>
      if allDigits digits then digits.toNat?.map fun n => (neg, n, 0) else none
  | [intPart, fracPart] =>
      if allDigits intPart && allDigits fracPart then
        (intPart ++ fracPart).toNat?.map fun n => (neg, n, fracPart.length)
      else none
  | _ => none

/-- Parse a decimal float literal with optional scientific notation. Accepted forms include
    `1.5`, `-0.25`, `1e2`, and `1.5e3`; leading-dot floats and digit separators remain symbols.
    Known issue: result is IEEE 64-bit double, so values like `0.1` carry binary float rounding. -/
def parseFloat? (s : String) : Option Float :=
  let parts := if s.contains "e" then s.splitOn "e" else s.splitOn "E"
  match parts with
  | [mantissa] =>
      if mantissa.contains "." then
        parseMantissa? mantissa |>.map fun p =>
          let f := Float.ofScientific p.2.1 true p.2.2
          if p.1 then -f else f
      else none
  | [mantissa, exponent] =>
      match parseMantissa? mantissa, parseInt? exponent with
      | some (neg, m, fracDigits), some e =>
          let scale := Int.ofNat fracDigits - e
          let f := if scale >= 0 then
            Float.ofScientific m true scale.toNat
          else
            Float.ofScientific m false (-scale).toNat
          some (if neg then -f else f)
      | _, _ => none
  | _ => none

/-- Parse a single token into an `Atom`: `$x` → variable, `True`/`False` → Bool, `()` → the empty
    expression, `"…"` → string, an integer/float literal → the grounded number, otherwise a symbol.
    The tokenizer splits `(` and `)` into separate tokens, so the `()` case here is only a guard. -/
def parseAtomToken (s : String) : Atom :=
  if s.startsWith "$" then Atom.var (s.drop 1).toString
  else if s == "True" then Atom.gnd (Ground.bool true)
  else if s == "False" then Atom.gnd (Ground.bool false)
  else if s == "()" then Atom.expr []
  else if s.startsWith "\"" then Atom.gnd (Ground.str ((s.drop 1).dropEnd 1).toString)
  else match parseInt? s with
    | some n => Atom.gnd (Ground.int n)
    | none => match parseFloat? s with
      | some f => Atom.gnd (Ground.float f)
      | none => Atom.sym s

/-- Interpret a non-parenthesis token at its unique position in the current
token stream. PeTTa maps every `$_` token to a fresh Prolog anonymous variable
instead of interning it by name (`parser.pl:41-42`). The embedded space makes
the generated name unreachable through the surface token grammar; the number
is the token's unique position in this parse. Public for the independent
reader-adequacy proof; callers should normally use `parseProgram` or
`parseSExpr`. -/
def parseTokenAt (position : Nat) (token : String) : Atom :=
  if token == "$_" then Atom.var s!"_ anonymous {position}"
  else parseAtomToken token

/-- Parse a flat token stream against an explicit stack of in-progress expression accumulators
    (each holding its atoms reversed); the bottom frame collects the top-level atoms. `(` pushes a
    frame, `)` pops and wraps it as an `Atom.expr`, any other token is appended to the current
    frame. Structurally recursive on the token list, hence total. -/
def parseTokens : List (List Atom) → List String → Except String (List Atom)
  | [top], [] => Except.ok top.reverse
  | _, [] => Except.error "unterminated expression"
  | stack, "(" :: rest => parseTokens ([] :: stack) rest
  | inner :: outer :: more, ")" :: rest =>
      parseTokens ((Atom.expr inner.reverse :: outer) :: more) rest
  | _, ")" :: _ => Except.error "unexpected )"
  | top :: more, tok :: rest =>
      parseTokens ((parseTokenAt rest.length tok :: top) :: more) rest
  | [], _ :: _ => Except.error "unexpected token at top level"

/-- Parse a whole program: a sequence of top-level atoms. -/
def parseProgram (s : String) : Except String (List Atom) := do
  let tokens ← tokenize s
  parseTokens [[]] tokens

/-- Parse exactly one runtime S-expression, matching PeTTa `sread/2`'s whole-input DCG. -/
def parseSExpr (s : String) : Except String Atom := do
  let tokens ← tokenizeSExpr s
  match ← parseTokens [[]] tokens with
  | [atom] => .ok atom
  | _ => .error "expected exactly one s-expression"

/-- State of pinned revision `6b7f52f`'s `filereader.pl:strip/3`.  That
revision toggles string state at every quote, including an escaped quote. -/
inductive FileStripState where
  | text (inString : Bool)
  | comment

/-- Strip source-file comments exactly as the pinned first pass does.  The
newline which terminates a comment is removed with the comment text. -/
def stripFileCommentsAux : FileStripState → List Char → List Char
  | _, [] => []
  | .comment, '\n' :: rest => stripFileCommentsAux (.text false) rest
  | .comment, _ :: rest => stripFileCommentsAux .comment rest
  | .text inString, '"' :: rest =>
      '"' :: stripFileCommentsAux (.text (!inString)) rest
  | .text false, ';' :: rest => stripFileCommentsAux .comment rest
  | .text true, ';' :: rest =>
      ';' :: stripFileCommentsAux (.text true) rest
  | .text inString, char :: rest =>
      char :: stripFileCommentsAux (.text inString) rest

def stripFileComments (source : String) : List Char :=
  stripFileCommentsAux (.text false) source.toList

/-- Single-pass transparent form collector for pinned
`filereader.pl:top_forms//2` plus `grab_until_balanced//6`. -/
inductive FileParseState where
  | between
  | afterBang
  | form (runnable : Bool) (depth : Nat) (inString : Bool)
      (charsRev : List Char)

def parseFileFormsAux (state : FileParseState) (atomsRev : List Atom) :
    List Char → Except String (List Atom)
  | [] =>
      match state with
      | .between => .ok atomsRev.reverse
      | .afterBang => .error "expected '(' after '!'"
      | .form _ _ _ _ => .error "missing ')'"
  | char :: rest =>
      match state with
      | .between =>
          if isSpace char then
            parseFileFormsAux .between atomsRev rest
          else if char == '!' then
            parseFileFormsAux .afterBang atomsRev rest
          else if char == '(' then
            parseFileFormsAux (.form false 1 false ['(']) atomsRev rest
          else
            .error "expected '(' or '!('"
      | .afterBang =>
          if char == '(' then
            parseFileFormsAux (.form true 1 false ['(']) atomsRev rest
          else
            .error "expected '(' after '!'"
      | .form runnable depth inString charsRev =>
          let nextString := if char == '"' then !inString else inString
          let nextDepth :=
            if inString then depth
            else if char == '(' then depth + 1
            else if char == ')' then depth - 1
            else depth
          let nextChars := char :: charsRev
          if nextDepth == 0 && !nextString then
            match parseSExpr (String.ofList nextChars.reverse) with
            | .error error => .error error
            | .ok atom =>
                let nextAtoms :=
                  if runnable then atom :: Atom.sym "!" :: atomsRev
                  else atom :: atomsRev
                parseFileFormsAux .between nextAtoms rest
          else
            parseFileFormsAux
              (.form runnable nextDepth nextString nextChars) atomsRev rest

/-- Parse a source file through the pinned two-pass file-loader contract:
comment stripping, top-level `(`/`!(` form collection, then runtime `sread` of
each balanced form. -/
def parseFile (source : String) : Except String (List Atom) :=
  parseFileFormsAux .between [] (stripFileComments source)

private def parseSucceeded {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/- Hyperon's program surface and pinned PeTTa's file-loader surface are
intentionally distinct.  The former accepts split runnable markers and bare
top-level atoms; the latter requires each stored form to start with `(` and
each runnable form with the contiguous prefix `!(`. -/
#guard parseSucceeded (parseProgram "! (foo)")
#guard !parseSucceeded (parseFile "! (foo)")
#guard parseSucceeded (parseProgram "bare top level atoms")
#guard !parseSucceeded (parseFile "bare top level atoms")

#guard parseSucceeded (parseSExpr "((shell a;b))")
#guard parseSucceeded (parseSExpr "((shell \"a;b\"))")
#guard parseSucceeded (parseSExpr "((cmd a) ... (cmd b))")
#guard !parseSucceeded (parseSExpr "foo bar")
#guard !parseSucceeded (parseSExpr "\"unterminated")
#guard !parseSucceeded (parseSExpr "((send \"unterminated))")
#guard !parseSucceeded (parseSExpr "\"trailing\\")

private def parsedSExprString? : Except String Atom → Option String
  | .ok (Atom.gnd (Ground.str value)) => some value
  | _ => none

-- PeTTa decodes one escape layer per runtime read. In particular, two input
-- backslashes become one literal backslash rather than a newline or two
-- retained backslashes.
#guard parsedSExprString? (parseSExpr "\"\\\\n\"") == some "\\n"
#guard parsedSExprString? (parseSExpr "\"a\\\\;b\"") == some "a\\;b"

private def namedVariableIdentityCorrect : Bool :=
  match parseSExpr "($X $X $X→$tail)" with
  | .ok (Atom.expr [Atom.var first, Atom.var second, Atom.var third]) =>
      first == second && first != third
  | _ => false

#guard namedVariableIdentityCorrect

private def parsedSingleString? : Except String (List Atom) → Option String
  | .ok [Atom.gnd (Ground.str value)] => some value
  | _ => none

#guard parsedSingleString? (parseProgram "\"line one\\nline two\"") ==
  some "line one\nline two"
#guard parsedSingleString? (parseProgram "\"plain n; tab=\\t; return=\\r\"") ==
  some "plain n; tab=\t; return=\r"
#guard parsedSingleString? (parseProgram "\"quote=\\\" slash=\\\\ unknown=\\q\"") ==
  some "quote=\" slash=\\ unknown=q"

private def anonymousAndNamedVariablesCorrect : Bool :=
  match parseProgram "($_ $_ $x $x)" with
  | .ok [Atom.expr [Atom.var first, Atom.var second,
      Atom.var namedFirst, Atom.var namedSecond]] =>
      first != second && namedFirst == "x" && namedSecond == namedFirst
  | _ => false

#guard anonymousAndNamedVariablesCorrect

end Metta.Runtime
