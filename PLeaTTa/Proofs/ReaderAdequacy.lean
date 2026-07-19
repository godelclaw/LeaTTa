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
open Metta

def modeOfComments : Bool → ReaderMode
  | true => .source
  | false => .sread

def stateOfRuntime : Metta.Runtime.TokState → LexState
  | .sym chars => .symbol chars.reverse
  | .str chars escaped => .string chars.reverse escaped
  | .comment => .comment

/-- Inverse encoding used to execute a derivation of the independent reader
relation. The executable keeps character accumulators in reverse order. -/
def runtimeStateOf : LexState → Metta.Runtime.TokState
  | .symbol chars => .sym chars.reverse
  | .string chars escaped => .str chars.reverse escaped
  | .comment => .comment

def commentsOfMode : ReaderMode → Bool
  | .source => true
  | .sread => false

@[simp] theorem modeOfComments_commentsOfMode (mode : ReaderMode) :
    modeOfComments (commentsOfMode mode) = mode := by
  cases mode <;> rfl

@[simp] theorem stateOfRuntime_runtimeStateOf (state : LexState) :
    stateOfRuntime (runtimeStateOf state) = state := by
  cases state <;> simp [stateOfRuntime, runtimeStateOf]

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

theorem runtime_allDigits_iff (text : String) :
    Metta.Runtime.allDigits text = true ↔ DigitString text := by
  simp [Metta.Runtime.allDigits, DigitString, Bool.and_eq_true]

private theorem decimalIntegerBody_iff (body : String) (negative : Bool)
    (value : Int) :
    (if Metta.Runtime.allDigits body then
      body.toNat?.map fun magnitude =>
        if negative then -Int.ofNat magnitude else Int.ofNat magnitude
    else none) = some value ↔
      DigitString body ∧ ∃ magnitude,
        body.toNat? = some magnitude ∧
        value = if negative then
          -Int.ofNat magnitude else Int.ofNat magnitude := by
  by_cases digits : Metta.Runtime.allDigits body = true
  · have digitMeaning := (runtime_allDigits_iff body).1 digits
    cases body.toNat?
    · simp [digits, digitMeaning]
    · simp [digits, digitMeaning, eq_comm]
  · have noMeaning : ¬ DigitString body :=
      fun meaning => digits ((runtime_allDigits_iff body).2 meaning)
    simp [digits, noMeaning]

theorem parseInt?_iff_decimalInteger (token : String) (value : Int) :
    Metta.Runtime.parseInt? token = some value ↔
      DecimalInteger token value := by
  simp only [Metta.Runtime.parseInt?, DecimalInteger]
  split <;> apply decimalIntegerBody_iff

theorem parseInt?_eq_none_iff (token : String) :
    Metta.Runtime.parseInt? token = none ↔
      ¬ ∃ value, DecimalInteger token value := by
  cases run : Metta.Runtime.parseInt? token with
  | none =>
      constructor
      · intro _ ⟨value, meaning⟩
        have succeeds := (parseInt?_iff_decimalInteger token value).2 meaning
        rw [run] at succeeds
        contradiction
      · intro _
        rfl
  | some value =>
      constructor
      · intro impossible
        contradiction
      · intro noMeaning
        exact False.elim (noMeaning
          ⟨value, (parseInt?_iff_decimalInteger token value).1 run⟩)

private theorem decimalMantissaOne_iff (digits : String)
    (parsedNegative expectedNegative : Bool)
    (magnitude fractionalDigits : Nat) :
    (if Metta.Runtime.allDigits digits then
      digits.toNat?.map fun value => (parsedNegative, value, 0)
    else none) = some (expectedNegative, magnitude, fractionalDigits) ↔
      expectedNegative = parsedNegative ∧ DigitString digits ∧
        digits.toNat? = some magnitude ∧ fractionalDigits = 0 := by
  by_cases valid : Metta.Runtime.allDigits digits = true
  · have meaning := (runtime_allDigits_iff digits).1 valid
    cases digits.toNat?
    · simp [valid, meaning]
    · simp [valid, meaning, eq_comm]
  · have noMeaning : ¬ DigitString digits :=
      fun meaning => valid ((runtime_allDigits_iff digits).2 meaning)
    simp [valid, noMeaning]

private theorem decimalMantissaTwo_iff (integerPart fractionalPart : String)
    (parsedNegative expectedNegative : Bool)
    (magnitude fractionalDigits : Nat) :
    (if Metta.Runtime.allDigits integerPart &&
        Metta.Runtime.allDigits fractionalPart then
      (integerPart ++ fractionalPart).toNat?.map fun value =>
        (parsedNegative, value, fractionalPart.length)
    else none) = some (expectedNegative, magnitude, fractionalDigits) ↔
      expectedNegative = parsedNegative ∧ DigitString integerPart ∧
        DigitString fractionalPart ∧
        (integerPart ++ fractionalPart).toNat? = some magnitude ∧
        fractionalDigits = fractionalPart.length := by
  by_cases integerValid : Metta.Runtime.allDigits integerPart = true
  · have integerMeaning :=
      (runtime_allDigits_iff integerPart).1 integerValid
    by_cases fractionalValid :
        Metta.Runtime.allDigits fractionalPart = true
    · have fractionalMeaning :=
        (runtime_allDigits_iff fractionalPart).1 fractionalValid
      cases (integerPart ++ fractionalPart).toNat?
      · simp [integerValid, fractionalValid, integerMeaning,
          fractionalMeaning]
      · simp [integerValid, fractionalValid, integerMeaning,
          fractionalMeaning, eq_comm]
    · have noFractionalMeaning : ¬ DigitString fractionalPart :=
        fun meaning => fractionalValid
          ((runtime_allDigits_iff fractionalPart).2 meaning)
      simp [integerValid, fractionalValid, integerMeaning,
        noFractionalMeaning]
  · have noIntegerMeaning : ¬ DigitString integerPart :=
      fun meaning => integerValid
        ((runtime_allDigits_iff integerPart).2 meaning)
    simp [integerValid, noIntegerMeaning]

theorem parseMantissa?_iff_decimalMantissa (token : String)
    (negative : Bool) (magnitude fractionalDigits : Nat) :
    Metta.Runtime.parseMantissa? token =
        some (negative, magnitude, fractionalDigits) ↔
      DecimalMantissa token negative magnitude fractionalDigits := by
  unfold Metta.Runtime.parseMantissa? DecimalMantissa
  let parsedNegative := token.startsWith "-"
  let parsedPositive := token.startsWith "+"
  let body := if parsedNegative || parsedPositive then
    (token.drop 1).toString else token
  change (match body.splitOn "." with
      | [digits] =>
          if Metta.Runtime.allDigits digits then
            digits.toNat?.map fun value => (parsedNegative, value, 0)
          else none
      | [integerPart, fractionalPart] =>
          if Metta.Runtime.allDigits integerPart &&
              Metta.Runtime.allDigits fractionalPart then
            (integerPart ++ fractionalPart).toNat?.map fun value =>
              (parsedNegative, value, fractionalPart.length)
          else none
      | _ => none) = some (negative, magnitude, fractionalDigits) ↔
    negative = parsedNegative ∧
      match body.splitOn "." with
      | [digits] =>
          DigitString digits ∧ digits.toNat? = some magnitude ∧
            fractionalDigits = 0
      | [integerPart, fractionalPart] =>
          DigitString integerPart ∧ DigitString fractionalPart ∧
            (integerPart ++ fractionalPart).toNat? = some magnitude ∧
            fractionalDigits = fractionalPart.length
      | _ => False
  cases body.splitOn "." with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => exact decimalMantissaOne_iff first _ _ _ _
      | cons second rest =>
          cases rest with
          | nil => exact decimalMantissaTwo_iff first second _ _ _ _
          | cons third rest => simp

theorem parseFloat?_sound {token : String} {value : Float}
    (run : Metta.Runtime.parseFloat? token = some value) :
    DecimalFloat token value := by
  unfold Metta.Runtime.parseFloat? at run
  change (match exponentParts token with
    | [mantissa] =>
        if mantissa.contains "." then
          Metta.Runtime.parseMantissa? mantissa |>.map fun parsed =>
            signedScientific parsed.1 parsed.2.1 parsed.2.2
        else none
    | [mantissa, exponentToken] =>
        match Metta.Runtime.parseMantissa? mantissa,
            Metta.Runtime.parseInt? exponentToken with
        | some (negative, magnitude, fractionalDigits),
            some exponentValue =>
          some (signedExponentScientific negative magnitude
            fractionalDigits exponentValue)
        | _, _ => none
    | _ => none) = some value at run
  cases partsEq : exponentParts token with
  | nil => simp [partsEq] at run
  | cons mantissa rest =>
      cases rest with
      | nil =>
          by_cases hasPoint : mantissa.contains "." = true
          · cases mantissaRun : Metta.Runtime.parseMantissa? mantissa with
            | none => simp [partsEq, hasPoint, mantissaRun] at run
            | some parsed =>
                rcases parsed with ⟨negative, magnitude, fractionalDigits⟩
                have meaning :=
                  (parseMantissa?_iff_decimalMantissa mantissa negative
                    magnitude fractionalDigits).1 mantissaRun
                simp [partsEq, hasPoint, mantissaRun] at run
                subst value
                exact DecimalFloat.fixed partsEq hasPoint meaning
          · simp [partsEq, hasPoint] at run
      | cons exponentToken rest =>
          cases rest with
          | nil =>
              cases mantissaRun : Metta.Runtime.parseMantissa? mantissa with
              | none => simp [partsEq, mantissaRun] at run
              | some parsed =>
                  rcases parsed with ⟨negative, magnitude, fractionalDigits⟩
                  cases exponentRun : Metta.Runtime.parseInt? exponentToken with
                  | none => simp [partsEq, mantissaRun, exponentRun] at run
                  | some exponentValue =>
                      have mantissaMeaning :=
                        (parseMantissa?_iff_decimalMantissa mantissa negative
                          magnitude fractionalDigits).1 mantissaRun
                      have exponentMeaning :=
                        (parseInt?_iff_decimalInteger exponentToken
                          exponentValue).1 exponentRun
                      simp [partsEq, mantissaRun, exponentRun] at run
                      subst value
                      exact DecimalFloat.exponent partsEq mantissaMeaning
                        exponentMeaning
          | cons third rest => simp [partsEq] at run

theorem parseFloat?_complete {token : String} {value : Float}
    (derivation : DecimalFloat token value) :
    Metta.Runtime.parseFloat? token = some value := by
  cases derivation with
  | @fixed mantissa negative magnitude fractionalDigits
      parts hasPoint mantissaMeaning =>
      have mantissaRun :=
        (parseMantissa?_iff_decimalMantissa mantissa negative magnitude
          fractionalDigits).2 mantissaMeaning
      unfold Metta.Runtime.parseFloat?
      change (match exponentParts token with
        | [part] =>
            if part.contains "." then
              Metta.Runtime.parseMantissa? part |>.map fun parsed =>
                signedScientific parsed.1 parsed.2.1 parsed.2.2
            else none
        | [part, exponentToken] =>
            match Metta.Runtime.parseMantissa? part,
                Metta.Runtime.parseInt? exponentToken with
            | some (parsedNegative, parsedMagnitude,
                parsedFractionalDigits), some exponentValue =>
              some (signedExponentScientific parsedNegative parsedMagnitude
                parsedFractionalDigits exponentValue)
            | _, _ => none
        | _ => none) = some
          (signedScientific negative magnitude fractionalDigits)
      rw [parts]
      simp [hasPoint, mantissaRun]
  | @exponent mantissa exponentToken negative magnitude
      fractionalDigits exponentValue parts mantissaMeaning exponentMeaning =>
      have mantissaRun :=
        (parseMantissa?_iff_decimalMantissa mantissa negative magnitude
          fractionalDigits).2 mantissaMeaning
      have exponentRun :=
        (parseInt?_iff_decimalInteger exponentToken exponentValue).2
          exponentMeaning
      unfold Metta.Runtime.parseFloat?
      change (match exponentParts token with
        | [part] =>
            if part.contains "." then
              Metta.Runtime.parseMantissa? part |>.map fun parsed =>
                signedScientific parsed.1 parsed.2.1 parsed.2.2
            else none
        | [part, parsedExponentToken] =>
            match Metta.Runtime.parseMantissa? part,
                Metta.Runtime.parseInt? parsedExponentToken with
            | some (parsedNegative, parsedMagnitude,
                parsedFractionalDigits), some parsedExponentValue =>
              some (signedExponentScientific parsedNegative parsedMagnitude
                parsedFractionalDigits parsedExponentValue)
            | _, _ => none
        | _ => none) = some
          (signedExponentScientific negative magnitude fractionalDigits
            exponentValue)
      rw [parts]
      simp [mantissaRun, exponentRun]

theorem parseFloat?_iff_decimalFloat (token : String) (value : Float) :
    Metta.Runtime.parseFloat? token = some value ↔
      DecimalFloat token value :=
  ⟨parseFloat?_sound, parseFloat?_complete⟩

theorem parseFloat?_eq_none_iff (token : String) :
    Metta.Runtime.parseFloat? token = none ↔
      ¬ ∃ value, DecimalFloat token value := by
  cases run : Metta.Runtime.parseFloat? token with
  | none =>
      constructor
      · intro _ ⟨value, meaning⟩
        have succeeds := parseFloat?_complete meaning
        rw [run] at succeeds
        contradiction
      · intro _
        rfl
  | some value =>
      constructor
      · intro impossible
        contradiction
      · intro noMeaning
        exact False.elim (noMeaning ⟨value, parseFloat?_sound run⟩)

/-- Every token receives a meaning in the independent priority relation. -/
theorem parseTokenAt_sound (position : Nat) (token : String) :
    TokenDenotes position token
      (Metta.Runtime.parseTokenAt position token) := by
  by_cases anonymous : token = "$_"
  · subst token
    simp only [Metta.Runtime.parseTokenAt, beq_self_eq_true, if_true]
    exact TokenDenotes.anonymous position
  · simp only [Metta.Runtime.parseTokenAt, beq_iff_eq, anonymous, if_false]
    unfold Metta.Runtime.parseAtomToken
    by_cases dollar : token.startsWith "$" = true
    · rw [if_pos dollar]
      exact TokenDenotes.namedVariable anonymous dollar
    · rw [if_neg dollar]
      have dollarFalse : token.startsWith "$" = false :=
        Bool.eq_false_iff.mpr dollar
      by_cases isTrue : token = "True"
      · subst token
        rw [if_pos (by simp)]
        exact TokenDenotes.trueLiteral position
      · rw [if_neg (by simpa using isTrue)]
        by_cases isFalse : token = "False"
        · subst token
          rw [if_pos (by simp)]
          exact TokenDenotes.falseLiteral position
        · rw [if_neg (by simpa using isFalse)]
          by_cases isEmpty : token = "()"
          · subst token
            rw [if_pos (by simp)]
            exact TokenDenotes.emptyExpression position
          · rw [if_neg (by simpa using isEmpty)]
            by_cases quote : token.startsWith "\"" = true
            · rw [if_pos quote]
              exact TokenDenotes.string
                ⟨dollarFalse, isTrue, isFalse, isEmpty⟩ quote
            · rw [if_neg quote]
              have quoteFalse : token.startsWith "\"" = false :=
                Bool.eq_false_iff.mpr quote
              have before : BeforeNumber token :=
                ⟨dollarFalse, isTrue, isFalse, isEmpty, quoteFalse⟩
              cases integerRun : Metta.Runtime.parseInt? token with
              | some value =>
                  exact TokenDenotes.integer before
                    ((parseInt?_iff_decimalInteger token value).1 integerRun)
              | none =>
                  have noInteger :=
                    (parseInt?_eq_none_iff token).1 integerRun
                  cases floatRun : Metta.Runtime.parseFloat? token with
                  | some value =>
                      exact TokenDenotes.float before noInteger
                        (parseFloat?_sound floatRun)
                  | none =>
                      exact TokenDenotes.symbol before noInteger
                        ((parseFloat?_eq_none_iff token).1 floatRun)

/-- The independent token relation determines exactly the executable atom. -/
theorem parseTokenAt_complete {position : Nat} {token : String} {atom : Atom}
    (derivation : TokenDenotes position token atom) :
    Metta.Runtime.parseTokenAt position token = atom := by
  cases derivation with
  | anonymous => simp [Metta.Runtime.parseTokenAt]
  | namedVariable notAnonymous startsDollar =>
      simp [Metta.Runtime.parseTokenAt, notAnonymous,
        Metta.Runtime.parseAtomToken, startsDollar]
  | trueLiteral =>
      simp [Metta.Runtime.parseTokenAt, Metta.Runtime.parseAtomToken]
  | falseLiteral =>
      simp [Metta.Runtime.parseTokenAt, Metta.Runtime.parseAtomToken]
  | emptyExpression =>
      simp [Metta.Runtime.parseTokenAt, Metta.Runtime.parseAtomToken]
  | string before startsQuote =>
      rcases before with ⟨noDollar, notTrue, notFalse, notEmpty⟩
      have notAnonymous : token ≠ "$_" := by
        intro equal
        subst token
        simp at noDollar
      simp [Metta.Runtime.parseTokenAt, notAnonymous,
        Metta.Runtime.parseAtomToken, noDollar, notTrue, notFalse,
        notEmpty, startsQuote]
  | integer before meaning =>
      rcases before with
        ⟨noDollar, notTrue, notFalse, notEmpty, noQuote⟩
      have notAnonymous : token ≠ "$_" := by
        intro equal
        subst token
        simp at noDollar
      have integerRun :=
        (parseInt?_iff_decimalInteger _ _).2 meaning
      simp [Metta.Runtime.parseTokenAt, notAnonymous,
        Metta.Runtime.parseAtomToken, noDollar, notTrue, notFalse,
        notEmpty, noQuote, integerRun]
  | float before notInteger meaning =>
      rcases before with
        ⟨noDollar, notTrue, notFalse, notEmpty, noQuote⟩
      have notAnonymous : token ≠ "$_" := by
        intro equal
        subst token
        simp at noDollar
      have integerRun := (parseInt?_eq_none_iff _).2 notInteger
      have floatRun := parseFloat?_complete meaning
      simp [Metta.Runtime.parseTokenAt, notAnonymous,
        Metta.Runtime.parseAtomToken, noDollar, notTrue, notFalse,
        notEmpty, noQuote, integerRun, floatRun]
  | symbol before notInteger notFloat =>
      rcases before with
        ⟨noDollar, notTrue, notFalse, notEmpty, noQuote⟩
      have notAnonymous : token ≠ "$_" := by
        intro equal
        subst token
        simp at noDollar
      have integerRun := (parseInt?_eq_none_iff _).2 notInteger
      have floatRun := (parseFloat?_eq_none_iff _).2 notFloat
      simp [Metta.Runtime.parseTokenAt, notAnonymous,
        Metta.Runtime.parseAtomToken, noDollar, notTrue, notFalse,
        notEmpty, noQuote, integerRun, floatRun]

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

theorem runtime_bangBoundary_iff (next : Option Char) :
    next.elim true (fun c => c == '(' || Metta.Runtime.isSpace c) = true ↔
      BangBoundary next := by
  cases next with
  | none => simp [BangBoundary]
  | some c =>
      simp [BangBoundary, Bool.or_eq_true, runtime_isSpace_iff]

/-- Every derivation of the independent lexical relation is executed by the
runtime tokenizer, for arbitrary pre-existing reverse token accumulator. -/
theorem tokenizeAux_complete {mode : ReaderMode} {state : LexState}
    {input : List Char} {suffix : List String}
    (derivation : Lexes mode state input suffix) (tokens : List String) :
    Metta.Runtime.tokenizeAux (commentsOfMode mode) (runtimeStateOf state)
        tokens input =
      .ok (tokens.reverse ++ suffix) := by
  induction derivation generalizing tokens with
  | doneSymbol mode chars =>
      simp [Metta.Runtime.tokenizeAux, runtimeStateOf, reverse_flushSym]
  | doneComment mode =>
      simp [Metta.Runtime.tokenizeAux, runtimeStateOf]
  | commentNewline tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf] using ih tokens
  | commentChar notNewline tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf, notNewline] using ih tokens
  | escapedChar tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf, List.reverse_append,
        runtime_decodeStringEscape_eq] using ih tokens
  | beginEscape tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf] using ih tokens
  | @closeString mode chars input suffix tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf, stringToken,
        List.append_assoc] using ih (stringToken chars :: tokens)
  | stringChar notSlash notQuote tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf, notSlash, notQuote,
        List.reverse_append] using ih tokens
  | @symbolBlank mode chars c input suffix blank tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        (runtime_isSpace_iff _).2 blank, reverse_flushSym,
        List.append_assoc] using ih
          (Metta.Runtime.flushSym chars.reverse tokens)
  | @sourceComment chars input suffix tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf, commentsOfMode,
        Metta.Runtime.isSpace, reverse_flushSym, List.append_assoc] using
        ih (Metta.Runtime.flushSym chars.reverse tokens)
  | openString tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        Metta.Runtime.isSpace, Metta.Runtime.flushSym] using ih tokens
  | @leftParen mode chars input suffix tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        Metta.Runtime.isSpace, reverse_flushSym, List.append_assoc] using
        ih ("(" :: Metta.Runtime.flushSym chars.reverse tokens)
  | @rightParen mode chars input suffix tail ih =>
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        Metta.Runtime.isSpace, reverse_flushSym, List.append_assoc] using
        ih (")" :: Metta.Runtime.flushSym chars.reverse tokens)
  | @standaloneBang mode input suffix boundary tail ih =>
      have boundaryTrue :
          input.head?.elim true (fun c =>
            c == '(' || (c == ' ' || c == '\n' || c == '\t' || c == '\r')) =
            true := by
        simpa [Metta.Runtime.isSpace] using
          (runtime_bangBoundary_iff input.head?).2 boundary
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        Metta.Runtime.isSpace, boundaryTrue, List.append_assoc] using
        ih ("!" :: tokens)
  | @symbolChar mode chars c input suffix notBlank notSourceComment
      notOpenString notLeftParen notRightParen notStandaloneBang tail ih =>
      have noComment :
          ¬ (commentsOfMode mode = true ∧ c = ';') := by
        cases mode <;> simp [commentsOfMode] at notSourceComment ⊢
        exact notSourceComment
      have noOpenString : ¬ (c = '"' ∧ chars = []) := by
        intro both
        rcases notOpenString with charsNonempty | notQuote
        · exact charsNonempty both.2
        · exact notQuote both.1
      have noStandaloneBang :
          ¬ ((c = '!' ∧ chars = []) ∧ BangBoundary input.head?) := by
        intro both
        rcases notStandaloneBang with charsNonempty | notBang | notBoundary
        · exact charsNonempty both.1.2
        · exact notBang both.1.1
        · exact notBoundary both.2
      simpa [Metta.Runtime.tokenizeAux, runtimeStateOf,
        (runtime_isSpace_eq_false_iff _).2 notBlank, List.reverse_append,
        noComment, noOpenString, notLeftParen, notRightParen,
        noStandaloneBang, runtime_bangBoundary_iff] using ih tokens

/-- Every successful executable tokenization has a derivation in the
independent lexical relation. The suffix excludes the caller's pre-existing
reverse accumulator, making this statement compositional. -/
theorem tokenizeAux_sound (comments : Bool) (state : Metta.Runtime.TokState)
    (tokens : List String) (input : List Char) (output : List String)
    (run : Metta.Runtime.tokenizeAux comments state tokens input = .ok output) :
    ∃ suffix,
      Lexes (modeOfComments comments) (stateOfRuntime state) input suffix ∧
      output = tokens.reverse ++ suffix := by
  induction input generalizing state tokens output with
  | nil =>
      cases state with
      | sym chars =>
          simp [Metta.Runtime.tokenizeAux] at run
          subst output
          exact ⟨emitSymbol chars.reverse, Lexes.doneSymbol _ _,
            reverse_flushSym chars tokens⟩
      | str chars escaped =>
          simp [Metta.Runtime.tokenizeAux] at run
      | comment =>
          simp [Metta.Runtime.tokenizeAux] at run
          subst output
          exact ⟨[], Lexes.doneComment _, by simp⟩
  | cons c input ih =>
      cases state with
      | comment =>
          by_cases newline : c = '\n'
          · have recurse := run
            simp [Metta.Runtime.tokenizeAux, newline] at recurse
            obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
            subst c
            exact ⟨suffix, Lexes.commentNewline tail, result⟩
          · have recurse := run
            simp [Metta.Runtime.tokenizeAux, newline] at recurse
            obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
            exact ⟨suffix, Lexes.commentChar newline tail, result⟩
      | str chars escaped =>
          cases escaped with
          | true =>
              have recurse := run
              simp [Metta.Runtime.tokenizeAux] at recurse
              obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
              have tail' :
                  Lexes (modeOfComments comments)
                    (.string (chars.reverse ++ [decodeEscape c]) false)
                    input suffix := by
                simpa [stateOfRuntime, List.reverse_cons,
                  runtime_decodeStringEscape_eq] using tail
              exact ⟨suffix, Lexes.escapedChar tail', result⟩
          | false =>
              by_cases slash : c = '\\'
              · have recurse := run
                simp [Metta.Runtime.tokenizeAux, slash] at recurse
                obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                subst c
                exact ⟨suffix, Lexes.beginEscape tail, result⟩
              · by_cases quote : c = '"'
                · have recurse := run
                  simp [Metta.Runtime.tokenizeAux, quote] at recurse
                  obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                  subst c
                  refine ⟨stringToken chars.reverse :: suffix,
                    Lexes.closeString tail, ?_⟩
                  simpa [stringToken, List.append_assoc] using result
                · have recurse := run
                  simp [Metta.Runtime.tokenizeAux, slash, quote] at recurse
                  obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                  have tail' :
                      Lexes (modeOfComments comments)
                        (.string (chars.reverse ++ [c]) false) input suffix := by
                    simpa [stateOfRuntime, List.reverse_cons] using tail
                  exact ⟨suffix, Lexes.stringChar slash quote tail', result⟩
      | sym chars =>
          by_cases blank : Metta.Runtime.isSpace c = true
          · have recurse := run
            simp [Metta.Runtime.tokenizeAux, blank] at recurse
            obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
            refine ⟨emitSymbol chars.reverse ++ suffix,
              Lexes.symbolBlank ((runtime_isSpace_iff c).1 blank) tail, ?_⟩
            simpa [reverse_flushSym, List.append_assoc] using result
          · by_cases startsComment : (comments && c == ';') = true
            · have parts : comments = true ∧ c = ';' := by
                simpa using startsComment
              have commentsTrue : comments = true := parts.1
              have semicolon : c = ';' := by simpa using parts.2
              subst comments
              subst c
              have recurse := run
              simp [Metta.Runtime.tokenizeAux, Metta.Runtime.isSpace] at recurse
              obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
              refine ⟨emitSymbol chars.reverse ++ suffix,
                Lexes.sourceComment tail, ?_⟩
              simpa [reverse_flushSym, List.append_assoc] using result
            · by_cases startsString : (c == '"' && chars.isEmpty) = true
              · have parts : c = '"' ∧ chars = [] := by
                  simpa using startsString
                have quote : c = '"' := by simpa using parts.1
                have charsEmpty : chars = [] := by simpa using parts.2
                subst c
                subst chars
                have recurse := run
                simp [Metta.Runtime.tokenizeAux, Metta.Runtime.isSpace] at recurse
                obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                exact ⟨suffix, Lexes.openString tail,
                  by simpa [Metta.Runtime.flushSym] using result⟩
              · by_cases parenthesis : (c == '(' || c == ')') = true
                · have recurse := run
                  simp [Metta.Runtime.tokenizeAux, blank, startsComment,
                    startsString, parenthesis] at recurse
                  obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                  have parts : c = '(' ∨ c = ')' := by
                    simpa using parenthesis
                  rcases parts with left | right
                  · have left' : c = '(' := by simpa using left
                    subst c
                    refine ⟨emitSymbol chars.reverse ++ "(" :: suffix,
                      Lexes.leftParen tail, ?_⟩
                    simpa [reverse_flushSym, List.append_assoc] using result
                  · have right' : c = ')' := by simpa using right
                    subst c
                    refine ⟨emitSymbol chars.reverse ++ ")" :: suffix,
                      Lexes.rightParen tail, ?_⟩
                    simpa [reverse_flushSym, List.append_assoc] using result
                · by_cases startsBang :
                    (c == '!' && chars.isEmpty &&
                      input.head?.elim true (fun d =>
                        d == '(' || Metta.Runtime.isSpace d)) = true
                  · have recurse := run
                    simp [Metta.Runtime.tokenizeAux, blank, startsComment,
                      startsString, parenthesis, startsBang] at recurse
                    obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                    have parts :
                        (c = '!' ∧ chars = []) ∧
                          input.head?.elim true (fun d =>
                            d == '(' || Metta.Runtime.isSpace d) = true := by
                      simpa using startsBang
                    have cBang : c = '!' := parts.1.1
                    have charsEmpty : chars = [] := parts.1.2
                    have boundary : BangBoundary input.head? :=
                      (runtime_bangBoundary_iff input.head?).1
                        parts.2
                    subst c
                    subst chars
                    refine ⟨"!" :: suffix,
                      Lexes.standaloneBang boundary tail, ?_⟩
                    simpa [List.append_assoc] using result
                  · have recurse := run
                    simp [Metta.Runtime.tokenizeAux, blank, startsComment,
                      startsString, parenthesis, startsBang] at recurse
                    obtain ⟨suffix, tail, result⟩ := ih _ _ _ recurse
                    have notBlank : ¬ IsBlank c := by
                      intro isBlank
                      exact blank ((runtime_isSpace_iff c).2 isBlank)
                    have notSourceComment :
                        modeOfComments comments ≠ .source ∨ c ≠ ';' := by
                      cases comments with
                      | false => simp [modeOfComments]
                      | true =>
                          right
                          intro semicolon
                          apply startsComment
                          simp [semicolon]
                    have notOpenString : chars.reverse ≠ [] ∨ c ≠ '"' := by
                      by_cases charsEmpty : chars = []
                      · right
                        intro quote
                        apply startsString
                        simp [charsEmpty, quote]
                      · left
                        simpa using charsEmpty
                    have notLeftParen : c ≠ '(' := by
                      intro left
                      apply parenthesis
                      simp [left]
                    have notRightParen : c ≠ ')' := by
                      intro right
                      apply parenthesis
                      simp [right]
                    have notBang :
                        chars.reverse ≠ [] ∨ c ≠ '!' ∨
                          ¬ BangBoundary input.head? := by
                      by_cases charsEmpty : chars = []
                      · by_cases cBang : c = '!'
                        · right; right
                          intro boundary
                          apply startsBang
                          have boundaryTrue :=
                            (runtime_bangBoundary_iff input.head?).2 boundary
                          simp [charsEmpty, cBang, boundaryTrue]
                        · exact Or.inr (Or.inl cBang)
                      · exact Or.inl (by simpa using charsEmpty)
                    have tail' :
                        Lexes (modeOfComments comments)
                          (.symbol (chars.reverse ++ [c])) input suffix := by
                      simpa [stateOfRuntime, List.reverse_cons] using tail
                    exact ⟨suffix,
                      Lexes.symbolChar notBlank notSourceComment notOpenString
                        notLeftParen notRightParen notBang tail',
                      result⟩

theorem tokenize_iff_sourceLexes (source : String) (tokens : List String) :
    Metta.Runtime.tokenize source = .ok tokens ↔ SourceLexes source tokens := by
  constructor
  · intro run
    have runAux :
        Metta.Runtime.tokenizeAux true (.sym []) [] source.toList =
          .ok tokens := by
      simpa [Metta.Runtime.tokenize] using run
    obtain ⟨suffix, derivation, result⟩ :=
      tokenizeAux_sound true (.sym []) [] source.toList tokens runAux
    simp at result
    subst tokens
    simpa [SourceLexes, modeOfComments, stateOfRuntime] using derivation
  · intro derivation
    unfold SourceLexes at derivation
    simpa [Metta.Runtime.tokenize, commentsOfMode, runtimeStateOf] using
      tokenizeAux_complete derivation []

theorem tokenizeSExpr_iff_runtimeLexes (source : String)
    (tokens : List String) :
    Metta.Runtime.tokenizeSExpr source = .ok tokens ↔
      RuntimeLexes source tokens := by
  constructor
  · intro run
    have runAux :
        Metta.Runtime.tokenizeAux false (.sym []) [] source.toList =
          .ok tokens := by
      simpa [Metta.Runtime.tokenizeSExpr] using run
    obtain ⟨suffix, derivation, result⟩ :=
      tokenizeAux_sound false (.sym []) [] source.toList tokens runAux
    simp at result
    subst tokens
    simpa [RuntimeLexes, modeOfComments, stateOfRuntime] using derivation
  · intro derivation
    unfold RuntimeLexes at derivation
    simpa [Metta.Runtime.tokenizeSExpr, commentsOfMode, runtimeStateOf] using
      tokenizeAux_complete derivation []

theorem tokenize_error_has_no_source_derivation {source error}
    (run : Metta.Runtime.tokenize source = .error error) :
    ¬ ∃ tokens, SourceLexes source tokens := by
  rintro ⟨tokens, derivation⟩
  have succeeds := (tokenize_iff_sourceLexes source tokens).2 derivation
  rw [run] at succeeds
  contradiction

theorem tokenizeSExpr_error_has_no_runtime_derivation {source error}
    (run : Metta.Runtime.tokenizeSExpr source = .error error) :
    ¬ ∃ tokens, RuntimeLexes source tokens := by
  rintro ⟨tokens, derivation⟩
  have succeeds :=
    (tokenizeSExpr_iff_runtimeLexes source tokens).2 derivation
  rw [run] at succeeds
  contradiction

theorem parseTokens_complete {Leaf : Nat → String → Atom → Prop}
    {stack : List (List Atom)} {tokens : List String} {output : List Atom}
    (derivation : ParsesTokens Leaf stack tokens output)
    (leafComplete : ∀ position token atom,
      Leaf position token atom →
        Metta.Runtime.parseTokenAt position token = atom) :
    Metta.Runtime.parseTokens stack tokens = .ok output := by
  induction derivation with
  | done top => rfl
  | push tail ih =>
      simpa [Metta.Runtime.parseTokens] using ih
  | pop tail ih =>
      simpa [Metta.Runtime.parseTokens] using ih
  | leaf notOpen notClose denotes tail ih =>
      have leafEq := leafComplete _ _ _ denotes
      simpa [Metta.Runtime.parseTokens, notOpen, notClose, leafEq] using ih

theorem parseTokens_sound {Leaf : Nat → String → Atom → Prop}
    (leafSound : ∀ position token,
      Leaf position token (Metta.Runtime.parseTokenAt position token))
    (stack : List (List Atom)) (tokens : List String) (output : List Atom)
    (run : Metta.Runtime.parseTokens stack tokens = .ok output) :
    ParsesTokens Leaf stack tokens output := by
  induction tokens generalizing stack output with
  | nil =>
      cases stack with
      | nil => simp [Metta.Runtime.parseTokens] at run
      | cons top more =>
          cases more with
          | nil =>
              simp [Metta.Runtime.parseTokens] at run
              subst output
              exact ParsesTokens.done top
          | cons outer more =>
              simp [Metta.Runtime.parseTokens] at run
  | cons token rest ih =>
      by_cases openToken : token = "("
      · subst token
        have recurse :
            Metta.Runtime.parseTokens ([] :: stack) rest = .ok output := by
          simpa [Metta.Runtime.parseTokens] using run
        exact ParsesTokens.push (ih _ _ recurse)
      · by_cases closeToken : token = ")"
        · subst token
          cases stack with
          | nil => simp [Metta.Runtime.parseTokens] at run
          | cons inner outerAndMore =>
              cases outerAndMore with
              | nil => simp [Metta.Runtime.parseTokens] at run
              | cons outer more =>
                  have recurse :
                      Metta.Runtime.parseTokens
                          ((Atom.expr inner.reverse :: outer) :: more) rest =
                        .ok output := by
                    simpa [Metta.Runtime.parseTokens] using run
                  exact ParsesTokens.pop (ih _ _ recurse)
        · cases stack with
          | nil =>
              simp [Metta.Runtime.parseTokens] at run
          | cons top more =>
              have recurse :
                  Metta.Runtime.parseTokens
                      ((Metta.Runtime.parseTokenAt rest.length token :: top) :: more)
                      rest = .ok output := by
                simpa [Metta.Runtime.parseTokens, openToken, closeToken] using run
              exact ParsesTokens.leaf openToken closeToken
                (leafSound rest.length token) (ih _ _ recurse)

/-- Conditional source-reader soundness.  The lexical and parenthesis layers
are fully discharged here; `leafSound` is deliberately explicit until token
meaning has its own independent adequacy proof. -/
theorem parseProgram_sound {Leaf : Nat → String → Atom → Prop}
    (leafSound : ∀ position token,
      Leaf position token (Metta.Runtime.parseTokenAt position token))
    {source : String} {output : List Atom}
    (run : Metta.Runtime.parseProgram source = .ok output) :
    ReadsProgram Leaf source output := by
  cases tokenRun : Metta.Runtime.tokenize source with
  | error error =>
      rw [Metta.Runtime.parseProgram, tokenRun] at run
      contradiction
  | ok tokens =>
      have treeRun :
          Metta.Runtime.parseTokens [[]] tokens = .ok output := by
        rw [Metta.Runtime.parseProgram, tokenRun] at run
        exact run
      exact ⟨tokens,
        (tokenize_iff_sourceLexes source tokens).1 tokenRun,
        parseTokens_sound leafSound [[]] tokens output treeRun⟩

/-- Conditional source-reader completeness, with the same explicit leaf-token
obligation as `parseProgram_sound`. -/
theorem parseProgram_complete {Leaf : Nat → String → Atom → Prop}
    (leafComplete : ∀ position token atom,
      Leaf position token atom →
        Metta.Runtime.parseTokenAt position token = atom)
    {source : String} {output : List Atom}
    (derivation : ReadsProgram Leaf source output) :
    Metta.Runtime.parseProgram source = .ok output := by
  obtain ⟨tokens, lexical, structural⟩ := derivation
  have tokenRun := (tokenize_iff_sourceLexes source tokens).2 lexical
  have treeRun := parseTokens_complete structural leafComplete
  rw [Metta.Runtime.parseProgram, tokenRun]
  exact treeRun

/-- Conditional runtime-`sread` soundness.  Requiring a singleton structural
result makes whole-input, exactly-one-expression behavior part of the
judgment rather than a post-hoc test. -/
theorem parseSExpr_sound {Leaf : Nat → String → Atom → Prop}
    (leafSound : ∀ position token,
      Leaf position token (Metta.Runtime.parseTokenAt position token))
    {source : String} {output : Atom}
    (run : Metta.Runtime.parseSExpr source = .ok output) :
    ReadsSExpr Leaf source output := by
  cases tokenRun : Metta.Runtime.tokenizeSExpr source with
  | error error =>
      rw [Metta.Runtime.parseSExpr, tokenRun] at run
      simp only [Bind.bind, Except.bind] at run
      contradiction
  | ok tokens =>
      rw [Metta.Runtime.parseSExpr, tokenRun] at run
      simp only [Bind.bind, Except.bind] at run
      cases treeRun : Metta.Runtime.parseTokens [[]] tokens with
      | error error =>
          rw [treeRun] at run
          contradiction
      | ok parsed =>
          rw [treeRun] at run
          cases parsed with
          | nil =>
              contradiction
          | cons atom rest =>
              cases rest with
              | nil =>
                  injection run with atomEq
                  subst output
                  exact ⟨tokens,
                    (tokenizeSExpr_iff_runtimeLexes source tokens).1 tokenRun,
                    parseTokens_sound leafSound [[]] tokens [atom] treeRun⟩
              | cons second rest =>
                  contradiction

/-- Conditional runtime-`sread` completeness. -/
theorem parseSExpr_complete {Leaf : Nat → String → Atom → Prop}
    (leafComplete : ∀ position token atom,
      Leaf position token atom →
        Metta.Runtime.parseTokenAt position token = atom)
    {source : String} {output : Atom}
    (derivation : ReadsSExpr Leaf source output) :
    Metta.Runtime.parseSExpr source = .ok output := by
  obtain ⟨tokens, lexical, structural⟩ := derivation
  have tokenRun := (tokenizeSExpr_iff_runtimeLexes source tokens).2 lexical
  have treeRun := parseTokens_complete structural leafComplete
  rw [Metta.Runtime.parseSExpr, tokenRun]
  simp only [Bind.bind, Except.bind]
  rw [treeRun]

/-- End-to-end executable/source-reader adequacy for the independently defined
token, lexical, and structural judgments.  This describes PLeaTTa's source
reader; equivalence with pinned PeTTa's distinct file loader is a subsequent
source-loader theorem. -/
theorem parseProgram_iff_readsProgram (source : String) (output : List Atom) :
    Metta.Runtime.parseProgram source = .ok output ↔
      ReadsProgram TokenDenotes source output :=
  ⟨parseProgram_sound parseTokenAt_sound,
    parseProgram_complete (fun _ _ _ => parseTokenAt_complete)⟩

/-- End-to-end adequacy of executable runtime `sread` against the independent
reader relation. -/
theorem parseSExpr_iff_readsSExpr (source : String) (output : Atom) :
    Metta.Runtime.parseSExpr source = .ok output ↔
      ReadsSExpr TokenDenotes source output :=
  ⟨parseSExpr_sound parseTokenAt_sound,
    parseSExpr_complete (fun _ _ _ => parseTokenAt_complete)⟩

end PLeaTTa.ReaderAdequacy
