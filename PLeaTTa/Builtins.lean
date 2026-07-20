-- SPDX-License-Identifier: Apache-2.0

/-
PLeaTTa builtin table: Core arithmetic/comparison/equality pass through;
tuple operations are CHAIN versions (values are cons-chains). `and`/`or`/
`not` are NOT builtins — they are prelude relations (truth tables), so
boolean constraint enumeration works exactly as in native PeTTa.
-/
import PLeaTTa.Chain
import MettaHyperonFull.Core.Alpha
import MettaHyperonFull.Core.Builtins
import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.FreeVars
import MettaHyperonFull.Runtime.Parser
import MettaHyperonFull.Core.Grounding

namespace PLeaTTa

open Metta (Atom Ground GroundingTable GroundMode ReduceResult)

private def chainList : Atom → Option (List Atom)
  | Atom.sym "#nil" => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainList t).map (h :: ·)
  | _ => none

def carC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some (h :: _) => .ok [h]
    | _ => .ok [nilA]
  | _ => .incorrectArgument "car-atom"

def cdrC : List Atom → ReduceResult
  | [a] => match a with
    | Atom.expr [Atom.sym "#c", _, t] => .ok [t]
    | _ => .ok [nilA]
  | _ => .incorrectArgument "cdr-atom"

def lastC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some [] => .incorrectArgument "last"
    | some l => .ok [l.getLast!]
    | none => .incorrectArgument "last"
  | _ => .incorrectArgument "last"

def consAtomC : List Atom → ReduceResult
  | [h, t] => .ok [consC h t]
  | _ => .incorrectArgument "cons-atom"

def printlnC : List Atom → ReduceResult
  | [_] => .ok [Atom.sym "True"]
  | _ => .incorrectArgument "println!"

/-- PeTTa's `assert/2` succeeds with `true` exactly when its evaluated goal
    succeeds [SPEC metta.pl:211-214]. Host diagnostic text is not a language
    value; a failed assertion follows the existing runtime-error path. -/
def assertOp : List Atom → ReduceResult
  | [value] =>
      if canonBool value == Atom.sym "True" then .ok [Atom.sym "True"]
      else .runtimeError "assertion failed"
  | _ => .incorrectArgument "assert"

private def groundTermIdentical : Ground → Ground → Bool
  | .int left, .int right => left == right
  | .float left, .float right => left.toBits == right.toBits
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .unit, .unit => true
  | .error left, .error right => left == right
  | .external leftTag leftPayload, .external rightTag rightPayload =>
      leftTag == rightTag && leftPayload == rightPayload
  | _, _ => false

mutual
private def atomTermIdentical : Atom → Atom → Bool
  | .sym left, .sym right => left == right
  | .var left, .var right => left == right
  | .gnd left, .gnd right => groundTermIdentical left right
  | .expr left, .expr right => atomListTermIdentical left right
  | _, _ => false

private def atomListTermIdentical : List Atom → List Atom → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      atomTermIdentical left right && atomListTermIdentical lefts rights
  | _, _ => false
end

/-- PeTTa `!=/3`: compare already-evaluated terms without binding them and
    return the negation of Prolog term identity [SPEC metta.pl:42].  This is
    constructor- and float-bit-sensitive: integer `1` is not float `1.0`, and
    signed zeroes are distinct, just as under SWI `==/2`. -/
def notEqualOp : List Atom → ReduceResult
  | [left, right] =>
      .ok [Atom.sym (if atomTermIdentical left right then "False" else "True")]
  | _ => .incorrectArgument "!="

def translatorRuleControlC : List Atom → ReduceResult
  | [_] => .ok [Atom.sym "True"]
  | _ => .incorrectArgument "translator-rule control"

def sizeC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some l => .ok [Atom.gnd (Ground.int l.length)]
    | none => .incorrectArgument "size-atom"
  | _ => .incorrectArgument "size-atom"

def indexC : List Atom → ReduceResult
  | [a, Atom.gnd (Ground.int i)] => match chainList a with
    | some l => match l[i.toNat]? with
      | some x => .ok [x]
      | none => .incorrectArgument "index-atom: out of range"
    | none => .incorrectArgument "index-atom"
  | _ => .incorrectArgument "index-atom"

def deconsC : List Atom → ReduceResult
  | [Atom.expr [Atom.sym "#c", h, t]] => .ok [consC h (consC t nilA)]
  | _ => .incorrectArgument "decons-atom"

private def asFloat : Atom → Option Float
  | Atom.gnd (Ground.int i) => some (Float.ofInt i)
  | Atom.gnd (Ground.float f) => some f
  | _ => none

/-- Binary `min`/`max` [SPEC metta.pl:303 registers min/max as builtins]:
    returns the ORIGINAL extremum atom (ints stay ints, floats floats). -/
def minMaxOp (isMin : Bool) : List Atom → ReduceResult
  | [x, y] => match asFloat x, asFloat y with
    | some a, some b =>
        .ok [if (if isMin then a ≤ b else b ≤ a) then x else y]
    | _, _ => .incorrectArgument "min/max"
  | _ => .incorrectArgument "min/max"

def divOp : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] =>
      if b == 0 then .runtimeError "division by zero"
      else if a % b == 0 then .ok [Atom.gnd (Ground.int (a / b))]
      else .ok [Atom.gnd (Ground.float (Float.ofInt a / Float.ofInt b))]
  | [x, y] => match asFloat x, asFloat y with
    | some a, some b =>
        if b == 0.0 then .runtimeError "division by zero"
        else .ok [Atom.gnd (Ground.float (a / b))]
    | _, _ => .incorrectArgument "/"
  | _ => .incorrectArgument "/"

def modOp : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] =>
      if b == 0 then .runtimeError "mod zero"
      else .ok [Atom.gnd (Ground.int (a % b))]
  | _ => .incorrectArgument "%"

/-- Convert host floating-point domain failures into PeTTa's arithmetic
    exception instead of exposing an IEEE NaN as a language value. -/
private def checkedFloatResult (value : Float) : ReduceResult :=
  if value.isNaN then .runtimeError "undefined"
  else .ok [Atom.gnd (Ground.float value)]

/-- `-math` family with int→float coercion (PeTTa is permissive). -/
def floatUnC (f : Float → Float) : List Atom → ReduceResult
  | [x] => match asFloat x with
    | some a => checkedFloatResult (f a)
    | none => .incorrectArgument "float op"
  | _ => .incorrectArgument "float op"

def floatBinC (f : Float → Float → Float) : List Atom → ReduceResult
  | [x, y] => match asFloat x, asFloat y with
    | some a, some b => checkedFloatResult (f a b)
    | _, _ => .incorrectArgument "float op"
  | _ => .incorrectArgument "float op"

def roundC (f : Float → Float) : List Atom → ReduceResult
  | [x] => match asFloat x with
    | some a => .ok [Atom.gnd (Ground.int (f a).toInt64.toInt)]
    | none => .incorrectArgument "round op"
  | _ => .incorrectArgument "round op"

def reprC : List Atom → ReduceResult
  | [Atom.gnd (Ground.str str)] =>
      -- repr of a string re-quotes with escaping (petta swrite)
      .ok [Atom.gnd (Ground.str (Metta.Pretty.ground (Ground.str str)))]
  | [a] => .ok [Atom.gnd (Ground.str (Metta.Pretty.atom (unchainify 10000 a)))]
  | _ => .incorrectArgument "repr"

/-- `repra/2` [SPEC metta.pl:30,306]: Prolog `term_to_atom`, surfaced as a
    MeTTa atom rather than a string. -/
def repraC : List Atom → ReduceResult
  | [a] => .ok [Atom.sym (Metta.Pretty.atom (unchainify 10000 a))]
  | _ => .incorrectArgument "repra"

private def compareString (a b : String) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

private def atomOrderRank : Atom → Nat
  | Atom.var _ => 0
  | Atom.gnd (Ground.int _) | Atom.gnd (Ground.float _) => 1
  | Atom.gnd _ => 2
  | Atom.sym _ => 3
  | Atom.expr _ => 4

private def compareGround (a b : Ground) : Ordering :=
  match a, b with
  | Ground.int x, Ground.int y => compare x y
  | Ground.int x, Ground.float y =>
      if Float.ofInt x < y then .lt else if y < Float.ofInt x then .gt else .eq
  | Ground.float x, Ground.int y =>
      if x < Float.ofInt y then .lt else if Float.ofInt y < x then .gt else .eq
  | Ground.float x, Ground.float y =>
      if x < y then .lt else if y < x then .gt else .eq
  | _, _ => compareString (Metta.Pretty.ground a) (Metta.Pretty.ground b)

mutual
private def compareAtomFuel : Nat → Atom → Atom → Ordering
  | 0, a, b => compareString (Metta.Pretty.atom a) (Metta.Pretty.atom b)
  | fuel + 1, a, b =>
      let ra := atomOrderRank a
      let rb := atomOrderRank b
      if ra < rb then .lt else if rb < ra then .gt else
      match a, b with
      | Atom.var x, Atom.var y => compareString x y
      | Atom.gnd x, Atom.gnd y => compareGround x y
      | Atom.sym x, Atom.sym y => compareString x y
      | Atom.expr xs, Atom.expr ys => compareAtomListsFuel fuel xs ys
      | _, _ => .eq

private def compareAtomListsFuel : Nat → List Atom → List Atom → Ordering
  | _, [], [] => .eq
  | _, [], _ :: _ => .lt
  | _, _ :: _, [] => .gt
  | 0, x :: xs, y :: ys =>
      compareString (reprStr (x :: xs)) (reprStr (y :: ys))
  | fuel + 1, x :: xs, y :: ys =>
      match compareAtomFuel fuel x y with
      | .eq => compareAtomListsFuel fuel xs ys
      | ord => ord
end

private def cmpAtom (a b : Atom) : Bool :=
  compareAtomFuel (a.size + b.size + 1) a b == .lt

def msortC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some l => .ok [chainOf ((l.map unchainTop).mergeSort cmpAtom |>.map id)]
    | none => .incorrectArgument "msort"
  | _ => .incorrectArgument "msort"
where unchainTop (x : Atom) : Atom := x

def uniqueC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some l =>
        let ded := l.foldl (fun acc x =>
          if acc.contains x then acc else acc ++ [x]) []
        .ok [chainOf ded]
    | none => .incorrectArgument "unique-atom"
  | _ => .incorrectArgument "unique-atom"

def listToSetC : List Atom → ReduceResult
  | [a] => match chainList a with
    | some l =>
        let ded := l.foldl (fun acc x =>
          if acc.contains x then acc else acc ++ [x]) []
        .ok [chainOf ded]
    | none => .incorrectArgument "list_to_set"
  | _ => .incorrectArgument "list_to_set"

def excludeItemC : List Atom → ReduceResult
  | [x, a] => match chainList a with
    | some l => .ok [chainOf (l.filter (fun y => y != x))]
    | none => .incorrectArgument "exclude-item"
  | _ => .incorrectArgument "exclude-item"

def unionC : List Atom → ReduceResult
  | [a, b] => match chainList a, chainList b with
    | some x, some y => .ok [chainOf (x ++ y)]
    | _, _ => .incorrectArgument "union-atom"
  | _ => .incorrectArgument "union-atom"

/-- MULTISET intersection: occurrence-counted (PeTTa bag semantics). -/
def intersectionC : List Atom → ReduceResult
  | [a, b] => match chainList a, chainList b with
    | some x, some y =>
        let (out, _) := x.foldl (fun (acc : List Atom × List Atom) e =>
          if acc.2.contains e then (acc.1 ++ [e], acc.2.erase e) else acc)
          ([], y)
        .ok [chainOf out]
    | _, _ => .incorrectArgument "intersection-atom"
  | _ => .incorrectArgument "intersection-atom"

/-- MULTISET subtraction: removes ONE occurrence per match. -/
def subtractionC : List Atom → ReduceResult
  | [a, b] => match chainList a, chainList b with
    | some x, some y =>
        let (out, _) := x.foldl (fun (acc : List Atom × List Atom) e =>
          if acc.2.contains e then (acc.1, acc.2.erase e)
          else (acc.1 ++ [e], acc.2)) ([], y)
        .ok [chainOf out]
    | _, _ => .incorrectArgument "subtraction-atom"
  | _ => .incorrectArgument "subtraction-atom"

def isVarOp : List Atom → ReduceResult
  | [Atom.var _] => .ok [Atom.sym "True"]
  | [_] => .ok [Atom.sym "False"]
  | _ => .incorrectArgument "is-var"

def isGroundOp : List Atom → ReduceResult
  | [a] => .ok [Atom.sym (if Metta.isGround a then "True" else "False")]
  | _ => .incorrectArgument "is-ground"

def isExprOp : List Atom → ReduceResult
  | [a] => .ok [Atom.sym (if (chainList a).isSome then "True" else "False")]
  | _ => .incorrectArgument "is-expr"

def isSpaceOp : List Atom → ReduceResult
  | [Atom.sym s] => .ok [Atom.sym (if s.startsWith "&" then "True" else "False")]
  | [_] => .ok [Atom.sym "False"]
  | _ => .incorrectArgument "is-space"

/-- Alpha-equivalence on values, preserving repeated-variable identity. -/
def alphaEqOp : List Atom → ReduceResult
  | [a, b] =>
      .ok [Atom.sym (if Metta.alphaEq a b then "True" else "False")]
  | _ => .incorrectArgument "=alpha"

/-- PeTTa's `test/3` compares one answer directly, but compares zero or
    multiple answers as the collected list [SPEC translator.pl:118-126,
    metta.pl:203-207]. Diagnostic output is outside the pure machine. -/
def testResultsOp : List Atom → ReduceResult
  | [results, expected] =>
      match chainList results with
      | some answers =>
          let actual := match answers with
            | [answer] => answer
            | _ => results
          if Metta.alphaEq (canonBools actual) (canonBools expected) then
            .ok [Atom.sym "True"]
          else .runtimeError "test failed"
      | none => .incorrectArgument "test: expected collected results"
  | _ => .incorrectArgument "test"
where
  canonBools : Atom → Atom
    | Atom.expr xs => Atom.expr (xs.map canonBools)
    | a => canonBool a

/-- min/max over a chain, returning the ORIGINAL extremum atom (ints stay
    ints — PeTTa does not coerce). -/
def extremumC (isMin : Bool) : List Atom → ReduceResult
  | [a] => match chainList a with
    | some (h :: t) =>
        let pick := t.foldl (fun best x =>
          match asFloat best, asFloat x with
          | some bv, some xv => if (if isMin then xv < bv else xv > bv) then x else best
          | _, _ => best) h
        .ok [pick]
    | _ => .incorrectArgument "min/max-atom"
  | _ => .incorrectArgument "min/max-atom"

def parseOp : List Atom → ReduceResult
  | [Atom.gnd (Ground.str s)] =>
      match Metta.Runtime.parseSExpr s with
      | .ok a => .ok [chainify a]
      | .error _ => .runtimeError s
  | _ => .incorrectArgument "parse"

def sreadC : List Atom → ReduceResult
  | [Atom.gnd (Ground.str source)] | [Atom.sym source] =>
      match Metta.Runtime.parseSExpr source with
      | .ok atom => .ok [chainify atom]
      | .error _ => .runtimeError source
  | _ => .incorrectArgument "sread"

private def stringLikeText? : Atom → Option String
  | Atom.gnd (Ground.str value) => some value
  | Atom.sym value => some value
  | _ => none

def stringLengthC : List Atom → ReduceResult
  | [value] =>
      match stringLikeText? value with
      | some text => .ok [Atom.gnd (Ground.int text.length)]
      | none => .incorrectArgument "string_length"
  | _ => .incorrectArgument "string_length"

def stringConcatC : List Atom → ReduceResult
  | [left, right] =>
      match stringLikeText? left, stringLikeText? right with
      | some left, some right => .ok [Atom.gnd (Ground.str (left ++ right))]
      | _, _ => .incorrectArgument "string_concat"
  | _ => .incorrectArgument "string_concat"

private def trimCharSet (padding : List Char) (value : List Char) : List Char :=
  let left := value.dropWhile padding.contains
  (left.reverse.dropWhile padding.contains).reverse

private def splitCharSet (separators padding : List Char)
    (value : String) : List String :=
  let rec go : List Char → List Char → List String → List String
    | [], current, parts =>
        (String.ofList (trimCharSet padding current.reverse) :: parts).reverse
    | char :: rest, current, parts =>
        if separators.contains char then
          go rest []
            (String.ofList (trimCharSet padding current.reverse) :: parts)
        else go rest (char :: current) parts
  go value.toList [] []

def splitStringC : List Atom → ReduceResult
  | [value, separators, padding] =>
      match stringLikeText? value, stringLikeText? separators,
          stringLikeText? padding with
      | some value, some separators, some padding =>
          .ok [chainOf <|
            (splitCharSet separators.toList padding.toList value).map
              (fun part => Atom.gnd (Ground.str part))]
      | _, _, _ => .incorrectArgument "split_string"
  | _ => .incorrectArgument "split_string"

private def atomicText? : Atom → Option String
  | Atom.sym value => some value
  | Atom.gnd (Ground.str value) => some value
  | Atom.gnd (Ground.int value) => some (toString value)
  | Atom.gnd (Ground.float value) => some (Metta.Pretty.ground (.float value))
  | _ => none

def atomicListConcatC : List Atom → ReduceResult
  | [items, separator] =>
      match chainList items, atomicText? separator with
      | some atoms, some sep =>
          match atoms.mapM atomicText? with
          | some parts => .ok [Atom.sym (String.intercalate sep parts)]
          | none => .incorrectArgument "atomic_list_concat"
      | _, _ => .incorrectArgument "atomic_list_concat"
  | _ => .incorrectArgument "atomic_list_concat"

def subStringC : List Atom → ReduceResult
  | [value, Atom.gnd (Ground.int before), length,
      Atom.gnd (Ground.int after)] =>
      match stringLikeText? value with
      | none => .incorrectArgument "sub_string"
      | some value =>
          if before < 0 || after < 0 then .incorrectArgument "sub_string"
          else
            let start := before.toNat
            let suffix := after.toNat
            if start + suffix > value.length then .incorrectArgument "sub_string"
            else
              let inferred := value.length - start - suffix
              match length with
              | Atom.gnd (Ground.int requested) =>
                  if requested < 0 || requested.toNat != inferred then
                    .incorrectArgument "sub_string"
                  else .ok [Atom.gnd (Ground.str
                    (((value.drop start).take inferred).toString))]
              | Atom.var _ =>
                  .ok [Atom.gnd (Ground.str
                    (((value.drop start).take inferred).toString))]
              | _ => .incorrectArgument "sub_string"
  | _ => .incorrectArgument "sub_string"

def firstCharC : List Atom → ReduceResult
  | [value] =>
      match stringLikeText? value with
      | some text =>
          match text.toList with
          | char :: _ => .ok [Atom.gnd (Ground.str (String.ofList [char]))]
          | [] => .incorrectArgument "first_char"
      | none => .incorrectArgument "first_char"
  | _ => .incorrectArgument "first_char"

def gcC : List Atom → ReduceResult
  | [] => .ok [Atom.sym "True"]
  | _ => .incorrectArgument "gc"

def unavailableHostOp (name : String) : List Atom → ReduceResult := fun _ =>
  .runtimeError s!"{name} requires the trusted Prolog host bridge"

/-- Registered functions that have a grounding-table marker but still require
    their declared Prolog module at runtime. Unknown registered functions are
    host-backed automatically; certified builtins such as `first_char` and
    `gc` remain in the pure executor. -/
def importedPrologHostBacked : String → Bool
  | "read_line_to_string" | "shell" | "safe_append_open" | "safe_write_open"
  | "call_with_inference_limit" | "consult" | "use_module"
  | "static-import!" | "git-import!" | "use-module!" => true
  | _ => false

/-- `translatePredicate` carries a quoted Prolog goal.  Loading a module that
    defines such a call is harmless; executing it remains an explicit trusted
    boundary until the Prolog host bridge is installed. -/
def translatePredicateMarker : List Atom → ReduceResult := fun _ =>
  .runtimeError "translatePredicate requires the trusted Prolog host bridge"

private def isWholeVar : Atom → Bool
  | Atom.var _ => true
  | _ => false

def isAlphaMemberOp : List Atom → ReduceResult
  | [x, l] => match chainList l with
    | some es =>
        let ok := es.any (fun y =>
          alphaEqOp [x, y] == .ok [Atom.sym "True"] ||
          (!(isWholeVar x && !isWholeVar y) &&
            (Metta.Unify.unifyTop x y).isSome))
        .ok [Atom.sym (if ok then "True" else "False")]
    | none => .incorrectArgument "is-alpha-member"
  | _ => .incorrectArgument "is-alpha-member"

/-- Marker grounding for the explicit host executor.  The ordinary pure
    machine fails loudly if a `py-call` escapes that boundary; HostMachine
    intercepts it before this implementation is invoked. -/
def pyCallMarker : List Atom → ReduceResult := fun _ =>
  .runtimeError "py-call escaped the host executor"

/-- Marker grounding for stdin (`readln!`).  Like `py-call`, HostMachine
    intercepts it before this loud-failure implementation is invoked. -/
def readlnMarker : List Atom → ReduceResult := fun _ =>
  .runtimeError "readln! escaped the host executor"



/-- The table: chain tuple-ops shadow Core's by order (first match wins). -/
def pleattaTable : GroundingTable :=
  ⟨"py-call", GroundMode.evalArgs, none, pyCallMarker⟩ ::
  ⟨"readln!", GroundMode.evalArgs, none, readlnMarker⟩ ::
  ⟨"translatePredicate", GroundMode.evalArgs, none,
    translatePredicateMarker⟩ ::
  ⟨"string_length", GroundMode.evalArgs, none, stringLengthC⟩ ::
  ⟨"string_concat", GroundMode.evalArgs, none, stringConcatC⟩ ::
  ⟨"split_string", GroundMode.evalArgs, none, splitStringC⟩ ::
  ⟨"atomic_list_concat", GroundMode.evalArgs, none, atomicListConcatC⟩ ::
  ⟨"sub_string", GroundMode.evalArgs, none, subStringC⟩ ::
  ⟨"swrite", GroundMode.evalArgs, none, reprC⟩ ::
  ⟨"sread", GroundMode.evalArgs, none, sreadC⟩ ::
  ⟨"first_char", GroundMode.evalArgs, none, firstCharC⟩ ::
  ⟨"gc", GroundMode.evalArgs, none, gcC⟩ ::
  ⟨"get_time", GroundMode.evalArgs, none, unavailableHostOp "get_time"⟩ ::
  ⟨"read_line_to_string", GroundMode.evalArgs, none,
    unavailableHostOp "read_line_to_string"⟩ ::
  ⟨"shell", GroundMode.evalArgs, none, unavailableHostOp "shell"⟩ ::
  ⟨"safe_append_open", GroundMode.evalArgs, none,
    unavailableHostOp "safe_append_open"⟩ ::
  ⟨"safe_write_open", GroundMode.evalArgs, none,
    unavailableHostOp "safe_write_open"⟩ ::
  ⟨"call_with_inference_limit", GroundMode.evalArgs, none,
    unavailableHostOp "call_with_inference_limit"⟩ ::
  ⟨"consult", GroundMode.evalArgs, none, unavailableHostOp "consult"⟩ ::
  ⟨"use_module", GroundMode.evalArgs, none,
    unavailableHostOp "use_module"⟩ ::
  ⟨"static-import!", GroundMode.evalArgs, none,
    unavailableHostOp "static-import!"⟩ ::
  ⟨"git-import!", GroundMode.evalArgs, none,
    unavailableHostOp "git-import!"⟩ ::
  ⟨"use-module!", GroundMode.evalArgs, none,
    unavailableHostOp "use-module!"⟩ ::
  ⟨"car-atom", GroundMode.evalArgs, none, carC⟩ ::
  ⟨"cdr-atom", GroundMode.evalArgs, none, cdrC⟩ ::
  ⟨"last", GroundMode.evalArgs, none, lastC⟩ ::
  ⟨"cons", GroundMode.evalArgs, none, consAtomC⟩ ::
  ⟨"cons-atom", GroundMode.evalArgs, none, consAtomC⟩ ::
  ⟨"println!", GroundMode.evalArgs, none, printlnC⟩ ::
  ⟨"assert", GroundMode.evalArgs, none, assertOp⟩ ::
  ⟨"!=", GroundMode.evalArgs, none, notEqualOp⟩ ::
  ⟨"add-translator-rule!", GroundMode.evalArgs, none, translatorRuleControlC⟩ ::
  ⟨"remove-translator-rule!", GroundMode.evalArgs, none, translatorRuleControlC⟩ ::
  ⟨"size-atom", GroundMode.evalArgs, none, sizeC⟩ ::
  ⟨"index-atom", GroundMode.evalArgs, none, indexC⟩ ::
  ⟨"decons-atom", GroundMode.evalArgs, none, deconsC⟩ ::
  ⟨"msort", GroundMode.evalArgs, none, msortC⟩ ::
  ⟨"unique-atom", GroundMode.evalArgs, none, uniqueC⟩ ::
  ⟨"list_to_set", GroundMode.evalArgs, none, listToSetC⟩ ::
  ⟨"exclude-item", GroundMode.evalArgs, none, excludeItemC⟩ ::
  ⟨"union-atom", GroundMode.evalArgs, none, unionC⟩ ::
  ⟨"intersection-atom", GroundMode.evalArgs, none, intersectionC⟩ ::
  ⟨"subtraction-atom", GroundMode.evalArgs, none, subtractionC⟩ ::
  ⟨"is-var", GroundMode.evalArgs, none, isVarOp⟩ ::
  ⟨"is-ground", GroundMode.evalArgs, none, isGroundOp⟩ ::
  ⟨"is-expr", GroundMode.evalArgs, none, isExprOp⟩ ::
  ⟨"is-space", GroundMode.evalArgs, none, isSpaceOp⟩ ::
  ⟨"min", GroundMode.evalArgs, none, minMaxOp true⟩ ::
  ⟨"max", GroundMode.evalArgs, none, minMaxOp false⟩ ::
  ⟨"min-atom", GroundMode.evalArgs, none, extremumC true⟩ ::
  ⟨"max-atom", GroundMode.evalArgs, none, extremumC false⟩ ::
  ⟨"/", GroundMode.evalArgs, none, divOp⟩ ::
  ⟨"%", GroundMode.evalArgs, none, modOp⟩ ::
  ⟨"repr", GroundMode.evalArgs, none, reprC⟩ ::
  ⟨"repra", GroundMode.evalArgs, none, repraC⟩ ::
  ⟨"sqrt-math", GroundMode.evalArgs, none, floatUnC Float.sqrt⟩ ::
  ⟨"sin-math", GroundMode.evalArgs, none, floatUnC Float.sin⟩ ::
  ⟨"cos-math", GroundMode.evalArgs, none, floatUnC Float.cos⟩ ::
  ⟨"tan-math", GroundMode.evalArgs, none, floatUnC Float.tan⟩ ::
  ⟨"pow-math", GroundMode.evalArgs, none, (fun args =>
    match args with
    | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] =>
        .ok [Atom.gnd (Ground.int (a ^ b.toNat))]
    | _ => floatBinC Float.pow args)⟩ ::
  ⟨"log-math", GroundMode.evalArgs, none,
    floatBinC (fun base x => Float.log x / Float.log base)⟩ ::
  ⟨"abs-math", GroundMode.evalArgs, none, (fun args =>
    match args with
    | [Atom.gnd (Ground.int a)] => .ok [Atom.gnd (Ground.int a.natAbs)]
    | _ => floatUnC Float.abs args)⟩ ::
  ⟨"trunc-math", GroundMode.evalArgs, none,
    roundC (fun x => if x ≥ 0 then x.floor else x.ceil)⟩ ::
  ⟨"ceil-math", GroundMode.evalArgs, none, roundC Float.ceil⟩ ::
  ⟨"floor-math", GroundMode.evalArgs, none, roundC Float.floor⟩ ::
  ⟨"round-math", GroundMode.evalArgs, none, roundC Float.round⟩ ::
  ⟨"alpha-unique-atom", GroundMode.evalArgs, none, (fun args =>
    match args with
    | [a] => match chainList a with
      | some l =>
          let ded := l.foldl (fun acc x =>
            if acc.any (fun y => alphaEqOp [x, y] == .ok [Atom.sym "True"])
            then acc else acc ++ [x]) []
          .ok [chainOf ded]
      | none => .incorrectArgument "alpha-unique-atom"
    | _ => .incorrectArgument "alpha-unique-atom")⟩ ::
  ⟨"=alpha", GroundMode.evalArgs, none, alphaEqOp⟩ ::
  ⟨"#test-results", GroundMode.evalArgs, none, testResultsOp⟩ ::
  ⟨"parse", GroundMode.evalArgs, none, parseOp⟩ ::
  ⟨"is-alpha-member", GroundMode.evalArgs, none, isAlphaMemberOp⟩ ::
  (Metta.Builtins.table.filter (fun g =>
    !["and", "or", "not"].contains g.name))

/-- The self-hosted prelude: PeTTa library functions AS PeTTa rules, compiled
    by the same equations as user code. Truth-table booleans enumerate. -/
def preludeSrc : String := "
(= (and True True) True)
(= (and True False) False)
(= (and False True) False)
(= (and False False) False)
(= (or True True) True)
(= (or True False) True)
(= (or False True) True)
(= (or False False) False)
(= (not True) False)
(= (not False) True)
(= (id $x) $x)
(= (= $x $y) (= $x $y))
(= (append () $ys) $ys)
(= (append (cons $h $t) $ys) (cons $h (append $t $ys)))
(= (member $x (cons $x $t)) True)
(= (member $x (cons $h $t)) (member $x $t))
(= (is-member $x $l) (member $x $l))
(= (reverse ()) ())
(= (reverse (cons $h $t)) (append (reverse $t) (cons $h ())))
(= (length ()) 0)
(= (length (cons $h $t)) (+ 1 (length $t)))
(= (first (cons $h $t)) $h)
(= (maplist $f ()) ())
(= (maplist $f (cons $h $t)) (cons ($f $h) (maplist $f $t)))
(= (foldl $f () $acc) $acc)
(= (foldl $f (cons $h $t) $acc) (foldl $f $t ($f $h $acc)))
(= (#foldacc $f () $acc) $acc)
(= (#foldacc $f (cons $h $t) $acc) (#foldacc $f $t ($f $acc $h)))
(= (xor True False) True)
(= (xor False True) True)
(= (xor True True) False)
(= (xor False False) False)
(= (map-atom () $f) ())
(= (map-atom (cons $h $t) $f) (cons ($f $h) (map-atom $t $f)))
(= (filter-atom () $f) ())
(= (filter-atom (cons $h $t) $f) (if ($f $h) (cons $h (filter-atom $t $f)) (filter-atom $t $f)))
(= (foldl-atom () $i $f) $i)
(= (foldl-atom (cons $h $t) $i $f) (foldl-atom $t ($f $i $h) $f))
(= (#allacc $p ()) True)
(= (#allacc $p (cons $h $t)) (and ($p $h) (#allacc $p $t)))
(= (first-from-pair (cons $a (cons $b ()))) $a)
(= (second-from-pair (cons $a (cons $b ()))) $b)
"

end PLeaTTa
