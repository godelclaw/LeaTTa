-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Compile

/-!
# Compiler generated-variable freshness regression

The pinned source language permits variables whose names resemble the
executable compiler's `_qN` temporaries.  Source-facing compilation must seed
its allocation supply beyond those variables before emitting any temporary.
-/

namespace PLeaTTa.CompilerFreshnessRegression

open Metta (Atom)

def collisionSource : Atom :=
  .expr [.sym "if", .gnd (.bool true),
    .expr [.sym "let", .var "_q25", .gnd (.int 1), .gnd (.int 2)]]

def emptyEnv : CEnv := mkEnv (fun _ => false) [] [] []

def expectedGoals : List Goal :=
  [.ite (.sym "True")
    (.gnd (.int 2), [.eq (.var "_q25") (.gnd (.int 1))])
    (.var "_q26", [.eq (.sym "True") (.sym "False")])
    (.var "_q26")]

#guard compilerGeneratedIndex? "_q25" == some 25
#guard compilerGeneratedIndex? "_q025" == some 25
#guard compilerGeneratedIndex? "ordinary" == none
#guard compilerFreshCounterForAtom 0 collisionSource == 26
#guard match compileExprFresh emptyEnv 0 collisionSource with
  | .ok (.var name, goals, next) =>
      name == "_q26" && goals == expectedGoals && next == 27
  | _ => false

end PLeaTTa.CompilerFreshnessRegression
