-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Compile
import PLeaTTa.Machine

/-!
# Syntactic-superpose branch-order regression

Pinned `build_branch/4` treats its three priority cases differently: an empty
conjunction is only a value equality, a variable-valued nonempty conjunction
aliases that value to the enclosing output during translation, and a
nonvariable-valued conjunction runs its equality before its effects.  These
guards pin the executable representation and the corresponding `amb` schedule.
-/

namespace PLeaTTa.CompilerSuperposeRegression

open Metta (Atom)

def output : Atom := .var "_q9"
def sourceVariable : Atom := .var "source"
def value : Atom := .sym "value"

#guard compileSuperposeBranch output (sourceVariable, []) ==
  ([], (sourceVariable, []))

#guard compileSuperposeBranch output (sourceVariable, [.cut]) ==
  ([.compileAlias sourceVariable output], (output, [.cut]))

#guard compileSuperposeBranch output (value, [.cut]) ==
  ([], (output, [.eq value output, .cut]))

#guard compileSuperposeBranches output
    [(sourceVariable, []), (sourceVariable, [.cut]), (value, [.cut])] ==
  ([.compileAlias sourceVariable output],
    [(sourceVariable, []), (output, [.cut]),
      (output, [.eq value output, .cut])])

#guard ambBranchGoals output (sourceVariable, []) ==
  [.eq output sourceVariable]

#guard ambBranchGoals output (output, [.cut]) == [.cut]

#guard ambBranchGoals output (output, [.eq value output, .cut]) ==
  [.eq value output, .cut]

end PLeaTTa.CompilerSuperposeRegression
