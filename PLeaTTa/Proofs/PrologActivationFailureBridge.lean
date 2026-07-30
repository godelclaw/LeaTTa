-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivationFailureBridge
Purpose: Pair exact independent and executable rejection of one retained
  local-clause head without assuming a false global inverse for the runtime
  term encoding.
Trusted boundary: none
Main exports: RetainedHeadFailureAgrees,
  RetainedHeadFailureAgrees.step_correspondence,
  repeated_variable_false_positive_steps_together
-/
import PLeaTTa.Proofs.PrologActivationUnifierBridge

namespace PLeaTTa.PrologActivationFailureBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologPrefilterBridge
open PrologStateBridge

/-!
`resolveAlts` deliberately retains conservative false positives.  The next
ordinary executable step runs the complete input-plus-output equality and
may reject the retained occurrence.  The independent cursor makes the same
decision by asking whether its normalized head equations have a canonical
finite-tree MGU.

The runtime encoding is not globally invertible: reserved atom spellings and
proper-list encodings have dual readings.  Therefore this file does not claim
that every independent rejection forces `unifyB = none`.  Instead it names
the exact source-guided certificate needed for the paired rejection step and
names the remaining bad case separately.  A later supported-source producer
must rule out `RetainedHeadEncodingLeak`; the step theorem below never assumes
that conclusion implicitly.
-/

/-- Exact agreement for one conservatively retained occurrence that both
resolvers reject at the full-head seam.

The normalized-head field relates the real output-last source head to the
runtime clause before suffix freshening.  `executableRejected` is about the
actual suffix-freshened complete equality executed by `Step.eq_fail`.
[SPEC translator.pl:251-256] -/
structure RetainedHeadFailureAgrees
    (branch : ClauseBranch)
    (args : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (qterm : Atom) (seed barrier : Nat)
    (clause : PLeaTTa.Clause) : Prop where
  normalized :
    NormalizedHeadAgrees branch
      (args.map (PLeaTTa.subst binding))
      (PLeaTTa.subst binding result) clause
  retained :
    resolutionClauseRetained
      (args.map (PLeaTTa.subst binding))
      (PLeaTTa.subst binding result) clause = true
  independentRejected :
    ¬ ∃ independentResult, HeadResolution branch independentResult
  executableRejected :
    PLeaTTa.unifyB binding
      (.expr (args ++ [result]))
      (.expr
        ((PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result])) = none

/-- The explicitly unproved alternative at this seam: the independent
canonical equations reject, but the non-injective runtime encoding admits a
runtime unifier.  Merely proving normalized-head agreement cannot exclude
this case. -/
structure RetainedHeadEncodingLeak
    (branch : ClauseBranch)
    (args : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (qterm : Atom) (seed barrier : Nat)
    (clause : PLeaTTa.Clause) : Prop where
  normalized :
    NormalizedHeadAgrees branch
      (args.map (PLeaTTa.subst binding))
      (PLeaTTa.subst binding result) clause
  retained :
    resolutionClauseRetained
      (args.map (PLeaTTa.subst binding))
      (PLeaTTa.subst binding result) clause = true
  independentRejected :
    ¬ ∃ independentResult, HeadResolution branch independentResult
  executableAccepted :
    PLeaTTa.unifyB binding
      (.expr (args ++ [result]))
      (.expr
        ((PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result])) ≠ none

/-- Joint rejection and an encoding leak are disjoint on the same concrete
head equality.  This is small but load-bearing: the two record types do not
merely relabel the same outcome. -/
theorem RetainedHeadFailureAgrees.not_encodingLeak
    {branch : ClauseBranch}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {clause : PLeaTTa.Clause}
    (failure :
      RetainedHeadFailureAgrees branch args result rest binding qterm seed
        barrier clause) :
    ¬ RetainedHeadEncodingLeak branch args result rest binding qterm seed
      barrier clause := by
  intro leak
  exact leak.executableAccepted failure.executableRejected

/-- One source-guided failure certificate produces the two actual silent
transitions.

The independent side consumes exactly the current prepared occurrence and
keeps the persistent session unchanged.  The executable side takes the real
`eq_fail` transition and changes no answer, world, or global fresh counter;
only its DFS control is pulled forward. -/
theorem RetainedHeadFailureAgrees.step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {session : Session} {scope : CutScopeId}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {clause : PLeaTTa.Clause} {conf : PLeaTTa.Conf}
    (failure :
      RetainedHeadFailureAgrees branch args result rest binding qterm seed
        barrier clause)
    (remaining : cursor.remaining = branch :: branches)
    (current :
      conf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [result]))
              (.expr
                ((PLeaTTa.freshenResolutionClause
                    (args.map (PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).params ++
                  [(PLeaTTa.freshenResolutionClause
                    (args.map (PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).result])) ::
            (PLeaTTa.freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest,
            binding)) :
    RawStep session (.clauses scope cursor) [] .none session
        (.running
          (.clauses scope (cursor.advance branch branches))) ∧
      PLeaTTa.Step prog gt conf (PLeaTTa.pull { conf with cur := none }) ∧
      (PLeaTTa.pull { conf with cur := none }).answers = conf.answers ∧
      (PLeaTTa.pull { conf with cur := none }).world = conf.world ∧
      (PLeaTTa.pull { conf with cur := none }).counter = conf.counter := by
  have pulled :
      LocalPull cursor (.silent (cursor.advance branch branches)) :=
    .rejected cursor branch branches remaining failure.independentRejected
  have sourceStep :
      RawStep session (.clauses scope cursor) [] .none session
        (.running
          (.clauses scope (cursor.advance branch branches))) := by
    simpa [localPullEvents, localPullTarget] using
      (RawStep.clausesPull scope cursor
        (.silent (cursor.advance branch branches)) session pulled)
  have executableStep :=
    leading_full_head_eq_failure_is_silent prog gt conf
      (.expr (args ++ [result]))
      (.expr
        ((PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]))
      ((PLeaTTa.freshenResolutionClause
        (args.map (PLeaTTa.subst binding)) args result rest binding qterm
        seed barrier clause).body ++ rest)
      binding current failure.executableRejected
  exact
    ⟨sourceStep, executableStep.1, executableStep.2.1,
      executableStep.2.2.1, executableStep.2.2.2⟩

/-! ## Anti-vacuity: a retained repeated-variable head really fails twice -/

private def repeatedReferenceBranch : ClauseBranch :=
  { sourceId := 0
    callGeneration := 0
    freshSubstitution := []
    headEquations :=
      [(.atom "left", .variable (.generated 0)),
        (.atom "right", .variable (.generated 0)),
        (.atom "ok", .atom "ok")]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 1 }

private def repeatedExecutableClause : PLeaTTa.Clause :=
  { params := [.var "shared", .var "shared"]
    result := .sym "ok"
    body := [] }

private def repeatedCursor : PreparedCursor :=
  { callGeneration := 0
    predicate := "repeated"
    arguments := [.atom "left", .atom "right", .atom "ok"]
    bindings := []
    reservationStart := 0
    remaining := [repeatedReferenceBranch]
    reservedUntil := 1 }

private def repeatedConf : PLeaTTa.Conf :=
  { cur :=
      some
        ([PLeaTTa.Goal.eq
          (.expr [.sym "left", .sym "right", .sym "ok"])
          (.expr [.var "shared#r0", .var "shared#r0", .sym "ok"])], [])
    alts := []
    world := {}
    counter := 1
    qterm := .var "query" }

private theorem repeatedReferenceBranch_has_no_resolution :
    ¬ ∃ result, HeadResolution repeatedReferenceBranch result := by
  rintro ⟨result, resolution⟩
  have unifies := resolution.unifies
  have left :
      DenotationalUnifier result
        (.atom "left") (.variable (.generated 0)) :=
    unifies (.atom "left", .variable (.generated 0)) (by
      simp [repeatedReferenceBranch])
  have right :
      DenotationalUnifier result
        (.atom "right") (.variable (.generated 0)) :=
    unifies (.atom "right", .variable (.generated 0)) (by
      simp [repeatedReferenceBranch])
  have impossible :
      DenotationalUnifier result (.atom "left") (.atom "right") := by
    unfold DenotationalUnifier at left right ⊢
    exact left.trans right.symm
  exact
    distinct_atoms_have_no_denotational_unifier "left" "right" (by decide)
      ⟨result, impossible⟩

/-- The concrete relation is inhabited by a genuine conservative false
positive: both slots accept a variable independently, but their shared head
variable makes the complete equality inconsistent for unequal actuals. -/
theorem repeated_variable_false_positive_agrees :
    RetainedHeadFailureAgrees repeatedReferenceBranch
      [.sym "left", .sym "right"] (.sym "ok") [] [] (.var "query") 0 1
      repeatedExecutableClause := by
  constructor
  · constructor
    · rfl
    · have equations :
          AlphaEquationsAgree
            [(.atom "left", .variable (.generated 0)),
              (.atom "right", .variable (.generated 0)),
              (.atom "ok", .atom "ok")]
            [.sym "left", .sym "right", .sym "ok"]
            [.var "shared", .var "shared", .sym "ok"] := by
        exact .cons
          (AlphaTermAgrees.atom (alpha := []) (name := "left")
            (by decide) (by decide))
          (AlphaTermAgrees.variable
            (alpha := [(.generated 0, "shared")])
            (identity := .generated 0) (name := "shared") (by simp))
          (.cons
            (AlphaTermAgrees.atom (alpha := []) (name := "right")
              (by decide) (by decide))
            (AlphaTermAgrees.variable
              (alpha := [(.generated 0, "shared")])
              (identity := .generated 0) (name := "shared") (by simp))
            (.cons
              (AlphaTermAgrees.atom (alpha := []) (name := "ok")
                (by decide) (by decide))
              (AlphaTermAgrees.atom (alpha := []) (name := "ok")
                (by decide) (by decide))
              .nil))
      simpa [repeatedReferenceBranch, repeatedExecutableClause,
        ClauseBranch.normalizedHeadEquations] using equations
  · simp [resolutionClauseRetained, repeatedExecutableClause,
      PLeaTTa.prologMatchCompatList, PLeaTTa.prologMatchCompat]
  · exact repeatedReferenceBranch_has_no_resolution
  · simp [repeatedExecutableClause, PLeaTTa.freshenResolutionClause,
      PLeaTTa.resolutionFreshSuffix, PLeaTTa.resolutionCompactSuffix,
      PLeaTTa.renameAtomSuffix, PLeaTTa.unifyB, PLeaTTa.unifyTopExact,
      Metta.Unify.unifyTopWith, Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith,
      Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup]

/-- Exact paired-step discriminator.  The retained repeated-variable
occurrence cannot be skipped by reflexivity or a zero-step quotient: each
machine consumes it through its own real rejection constructor, and neither
machine publishes an answer. -/
theorem repeated_variable_false_positive_steps_together
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (session : Session) :
    RawStep session (.clauses 0 repeatedCursor) [] .none session
        (.running
          (.clauses 0
            (repeatedCursor.advance repeatedReferenceBranch []))) ∧
      PLeaTTa.Step prog gt repeatedConf
        (PLeaTTa.pull { repeatedConf with cur := none }) ∧
      (PLeaTTa.pull { repeatedConf with cur := none }).answers =
        repeatedConf.answers ∧
      (PLeaTTa.pull { repeatedConf with cur := none }).world =
        repeatedConf.world ∧
      (PLeaTTa.pull { repeatedConf with cur := none }).counter =
        repeatedConf.counter := by
  apply repeated_variable_false_positive_agrees.step_correspondence
  · rfl
  · simp [repeatedConf, repeatedExecutableClause,
      PLeaTTa.freshenResolutionClause, PLeaTTa.resolutionFreshSuffix,
      PLeaTTa.resolutionCompactSuffix, PLeaTTa.renameAtomSuffix]
    decide

end PLeaTTa.PrologActivationFailureBridge
