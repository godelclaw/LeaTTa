/-
Module: PLeaTTa.Proofs.PrologCoreAdequacy
Purpose: Relate independently specified pure Prolog behavior to compiled
  PLeaTTa goals and the sealed small-step machine.
Trusted boundary: none
-/
import PLeaTTa.Compile
import PLeaTTa.Semantics
import PLeaTTa.PeTTaSpec.PrologSemantics
import PLeaTTa.Proofs.BarrierCache
import PLeaTTa.Proofs.Unification

namespace PLeaTTa.PrologCoreAdequacy

open Metta (Atom Subst GroundingTable)
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.Declarative

/-- The public compiler exposes the explicit-failure implementation of the
pinned zero-argument `empty` operation whenever no translator hook shadows
the built-in. -/
theorem compileExpr_empty_eq (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "empty" = false) :
    compileExpr env counter (.expr [.sym "empty"]) =
      .ok (.sym "True",
        [PLeaTTa.Goal.eq (.sym "True") (.sym "False")], counter) := by
  simpa only [compileExpr, Nat.add_assoc, Nat.reduceAdd] using
    compileExprFuel_empty_eq
      (compilerFuel (.expr [.sym "empty"]) + 61) counter env noHook

/-- An immediately inconsistent equation worklist fails independently of the
unifier's structurally decreasing fuel. -/
theorem unifyRounds_of_decomposeAll_none (fuel : Nat)
    (equations : List (Atom × Atom)) (binding : Subst)
    (inconsistent : Metta.Unify.decomposeAll equations = none) :
    Metta.Unify.unifyRounds fuel equations binding = none := by
  cases fuel <;> simp [Metta.Unify.unifyRounds, inconsistent]

/-- The executable unifier rejects the distinct canonical truth values under
every existing substitution. -/
theorem unifyB_true_false_none (binding : Subst) :
    unifyB binding (.sym "True") (.sym "False") = none := by
  have hunify : Metta.Unify.unifyTop (.sym "True") (.sym "False") = none := by
    unfold Metta.Unify.unifyTop
    rw [unifyRounds_of_decomposeAll_none]
    rfl
  simp [unifyB, unifyTopExact, hunify]

/-- An executable branch containing only the false equality takes one
seal-covered semantic step to a terminal branch with no new answer when no
alternative remains. -/
theorem compiled_empty_step_fails (program : Prog) (grounding : GroundingTable)
    (c : Conf) (binding : Subst)
    (current : c.cur = some
      ([PLeaTTa.Goal.eq (.sym "True") (.sym "False")], binding))
    (noAlternatives : c.alts = []) :
    ∃ terminal,
      Step program grounding c terminal ∧
      Terminal terminal ∧
      terminal.answers = c.answers := by
  let terminal := pull { c with cur := none }
  refine ⟨terminal, ?_, ?_, ?_⟩
  · exact Step.eq_fail c (.sym "True") (.sym "False") [] binding current
      (unifyB_true_false_none binding)
  · cases barrierCache : c.barriers <;>
      simp [terminal, Terminal, pull, pullAuxTracked, pullAuxCached,
        pullAux, noAlternatives, barrierCache]
  · cases barrierCache : c.barriers <;>
      simp [terminal, pull, pullAuxTracked, pullAuxCached, pullAux,
        noAlternatives, barrierCache]

/-- The compiler's explicit false equality and pinned PeTTa's `empty/1`
call agree on pure declarative success: neither can produce a solution.  The
machine theorem above separately connects the executable equality to the
sealed operational semantics. -/
theorem compileExpr_empty_failure_adequate (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "empty" = false)
    (nativeResult : Term) :
    compileExpr env counter (.expr [.sym "empty"]) =
        .ok (.sym "True",
          [PLeaTTa.Goal.eq (.sym "True") (.sym "False")], counter) ∧
      DeclarativelyEquivalent emptyProgram
        [.call "empty" [nativeResult]]
        [.unify (.atom "true") (.atom "false")] := by
  exact ⟨compileExpr_empty_eq env counter noHook,
    empty_call_false_unification_equivalent nativeResult⟩

/-! ## Fresh-result capture for `once/1` -/

/-- A variable absent from its target decomposes to exactly one binding.
The occurs premise is essential: recursive targets are rejected below. -/
theorem decomposeEq_fresh_variable (fresh : String) (target : Atom)
    (hoccurs : Metta.Subst.occurs fresh target = false) :
    Metta.Unify.decomposeEq (.var fresh) target = some [(fresh, target)] := by
  cases target with
  | sym name => rfl
  | var name =>
      have hne : fresh ≠ name := by
        simpa [Metta.Subst.occurs] using hoccurs
      simp [Metta.Unify.decomposeEq, hne]
  | gnd ground => rfl
  | expr atoms => rfl

/-- The structurally recursive unifier eliminates one fresh variable and
returns precisely its singleton binding. -/
theorem unifyTop_fresh_variable (fresh : String) (target : Atom)
    (hoccurs : Metta.Subst.occurs fresh target = false) :
    Metta.Unify.unifyTop (.var fresh) target = some [(fresh, target)] := by
  have hdecompose := decomposeEq_fresh_variable fresh target hoccurs
  have hpositive : 0 < (Atom.var fresh).size + target.size := by
    cases target <;> simp [Atom.size]
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hpositive)
  have hdone : Metta.Unify.unifyRounds fuel [] [(fresh, target)] =
      some [(fresh, target)] := by
    cases fuel <;> rfl
  unfold Metta.Unify.unifyTop
  rw [hfuel]
  simp [Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
    hdecompose, hoccurs, Metta.Subst.extend, Metta.Subst.erase, hdone]

/-- Capturing a template into a name fresh for both the incoming binding and
the resolved template succeeds with the exact composed substitution. -/
theorem unifyB_fresh_capture (binding : Subst) (fresh : String)
    (template : Atom)
    (hlookup : Metta.Subst.lookup binding fresh = none)
    (hfresh : fresh ∉ (subst binding template).vars) :
    unifyB binding (.var fresh) template =
      some (Metta.Subst.compose [(fresh, subst binding template)] binding) := by
  have hoccurs : Metta.Subst.occurs fresh (subst binding template) = false :=
    occurs_eq_false_of_not_mem_vars fresh (subst binding template) hfresh
  let target := subst binding template
  have hunify : Metta.Unify.unifyTop (.var fresh) target =
      some [(fresh, target)] :=
    unifyTop_fresh_variable fresh target hoccurs
  have htopological : SubstTopological [(fresh, target)] :=
    SubstTopological.cons_of_fresh [] emptySubstTopological fresh target
      (by simp [Metta.Subst.lookup]) hfresh
      (by simp [AtomAvoids, Metta.Subst.lookup])
  have hlookupSingleton :
      Metta.Subst.lookup [(fresh, target)] fresh = some target := by
    simp [Metta.Subst.lookup]
  have hexact : subst [(fresh, target)] (.var fresh) =
      subst [(fresh, target)] target :=
    htopological.subst_var_of_lookup [(fresh, target)] fresh target
      hlookupSingleton
  have hwrapped : unifyTopExact (.var fresh) target =
      some [(fresh, target)] :=
    unifyTopExact_of_underlying_exact (.var fresh) target
      [(fresh, target)] hunify hexact
  unfold unifyB
  rw [subst_var_of_lookup_none binding fresh hlookup]
  simp [target, hwrapped]

/-- The successful fresh capture remains topological and its result variable
denotes exactly the body template under the extended binding. -/
theorem unifyB_fresh_capture_denotes (binding : Subst)
    (topological : SubstTopological binding) (fresh : String)
    (template : Atom)
    (hlookup : Metta.Subst.lookup binding fresh = none)
    (hfresh : fresh ∉ (subst binding template).vars) :
    ∃ result,
      unifyB binding (.var fresh) template = some result ∧
      Nonempty (SubstTopological result) ∧
      Metta.Subst.lookup result fresh = some (subst binding template) ∧
      subst result (.var fresh) = subst result template := by
  let result := Metta.Subst.compose
    [(fresh, subst binding template)] binding
  have hresult : unifyB binding (.var fresh) template = some result :=
    unifyB_fresh_capture binding fresh template hlookup hfresh
  have hresultTopological : SubstTopological result :=
    unifyB_topological binding (.var fresh) template result topological hresult
  have hresultLookup : Metta.Subst.lookup result fresh =
      some (subst binding template) := by
    simp [result, lookup_compose, hlookup, Metta.Subst.lookup]
  have hlookupDenotes :
      subst result (.var fresh) = subst result (subst binding template) :=
    hresultTopological.subst_var_of_lookup result fresh
      (subst binding template) hresultLookup
  have habsorbs : subst result (subst binding template) =
      subst result template :=
    unifyB_absorbs_base binding (.var fresh) template result topological
      hresult template
  exact ⟨result, hresult, ⟨hresultTopological⟩, hresultLookup,
    hlookupDenotes.trans habsorbs⟩

/-- Positive computation witness for fresh capture. -/
theorem fresh_capture_closed_example :
    unifyB [] (.var "_q0") (.sym "answer") =
      some [("_q0", .sym "answer")] := by
  simpa [Metta.Subst.compose] using
    (unifyB_fresh_capture [] "_q0" (.sym "answer")
      (by simp [Metta.Subst.lookup]) (by simp [Atom.vars]))

/-- Negative witness showing why capture freshness cannot be omitted. -/
theorem recursive_capture_rejected :
    unifyB [] (.var "_q0") (.expr [.sym "f", .var "_q0"]) = none := by
  have hunify : Metta.Unify.unifyTop (.var "_q0")
      (.expr [.sym "f", .var "_q0"]) = none := by
    simp [Metta.Unify.unifyTop, Atom.size, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Subst.occurs]
  simp [unifyB, unifyTopExact, hunify]

/-! ## Scoped first-answer control for `onceg` -/

/-- Executable `onceg` opens one private barrier and schedules result capture
after the body and its committing cut. -/
theorem onceg_enters_scoped_branch (program : Prog)
    (grounding : GroundingTable) (c : Conf) (template : Atom)
    (body rest : List PLeaTTa.Goal) (result : Atom) (binding : Subst)
    (current : c.cur = some
      (PLeaTTa.Goal.onceg template body result :: rest, binding)) :
    Step program grounding c
      { c with
        cur := some
          (body ++ [PLeaTTa.Goal.cutAt (barrierDepth c + 1),
            PLeaTTa.Goal.eq result template] ++ rest, binding)
        alts := Alt.barrier :: c.alts
        barriers := pushBarrierCache c.barriers } := by
  have hpull :
      pull { c with
        cur := none
        alts := Alt.br
          (body ++ [PLeaTTa.Goal.cutAt (barrierDepth c + 1),
            PLeaTTa.Goal.eq result template] ++ rest) binding ::
          Alt.barrier :: c.alts
        barriers := pushBarrierCache c.barriers } =
      { c with
        cur := some
          (body ++ [PLeaTTa.Goal.cutAt (barrierDepth c + 1),
            PLeaTTa.Goal.eq result template] ++ rest, binding)
        alts := Alt.barrier :: c.alts
        barriers := pushBarrierCache c.barriers } := by
    cases c.barriers <;> rfl
  rw [← hpull]
  exact Step.onceg c template body result rest binding current

/-- A cut tagged one level above an outer stack leaves that outer stack
untouched when it is already below the tag. -/
theorem cutTo_below_own_barrier {Binding : Type}
    (outer : List (Alt Binding)) :
    cutTo (barrierCount outer + 1) outer = outer := by
  cases outer with
  | nil => rfl
  | cons head tail =>
      unfold cutTo
      rw [if_neg (by omega)]

/-- The private `onceg` cut deletes every inner alternative and its own
barrier, independently of how many nested barriers occur in the inner stack. -/
theorem cutTo_own_barrier {Binding : Type}
    (inner outer : List (Alt Binding)) :
    cutTo (barrierCount outer + 1)
      (inner ++ Alt.barrier :: outer) = outer := by
  induction inner with
  | nil =>
      simp only [List.nil_append]
      unfold cutTo
      rw [if_pos (by simp)]
      exact cutTo_below_own_barrier outer
  | cons head tail ih =>
      rw [List.cons_append]
      unfold cutTo
      have hcount : barrierCount outer + 1 ≤
          barrierCount (head :: (tail ++ Alt.barrier :: outer)) := by
        cases head <;> simp
        omega
      rw [if_pos hcount]
      exact ih

/-- At the first successful body answer, the private cut commits to that
answer by removing all alternatives above its own barrier while preserving
the caller's alternatives and a coherent barrier cache. -/
theorem once_cut_commits_inner_alternatives (program : Prog)
    (grounding : GroundingTable) (d : Conf) (inner outer : List Alt)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (altsShape : d.alts = inner ++ Alt.barrier :: outer)
    (current : d.cur = some
      (PLeaTTa.Goal.cutAt (barrierCount outer + 1) :: rest, binding))
    (coherent : BarrierCacheCoherent d) :
    ∃ nextCache : Option Nat,
      Step program grounding d
        { d with
          cur := some (rest, binding)
          alts := outer
          barriers := nextCache } ∧
      match nextCache with
      | none => True
      | some depth => depth = barrierCount outer := by
  have rawCoherent : match d.barriers with
      | none => True
      | some depth => depth = barrierCount d.alts := coherent
  have trackedFst :
      (cutToTracked (barrierCount outer + 1) d.barriers d.alts).1 = outer := by
    rw [cutToTracked_fst_of_coherent _ _ _ rawCoherent, altsShape]
    exact cutTo_own_barrier inner outer
  let nextCache :=
    (cutToTracked (barrierCount outer + 1) d.barriers d.alts).2
  have nextCoherent : match nextCache with
      | none => True
      | some depth => depth = barrierCount outer := by
    have result := cutToTracked_coherent (barrierCount outer + 1)
      d.barriers d.alts rawCoherent
    rw [trackedFst] at result
    exact result
  refine ⟨nextCache, ?_, nextCoherent⟩
  have step := Step.cut_at (prog := program) (gt := grounding) d
    (barrierCount outer + 1) rest binding current
  simpa [trackedFst, nextCache] using step

/-- Once result capture is reached, the fresh output is installed in one
seal-covered equality step. If the output remains observable, trimming keeps
its complete denotation equal to the body template. -/
theorem once_capture_eq_step_observable (program : Prog)
    (grounding : GroundingTable) (c : Conf) (binding : Subst)
    (topological : SubstTopological binding) (fresh : String)
    (template : Atom) (rest : List PLeaTTa.Goal)
    (current : c.cur = some
      (PLeaTTa.Goal.eq (.var fresh) template :: rest, binding))
    (hlookup : Metta.Subst.lookup binding fresh = none)
    (hfresh : fresh ∉ (subst binding template).vars)
    (observable : isTrimRoot rest c.qterm fresh = true) :
    ∃ result,
      Step program grounding c
        { c with cur := some (rest, trimFor rest c.qterm result) } ∧
      Nonempty (SubstTopological result) ∧
      Metta.Subst.lookup result fresh = some (subst binding template) ∧
      subst (trimFor rest c.qterm result) (.var fresh) =
        subst result template := by
  obtain ⟨result, unifies, ⟨resultTopological⟩, resultLookup,
      captureDenotes⟩ :=
    unifyB_fresh_capture_denotes binding topological fresh template
      hlookup hfresh
  have step : Step program grounding c
      { c with cur := some (rest, trimFor rest c.qterm result) } :=
    Step.eq_ok c (.var fresh) template rest binding result current unifies
  have trimmedLookup :
      Metta.Subst.lookup (trimFor rest c.qterm result) fresh =
        some (subst binding template) := by
    rw [trimFor_lookup_of_root rest c.qterm result fresh observable,
      resultLookup]
  have preserved := subst_trimFor_var_eq_of_lookup_some rest c.qterm result
    resultTopological fresh (subst binding template) trimmedLookup
  exact ⟨result, step, ⟨resultTopological⟩, resultLookup,
    preserved.trans captureDenotes⟩

end PLeaTTa.PrologCoreAdequacy
