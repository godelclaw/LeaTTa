-- SPDX-License-Identifier: Apache-2.0

/-
The FORMAL operational semantics of core PeTTa (PETTA-LP.md §3), as a
small-step relation over machine configurations. `Machine.lean`'s executable
`step` mirrors this relation constructor-for-constructor (the shared
constructions — `pull`, `cutTo`, `unifyB`, clause renaming — are the same
definitions, so each case is checkable by unfolding).

`findall` nests the reflexive-transitive closure: `Step` and `StepStar` are a
mutual inductive family. Its premise requires the sub-run to reach a TERMINAL
configuration — the executable's fuel truncation is therefore *outside* the
relation (a fuel-exhausted machine result is not a `Step`; soundness for the
findall case is stated relative to terminating sub-runs, the same honesty as
LeaTTa's fuel-bounded kernel vs its spec).
-/
import PLeaTTa.Machine

namespace PLeaTTa

open Metta (Atom Subst GroundingTable ReduceResult callGrounded)

/-- A configuration with nothing left to do. -/
def Terminal (c : Conf) : Prop := c.cur = none ∧ c.alts = []

mutual

inductive Step (prog : Prog) (gt : GroundingTable) : Conf → Conf → Prop where
  | pull_next (c : Conf) (h : c.cur = none) (hne : c.alts ≠ []) :
      Step prog gt c (pull c)
  | answer (c : Conf) (b : Subst) (h : c.cur = some ([], b)) :
      Step prog gt c
        (pull { c with cur := none,
                       answers := subst b c.qterm :: c.answers
                       answerKeys :=
                         PersistentSubst.atomExactKey (subst b c.qterm) ::
                           c.answerKeys
                       answerKeys_sound := by
                         simp only [List.map_cons]
                         rw [c.answerKeys_sound] })
  | eq_ok (c : Conf) (x y : Atom) (rest : List Goal) (b b' : Subst)
      (h : c.cur = some (Goal.eq x y :: rest, b))
      (hu : unifyB b x y = some b') :
      Step prog gt c { c with cur := some (rest, trimFor rest c.qterm b') }
  | eq_fail (c : Conf) (x y : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.eq x y :: rest, b))
      (hu : unifyB b x y = none) :
      Step prog gt c (pull { c with cur := none })
  | cut_at (c : Conf) (k : Nat) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.cutAt k :: rest, b)) :
      Step prog gt c
        { c with
          cur := some (rest, b)
          alts := (cutToTracked k c.barriers c.alts).1
          barriers := (cutToTracked k c.barriers c.alts).2 }
  -- an UNTAGGED cut is a compile artifact (the resolution freshener tags it
  -- its clause barrier at clause entry); at runtime it kills the branch
  | cut_untagged (c : Conf) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.cut :: rest, b)) :
      Step prog gt c (pull { c with cur := none })
  -- [SPEC translator.pl:62-64] a head with NO clauses reduces to data
  | call_data (c : Conf) (f : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (he : c.world.clauseHeadCandidates f = [])
      (g : Goal) (hg : g = Goal.eq res (chainOf (Atom.sym f :: args))) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- [SPEC translator.pl:328-339] under-application -> partial(f, args)
  | call_partial (c : Conf) (f : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (hne : c.world.clauseHeadCandidates f ≠ [])
      (hna : ¬ ((c.world.resolutionCandidates f args.length).any
        (fun cl => cl.params.length == args.length)))
      (g : Goal) (hg : g = Goal.eq res
        (chainOf [Atom.sym "partial", Atom.sym f, chainOf args])) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- cached tabled call [SPEC lib_tabling.metta:7-11]: replay table answers
  | call_table_cached (c : Conf) (f : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (answers : List Atom)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (hcan : c.world.canTableCall f (args.map (subst b)) = true)
      (hcache : c.world.tableLookup (tableKey f (args.map (subst b)))
        = some answers) :
      Step prog gt c
        (pull { c with cur := none,
                       counter := advanceCounterPastAtoms c.counter answers,
                       alts := answers.map (fun ans =>
                         Alt.br (Goal.eq res ans :: rest) b) ++ c.alts })
  -- right-arity resolution (clauses tried in order, first-arg indexed)
  | call_resolve (c : Conf) (f : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (branches : List Alt) (counter' : Nat)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (hne : c.world.clauseHeadCandidates f ≠ [])
      (ha : (c.world.resolutionCandidates f args.length).any
        (fun cl => cl.params.length == args.length))
      (hres : resolveAlts (c.world.resolutionCandidates f args.length)
        (args.map (subst b)) args
        res rest b c.qterm (barrierDepth c + 1) c.counter
        = (branches, counter')) :
      Step prog gt c
        (pull { c with
          cur := none
          counter := counter'
          alts := branches ++ (Alt.barrier :: c.alts)
          barriers := pushBarrierCache c.barriers })
  -- under-applied builtin -> partial (same root as call_partial)
  | bin_partial (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (hb : binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (g : Goal) (hg : g = Goal.eq res
        (chainOf [Atom.sym "partial", Atom.sym op, chainOf (args.map (subst b))])) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- `translatePredicate` calls owned by the PLeaTTa world remain in the pure
  -- core: named spaces become `smatch`, while locally asserted/compiled
  -- predicates become ordinary `call` goals. Imported predicates are absent
  -- here and remain an explicit host boundary.
  | bin_local_translate (c : Conf) (op : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (b : Subst) (goals : List Goal)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧
        (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = some goals) :
      Step prog gt c
        { c with
          cur := some (goals, b)
          counter := advanceCounterPastGoals c.counter goals }
  -- get-type (machine oracle getTypeP)
  | bin_gettype (c : Conf) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (ts : List Atom) (c' : Nat)
      (h : c.cur = some (Goal.bin "get-type" args res :: rest, b))
      (hnp : ¬ (binArity "get-type" ≠ 0 ∧
        (args.map (subst b)).length < binArity "get-type"))
      (hl : localTranslatePredicateGoals? c.world gt "get-type"
        (args.map (subst b)) res rest = none)
      (ho : getTypeP c.world 100 c.counter
        ((args.map (subst b)).headD (Atom.sym "?")) = (ts, c')) :
      Step prog gt c
        (pull { c with cur := none,
                       counter := advanceCounterPastAtoms (max c.counter c') ts,
                       alts := ts.map (fun t =>
                         Alt.br (Goal.eq res t :: rest) b) ++
                         localGetTypeExtensionAlts c.world
                           ((args.map (subst b)).headD (Atom.sym "?"))
                           res rest b ++ c.alts })
  -- get-metatype (machine computes a fixed tag from the head atom)
  | bin_getmetatype (c : Conf) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (mt : String)
      (h : c.cur = some (Goal.bin "get-metatype" args res :: rest, b))
      (hnp : ¬ (binArity "get-metatype" ≠ 0 ∧
        (args.map (subst b)).length < binArity "get-metatype"))
      (hl : localTranslatePredicateGoals? c.world gt "get-metatype"
        (args.map (subst b)) res rest = none)
      (hmt : mt = (match (args.map (subst b)).headD (Atom.sym "?") with
        | Atom.var _ => "Variable"
        | Atom.gnd _ => "Grounded"
        | Atom.sym s =>
            if (Metta.GroundingTable.lookup gt s).isSome then "Grounded"
            else "Symbol"
        | Atom.expr _ => "Expression"))
      (g : Goal) (hg : g = Goal.eq res (Atom.sym mt)) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- nonstrict op (terms as terms), success
  | bin_nonstrict_ok (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (rs : List Atom)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype")
      (hnso : nonstrictOps.contains op)
      (hr : callGrounded gt op (args.map (subst b)) = ReduceResult.ok rs) :
      Step prog gt c
        (pull { c with
          cur := none
          counter := advanceCounterPastAtoms c.counter rs
          alts := rs.map (fun r =>
            Alt.br (Goal.eq res (canonBool r) :: rest) b) ++ c.alts })
  -- nonstrict op, failure (branch dies)
  | bin_nonstrict_fail (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype")
      (hnso : nonstrictOps.contains op)
      (hr : ¬ ∃ rs, callGrounded gt op (args.map (subst b)) = ReduceResult.ok rs) :
      Step prog gt c (pull { c with cur := none })
  | bin_ok (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (rs : List Atom)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hg : (args.map (subst b)).all Metta.isGround = true)
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hspecial : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧
                  ¬ (nonstrictOps.contains op))
      (hnm : ¬(["+", "-", "*"].contains op ∧
               ¬((args.map (subst b)).all Metta.isGround = true)))
      (hr : callGrounded gt op (args.map (subst b)) = ReduceResult.ok rs) :
      Step prog gt c
        (pull { c with
          cur := none
          counter := advanceCounterPastAtoms c.counter rs
          alts := rs.map (fun r =>
            Alt.br (Goal.eq res (canonBool r) :: rest) b) ++ c.alts })
  -- moded arithmetic [SPEC metta.pl:53-60 CLP(FD)]: +/-/* with a ground
  -- result inverts to the solvable operation
  | bin_mode (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (x y : Atom)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧ ¬ nonstrictOps.contains op)
      (hop : ["+", "-", "*"].contains op)
      (hav : args.map (subst b) = [x, y])
      (hng : ¬ ((args.map (subst b)).all Metta.isGround))
      (hrv : Metta.isGround (subst b res))
      (g : Goal) (hg : g = (match op with
        | "+" => if Metta.isGround x then Goal.bin "-" [subst b res, x] y
                                     else Goal.bin "-" [subst b res, y] x
        | "-" => if Metta.isGround x then Goal.bin "-" [x, subst b res] y
                                     else Goal.bin "+" [subst b res, y] x
        | _   => if Metta.isGround x then Goal.bin "/" [subst b res, x] y
                                     else Goal.bin "/" [subst b res, y] x)) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- moded guard fired but the argument list is not a 2-list: no inversion
  -- exists, the branch fails
  | bin_mode_fail (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧ ¬ nonstrictOps.contains op)
      (hop : ["+", "-", "*"].contains op)
      (hng : ¬ ((args.map (subst b)).all Metta.isGround))
      (hrv : Metta.isGround (subst b res))
      (hnav : ∀ x y, args.map (subst b) ≠ [x, y]) :
      Step prog gt c (pull { c with cur := none })
  -- ground builtin call that errors -> branch fails
  | bin_fail (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧ ¬ nonstrictOps.contains op)
      (hnmode : ¬ (["+", "-", "*"].contains op ∧
                   ¬ ((args.map (subst b)).all Metta.isGround) ∧
                   Metta.isGround (subst b res)))
      (hgnd : (args.map (subst b)).all Metta.isGround = true)
      (hr : ¬ ∃ rs, callGrounded gt op (args.map (subst b)) = ReduceResult.ok rs) :
      Step prog gt c (pull { c with cur := none })
  -- not ground, not moded -> delay to the end (or flounder if last)
  | bin_union_reverse (c : Conf) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (alts : List Alt)
      (h : c.cur = some (Goal.bin "union-atom" args res :: rest, b))
      (hnp : ¬ (binArity "union-atom" ≠ 0 ∧
        (args.map (subst b)).length < binArity "union-atom"))
      (hl : localTranslatePredicateGoals? c.world gt "union-atom"
        (args.map (subst b)) res rest = none)
      (hns : "union-atom" ≠ "get-type" ∧ "union-atom" ≠ "get-metatype" ∧
        ¬ nonstrictOps.contains "union-atom")
      (hnmode : ¬ (["+", "-", "*"].contains "union-atom" ∧
                   ¬ ((args.map (subst b)).all Metta.isGround) ∧
                   Metta.isGround (subst b res)))
      (hgnd : ¬ ((args.map (subst b)).all Metta.isGround = true))
      (hur : unionReverseAlts args res rest b = some alts) :
      Step prog gt c (pull { c with cur := none, alts := alts ++ c.alts })
  | bin_delay (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧ ¬ nonstrictOps.contains op)
      (hnmode : ¬ (["+", "-", "*"].contains op ∧
                   ¬ ((args.map (subst b)).all Metta.isGround) ∧
                   Metta.isGround (subst b res)))
      (hgnd : ¬ ((args.map (subst b)).all Metta.isGround = true))
      (hrest : rest ≠ []) :
      Step prog gt c { c with cur := some (rest ++ [Goal.bin op args res], b) }
  | bin_flounder (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (hnp : ¬ (binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op))
      (hl : localTranslatePredicateGoals? c.world gt op
        (args.map (subst b)) res rest = none)
      (hns : op ≠ "get-type" ∧ op ≠ "get-metatype" ∧ ¬ nonstrictOps.contains op)
      (hnmode : ¬ (["+", "-", "*"].contains op ∧
                   ¬ ((args.map (subst b)).all Metta.isGround) ∧
                   Metta.isGround (subst b res)))
      (hgnd : ¬ ((args.map (subst b)).all Metta.isGround = true))
      (hrest : rest = []) :
      Step prog gt c (pull { c with cur := none })
  | ite_true (c : Conf) (cond : Atom) (thn els : Atom × List Goal)
      (res : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.ite cond thn els res :: rest, b))
      (hc : subst b cond = Atom.sym "True") :
      Step prog gt c
        { c with cur := some (iteBranchGoals res thn ++ rest, b) }
  | ite_else (c : Conf) (cond : Atom) (thn els : Atom × List Goal)
      (res : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.ite cond thn els res :: rest, b))
      (hc : subst b cond ≠ Atom.sym "True") :
      Step prog gt c
        { c with cur := some (iteBranchGoals res els ++ rest, b) }
  | amb (c : Conf) (branches : List (Atom × List Goal)) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.amb branches res :: rest, b)) :
      Step prog gt c
        (pull { c with cur := none,
                       alts := branches.map (fun (t, gs) =>
                         Alt.br (gs ++ [Goal.eq res t] ++ rest) b)
                         ++ c.alts })
  | smatch (c : Conf) (pat : Atom) (rest : List Goal) (b : Subst)
      (alts : List Alt) (counter' : Nat)
      (h : c.cur = some (Goal.smatch pat :: rest, b))
      (hs : smatchAlts c.world c.counter b pat rest c.qterm =
        (alts, counter')) :
      Step prog gt c
        (pull { c with cur := none,
                       counter := counter',
                       alts := alts ++ c.alts })
  -- enumerate a chain value's members; a non-chain value is its own
  -- singleton (superpose over a computed tuple)
  | spread (c : Conf) (v res : Atom) (rest : List Goal) (b : Subst)
      (elems : List Atom)
      (h : c.cur = some (Goal.spread v res :: rest, b))
      (he : elems = (chainListM (subst b v)).getD [subst b v]) :
      Step prog gt c
        (pull { c with cur := none,
                       alts := elems.map (fun e =>
                         Alt.br (Goal.eq res e :: rest) b) ++ c.alts })
  -- callDyn dispatch mirrors the machine: sym head -> call / bin / data;
  -- non-sym head -> partial-dispatch / data
  | callDyn_call (c : Conf) (hd : Atom) (f : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.callDyn hd args res :: rest, b))
      (hf : subst b hd = Atom.sym f)
      (hdef : c.world.clauseHeadCandidates f ≠ []) :
      Step prog gt c { c with cur := some (Goal.call f args res :: rest, b) }
  | callDyn_bin (c : Conf) (hd : Atom) (f : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.callDyn hd args res :: rest, b))
      (hf : subst b hd = Atom.sym f)
      (he : c.world.clauseHeadCandidates f = [])
      (hbin : (Metta.GroundingTable.lookup gt f).isSome) :
      Step prog gt c { c with cur := some (Goal.bin f args res :: rest, b) }
  | callDyn_symdata (c : Conf) (hd : Atom) (f : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.callDyn hd args res :: rest, b))
      (hf : subst b hd = Atom.sym f)
      (he : c.world.clauseHeadCandidates f = [])
      (hnb : Metta.GroundingTable.lookup gt f = none)
      (g : Goal) (hg : g = Goal.eq res (chainOf (Atom.sym f :: args))) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  | callDyn_partial (c : Conf) (hd : Atom) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (base : String) (boundList : Atom)
      (bound : List Atom)
      (h : c.cur = some (Goal.callDyn hd args res :: rest, b))
      (hns : ∀ f, subst b hd ≠ Atom.sym f)
      (hp : chainListM (subst b hd)
        = some [Atom.sym "partial", Atom.sym base, boundList])
      (hbd : bound = (chainListM boundList).getD [])
      (g : Goal) (hg : g = Goal.callDyn (Atom.sym base) (bound ++ args) res) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  | callDyn_data (c : Conf) (hd : Atom) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.callDyn hd args res :: rest, b))
      (hns : ∀ f, subst b hd ≠ Atom.sym f)
      (hnp : ∀ base boundList, chainListM (subst b hd)
        ≠ some [Atom.sym "partial", Atom.sym base, boundList])
      (g : Goal) (hg : g = Goal.eq res (chainOf (subst b hd :: args))) :
      Step prog gt c { c with cur := some (g :: rest, b) }
  -- meta-circular eval [SPEC metta.pl:245]: re-compile the runtime value
  -- against the live definitions and splice the cut-tagged goals, preserving
  -- caller variables so `reduce/2` can bind variables inside its input term.
  | evalg_ok (c : Conf) (v res : Atom) (rest : List Goal) (b : Subst)
      (t : Atom) (gs : List Goal) (m : Nat) (profileWorld : PWorld)
      (profileGoals newgoals : List Goal)
      (h : c.cur = some (Goal.evalg v res :: rest, b))
      (ho : compileExprFresh (runtimeEnv c.world gt) (c.counter + 1)
              (unchainify 10000 (subst b v)) = .ok (t, gs, m))
      (hs : specializeGoals (specializationIsBin gt) specializationBuildFuel
              c.world gs = (profileWorld, profileGoals))
      (hng : newgoals = tagCutsGoals (barrierDepth c + 1) profileGoals
               ++ [Goal.eq res t] ++ rest) :
      Step prog gt c
        { c with cur := some (newgoals, b), world := profileWorld,
                 counter := advanceCounterPastGoals (max c.counter m)
                   (profileGoals ++ [Goal.eq res t] ++ rest) }
  | evalg_err (c : Conf) (v res : Atom) (rest : List Goal) (b : Subst)
      (e : String)
      (h : c.cur = some (Goal.evalg v res :: rest, b))
      (ho : compileExprFresh (runtimeEnv c.world gt) (c.counter + 1)
              (unchainify 10000 (subst b v)) = .error e)
      (g : Goal) (hg : g = Goal.eq res (chainify (unchainify 10000 (subst b v)))) :
      Step prog gt c
        { c with cur := some (g :: rest, b),
                 counter := advanceCounterPastAtoms c.counter
                   [chainify (unchainify 10000 (subst b v))] }
  -- catchg, direct fast path: caught grounded errors become values; ordinary
  -- successful direct answers are replayed as alternatives.
  | catch_direct_error (c : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
      (rest : List Goal) (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.catchg tmpl sub res :: rest, b))
      (hc : catchDirect? gt b tmpl sub = some (.error err)) :
      Step prog gt c
        { c with cur := some (Goal.eq res err :: rest, b),
                 world := c.world,
                 counter := advanceCounterPastAtoms c.counter [err] }
  | catch_direct_answers (c : Conf) (tmpl : Atom) (sub : List Goal)
      (res : Atom) (rest : List Goal) (b : Subst) (answers : List Atom)
      (h : c.cur = some (Goal.catchg tmpl sub res :: rest, b))
      (hc : catchDirect? gt b tmpl sub = some (.answers answers)) :
      Step prog gt c
        (pull { c with
          cur := none
          counter := advanceCounterPastAtoms c.counter answers
          alts := answers.map (fun inst =>
            Alt.br (Goal.eq res inst :: rest) b) ++ c.alts })
  -- catchg, general path: run the guarded sub-goals to terminality, then
  -- replay their positive answers. Failure is ordinary branch failure.
  | catch_run (c d : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.catchg tmpl sub res :: rest, b))
      (hc : catchDirect? gt b tmpl sub = none)
      (hrun : StepStar prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) :
      Step prog gt c
        (pull { c with cur := none, world := d.world, counter := d.counter,
                       alts := d.answerValues.map (fun inst =>
                         Alt.br (Goal.eq res inst :: rest) b) ++ c.alts })
  | catch_run_error (c d : Conf) (tmpl : Atom) (sub : List Goal)
      (res : Atom) (rest : List Goal) (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.catchg tmpl sub res :: rest, b))
      (hc : catchDirect? gt b tmpl sub = none)
      (hrun : Raises prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d err) :
      Step prog gt c
        { c with cur := some (Goal.eq res err :: rest, b),
                 world := d.world,
                 counter := advanceCounterPastAtoms d.counter [err] }
  | softcut_some (c d : Conf) (tmpl : Atom) (sub thn els rest : List Goal)
      (b : Subst)
      (h : c.cur = some (Goal.softcut tmpl sub thn els :: rest, b))
      (hrun : StepStar prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) (hne : d.answers ≠ []) :
      Step prog gt c
        (pull { c with cur := none, world := d.world, counter := d.counter,
                       alts := d.answerValues.map (fun inst =>
                         Alt.br (Goal.eq tmpl inst :: thn ++ rest) b)
                         ++ c.alts })
  | softcut_none (c d : Conf) (tmpl : Atom) (sub thn els rest : List Goal)
      (b : Subst)
      (h : c.cur = some (Goal.softcut tmpl sub thn els :: rest, b))
      (hrun : StepStar prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) (he : d.answers = []) :
      Step prog gt c
        { c with cur := some (els ++ rest, b),
                 world := d.world, counter := d.counter }
  | transaction_some (c d : Conf) (tmpl : Atom) (sub rest : List Goal)
      (b : Subst)
      (h : c.cur = some (Goal.transactiong tmpl sub :: rest, b))
      (hrun : StepStar prog gt
        { cur := some (transactionSub tmpl sub, b), alts := [],
          world := c.world, counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) (hne : d.answers ≠ []) :
      Step prog gt c
        (pull { c with cur := none, world := d.world, counter := d.counter,
                       alts := d.answerValues.map (fun inst =>
                         Alt.br (Goal.eq tmpl inst :: rest) b) ++ c.alts })
  | transaction_none (c d : Conf) (tmpl : Atom) (sub rest : List Goal)
      (b : Subst)
      (h : c.cur = some (Goal.transactiong tmpl sub :: rest, b))
      (hrun : StepStar prog gt
        { cur := some (transactionSub tmpl sub, b), alts := [],
          world := c.world, counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) (he : d.answers = []) :
      Step prog gt c
        (pull { c with cur := none, world := c.world, counter := d.counter })
  -- world effects go through the SHARED wactDispatch (assert/retract of
  -- compiled rule forms + the plain wactRun ops) — correspondence by
  -- construction, like resolveAlts
  | wact_ok (c : Conf) (op : String) (args : List Atom) (res r : Atom)
      (rest : List Goal) (b : Subst) (w' : PWorld) (k' : Nat)
      (h : c.cur = some (Goal.wact op args res :: rest, b))
      (hw : wactDispatch c.world gt c.counter op (args.map (subst b))
        = some (r, w', k')) :
      Step prog gt c
        { c with cur := some (Goal.eq res r :: rest, b),
                 world := w', counter := max c.counter k' }
  | wact_fail (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.wact op args res :: rest, b))
      (hw : wactDispatch c.world gt c.counter op (args.map (subst b)) = none) :
      Step prog gt c (pull { c with cur := none })
  | onceg (c : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.onceg tmpl sub res :: rest, b)) :
      Step prog gt c
        (pull { c with
          cur := none
          alts := Alt.br (sub ++ [Goal.cutAt (barrierDepth c + 1),
              Goal.eq res tmpl] ++ rest) b :: (Alt.barrier :: c.alts)
          barriers := pushBarrierCache c.barriers })
  | findall (c d : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
      (rest : List Goal) (b : Subst)
      (h : c.cur = some (Goal.findall tmpl sub res :: rest, b))
      (hrun : StepStar prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) :
      Step prog gt c
        { c with
          cur := some (Goal.eq res (chainOf d.answerValues) :: rest, b),
                 world := d.world, counter := d.counter }
  -- uncached tabled calls compute the ground variant once, cache the answer
  -- bank, then replay the answers. Fuel exhaustion is not a semantic step.
  | call_table_compute (c d : Conf) (f : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (b : Subst) (tres : Atom)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (hcan : c.world.canTableCall f (args.map (subst b)) = true)
      (hcache : c.world.tableLookup (tableKey f (args.map (subst b))) = none)
      (htres : tres = tableFresh c)
      (hrun : StepStar prog gt
        { cur := some ([Goal.call f (args.map (subst b)) tres], []),
          alts := [],
          world := { c.world with
            tableActive := tableKey f (args.map (subst b)) :: c.world.tableActive },
          counter := advanceCounterPastAtoms (c.counter + 1) [tres],
          qterm := tres,
          barriers := resetBarrierCache c.barriers } d)
      (hdone : Terminal d) :
      Step prog gt c
        (pull { c with cur := none,
                       world := (d.world.deactivateTable
                         (tableKey f (args.map (subst b)))).tableInsert
                           (tableKey f (args.map (subst b))) d.answerValues,
                       counter := d.counter,
                       alts := d.answerValues.map (fun ans =>
                         Alt.br (Goal.eq res ans :: rest) b) ++ c.alts })

inductive StepStar (prog : Prog) (gt : GroundingTable) : Conf → Conf → Prop where
  | refl (c : Conf) : StepStar prog gt c c
  | tail (a b c : Conf) : Step prog gt a b → StepStar prog gt b c →
      StepStar prog gt a c

/-- Exceptional execution of the clean machine. `Raises c d err` means that
    ordinary semantic steps and/or a nested semantic sub-run reach the exact
    configuration `d` at which `err` escapes. Catch is deliberately absent:
    `Step.catch_run_error` converts a nested exception back into an ordinary
    value-producing step. -/
inductive Raises (prog : Prog) (gt : GroundingTable) :
    Conf → Conf → Atom → Prop where
  | bin (c : Conf) (op : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.bin op args res :: rest, b))
      (herr : catchDirect? gt b res [Goal.bin op args res] =
        some (.error err)) :
      Raises prog gt c c err
  | step (a b d : Conf) (err : Atom)
      (hstep : Step prog gt a b) (hraise : Raises prog gt b d err) :
      Raises prog gt a d err
  | transaction (c d : Conf) (tmpl : Atom) (sub rest : List Goal)
      (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.transactiong tmpl sub :: rest, b))
      (hrun : Raises prog gt
        { cur := some (transactionSub tmpl sub, b), alts := [],
          world := c.world, counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d err) :
      Raises prog gt c d err
  | softcut (c d : Conf) (tmpl : Atom) (sub thn els rest : List Goal)
      (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.softcut tmpl sub thn els :: rest, b))
      (hrun : Raises prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d err) :
      Raises prog gt c d err
  | findall (c d : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
      (rest : List Goal) (b : Subst) (err : Atom)
      (h : c.cur = some (Goal.findall tmpl sub res :: rest, b))
      (hrun : Raises prog gt
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers } d err) :
      Raises prog gt c d err
  | table (c d : Conf) (f : String) (args : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (tres : Atom) (err : Atom)
      (h : c.cur = some (Goal.call f args res :: rest, b))
      (hcan : c.world.canTableCall f (args.map (subst b)) = true)
      (hcache : c.world.tableLookup (tableKey f (args.map (subst b))) = none)
      (htres : tres = tableFresh c)
      (hrun : Raises prog gt
        { cur := some ([Goal.call f (args.map (subst b)) tres], []),
          alts := [],
          world := { c.world with
            tableActive := tableKey f (args.map (subst b)) ::
              c.world.tableActive },
          counter := advanceCounterPastAtoms (c.counter + 1) [tres],
          qterm := tres,
          barriers := resetBarrierCache c.barriers } d err) :
      Raises prog gt c d err

end

def findallRunHead (c : Conf) : Prop :=
  ∃ tmpl sub res rest b,
    c.cur = some (Goal.findall tmpl sub res :: rest, b)

def softcutRunHead (c : Conf) : Prop :=
  ∃ tmpl sub thn els rest b,
    c.cur = some (Goal.softcut tmpl sub thn els :: rest, b)

def catchRunHead (c : Conf) : Prop :=
  ∃ tmpl sub res rest b,
    c.cur = some (Goal.catchg tmpl sub res :: rest, b)

def transactionRunHead (c : Conf) : Prop :=
  ∃ tmpl sub rest b,
    c.cur = some (Goal.transactiong tmpl sub :: rest, b)

def tableRunHead (c : Conf) : Prop :=
  ∃ f args res rest b,
    c.cur = some (Goal.call f args res :: rest, b) ∧
    c.world.needsTableCompute f (args.map (subst b)) = true

/-- The current branch's head goal nests a fuel-bounded sub-run (`findall`,
    `softcut`, `catchg`, or uncached tabled call). These are the machine's
    fuel-truncatable steps. -/
def nestedRunHead (c : Conf) : Prop :=
  findallRunHead c ∨
    (softcutRunHead c ∨
      (catchRunHead c ∨ (tableRunHead c ∨ transactionRunHead c)))

/-- Correspondence: whenever the executable makes progress on a goal that
    does not nest a sub-run, the relation licenses that exact step. Nested
    heads (`findall`/`softcut`/`catchg`) are excluded per `nestedRunHead` —
    for those the relation demands terminal sub-runs, which fuel cannot
    promise. -/
def machineMirrorsSpec : Prop :=
  ∀ (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf),
    (c.cur.isSome ∨ c.alts ≠ []) →
    Step prog gt c (step prog gt fuel c) ∨ nestedRunHead c

/-- Total correspondence for the clean executable lane. Unlike
    `machineMirrorsSpec`, this speaks about `stepClean`/`runClean`, the machine
    the CLI executes, and has no `nestedRunHead` escape. Successful outcomes
    are licensed by `Step`/`StepStar`; exceptional outcomes are licensed by
    `Raises`, including propagation through nested runs and recovery by catch.
    Fuel-limited or exhausted clean runs are deliberately outside the claim. -/
def machineMirrorsSpecTotal : Prop :=
  (∀ (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c c' : Conf),
    (c.cur.isSome ∨ c.alts ≠ []) →
    stepClean prog gt fuel c = .progressed c' →
    Step prog gt c c') ∧
  (∀ (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
      (limit : Option Nat) (d : Conf),
    runClean prog gt fuel c limit = .done d →
    StepStar prog gt c d ∧ Terminal d) ∧
  (∀ (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c d : Conf)
      (err : Atom),
    stepClean prog gt fuel c = .errored d err →
    Raises prog gt c d err) ∧
  (∀ (prog : Prog) (gt : GroundingTable) (fuel : Nat) (c : Conf)
      (limit : Option Nat) (d : Conf) (err : Atom),
    runClean prog gt fuel c limit = .errored d err →
    Raises prog gt c d err)

end PLeaTTa
