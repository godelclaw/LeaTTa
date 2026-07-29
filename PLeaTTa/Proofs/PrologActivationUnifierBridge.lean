-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivationUnifierBridge
Purpose: Rule out executable head-unification failure for one independently
  resolved, supported local clause occurrence.
Trusted boundary: none
Main exports:
  SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
-/
import PLeaTTa.Proofs.PrologCallPayloadBridge
import PLeaTTa.Proofs.PrologMguValuation

namespace PLeaTTa.PrologActivationUnifierBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge
open PrologCallEntryBridge
open PrologPrefilterBridge
open PrologCallPayloadBridge
open PrologMguBridge

/-! ## One semantically matched prepared occurrence -/

/-- If the independent local resolver has an ordered canonical MGU for one
real prepared clause occurrence, the executable full-head `unifyB` call for
that same occurrence succeeds.

This is intentionally only a success theorem.  It rules out the executable
`eq_fail` transition on a semantically matched branch, but does not identify
the returned executable substitution with the independent MGU and does not
justify the subsequent executable `trimFor`.  Those output obligations remain
the next activation-refinement seam. -/
theorem SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ executableResult,
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some executableResult := by
  cases agreement with
  | intro reference freshSeed executable base encoding =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (queryAlpha.map Prod.fst) :=
        queryReferenceBelow.mono startsAbove
      have bindingBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index
          (List.mem_append_right _ indexMember)
      have bindingBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (substitutionVariables cursor.bindings) :=
        bindingBelowStart.mono startsAbove
      have domains :
          Substitution.DomainsBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            cursor.bindings :=
        Substitution.domainsBelow_of_generatedBelow bindingBelowFresh
      have headAgreement :=
        freshCopy_prefilter_head_alpha_agrees base freshSeed
      rcases headAgreement.outputLast with
        ⟨referenceParameters, referenceResult, referenceArguments,
          parameterAgreement, resultAgreement⟩
      have fullClauseAgreement :
          AlphaTermsAgree
            (prefilterAlpha reference.clause freshSeed)
            (reference.clause.freshCopy freshSeed).clause.arguments
            (clause.params ++ [clause.result]) := by
        rw [referenceArguments]
        exact AlphaTermsAgree.append_singleton
          parameterAgreement resultAgreement
      have generated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have stable :
          cursor.bindings.applyTerms
              (reference.clause.freshCopy freshSeed).clause.arguments =
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        Substitution.applyTerms_eq_self_of_generatedAtLeast domains generated
      have normalizedLengths :
          (cursor.bindings.applyTerms cursor.arguments).length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        have queryLength := AlphaTermsAgree.length_eq query.arguments
        have clauseLength := AlphaTermsAgree.length_eq fullClauseAgreement
        simp only [List.length_append, List.length_singleton,
          List.length_map] at queryLength clauseLength
        omega
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        simpa only [Substitution.applyTerms_length] using normalizedLengths
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments) :=
        preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      rcases resolved with
        ⟨extension, ⟨canonical, derivation, extensionShape⟩, resultShape⟩
      have ordered :
          OrderedTreeMgu
            (denoteEquations
              (argumentEquations
                (cursor.bindings.applyTerms cursor.arguments)
                (reference.clause.freshCopy freshSeed).clause.arguments))
            canonical := by
        rw [← stable, ← normalizedEquations]
        exact derivation
      have freshened :=
        freshenClause_actual_alpha_agrees
          base encoding freshSeed
          (args.map (PLeaTTa.subst binding)) args result rest binding qterm
          seed barrier
      exact
        PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.unifyB_complete_of_ordered_mgu
            freshened rfl queryShared query.arguments queryBelowFresh
            queryExecutableLive highWater normalizedLengths ordered

/-- Equivalent negative formulation used when excluding the executable
`eq_fail` constructor in a step correspondence proof. -/
theorem SupportedPreparedCandidateAgrees.unifyB_ne_none_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    PLeaTTa.unifyB binding (.expr (args ++ [result]))
        (.expr
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result])) ≠
      none := by
  obtain ⟨executableResult, success⟩ :=
    PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
        query wellFormed member agreement arity queryShared
        queryReferenceBelow queryExecutableLive highWater resolved
  rw [success]
  simp

/-! ## Paired activation step -/

/-- A matched independent cursor pull and the corresponding executable
full-head equality both advance successfully.

The theorem pins the actual `RawStep.clausesPull` splice and actual
`PLeaTTa.Step.eq_ok` constructor.  Its two successors intentionally remain
unrelated at the binding payload: proving that `trimFor executableResult`
represents `branch.enter independentResult` is the still-open output
refinement, rather than a premise smuggled into this input-success result. -/
theorem matched_clause_eq_ok_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {session : Session} {scope : CutScopeId}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch} {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution} {conf : PLeaTTa.Conf}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (remaining : cursor.remaining = branch :: branches)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult)
    (current :
      conf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [result]))
              (.expr
                ((freshenResolutionClause
                    (args.map (PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).params ++
                  [(freshenResolutionClause
                    (args.map (PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).result])) ::
            (freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest,
            binding)) :
    ∃ executableResult,
      RawStep session (.clauses scope cursor) [] .none session
          (.running
            (.choice scope
              (.task scope (branch.enter independentResult).rawBody
                (branch.enter independentResult).bindings)
              (.clauses scope (cursor.advance branch branches)))) ∧
        PLeaTTa.Step prog gt conf
          { conf with
            cur :=
              some
                ((freshenResolutionClause
                    (args.map (PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).body ++ rest,
                  PLeaTTa.trimFor
                    ((freshenResolutionClause
                      (args.map (PLeaTTa.subst binding)) args result rest
                      binding qterm seed barrier clause).body ++ rest)
                    conf.qterm executableResult) } := by
  have member : branch ∈ cursor.remaining := by
    rw [remaining]
    simp
  obtain ⟨executableResult, success⟩ :=
    PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  refine ⟨executableResult, ?_, ?_⟩
  · exact matched_clause_splices_body_first scope session
      (.matched cursor branch branches independentResult remaining resolved)
  · exact .eq_ok conf
      (.expr (args ++ [result]))
      (.expr
        ((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding qterm
            seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding qterm
            seed barrier clause).result]))
      ((freshenResolutionClause
        (args.map (PLeaTTa.subst binding)) args result rest binding qterm seed
        barrier clause).body ++ rest)
      binding executableResult current success

end PLeaTTa.PrologActivationUnifierBridge
