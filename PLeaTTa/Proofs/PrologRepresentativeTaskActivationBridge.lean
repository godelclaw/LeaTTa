-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeTaskActivationBridge
Purpose: Compose one representation-independent retained-clause head
  activation into the exact cumulative clause-body task payload.
Trusted boundary: none
Main exports:
  SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution
-/
import PLeaTTa.Proofs.PrologRepresentativeActivationBridge
import PLeaTTa.Proofs.PrologOrdinaryStepBridge

namespace PLeaTTa.PrologRepresentativeTaskActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologGoalAlpha
open PrologAlphaFreshFrontierBridge
open PrologCallPayloadBridge
open PrologCallEntryBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeActivationBridge
open PrologStateBridge

/-! ## Structural transport into the activated task -/

/-- A supported prepared occurrence carries exactly the cursor binding used
to construct it.  Naming this constructor projection keeps the composition
proof independent of the concrete `preparedBranchOf` record fields. -/
theorem SupportedPreparedCandidateAgrees.branch_bindings_eq
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (agreement :
      SupportedPreparedCandidateAgrees callGeneration predicate
        arguments bindings branch clause) :
    branch.bindings = bindings := by
  cases agreement
  rfl

/-- Alpha coverage of a canonical substitution is monotone under inclusion
of the shared alpha graph. -/
theorem TreeSubstitutionVariablesSatisfy.monoAlpha
    {smaller larger : List (LogicVar × String)}
    {binding : TreeSubstitution}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (covered :
      TreeSubstitutionVariablesSatisfy (AlphaCovers smaller) binding) :
    TreeSubstitutionVariablesSatisfy (AlphaCovers larger) binding := by
  intro entry member
  have entryCovered := covered entry member
  exact
    ⟨by
      rcases entryCovered.1 with ⟨name, linked⟩
      exact ⟨name, included _ linked⟩,
      TreeVariablesSatisfy.mono
        (fun identity identityCovered => by
          rcases identityCovered with ⟨name, linked⟩
          exact ⟨name, included _ linked⟩)
        entryCovered.2⟩

/-- A cumulative valuation already known on a smaller alpha graph remains
valid when every link is embedded in the larger shared graph. -/
theorem AlphaValuationAgreesOn.monoAlpha
    {smaller larger support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (valuation :
      AlphaValuationAgreesOn smaller support canonical runtime) :
    AlphaValuationAgreesOn larger support canonical runtime := by
  intro identity name linked
  exact
    PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
      included (valuation linked)

/-! ## Exact clause-body activation -/

/-- The generated executable MGU remains related to the chosen canonical
representative before it is installed over the caller's carried binding.

This evidence is deliberately separate from the support-restricted
cumulative payload. Fresh clause-body variables belong to the enlarged alpha
graph but not to the caller's fixed observable support; recursive call
materialization therefore needs this full generated valuation. -/
structure GeneratedMguAgrees
    (alpha : List (LogicVar × String))
    (flattened : TreeSubstitution) (base generated installed : Subst) : Prop
    where
  substitution : AlphaTreeSubstitutionAgrees alpha flattened generated
  topological : Nonempty (PLeaTTa.SubstTopological generated)
  valuation : AlphaValuationAgrees alpha flattened generated
  avoidsBase : PLeaTTa.SubstEntriesAvoid base generated
  installedShape : installed = installGenerated generated base

/-- One source-resolved retained clause activates the actual executable
head, composes that new MGU over both carried states, and enters the exact
clause body while preserving the single representative selected for the
recursive call.

The result is deliberately stronger than a bare `TaskPayloadAgrees`: the
selected successor representative remains visible, so a later call or
backtracking proof cannot silently choose a different variant witness. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution_extension
    {payloadAlpha ambientAlpha support : List (LogicVar × String)}
    {oldCanonical residualRepresentative : TreeSubstitution}
    {referenceBase : Substitution}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {referenceFrontier executableFrontier : Nat}
    {protectedExecutableEnd : Nat}
    {independentResult : Substitution}
    (oldCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        payloadAlpha support oldCanonical referenceBase binding
        residualRepresentative)
    (query :
      RepresentativeNormalizedCallAgreesWith payloadAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result)
        residualRepresentative referenceBase)
    (cursorBindingShape :
      cursor.bindings =
        TreeSubstitution.reify oldCanonical ++ referenceBase)
    (oldCanonicalWellFormed : oldCanonical.WellFormed)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (payloadIncluded :
      ∀ pair, pair ∈ payloadAlpha → pair ∈ ambientAlpha)
    (ambientShared : SharedRuntimeAlpha ambientAlpha)
    (payloadReferenceBelow :
      GeneratedBelow cursor.reservationStart (payloadAlpha.map Prod.fst))
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (ambientFresh :
      AlphaFreshFrontier ambientAlpha referenceFrontier executableFrontier)
    (referenceEnd : branch.nextFresh ≤ referenceFrontier)
    (executableEnd : seed + 1 ≤ executableFrontier)
    (ambientGap :
      AlphaAllocationGap ambientAlpha cursor.reservationStart
        cursor.reservedUntil seed protectedExecutableEnd)
    (seedReserved : seed + 1 ≤ protectedExecutableEnd)
    (live :
      AlphaRuntimeNamesLive support
        ((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).body ++ rest)
        qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha sourceCanonical flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      (∀ pair, pair ∈ ambientAlpha → pair ∈ alpha) ∧
      AlphaExtendsAbove ambientAlpha alpha branch.firstFresh seed ∧
      AlphaFreshFrontier alpha referenceFrontier executableFrontier ∧
      AlphaAllocationGap alpha branch.nextFresh cursor.reservedUntil
        (seed + 1) protectedExecutableEnd ∧
      (∀ index, branch.firstFresh ≤ index → index < branch.nextFresh →
        AlphaCovers alpha (.generated index)) ∧
      independentResult =
        TreeSubstitution.reify (sourceCanonical ++ oldCanonical) ++
          referenceBase ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      GeneratedMguAgrees alpha flattened binding generated installed ∧
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support (sourceCanonical ++ oldCanonical) referenceBase
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) ∧
      TaskPayloadAgrees alpha support barrier
        (sourceCanonical ++ oldCanonical) referenceBase independentResult
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      MaterializedLocalCallHeadsAgreeWith alpha independentResult branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) referenceBase := by
  obtain
    ⟨alpha, sourceCanonical, representative, _semanticCanonical,
      flattened, generated, installed, shared, queryIncluded, extensionAbove,
      freshFrontier, allocationGap, selectedIntervalCovered, bodyControl,
      representativeExact,
      independentShape,
      sourceOrdered,
      successorVariants, _semanticOrdered, _equationAgreement,
      generatedExact, generatedAgreement, flattenedTopological,
      ⟨generatedTopological⟩, generatedValuation, _flattenedMgu,
      _flattenedFactors, _semanticFactors, installedExact,
      installedShape⟩ :=
    PLeaTTa.PrologRepresentativeActivationBridge.SupportedPreparedCandidateAgrees.unifyB_representativeWith_of_headResolution_extension
      (barrier := barrier) query wellFormed member agreement arity
      payloadIncluded ambientShared payloadReferenceBelow highWater
      ambientFresh referenceEnd executableEnd ambientGap seedReserved resolved
  have branchBindings : branch.bindings = cursor.bindings :=
    PLeaTTa.PrologRepresentativeTaskActivationBridge.SupportedPreparedCandidateAgrees.branch_bindings_eq
      agreement
  have sourceWellFormed : sourceCanonical.WellFormed :=
    sourceOrdered.binding_wellFormed
      (denoteEquations_wellFormed branch.normalizedHeadEquations)
  have compositeWellFormed :
      (sourceCanonical ++ oldCanonical).WellFormed :=
    sourceWellFormed.append oldCanonicalWellFormed
  have compositeResultShape :
      independentResult =
        TreeSubstitution.reify (sourceCanonical ++ oldCanonical) ++
          referenceBase := by
    calc
      independentResult =
          TreeSubstitution.reify sourceCanonical ++ branch.bindings :=
        independentShape
      _ =
          TreeSubstitution.reify sourceCanonical ++
            (TreeSubstitution.reify oldCanonical ++ referenceBase) := by
        rw [branchBindings, cursorBindingShape]
      _ =
          TreeSubstitution.reify (sourceCanonical ++ oldCanonical) ++
            referenceBase := by
        rw [
          PLeaTTa.PrologSequentialMgu.TreeSubstitution.reify_append]
        simp only [List.append_assoc]
  have normalizedEquationShape :
      denoteEquations branch.normalizedHeadEquations =
        TreeSubstitution.applyEquations
          (oldCanonical ++ Substitution.denote referenceBase)
          (denoteEquations branch.headEquations) := by
    rw [ClauseBranch.denote_normalizedHeadEquations, branchBindings,
      cursorBindingShape, Substitution.denote_append,
      TreeSubstitution.denote_reify oldCanonicalWellFormed]
  have sourceEquationsAvoidOld :
      TreeEquationsVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys oldCanonical)
        (denoteEquations branch.normalizedHeadEquations) := by
    rw [normalizedEquationShape]
    exact
      PLeaTTa.PrologMguComposition.TreeSubstitutionTopological.applyEquations_append_avoids
        (older := Substitution.denote referenceBase)
        oldCumulative.canonicalTopological
        (denoteEquations branch.headEquations)
  have sourceCompositeTopological :
      TreeSubstitutionTopological (sourceCanonical ++ oldCanonical) :=
    PrologSequentialMgu.OrderedTreeMgu.prepend_topological_of_equations_avoid
      oldCumulative.canonicalTopological sourceOrdered
      sourceEquationsAvoidOld
  have cumulativeVariants :
      TreeSubstitutionVariants
        ((sourceCanonical ++ oldCanonical) ++
          Substitution.denote referenceBase)
        ((flattened ++ residualRepresentative) ++
          Substitution.denote referenceBase) := by
    have variants := successorVariants
    rw [compositeResultShape, Substitution.denote_append,
      TreeSubstitution.denote_reify compositeWellFormed,
      representativeExact] at variants
    simpa [List.append_assoc] using variants
  have successorRepresentativeCovered :
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha)
        (flattened ++ residualRepresentative) :=
    treeSubstitutionVariablesSatisfy_append
      generatedAgreement.variablesSatisfy
      (PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
        (fun pair member =>
          queryIncluded pair (payloadIncluded pair member))
        oldCumulative.representativeCovered)
  have selectedStartsAbove : cursor.reservationStart ≤ branch.firstFresh :=
    wellFormed.1.start_le_member_first member
  have payloadBelowSelected :
      GeneratedBelow branch.firstFresh (payloadAlpha.map Prod.fst) :=
    payloadReferenceBelow.mono selectedStartsAbove
  have cursorBelowStart :
      GeneratedBelow cursor.reservationStart
        (substitutionVariables cursor.bindings) := by
    intro index indexMember
    exact wellFormed.2.1 index
      (List.mem_append_right _ indexMember)
  have cursorBelowSelected :
      GeneratedBelow branch.firstFresh
        (substitutionVariables cursor.bindings) :=
    cursorBelowStart.mono selectedStartsAbove
  have residualKeysBelow :
      ∀ identity,
        identity ∈ TreeSubstitution.keys residualRepresentative →
          identity.GeneratedBelowBoundary branch.firstFresh :=
    PLeaTTa.PrologRepresentativeActivationBridge.TreeSubstitutionVariablesSatisfy.keysGeneratedBelow
      oldCumulative.representativeCovered payloadBelowSelected
  have referenceBaseKeysBelow :
      ∀ identity,
        identity ∈
            TreeSubstitution.keys (Substitution.denote referenceBase) →
          identity.GeneratedBelowBoundary branch.firstFresh :=
    Substitution.denote_keysGeneratedBelow_of_subset
      query.olderBaseIncluded cursorBelowSelected
  have oldRepresentativeKeysBelow :
      ∀ identity,
        identity ∈ TreeSubstitution.keys
            (residualRepresentative ++ Substitution.denote referenceBase) →
          identity.GeneratedBelowBoundary branch.firstFresh := by
    intro identity identityMember
    have split :
        identity ∈ TreeSubstitution.keys residualRepresentative ∨
          identity ∈
            TreeSubstitution.keys (Substitution.denote referenceBase) := by
      simpa [TreeSubstitution.keys, List.map_append] using identityMember
    exact split.elim (residualKeysBelow identity)
      (referenceBaseKeysBelow identity)
  rcases oldCumulative.runtimeTopological with ⟨bindingTopological⟩
  have resolvedAvoids (atom : Atom) :
      PLeaTTa.AtomAvoids binding (PLeaTTa.subst binding atom) := by
    intro name nameMember
    exact bindingTopological.subst_resolvesDomain
      binding atom name nameMember
  have leftAvoids :
      PLeaTTa.AtomAvoids binding
        (.expr ((args ++ [result]).map (PLeaTTa.subst binding))) := by
    simpa only [PLeaTTa.subst_expr] using
      resolvedAvoids (.expr (args ++ [result]))
  have rightAvoids :
      PLeaTTa.AtomAvoids binding
        (.expr
          (((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]).map
            (PLeaTTa.subst binding))) := by
    simpa only [PLeaTTa.subst_expr] using
      resolvedAvoids
        (.expr
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]))
  have generatedAvoidsBinding :
      PLeaTTa.SubstEntriesAvoid binding generated :=
    PLeaTTa.unifyTopExact_avoidsExternal binding
      (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
      (.expr
        (((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]).map
          (PLeaTTa.subst binding)))
      generated leftAvoids rightAvoids generatedExact
  have installedShape' :
      installed = installGenerated generated binding := by
    cases generated with
    | nil =>
        simpa [installGenerated] using installedShape
    | cons head tail =>
        simpa [installGenerated] using installedShape
  have installedTopological :
      PLeaTTa.SubstTopological installed := by
    rw [installedShape']
    exact
      installGeneratedTopological bindingTopological generatedTopological
        generatedAvoidsBinding
  have oldValuation :
      AlphaValuationAgreesOn alpha support
        (residualRepresentative ++ Substitution.denote referenceBase)
        binding :=
    PLeaTTa.PrologRepresentativeTaskActivationBridge.AlphaValuationAgreesOn.monoAlpha
      (fun pair member =>
        queryIncluded pair (payloadIncluded pair member))
      oldCumulative.valuation
  have installedValuation :
      AlphaValuationAgreesOn alpha support
        ((flattened ++ residualRepresentative) ++
          Substitution.denote referenceBase)
        installed := by
    have lifted :
        AlphaValuationAgreesOn alpha support
          (flattened ++
            (residualRepresentative ++ Substitution.denote referenceBase))
          (installGenerated generated binding) :=
      AlphaValuationAgreesOn.installGenerated_compose
        oldValuation bindingTopological generatedTopological
        generatedAvoidsBinding generatedValuation
    intro identity name linked
    rw [installedShape']
    simpa [List.append_assoc] using lifted linked
  have installedCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support (sourceCanonical ++ oldCanonical) referenceBase
        installed (flattened ++ residualRepresentative) :=
    ⟨cumulativeVariants, sourceCompositeTopological,
      successorRepresentativeCovered, ⟨installedTopological⟩,
      installedValuation⟩
  have trimmedCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support (sourceCanonical ++ oldCanonical) referenceBase
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) :=
    installedCumulative.trimFor live
  have task :
      TaskPayloadAgrees alpha support barrier
        (sourceCanonical ++ oldCanonical) referenceBase independentResult
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body :=
    ⟨shared, compositeWellFormed, compositeResultShape,
      NormalizedAlphaGoalsAgree.ofAlphaGoalsAgree bodyControl,
      trimmedCumulative.weak⟩
  have bodyHeadMaterialized :
      MaterializedLocalCallHeadsAgreeWith alpha independentResult branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) referenceBase := by
    cases agreement with
    | intro reference freshSeed executable base encoding bodySupported =>
        intro predicate referencePayload referenceRest executableArguments
          executableResult executableRest referenceShape executableShape
        let suffix :=
          resolutionFreshSuffix
            (args.map (PLeaTTa.subst binding)) result rest binding qterm seed
        let clauseAlpha :=
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.clause.freshCopy freshSeed).firstFresh
              reference.clause.variables)
            (executableFreshTargets suffix reference.clause.variables)
        have clauseRuntimeAlpha :
            RuntimeAlpha
              (referenceFreshTargets
                (reference.clause.freshCopy freshSeed).firstFresh
                reference.clause.variables)
              (executableFreshTargets suffix reference.clause.variables) := by
          exact freshenClause_alpha_agrees reference.clause freshSeed suffix
            encoding
        have sourceBodyShape :
            (reference.clause.freshCopy freshSeed).clause.body =
              .call predicate referencePayload :: referenceRest := by
          simpa [preparedBranchOf] using referenceShape
        have clauseBodyControl :
            AlphaGoalsAgree clauseAlpha barrier
              (reference.clause.freshCopy freshSeed).clause.body
              (freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).body := by
          simpa [clauseAlpha, suffix] using
            (freshenClause_body_alpha_agrees base bodySupported freshSeed
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier)
        have localHeadControl :
            NormalizedAlphaGoalsAgree clauseAlpha barrier
              (.call predicate referencePayload :: referenceRest)
              (.call predicate executableArguments executableResult ::
                executableRest) := by
          have normalized :=
            NormalizedAlphaGoalsAgree.ofAlphaGoalsAgree clauseBodyControl
          rw [sourceBodyShape, executableShape] at normalized
          exact normalized
        have ambientHeadControl :
            NormalizedAlphaGoalsAgree alpha barrier
              (.call predicate referencePayload :: referenceRest)
              (.call predicate executableArguments executableResult ::
                executableRest) := by
          have normalized :=
            NormalizedAlphaGoalsAgree.ofAlphaGoalsAgree bodyControl
          rw [referenceShape, executableShape] at normalized
          exact normalized
        obtain
          ⟨ambientReferenceArguments, ambientReferenceResult,
            ambientPayloadShape, ambientArguments, ambientResult, _⟩ :=
          NormalizedAlphaGoalsAgree.localCallHead ambientHeadControl
        have ambientPayload :
            AlphaTermsAgree alpha referencePayload
              (executableArguments ++ [executableResult]) := by
          rw [ambientPayloadShape]
          exact AlphaTermsAgree.append_singleton ambientArguments ambientResult
        obtain
          ⟨localReferenceArguments, localReferenceResult,
            localPayloadShape, localArguments, localResult, _⟩ :=
          NormalizedAlphaGoalsAgree.localCallHead localHeadControl
        have localPayload :
            AlphaTermsAgree clauseAlpha referencePayload
              (executableArguments ++ [executableResult]) := by
          rw [localPayloadShape]
          exact AlphaTermsAgree.append_singleton localArguments localResult
        have clauseReferenceRange :
            ∀ identity name, (identity, name) ∈ clauseAlpha →
              ∃ index, identity = .generated index ∧
                (reference.clause.freshCopy freshSeed).firstFresh ≤ index := by
          intro identity name linked
          have projectionMember :
              identity ∈ clauseAlpha.map Prod.fst :=
            List.mem_map.mpr ⟨(identity, name), linked, rfl⟩
          rw [clauseRuntimeAlpha.graph_reference] at projectionMember
          exact referenceFreshTargets_generated_lower projectionMember
        have sourceFresh :
            Terms.GeneratedAtLeast
              (reference.clause.freshCopy freshSeed).firstFresh
              referencePayload :=
          AlphaTermsAgree.generatedAtLeast_of_graph localPayload
            clauseReferenceRange
        have runtimeAvoidsBase :
            List.Forall₂
              (fun _ atom => PLeaTTa.AtomAvoids binding atom)
              referencePayload
              (executableArguments ++ [executableResult]) := by
          have runtimeAvoidsBase_of_agrees :
              ∀ {referenceAtoms runtimeAtoms},
                AlphaTermsAgree clauseAlpha referenceAtoms runtimeAtoms →
                  List.Forall₂
                    (fun _ atom => PLeaTTa.AtomAvoids binding atom)
                    referenceAtoms runtimeAtoms := by
            intro referenceAtoms runtimeAtoms termsAgree
            induction termsAgree with
            | nil => exact .nil
            | cons head tail inductionHypothesis =>
                apply List.Forall₂.cons
                · intro name nameMember
                  obtain ⟨identity, linked⟩ :=
                    PLeaTTa.PrologMguTopology.AlphaTermAgrees.runtime_variable_linked
                      head nameMember
                  have projectionMember : name ∈ clauseAlpha.map Prod.snd :=
                    List.mem_map.mpr ⟨(identity, name), linked, rfl⟩
                  rw [clauseRuntimeAlpha.graph_executable] at projectionMember
                  simp only [executableFreshTargets, List.mem_map] at projectionMember
                  obtain ⟨source, _sourceMember, targetShape⟩ := projectionMember
                  rw [← targetShape]
                  exact resolutionFreshSuffix_lookup_none
                    (args.map (PLeaTTa.subst binding)) result rest binding qterm
                    seed highWater
                    (OpenBindingAgreement.logicVarExecutableName source)
                · exact inductionHypothesis
          exact runtimeAvoidsBase_of_agrees localPayload
        refine
          ⟨?_, successorRepresentativeCovered, ?_, ?_⟩
        · rw [compositeResultShape, Substitution.denote_append,
              TreeSubstitution.denote_reify compositeWellFormed]
          exact cumulativeVariants
        · intro entry entryMember
          rw [compositeResultShape]
          simp [entryMember]
        · let allRuntimeAtoms := executableArguments ++ [executableResult]
          have transport :
              ∀ {sourceTerms runtimeAtoms},
                AlphaTermsAgree alpha sourceTerms runtimeAtoms →
                Terms.GeneratedAtLeast
                  (reference.clause.freshCopy freshSeed).firstFresh
                  sourceTerms →
                List.Forall₂
                  (fun _ atom => PLeaTTa.AtomAvoids binding atom)
                  sourceTerms runtimeAtoms →
                (∀ atom, atom ∈ runtimeAtoms → atom ∈ allRuntimeAtoms) →
                List.Forall₂
                  (fun term atom =>
                    CanonicalRuntimeAgrees alpha
                      (TreeSubstitution.apply
                        ((flattened ++ residualRepresentative) ++
                          Substitution.denote referenceBase)
                        (Term.denote term))
                      (PLeaTTa.subst
                        (PLeaTTa.trimFor
                          ((freshenResolutionClause
                              (args.map (PLeaTTa.subst binding)) args result
                              rest binding qterm seed barrier clause).body ++
                            rest)
                          qterm installed)
                        atom))
                  sourceTerms runtimeAtoms := by
            intro sourceTerms runtimeAtoms agreement sourceBounds atomAvoids
              included
            induction agreement with
            | nil => exact .nil
            | @cons sourceTerm runtimeAtom sourceTail runtimeTail head tail
                inductionHypothesis =>
                rcases sourceBounds with ⟨sourceBound, tailBounds⟩
                cases atomAvoids with
                | cons runtimeAvoids tailAvoids =>
                    apply List.Forall₂.cons
                    · have atomMember : runtimeAtom ∈ allRuntimeAtoms :=
                        included runtimeAtom (by simp)
                      have callAtomMember :
                          runtimeAtom ∈ executableResult :: executableArguments := by
                        rcases List.mem_append.mp atomMember with argumentMember |
                            resultMember
                        · exact List.mem_cons_of_mem executableResult argumentMember
                        · have runtimeAtomEq : runtimeAtom = executableResult :=
                            List.mem_singleton.mp resultMember
                          subst runtimeAtom
                          exact List.mem_cons_self
                      have sourceOutside :
                          TreeVariablesSatisfy
                            (fun identity =>
                              identity ∉ TreeSubstitution.keys
                                (residualRepresentative ++
                                  Substitution.denote referenceBase))
                            (Term.denote sourceTerm) :=
                        Term.denote_variablesSatisfy_of_generatedAtLeast
                          (fun index above identityMember => by
                            have below := oldRepresentativeKeysBelow
                              (.generated index) identityMember
                            simpa [preparedBranchOf] using
                              below.ne_generated_atLeast above rfl)
                          sourceTerm sourceBound
                      have oldReferenceFixed :
                          TreeSubstitution.apply
                              (residualRepresentative ++
                                Substitution.denote referenceBase)
                              (Term.denote sourceTerm) =
                            Term.denote sourceTerm :=
                        TreeSubstitution.apply_eq_self_of_variables_outside
                          sourceOutside
                      have canonicalApplied :
                          TreeSubstitution.apply
                              ((flattened ++ residualRepresentative) ++
                                Substitution.denote referenceBase)
                              (Term.denote sourceTerm) =
                            TreeSubstitution.apply flattened
                              (Term.denote sourceTerm) := by
                        rw [show
                          (flattened ++ residualRepresentative) ++
                              Substitution.denote referenceBase =
                            flattened ++
                              (residualRepresentative ++
                                Substitution.denote referenceBase) by
                              simp [List.append_assoc]]
                        rw [TreeSubstitution.apply_append, oldReferenceFixed]
                      have baseApplied :
                          PLeaTTa.subst binding runtimeAtom = runtimeAtom :=
                        PLeaTTa.subst_eq_self_of_domain_free binding runtimeAtom
                          runtimeAvoids
                      have installedApplied :
                          PLeaTTa.subst installed runtimeAtom =
                            PLeaTTa.subst generated runtimeAtom := by
                        rw [installedShape',
                          subst_installGenerated_eq_generated_after_base
                            bindingTopological generatedTopological
                            generatedAvoidsBinding runtimeAtom,
                          baseApplied]
                      have callMember :
                          PLeaTTa.Goal.call predicate executableArguments
                              executableResult ∈
                            (freshenResolutionClause
                                (args.map (PLeaTTa.subst binding)) args result
                                rest binding qterm seed barrier clause).body ++
                              rest := by
                        rw [executableShape]
                        simp
                      have trimApplied :
                          PLeaTTa.subst
                              (PLeaTTa.trimFor
                                ((freshenResolutionClause
                                    (args.map (PLeaTTa.subst binding)) args
                                    result rest binding qterm seed barrier
                                    clause).body ++ rest)
                                qterm installed)
                              runtimeAtom =
                            PLeaTTa.subst installed runtimeAtom :=
                        PLeaTTa.subst_trimFor_eq_of_topological
                          ((freshenResolutionClause
                              (args.map (PLeaTTa.subst binding)) args result
                              rest binding qterm seed barrier clause).body ++
                            rest)
                          qterm installed installedTopological runtimeAtom
                          (fun name nameMember =>
                            PLeaTTa.isTrimRoot_call_atom_of_mem _ qterm predicate
                              executableArguments executableResult runtimeAtom
                              name callMember callAtomMember nameMember)
                      rw [canonicalApplied, trimApplied, installedApplied]
                      exact canonicalRuntimeAgrees_apply
                        (AlphaTermAgrees.canonicalRuntimeAgrees head)
                        generatedValuation
                    · exact inductionHypothesis tailBounds tailAvoids
                        (fun atom atomMember =>
                          included atom (by simp [atomMember]))
          have transported :=
            transport ambientPayload sourceFresh runtimeAvoidsBase
              (fun atom atomMember => by
                simpa [allRuntimeAtoms] using atomMember)
          simpa only [List.map_append, List.map_singleton] using
            (List.forall₂_map_right_iff.mpr transported)
  refine
    ⟨alpha, sourceCanonical, flattened, generated, installed,
      shared, queryIncluded, extensionAbove, freshFrontier, allocationGap,
      selectedIntervalCovered, compositeResultShape, sourceOrdered,
      generatedExact, installedExact, ?_, trimmedCumulative, task,
      bodyHeadMaterialized⟩
  exact
    { substitution := generatedAgreement
      topological := ⟨generatedTopological⟩
      valuation := generatedValuation
      avoidsBase := generatedAvoidsBinding
      installedShape := installedShape' }

/-- Immediate-call view of
`unifyB_body_cumulativeWith_of_headResolution_extension`.

The alpha graph is historical: entries may remain after their variables have
left the current call syntax.  Fresh extension therefore needs only the exact
allocator fact that every recorded runtime name lies below `seed`, not the
strictly stronger claim that every such name occurs in this call's occupied
set. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution
    {queryAlpha support : List (LogicVar × String)}
    {oldCanonical residualRepresentative : TreeSubstitution}
    {referenceBase : Substitution}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (oldCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        queryAlpha support oldCanonical referenceBase binding
        residualRepresentative)
    (query :
      RepresentativeNormalizedCallAgreesWith queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result)
        residualRepresentative referenceBase)
    (cursorBindingShape :
      cursor.bindings =
        TreeSubstitution.reify oldCanonical ++ referenceBase)
    (oldCanonicalWellFormed : oldCanonical.WellFormed)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableBelow :
      resolutionSeedHighWaterNames (queryAlpha.map Prod.snd) ≤ seed)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (live :
      AlphaRuntimeNamesLive support
        ((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).body ++ rest)
        qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha sourceCanonical flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      (∀ pair, pair ∈ queryAlpha → pair ∈ alpha) ∧
      AlphaExtendsAbove queryAlpha alpha branch.firstFresh seed ∧
      AlphaFreshFrontier alpha branch.nextFresh (seed + 1) ∧
      independentResult =
        TreeSubstitution.reify (sourceCanonical ++ oldCanonical) ++
          referenceBase ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      GeneratedMguAgrees alpha flattened binding generated installed ∧
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support (sourceCanonical ++ oldCanonical) referenceBase
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) ∧
      TaskPayloadAgrees alpha support barrier
        (sourceCanonical ++ oldCanonical) referenceBase independentResult
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      MaterializedLocalCallHeadsAgreeWith alpha independentResult branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body
        (PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (flattened ++ residualRepresentative) referenceBase := by
  cases agreement with
  | intro reference freshSeed _ base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryEnd :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).nextFresh := by
        exact Nat.le_trans startsAbove (by
          rw [reference.clause.freshCopy_next]
          exact Nat.le_add_right _ _)
      have queryFresh :
          AlphaFreshFrontier queryAlpha
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh
            (seed + 1) := by
        constructor
        · simpa [preparedBranchOf] using
            queryReferenceBelow.mono queryEnd
        · exact Nat.le_trans queryExecutableBelow
            (Nat.le_add_right seed 1)
      have supported :
          SupportedPreparedCandidateAgrees cursor.callGeneration
            cursor.predicate cursor.arguments cursor.bindings
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference)
            clause :=
        .intro reference freshSeed clause base encoding bodySupported
      have queryLowFrontier :
          AlphaFreshFrontier queryAlpha cursor.reservationStart seed := by
        constructor
        · exact queryReferenceBelow
        · exact queryExecutableBelow
      have queryGap :
          AlphaAllocationGap queryAlpha cursor.reservationStart
            cursor.reservedUntil seed (seed + 1) :=
        AlphaAllocationGap.of_frontier queryLowFrontier
      obtain
        ⟨alpha, sourceCanonical, flattened, generated, installed,
          resultBundle⟩ :=
        SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution_extension
          oldCumulative query cursorBindingShape oldCanonicalWellFormed
          wellFormed member supported arity (fun _ member => member)
          queryShared queryReferenceBelow highWater queryFresh
          (Nat.le_refl _) (Nat.le_refl _) queryGap (Nat.le_refl _) live
          resolved
      exact
        ⟨alpha, sourceCanonical, flattened, generated, installed,
          resultBundle.1, resultBundle.2.1, resultBundle.2.2.1,
          resultBundle.2.2.2.1,
          resultBundle.2.2.2.2.2.2⟩

/-! ## Anti-vacuity: previously bound support really composes -/

private def boundWitnessX : LogicVar := .source "$bound_x"
private def boundWitnessY : LogicVar := .source "$bound_y"
private def boundWitnessAlpha : List (LogicVar × String) :=
  [(boundWitnessX, "$runtime_x"), (boundWitnessY, "$runtime_y")]
private def boundWitnessSupport : List (LogicVar × String) :=
  [(boundWitnessX, "$runtime_x")]
private def boundWitnessOldCanonical : TreeSubstitution :=
  [(boundWitnessX, .variable boundWitnessY)]
private def boundWitnessExtension : TreeSubstitution :=
  [(boundWitnessY, .node (.atom "done") [])]
private def boundWitnessBase : Subst :=
  [("$runtime_x", .var "$runtime_y")]
private def boundWitnessGenerated : Subst :=
  [("$runtime_y", .sym "done")]

/-- A supported runtime name may already be bound and still compose
correctly through a later MGU.

Here the older states agree on `X ↦ Y` / `x ↦ y`; the new blocks agree on
`Y ↦ done` / `y ↦ done`.  Eager installation therefore carries the observed
`x` all the way to `done`, even though the conservative
`AlphaRuntimeNamesAvoid` premise is false for `x`. -/
theorem bound_observable_value_composes_through_later_mgu :
    ¬ AlphaRuntimeNamesAvoid boundWitnessSupport boundWitnessBase ∧
    AlphaValuationAgreesOn boundWitnessAlpha boundWitnessSupport
      (boundWitnessExtension ++ boundWitnessOldCanonical)
      (installGenerated boundWitnessGenerated boundWitnessBase) := by
  have baseTopological :
      PLeaTTa.SubstTopological boundWitnessBase :=
    PLeaTTa.SubstTopological.cons_of_fresh []
      PLeaTTa.emptySubstTopological "$runtime_x" (.var "$runtime_y")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [PLeaTTa.AtomAvoids, Metta.Subst.lookup])
  have generatedTopological :
      PLeaTTa.SubstTopological boundWitnessGenerated :=
    PLeaTTa.SubstTopological.cons_of_fresh []
      PLeaTTa.emptySubstTopological "$runtime_y" (.sym "done")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [PLeaTTa.AtomAvoids, Metta.Subst.lookup])
  have generatedAvoidsBase :
      PLeaTTa.SubstEntriesAvoid boundWitnessBase boundWitnessGenerated := by
    intro entry member
    have entryEq : entry = ("$runtime_y", .sym "done") := by
      simpa [boundWitnessGenerated] using member
    subst entry
    exact
      ⟨by simp [boundWitnessBase, Metta.Subst.lookup],
        by
          intro name member
          simp [Atom.vars] at member⟩
  have oldCanonicalX :
      TreeSubstitution.apply boundWitnessOldCanonical
          (.variable boundWitnessX) =
        .variable boundWitnessY := by
    simp [boundWitnessOldCanonical, boundWitnessX, boundWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have extensionX :
      TreeSubstitution.apply boundWitnessExtension
          (.variable boundWitnessX) =
        .variable boundWitnessX := by
    simp [boundWitnessExtension, boundWitnessX, boundWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have extensionY :
      TreeSubstitution.apply boundWitnessExtension
          (.variable boundWitnessY) =
        .node (.atom "done") [] := by
    simp [boundWitnessExtension, boundWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have baseY :
      PLeaTTa.subst boundWitnessBase (.var "$runtime_y") =
        .var "$runtime_y" :=
    PLeaTTa.subst_var_of_lookup_none boundWitnessBase "$runtime_y" (by
      simp [boundWitnessBase, Metta.Subst.lookup])
  have baseX :
      PLeaTTa.subst boundWitnessBase (.var "$runtime_x") =
        .var "$runtime_y" := by
    rw [baseTopological.subst_var_of_lookup
      boundWitnessBase "$runtime_x" (.var "$runtime_y")
      (by simp [boundWitnessBase, Metta.Subst.lookup])]
    exact baseY
  have generatedX :
      PLeaTTa.subst boundWitnessGenerated (.var "$runtime_x") =
        .var "$runtime_x" :=
    PLeaTTa.subst_var_of_lookup_none
      boundWitnessGenerated "$runtime_x" (by
        simp [boundWitnessGenerated, Metta.Subst.lookup])
  have generatedY :
      PLeaTTa.subst boundWitnessGenerated (.var "$runtime_y") =
        .sym "done" :=
    PLeaTTa.subst_var_of_lookup_sym
      boundWitnessGenerated "$runtime_y" "done" (by
        simp [boundWitnessGenerated, Metta.Subst.lookup])
  have oldValuation :
      AlphaValuationAgreesOn boundWitnessAlpha boundWitnessSupport
        boundWitnessOldCanonical boundWitnessBase := by
    intro identity name linked
    have linkedEq :
        (identity, name) = (boundWitnessX, "$runtime_x") := by
      simpa [boundWitnessSupport] using linked
    have identityEq := congrArg Prod.fst linkedEq
    have nameEq := congrArg Prod.snd linkedEq
    simp only at identityEq nameEq
    subst identity
    subst name
    rw [oldCanonicalX, baseX]
    exact
      CanonicalRuntimeAgrees.variable (alpha := boundWitnessAlpha)
        (by
          show
            (boundWitnessY, "$runtime_y") ∈ boundWitnessAlpha
          simp [boundWitnessAlpha])
  have extensionValuation :
      AlphaValuationAgrees boundWitnessAlpha boundWitnessExtension
        boundWitnessGenerated := by
    intro identity name linked
    simp only [boundWitnessAlpha, List.mem_cons, List.not_mem_nil,
      or_false] at linked
    rcases linked with linked | linked
    · have identityEq := congrArg Prod.fst linked
      have nameEq := congrArg Prod.snd linked
      simp only at identityEq nameEq
      subst identity
      subst name
      rw [extensionX, generatedX]
      exact
        CanonicalRuntimeAgrees.variable (alpha := boundWitnessAlpha)
          (by
            show
              (boundWitnessX, "$runtime_x") ∈ boundWitnessAlpha
            simp [boundWitnessAlpha])
    · have identityEq := congrArg Prod.fst linked
      have nameEq := congrArg Prod.snd linked
      simp only at identityEq nameEq
      subst identity
      subst name
      rw [extensionY, generatedY]
      exact
        CanonicalRuntimeAgrees.atom
          (alpha := boundWitnessAlpha) (name := "done")
          (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · intro avoids
    have lookupNone :=
      avoids
        (identity := boundWitnessX) (name := "$runtime_x")
        (by simp [boundWitnessSupport])
    simp [boundWitnessBase, Metta.Subst.lookup] at lookupNone
  · exact
      AlphaValuationAgreesOn.installGenerated_compose
        oldValuation baseTopological generatedTopological
        generatedAvoidsBase extensionValuation

end PLeaTTa.PrologRepresentativeTaskActivationBridge
