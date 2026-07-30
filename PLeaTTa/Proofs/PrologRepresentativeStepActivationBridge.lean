-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeStepActivationBridge
Purpose: Compose the semantic retained-call frontier with the actual
  independent clausesPull and sealed executable eq_ok successors.
Trusted boundary: none
Main exports:
  RepresentativeRetainedCallFrontier.activate_task_step
-/
import PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge
import PLeaTTa.Proofs.PrologRepresentativeTaskActivationBridge

namespace PLeaTTa.PrologRepresentativeStepActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologActivationMacro
open PrologCallStepBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeTaskActivationBridge

/-! ## Exact paired activation successor -/

/-- The sealed successor after the retained clause's full-head equality
succeeds.  Naming it keeps the ownership frame explicit: only `cur` changes;
the executable world, counter, alternatives, query term, answer accumulator,
and barrier cache are inherited from the pulled frontier. -/
def activatedExecutableSuccessor
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) : PLeaTTa.Conf :=
  { pending.pulled.toConf with
    cur :=
      some
        (copied.body ++ rest,
          PLeaTTa.trimFor (copied.body ++ rest) qterm installed) }

/-- Fine-grained executable spelling of the activated successor.  The sealed
configuration changes, while the pending call's suspended frame stack is
carried literally and in order. -/
def activatedOpenSuccessor
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) : DemandDrivenStep.OpenConf :=
  DemandDrivenStep.OpenConf.ofConf
    (activatedExecutableSuccessor pending copied rest qterm installed)
    pending.frames

@[simp] theorem activatedOpenSuccessor_toConf
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedOpenSuccessor pending copied rest qterm installed).toConf =
      activatedExecutableSuccessor pending copied rest qterm installed :=
  rfl

@[simp] theorem activatedOpenSuccessor_frames
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedOpenSuccessor pending copied rest qterm installed).frames =
      pending.frames :=
  rfl

@[simp] theorem activatedExecutableSuccessor_cur
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).cur =
      some
        (copied.body ++ rest,
          PLeaTTa.trimFor (copied.body ++ rest) qterm installed) :=
  rfl

@[simp] theorem activatedExecutableSuccessor_alts
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).alts =
      pending.pulled.toConf.alts :=
  rfl

@[simp] theorem activatedExecutableSuccessor_world
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).world =
      pending.pulled.toConf.world :=
  rfl

@[simp] theorem activatedExecutableSuccessor_counter
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).counter =
      pending.pulled.toConf.counter :=
  rfl

@[simp] theorem activatedExecutableSuccessor_qterm
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).qterm =
      pending.pulled.toConf.qterm :=
  rfl

@[simp] theorem activatedExecutableSuccessor_answers
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).answers =
      pending.pulled.toConf.answers :=
  rfl

@[simp] theorem activatedExecutableSuccessor_barriers
    (pending : DemandDrivenCallStep.PendingCall)
    (copied : PLeaTTa.Clause) (rest : List PLeaTTa.Goal)
    (qterm : Atom) (installed : Subst) :
    (activatedExecutableSuccessor pending copied rest qterm installed).barriers =
      pending.pulled.toConf.barriers :=
  rfl

/-! ## Semantic frontier to paired machine step -/

/-- One actual active recursive task, one actual retained-call frontier, and
one independent head resolution advance together.

The active task selects the residual representative once.  The immutable
cursor context transports that same witness across every rejected occurrence;
the retained clause then composes its source and executable MGUs into the
exact body task.  The two step constructors are the real
`RawStep.clausesPull` and sealed `PLeaTTa.Step.eq_ok`.

Only three semantic support obligations remain caller-visible:

* source alpha identities are below the call reservation;
* linked runtime names occur in the executable resolver input;
* names observed by the body continuation survive `trimFor`.

The frontier itself discharges the executable fresh-counter high-water and
pins the retained alternative tail, world, counter, order, and multiplicity. -/
theorem RepresentativeRetainedCallFrontier.activate_task_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {referenceBindings : Substitution}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {referencePayload : List Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    {independentResult : Substitution}
    (entry :
      RepresentativeSupportedCallEntryRelates alpha opened before pending
        argsv args res rest binding qterm barrier startCounter)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res rest
        binding qterm barrier startCounter)
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase
        referenceBindings binding
        (.call opened.cursor.predicate referencePayload :: referenceRest)
        (.call opened.cursor.predicate args res :: rest))
    (payloadSupported :
      AlphaTermsSupported alpha support referencePayload)
    (openedArguments : opened.cursor.arguments = referencePayload)
    (openedBindings : opened.cursor.bindings = referenceBindings)
    (queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ alpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) res rest binding qterm)
    (live :
      AlphaRuntimeNamesLive support (copied.body ++ rest) qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ representative nextAlpha sourceCanonical flattened installed,
      SharedRuntimeAlpha nextAlpha ∧
      (∀ pair, pair ∈ alpha → pair ∈ nextAlpha) ∧
      AlphaFreshFrontier nextAlpha branch.nextFresh (startCounter + 1) ∧
      independentResult =
        TreeSubstitution.reify (sourceCanonical ++ canonical) ++
          referenceBase ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      RawStep opened.session (.clauses opened.scope finish) [] .none
        opened.session
        (.running
          (.choice opened.scope
            (.task opened.scope (branch.enter independentResult).rawBody
              (branch.enter independentResult).bindings)
            (.clauses opened.scope
              (finish.advance branch branchTail)))) ∧
      PLeaTTa.Step prog gt pending.pulled.toConf
        (activatedExecutableSuccessor pending copied rest qterm installed) ∧
      AlphaCumulativeResidualVariantAgreesOnWith
        nextAlpha support (sourceCanonical ++ canonical) referenceBase
        (PLeaTTa.trimFor (copied.body ++ rest) qterm installed)
        (flattened ++ representative) ∧
      TaskPayloadAgrees nextAlpha support barrier
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor (copied.body ++ rest) qterm installed)
        branch.body copied.body ∧
      (activatedExecutableSuccessor pending copied rest qterm installed).alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts ∧
      (activatedExecutableSuccessor pending copied rest qterm installed).world =
        pending.persistent.world ∧
      (activatedExecutableSuccessor pending copied rest qterm installed).counter =
        pending.persistent.counter := by
  obtain ⟨representative, oldCumulative, queryAtOpen⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgreesWith
      payload payloadSupported opened.cursor openedArguments openedBindings
  have queryAtFinish :
      RepresentativeNormalizedCallAgreesWith alpha finish
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) representative referenceBase :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgreesWith
      frontier.finishContext (.refl opened.cursor) queryAtOpen
  have cursorBindingShape :
      finish.bindings =
        TreeSubstitution.reify canonical ++ referenceBase := by
    calc
      finish.bindings = opened.cursor.bindings :=
        frontier.finishContext.bindings_eq
      _ = referenceBindings := openedBindings
      _ = TreeSubstitution.reify canonical ++ referenceBase :=
        payload.bindingShape
  have member : branch ∈ finish.remaining := by
    rw [frontier.finishRemaining]
    simp
  have copiedExact :
      copied =
        PLeaTTa.freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args res rest binding qterm
          startCounter barrier clause := by
    simpa only [frontier.substitutedArgs] using frontier.copiedExact
  have highWater :
      resolutionSeedHighWaterNames
          (resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) res rest binding qterm) ≤
        startCounter := by
    simpa only [frontier.substitutedArgs] using frontier.highWater
  have exactLive :
      AlphaRuntimeNamesLive support
        ((PLeaTTa.freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args res rest binding qterm
            startCounter barrier clause).body ++ rest)
        qterm := by
    intro identity name linked
    have observed := live linked
    rw [copiedExact] at observed
    exact observed
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, generated, installed,
      nextShared, alphaIncluded, freshFrontier, independentShape,
      sourceOrdered,
      _generatedExact, installedExact, successorCumulative, successorTask⟩ :=
    PLeaTTa.PrologRepresentativeTaskActivationBridge.SupportedPreparedCandidateAgrees.unifyB_body_cumulativeWith_of_headResolution
      oldCumulative queryAtFinish cursorBindingShape
      payload.canonicalWellFormed frontier.finishWellFormed member
      frontier.supported frontier.arity payload.alphaShared queryReferenceBelow
      queryExecutableLive highWater exactLive resolved
  have sourceStep :
      RawStep opened.session (.clauses opened.scope finish) [] .none
        opened.session
        (.running
          (.choice opened.scope
            (.task opened.scope (branch.enter independentResult).rawBody
              (branch.enter independentResult).bindings)
            (.clauses opened.scope
              (finish.advance branch branchTail)))) :=
    matched_clause_splices_body_first opened.scope opened.session
      (.matched finish branch branchTail independentResult
        frontier.finishRemaining resolved)
  have current :
      pending.pulled.toConf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
              (.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest,
            binding) := by
    rw [frontier.pulledExact]
  have installedExactCopied :
      PLeaTTa.unifyB binding (.expr (args ++ [res]))
          (.expr (copied.params ++ [copied.result])) =
        some installed := by
    simpa only [copiedExact] using installedExact
  have executableQueryTerm : pending.pulled.toConf.qterm = qterm := by
    calc
      pending.pulled.toConf.qterm = pending.installed.toConf.qterm := by
        rw [frontier.pulledExact]
      _ = pending.outer.qterm := rfl
      _ = before.control.qterm := by rw [entry.entry.outer]
      _ = before.toConf.qterm := rfl
      _ = qterm := frontier.queryTerm.symm
  have executableStep :
      PLeaTTa.Step prog gt pending.pulled.toConf
        (activatedExecutableSuccessor pending copied rest qterm installed) := by
    simpa only [activatedExecutableSuccessor, executableQueryTerm] using
      (PLeaTTa.Step.eq_ok pending.pulled.toConf
        (.expr (args ++ [res]))
        (.expr (copied.params ++ [copied.result]))
        (copied.body ++ rest) binding installed current
        installedExactCopied)
  have cumulativeCopied :
      AlphaCumulativeResidualVariantAgreesOnWith
        nextAlpha support (sourceCanonical ++ canonical) referenceBase
        (PLeaTTa.trimFor (copied.body ++ rest) qterm installed)
        (flattened ++ representative) := by
    simpa only [copiedExact] using successorCumulative
  have taskCopied :
      TaskPayloadAgrees nextAlpha support barrier
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor (copied.body ++ rest) qterm installed)
        branch.body copied.body := by
    simpa only [copiedExact] using successorTask
  have retainedAlts :
      (activatedExecutableSuccessor pending copied rest qterm installed).alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts := by
    simp only [activatedExecutableSuccessor_alts]
    rw [frontier.pulledExact]
  have worldPreserved :
      (activatedExecutableSuccessor pending copied rest qterm installed).world =
        pending.persistent.world := by
    simp only [activatedExecutableSuccessor_world]
    rw [frontier.pulledExact]
    rfl
  have counterPreserved :
      (activatedExecutableSuccessor pending copied rest qterm installed).counter =
        pending.persistent.counter := by
    simp only [activatedExecutableSuccessor_counter]
    rw [frontier.pulledExact]
    rfl
  refine
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      nextShared, alphaIncluded, freshFrontier, independentShape,
      sourceOrdered, sourceStep, executableStep, ?_, taskCopied, retainedAlts,
      worldPreserved, counterPreserved⟩
  simpa only using cumulativeCopied

end PLeaTTa.PrologRepresentativeStepActivationBridge
