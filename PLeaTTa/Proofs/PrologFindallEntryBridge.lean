-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallEntryBridge
Purpose: Pair one independent local findall entry with the fine executable
  entry transition and its exact typed-control chronology.
Trusted boundary: none
Main exports: FindallControlEntryRelates,
  taskFindall_findallEnter_control_correspondence
-/
import PLeaTTa.Proofs.PrologStateBridge

namespace PLeaTTa.PrologFindallEntryBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.GoalSemantics
open PrologStateBridge
open DemandDrivenStep

/-!
The independent semantics allocates nominally typed cut and collection
identities at `taskFindall`.  The fine executable lane deliberately keeps its
`FindallFrame` anonymous, but advances separate cut and collection allocation
frontiers while pushing exactly one frame.

This file pairs one occurrence at its entry point.  The relation is indexed
by the two *pre-entry* frontier values: it never reconstructs an occurrence by
subtracting from a later frontier.  A nested frame zipper will retain those
indices cell-by-cell.  Equality of the global frontiers alone remains only a
counting invariant and is not presented as nested occurrence correspondence.

Term, goal, and substitution payload agreement is intentionally outside this
control-only tranche.  The two real transition witnesses below do not assume
it and do not claim it.
-/

/-- The exact independent target of one source `taskFindall` transition. -/
def sourceFindallTarget (session : Session) (outerScope : CutScopeId)
    (template : Term) (generator : PeTTaSpec.PrologCore.Goal)
    (output : Term) (rest : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) : Search :=
  .collectionBoundary (openFindall session).collectionScope outerScope
    (.cutBoundary (openFindall session).cutScope
      (.task (openFindall session).cutScope [generator] bindings))
    template output bindings rest []

/-- The unique anonymous frame installed by one fine `findall` entry.  It
contains executable continuation payload only; no source scope identity is
copied into the machine. -/
def executableFindallFrame (before : OpenConf) (template : Atom)
    (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) : FindallFrame :=
  { outer := before.control
    template := template
    result := result
    rest := rest
    binding := binding }

/-- Exact control-side correspondence for one `findall/3` entry.

`preCut` and `preCollection` name this occurrence before either allocator
advances.  Both the nominal source identities and the fine pre-entry
frontiers equal those indices.  The target relation separately proves the
three global frontier counts, while `frameHead` records the positional
occurrence on the executable side. -/
structure FindallControlEntryRelates
    (freshFrontier : FreshFrontierRelation)
    (prog : Prog) (gt : GroundingTable)
    (session : Session) (before after : OpenConf)
    (outerScope : CutScopeId)
    (referenceTemplate : Term)
    (referenceGenerator : PeTTaSpec.PrologCore.Goal)
    (referenceOutput : Term)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings : Substitution)
    (executableTemplate : Atom) (executableGenerator : List PLeaTTa.Goal)
    (executableResult : Atom) (executableRest : List PLeaTTa.Goal)
    (executableBinding : Subst)
    (preCut preCollection : Nat) : Prop where
  beforeAgreement :
    SessionRelatesOpenConf freshFrontier ExactControlFrontiers
      session before
  sourceStep :
    RawStep session
      (.task outerScope
        (.findall referenceTemplate referenceGenerator referenceOutput ::
          referenceRest)
        referenceBindings)
      [] .none (openFindall session).session
      (.running
        (sourceFindallTarget session outerScope referenceTemplate
          referenceGenerator referenceOutput referenceRest
          referenceBindings))
  fineHead :
    before.toConf.cur =
      some
        (PLeaTTa.Goal.findall executableTemplate executableGenerator
            executableResult ::
          executableRest,
          executableBinding)
  fineStep :
    DemandDrivenStep.Step prog gt before after
  target :
    after =
      enterFindall before executableTemplate executableGenerator
        executableResult executableRest executableBinding
  afterAgreement :
    SessionRelatesOpenConf freshFrontier ExactControlFrontiers
      (openFindall session).session after
  sourceCutOccurrence :
    (openFindall session).cutScope = preCut
  fineCutOccurrence :
    before.scopes.nextCutScope = preCut
  sourceCollectionOccurrence :
    (openFindall session).collectionScope.index = preCollection
  fineCollectionOccurrence :
    before.scopes.nextCollectionScope = preCollection
  frameHead :
    after.frames =
      .findall
        (executableFindallFrame before executableTemplate executableResult
          executableRest executableBinding) ::
        before.frames
  targetScopes :
    after.scopes = before.scopes.afterFindall
  persistentUnchanged :
    after.persistent = before.persistent

/-- The actual independent and fine constructors inhabit the exact entry
relation.  No terminal generator premise is involved: allocation and frame
ownership are established before the generator takes its first step.

[SPEC translator.pl:112-116] -/
theorem taskFindall_findallEnter_control_correspondence
    {freshFrontier : FreshFrontierRelation}
    {prog : Prog} {gt : GroundingTable}
    {session : Session} {before : OpenConf}
    (agreement :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        session before)
    (outerScope : CutScopeId)
    (referenceTemplate : Term)
    (referenceGenerator : PeTTaSpec.PrologCore.Goal)
    (referenceOutput : Term)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings : Substitution)
    (executableTemplate : Atom)
    (executableGenerator : List PLeaTTa.Goal)
    (executableResult : Atom) (executableRest : List PLeaTTa.Goal)
    (executableBinding : Subst)
    (head :
      before.toConf.cur =
        some
          (PLeaTTa.Goal.findall executableTemplate executableGenerator
              executableResult ::
            executableRest,
            executableBinding)) :
    FindallControlEntryRelates freshFrontier prog gt session before
      (enterFindall before executableTemplate executableGenerator
        executableResult executableRest executableBinding)
      outerScope referenceTemplate referenceGenerator referenceOutput
      referenceRest referenceBindings executableTemplate executableGenerator
      executableResult executableRest executableBinding
      session.nextCutScope session.nextCollectionScope := by
  let after :=
    enterFindall before executableTemplate executableGenerator
      executableResult executableRest executableBinding
  have persistentUnchanged : after.persistent = before.persistent := by
    simp [after, enterFindall, OpenConf.stepOpen, OpenConf.ofConfWith,
      persistentOf, subConfOf, OpenConf.toConf, Control.toConf]
  have persistent :
      SessionRelatesPersistent freshFrontier
        (openFindall session).session after.persistent := by
    rw [persistentUnchanged]
    exact
      openFindall_preserves_persistent_relation freshFrontier session
        before.persistent agreement.persistent
  have afterAgreement :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        (openFindall session).session after := by
    apply SessionRelatesOpenConf.exact_afterFindall agreement persistent
    rfl
  refine
    { beforeAgreement := agreement
      sourceStep := ?_
      fineHead := head
      fineStep := ?_
      target := rfl
      afterAgreement := afterAgreement
      sourceCutOccurrence := rfl
      fineCutOccurrence := ?_
      sourceCollectionOccurrence := rfl
      fineCollectionOccurrence := ?_
      frameHead := ?_
      targetScopes := rfl
      persistentUnchanged := persistentUnchanged }
  · exact
      .taskFindall outerScope referenceTemplate referenceGenerator
        referenceOutput referenceRest referenceBindings session
  · exact
      DemandDrivenStep.Step.findallEnter before executableTemplate
        executableGenerator
        executableResult executableRest executableBinding head
  · exact agreement.cut.symm
  · exact agreement.collection.symm
  · rfl

/-- A related `findall` entry necessarily owns one additional top frame.
Advancing only the frontiers while omitting the frame push cannot satisfy the
occurrence relation. -/
theorem FindallControlEntryRelates.frames_ne_before
    {freshFrontier : FreshFrontierRelation}
    {prog : Prog} {gt : GroundingTable}
    {session : Session} {before after : OpenConf}
    {outerScope : CutScopeId}
    {referenceTemplate : Term}
    {referenceGenerator : PeTTaSpec.PrologCore.Goal}
    {referenceOutput : Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate : Atom}
    {executableGenerator : List PLeaTTa.Goal}
    {executableResult : Atom} {executableRest : List PLeaTTa.Goal}
    {executableBinding : Subst}
    {preCut preCollection : Nat}
    (entry :
      FindallControlEntryRelates freshFrontier prog gt session before after
        outerScope referenceTemplate referenceGenerator referenceOutput
        referenceRest referenceBindings executableTemplate
        executableGenerator executableResult executableRest
        executableBinding preCut preCollection) :
    after.frames ≠ before.frames := by
  intro same
  have lengths :=
    congrArg List.length (entry.frameHead.symm.trans same)
  simp at lengths

/-- The explicit occurrence indices are forced by the relation.  They cannot
be replaced by arbitrary post-entry values even though the global frontier
relation only counts allocations. -/
theorem FindallControlEntryRelates.indices_exact
    {freshFrontier : FreshFrontierRelation}
    {prog : Prog} {gt : GroundingTable}
    {session : Session} {before after : OpenConf}
    {outerScope : CutScopeId}
    {referenceTemplate : Term}
    {referenceGenerator : PeTTaSpec.PrologCore.Goal}
    {referenceOutput : Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate : Atom}
    {executableGenerator : List PLeaTTa.Goal}
    {executableResult : Atom} {executableRest : List PLeaTTa.Goal}
    {executableBinding : Subst}
    {preCut preCollection : Nat}
    (entry :
      FindallControlEntryRelates freshFrontier prog gt session before after
        outerScope referenceTemplate referenceGenerator referenceOutput
        referenceRest referenceBindings executableTemplate
        executableGenerator executableResult executableRest
        executableBinding preCut preCollection) :
    preCut = session.nextCutScope ∧
      preCollection = session.nextCollectionScope := by
  exact
    ⟨entry.sourceCutOccurrence.symm,
      entry.sourceCollectionOccurrence.symm⟩

end PLeaTTa.PrologFindallEntryBridge
