-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerPullClassificationBridge
Purpose: Classify the exact executable pull landing selected by an
  answer-origin resource zipper
Trusted boundary: none
Main exports: OriginPullOutcome,
  AnswerOriginResourceAgrees.classifyPull
-/
import PLeaTTa.Proofs.PrologFindallAnswerResourceBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge

namespace PLeaTTa.PrologAnswerPullClassificationBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PLeaTTa.PrologAnswerOriginBridge
open PLeaTTa.PrologAnswerResourceBridge
open PLeaTTa.PrologFindallAnswerResourceBridge
open PLeaTTa.PrologProductResourceContextBridge
open PLeaTTa.PrologRetainedCursorOwnershipBridge

/-!
# Exact pull landing over an answer-origin zipper

An executable answer records its value and calls `pullAux` immediately.  The
independent source instead leaves `done` at the answer leaf and reaches the
same alternative through later control transitions.  Before those source
steps can be related, the executable landing must be named without confusing
the zipper's terminal suffix with the machine's post-pull bank.

The four mutually inductive relations below follow the existing mutual
`AnswerOriginResourceAgrees` / `RightAlternativeRegionAgrees` provenance.
A landing always names a real ordinary branch in a literal source region.
A fall-through proves that every local region and marker was skipped and that
the result is exactly the supplied older base.  Scheduled historical regions
recurse through their carried origin proof, so arbitrary depth is preserved.
-/

mutual

  /-- The first executable branch in one literal source right region. -/
  inductive RightRegionLanding
      (alpha : List (LogicVar × String)) :
      {right : Search} →
      {resources : List RetainedAlternativeSegment} →
      {segment : List PLeaTTa.Alt} →
      (agreement :
        RightAlternativeRegionAgrees alpha right resources segment) →
      List PLeaTTa.Goal → Subst → List PLeaTTa.Alt → Prop where
    | clauses (scope : CutScopeId)
        (original cursor : Resolver.PreparedCursor) (position : Nat)
        (resource : RetainedAlternativeSegment)
        (ownership : resource.Owns alpha original cursor position)
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (tail : List PLeaTTa.Alt)
        (head : resource.alts = .br goals binding :: tail)
        (pullExact :
          PLeaTTa.pullAux resource.alts =
            some (.branch goals binding, tail)) :
        RightRegionLanding alpha
          (.clauses scope original cursor position resource ownership)
          goals binding tail
    | scheduled (callerScope : CutScopeId)
        (callerTail : List PeTTaSpec.PrologCore.Goal)
        {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
        {head next : Search}
        (origin : AnswerOrigin leafScope bindings head next)
        (resources : List RetainedAlternativeSegment)
        (nonempty : resources ≠ [])
        (history :
          AnswerOriginResourceAgrees alpha origin resources []
            (flattenOwnedAlts resources []) [])
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (tail : List PLeaTTa.Alt)
        (inside : OriginPrefixLanding alpha history goals binding tail)
        (pullExact :
          PLeaTTa.pullAux (flattenOwnedAlts resources []) =
            some (.branch goals binding, tail)) :
        RightRegionLanding alpha
          (.scheduled callerScope callerTail origin resources nonempty history)
          goals binding tail
    | taskChoices (support : List (LogicVar × String))
        (scope : CutScopeId) (barrier : Nat)
        (canonical : Canonical.TreeSubstitution)
        (referenceBase current : OpenSubstitution.Substitution)
        (runtime : Subst) (right : Search)
        (goals : List PLeaTTa.Goal) (tail : List PLeaTTa.Alt)
        (choices :
          TaskChoiceAlternativeRegionAgrees alpha support scope barrier
            canonical referenceBase current runtime right
            (.br goals runtime :: tail))
        (pullExact :
          PLeaTTa.pullAux (.br goals runtime :: tail) =
            some (.branch goals runtime, tail)) :
        RightRegionLanding alpha
          (.taskChoices support scope barrier canonical referenceBase current
            runtime right goals tail choices)
          goals runtime tail

  /-- One literal source right region contains no executable branch. -/
  inductive RightRegionEmpty
      (alpha : List (LogicVar × String)) :
      {right : Search} →
      {resources : List RetainedAlternativeSegment} →
      {segment : List PLeaTTa.Alt} →
      (agreement :
        RightAlternativeRegionAgrees alpha right resources segment) →
      Prop where
    | clauses (scope : CutScopeId)
        (original cursor : Resolver.PreparedCursor) (position : Nat)
        (resource : RetainedAlternativeSegment)
        (ownership : resource.Owns alpha original cursor position)
        (empty : resource.alts = [])
        (pullNone : PLeaTTa.pullAux resource.alts = none) :
        RightRegionEmpty alpha
          (.clauses scope original cursor position resource ownership)
    | scheduled (callerScope : CutScopeId)
        (callerTail : List PeTTaSpec.PrologCore.Goal)
        {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
        {head next : Search}
        (origin : AnswerOrigin leafScope bindings head next)
        (resources : List RetainedAlternativeSegment)
        (nonempty : resources ≠ [])
        (history :
          AnswerOriginResourceAgrees alpha origin resources []
            (flattenOwnedAlts resources []) [])
        (inside : OriginPrefixFallsThrough alpha history)
        (pullNone :
          PLeaTTa.pullAux (flattenOwnedAlts resources []) = none) :
        RightRegionEmpty alpha
          (.scheduled callerScope callerTail origin resources nonempty history)

  /-- The first executable branch lies in a right region consumed by this
  answer origin.  `rest` is the literal complete bank after that branch. -/
  inductive OriginPrefixLanding
      (alpha : List (LogicVar × String)) :
      {leafScope : CutScopeId} →
      {bindings : OpenSubstitution.Substitution} →
      {source next : Search} →
      {origin : AnswerOrigin leafScope bindings source next} →
      {beforeResources afterResources :
        List RetainedAlternativeSegment} →
      {beforeAlts afterAlts : List PLeaTTa.Alt} →
      (agreement :
        AnswerOriginResourceAgrees alpha origin beforeResources afterResources
          beforeAlts afterAlts) →
      List PLeaTTa.Goal → Subst → List PLeaTTa.Alt → Prop where
    | choiceInside (scope : CutScopeId) (right : Search)
        {leafScope : CutScopeId}
        {bindings : OpenSubstitution.Substitution}
        {left next : Search}
        (insideOrigin : AnswerOrigin leafScope bindings left next)
        {beforeResources afterResources regionResources :
          List RetainedAlternativeSegment}
        {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
        (insideAgreement :
          AnswerOriginResourceAgrees alpha insideOrigin beforeResources
            (regionResources ++ afterResources) beforeAlts
            (regionAlts ++ afterAlts))
        (regionAgreement :
          RightAlternativeRegionAgrees alpha right regionResources regionAlts)
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (rest : List PLeaTTa.Alt)
        (inside :
          OriginPrefixLanding alpha insideAgreement goals binding rest)
        (pullExact :
          PLeaTTa.pullAux beforeAlts =
            some (.branch goals binding, rest)) :
        OriginPrefixLanding alpha
          (.choice scope right insideOrigin insideAgreement regionAgreement)
          goals binding rest
    | choiceRegion (scope : CutScopeId) (right : Search)
        {leafScope : CutScopeId}
        {bindings : OpenSubstitution.Substitution}
        {left next : Search}
        (insideOrigin : AnswerOrigin leafScope bindings left next)
        {beforeResources afterResources regionResources :
          List RetainedAlternativeSegment}
        {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
        (insideAgreement :
          AnswerOriginResourceAgrees alpha insideOrigin beforeResources
            (regionResources ++ afterResources) beforeAlts
            (regionAlts ++ afterAlts))
        (regionAgreement :
          RightAlternativeRegionAgrees alpha right regionResources regionAlts)
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (regionTail : List PLeaTTa.Alt)
        (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
        (regionLive :
          RightRegionLanding alpha regionAgreement goals binding regionTail)
        (pullExact :
          PLeaTTa.pullAux beforeAlts =
            some (.branch goals binding, regionTail ++ afterAlts)) :
        OriginPrefixLanding alpha
          (.choice scope right insideOrigin insideAgreement regionAgreement)
          goals binding (regionTail ++ afterAlts)
    | cutBoundary (scope : CutScopeId)
        {leafScope : CutScopeId}
        {bindings : OpenSubstitution.Substitution}
        {body next : Search}
        (insideOrigin : AnswerOrigin leafScope bindings body next)
        {beforeResources afterResources :
          List RetainedAlternativeSegment}
        {beforeAlts afterAlts : List PLeaTTa.Alt}
        (insideAgreement :
          AnswerOriginResourceAgrees alpha insideOrigin beforeResources
            afterResources beforeAlts (.barrier :: afterAlts))
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (rest : List PLeaTTa.Alt)
        (inside :
          OriginPrefixLanding alpha insideAgreement goals binding rest)
        (pullExact :
          PLeaTTa.pullAux beforeAlts =
            some (.branch goals binding, rest)) :
        OriginPrefixLanding alpha
          (.cutBoundary scope insideOrigin insideAgreement)
          goals binding rest

  /-- Every branch and marker belonging to this origin is skipped.  The
  executable pull from `beforeAlts` is therefore exactly the pull from the
  older `afterAlts` base. -/
  inductive OriginPrefixFallsThrough
      (alpha : List (LogicVar × String)) :
      {leafScope : CutScopeId} →
      {bindings : OpenSubstitution.Substitution} →
      {source next : Search} →
      {origin : AnswerOrigin leafScope bindings source next} →
      {beforeResources afterResources :
        List RetainedAlternativeSegment} →
      {beforeAlts afterAlts : List PLeaTTa.Alt} →
      (agreement :
        AnswerOriginResourceAgrees alpha origin beforeResources afterResources
          beforeAlts afterAlts) →
      Prop where
    | task (leafScope : CutScopeId)
        (bindings : OpenSubstitution.Substitution)
        (resources : List RetainedAlternativeSegment)
        (alts : List PLeaTTa.Alt)
        (pullEq : PLeaTTa.pullAux alts = PLeaTTa.pullAux alts) :
        OriginPrefixFallsThrough alpha
          (.task leafScope bindings resources alts)
    | choice (scope : CutScopeId) (right : Search)
        {leafScope : CutScopeId}
        {bindings : OpenSubstitution.Substitution}
        {left next : Search}
        (insideOrigin : AnswerOrigin leafScope bindings left next)
        {beforeResources afterResources regionResources :
          List RetainedAlternativeSegment}
        {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
        (insideAgreement :
          AnswerOriginResourceAgrees alpha insideOrigin beforeResources
            (regionResources ++ afterResources) beforeAlts
            (regionAlts ++ afterAlts))
        (regionAgreement :
          RightAlternativeRegionAgrees alpha right regionResources regionAlts)
        (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
        (regionEmpty : RightRegionEmpty alpha regionAgreement)
        (pullEq :
          PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts) :
        OriginPrefixFallsThrough alpha
          (.choice scope right insideOrigin insideAgreement regionAgreement)
    | cutBoundary (scope : CutScopeId)
        {leafScope : CutScopeId}
        {bindings : OpenSubstitution.Substitution}
        {body next : Search}
        (insideOrigin : AnswerOrigin leafScope bindings body next)
        {beforeResources afterResources :
          List RetainedAlternativeSegment}
        {beforeAlts afterAlts : List PLeaTTa.Alt}
        (insideAgreement :
          AnswerOriginResourceAgrees alpha insideOrigin beforeResources
            afterResources beforeAlts (.barrier :: afterAlts))
        (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
        (pullEq :
          PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts) :
        OriginPrefixFallsThrough alpha
          (.cutBoundary scope insideOrigin insideAgreement)

end

/-! ## Exact executable equations -/

/-- A selected branch in a prefix remains first after appending an arbitrary
older bank; the selected tail is extended by that bank literally. -/
theorem pullAux_append_of_some
    {front suffix : List PLeaTTa.Alt}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (selected :
      PLeaTTa.pullAux front = some (.branch goals binding, tail)) :
    PLeaTTa.pullAux (front ++ suffix) =
      some (.branch goals binding, tail ++ suffix) := by
  induction front with
  | nil => simp [PLeaTTa.pullAux] at selected
  | cons head rest inductionHypothesis =>
      cases head with
      | barrier =>
          simpa [PLeaTTa.pullAux] using inductionHypothesis selected
      | br branchGoals branchBinding =>
          cases selected
          rfl
      | catchActive frame =>
          simpa [PLeaTTa.pullAux] using inductionHypothesis selected
      | catchDormant frame protectedAlts =>
          simp [PLeaTTa.pullAux] at selected

/-- A branch-free prefix contributes no result to `pullAux`; appending it is
observationally identical to pulling the older suffix directly. -/
theorem pullAux_append_of_none
    {front suffix : List PLeaTTa.Alt}
    (empty : PLeaTTa.pullAux front = none) :
    PLeaTTa.pullAux (front ++ suffix) = PLeaTTa.pullAux suffix := by
  induction front with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      cases head with
      | barrier =>
          simpa [PLeaTTa.pullAux] using inductionHypothesis empty
      | br goals binding =>
          simp [PLeaTTa.pullAux] at empty
      | catchActive frame =>
          simpa [PLeaTTa.pullAux] using inductionHypothesis empty
      | catchDormant frame protectedAlts =>
          simp [PLeaTTa.pullAux] at empty

/-- A marker-free bank whose pull is exhausted is literally empty.  This
rules out treating a skipped marker as an exhausted owned clause region. -/
theorem eq_nil_of_pullAux_none_of_barrierCount_zero
    {alts : List PLeaTTa.Alt}
    (markerFree : PLeaTTa.barrierCount alts = 0)
    (empty : PLeaTTa.pullAux alts = none) :
    alts = [] := by
  cases alts with
  | nil => rfl
  | cons head tail =>
      cases head with
      | barrier =>
          simp at markerFree
      | br goals binding =>
          simp [PLeaTTa.pullAux] at empty
      | catchActive frame =>
          simp at markerFree
      | catchDormant frame protectedAlts =>
          simp [PLeaTTa.pullAux] at empty

/-- In a marker-free bank, the branch selected by `pullAux` is the literal
head and its returned remainder is the literal tail. -/
theorem eq_cons_of_pullAux_some_of_barrierCount_zero
    {alts : List PLeaTTa.Alt}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (markerFree : PLeaTTa.barrierCount alts = 0)
    (selected :
      PLeaTTa.pullAux alts = some (.branch goals binding, tail)) :
    alts = .br goals binding :: tail := by
  cases alts with
  | nil =>
      simp [PLeaTTa.pullAux] at selected
  | cons head rest =>
      cases head with
      | barrier =>
          simp at markerFree
      | br branchGoals branchBinding =>
          simp only [PLeaTTa.pullAux] at selected
          cases selected
          rfl
      | catchActive frame =>
          simp at markerFree
      | catchDormant frame protectedAlts =>
          simp [PLeaTTa.pullAux] at selected

/-- A bank consisting solely of resolution branches cannot produce a dormant
catch-resumption target.  Unlike barrier counting, this discriminator also
excludes dormant markers, whose barrier contribution is intentionally zero. -/
theorem pullAux_catchResume_impossible_of_all_branches
    {alts : List PLeaTTa.Alt} {frame : PLeaTTa.CatchFrame}
    {protectedAlts rest : List PLeaTTa.Alt}
    (branchOnly :
      ∀ alt ∈ alts,
        ∃ goals binding, alt = PLeaTTa.Alt.br goals binding) :
    PLeaTTa.pullAux alts ≠
      some (.catchResume frame protectedAlts, rest) := by
  intro resumed
  cases alts with
  | nil => simp [PLeaTTa.pullAux] at resumed
  | cons head tail =>
      rcases branchOnly head (by simp) with ⟨goals, binding, headEq⟩
      subst head
      simp [PLeaTTa.pullAux] at resumed

namespace RightRegionLanding

theorem pullAux_exact
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement :
      RightAlternativeRegionAgrees alpha right resources segment}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : RightRegionLanding alpha agreement goals binding tail) :
    PLeaTTa.pullAux segment = some (.branch goals binding, tail) := by
  cases landing with
  | clauses _ _ _ _ _ _ _ _ _ _ pullExact => exact pullExact
  | scheduled _ _ _ _ _ _ _ _ _ _ pullExact => exact pullExact
  | taskChoices _ _ _ _ _ _ _ _ _ _ _ pullExact => exact pullExact

end RightRegionLanding

namespace RightRegionEmpty

theorem pullAux_none
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement :
      RightAlternativeRegionAgrees alpha right resources segment}
    (empty : RightRegionEmpty alpha agreement) :
    PLeaTTa.pullAux segment = none := by
  cases empty with
  | clauses _ _ _ _ _ _ _ pullNone => exact pullNone
  | scheduled _ _ _ _ _ _ _ pullNone => exact pullNone

end RightRegionEmpty

namespace OriginPrefixLanding

theorem pullAux_exact
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {rest : List PLeaTTa.Alt}
    (landing : OriginPrefixLanding alpha agreement goals binding rest) :
    PLeaTTa.pullAux beforeAlts = some (.branch goals binding, rest) := by
  cases landing with
  | choiceInside _ _ _ _ _ _ _ _ _ pullExact => exact pullExact
  | choiceRegion _ _ _ _ _ _ _ _ _ _ pullExact => exact pullExact
  | cutBoundary _ _ _ _ _ _ _ pullExact => exact pullExact

end OriginPrefixLanding

namespace OriginPrefixFallsThrough

theorem pullAux_eq
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    (falls : OriginPrefixFallsThrough alpha agreement) :
    PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts := by
  cases falls with
  | task _ _ _ _ pullEq => exact pullEq
  | choice _ _ _ _ _ _ _ pullEq => exact pullEq
  | cutBoundary _ _ _ _ pullEq => exact pullEq

end OriginPrefixFallsThrough

namespace AnswerOriginResourceAgrees

/-- If the literal successor of one exact answer origin completes in the
next source transition, every alternative region owned by that origin must
fall through.  A choice successor cannot satisfy the premise:
`choiceComplete` enters its right branch rather than terminating.  Cut
boundaries merely propagate the same completion proof inward.

This is the source-driven exhaustion bridge used to justify an executable
terminal answer-pull without assuming terminality independently. -/
theorem fallsThrough_of_next_completed
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts)
    {before after : Session}
    (completed :
      RawStep before next [.completed] .none after
        (.terminal .completed)) :
    OriginPrefixFallsThrough alpha agreement := by
  exact AnswerOriginResourceAgrees.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun {_} {_} {_} {next} _ _ _ _ _ originAgreement =>
      ∀ {before after : Session},
        RawStep before next [.completed] .none after
          (.terminal .completed) →
        OriginPrefixFallsThrough alpha originAgreement)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by
      intro leafScope bindings resources alts before after completed
      exact OriginPrefixFallsThrough.task leafScope bindings resources alts rfl)
    (by
      intro scope right leafScope bindings left next insideOrigin
        beforeResources afterResources regionResources beforeAlts afterAlts
        regionAlts insideAgreement regionAgreement insideIH regionIH before
        after completed
      have target_ne :
          ∀ {events signal nextAfter target},
            RawStep before (.choice scope next right) events signal nextAfter
              target →
            target ≠ .terminal .completed := by
        intro events signal nextAfter target step targetEq
        cases step <;> cases targetEq
      exact False.elim (target_ne completed rfl))
    (by
      intro scope leafScope bindings body next insideOrigin beforeResources
        afterResources beforeAlts afterAlts insideAgreement insideIH before
        after completed
      cases completed with
      | cutBoundaryComplete _ _ _ _ child =>
          have insideFalls := insideIH child
          exact .cutBoundary scope insideOrigin insideAgreement insideFalls (by
            simpa [PLeaTTa.pullAux] using insideFalls.pullAux_eq))
    agreement completed

end AnswerOriginResourceAgrees

/-! ## Total structural classification -/

namespace AnswerOriginResourceAgrees

/-- Every exact answer-origin zipper either selects the first branch in one
of its own literal right regions or falls through exactly to its supplied
older bank.

The proof is the generated mutual recursor of the original provenance
relations.  In particular, scheduled historical regions recurse through the
origin proof they already carry; they are not flattened into an untyped list
and then re-associated by equality. -/
theorem classifyPrefix
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    (∃ goals binding rest,
        OriginPrefixLanding alpha agreement goals binding rest) ∨
      OriginPrefixFallsThrough alpha agreement := by
  exact AnswerOriginResourceAgrees.rec
    (motive_1 := fun _ _ _ regionAgreement =>
      (∃ goals binding tail,
          RightRegionLanding alpha regionAgreement goals binding tail) ∨
        RightRegionEmpty alpha regionAgreement)
    (motive_2 := fun _ _ _ _ _ originAgreement =>
      (∃ goals binding rest,
          OriginPrefixLanding alpha originAgreement goals binding rest) ∨
        OriginPrefixFallsThrough alpha originAgreement)
    (fun scope original cursor position resource ownership => by
      cases pullEq : PLeaTTa.pullAux resource.alts with
      | none =>
          have empty := eq_nil_of_pullAux_none_of_barrierCount_zero
            (resource.barrierCount_zero ownership) pullEq
          exact .inr
            (.clauses scope original cursor position resource ownership empty
              pullEq)
      | some result =>
          rcases result with ⟨target, tail⟩
          cases target with
          | branch goals binding =>
              have head := eq_cons_of_pullAux_some_of_barrierCount_zero
                (resource.barrierCount_zero ownership) pullEq
              exact .inl
                ⟨goals, binding, tail,
                  .clauses scope original cursor position resource ownership
                    goals binding tail head pullEq⟩
          | catchResume frame protectedAlts =>
              exact False.elim
                (pullAux_catchResume_impossible_of_all_branches
                  (RetainedCursorAlternativeOwnership.alts_all_branches
                    ownership.scan)
                  pullEq))
    (by
      intro callerScope callerTail leafScope bindings head next historyOrigin
        resources nonempty history historyIH
      rcases historyIH with ⟨goals, binding, tail, landing⟩ | falls
      · exact .inl
          ⟨goals, binding, tail,
            .scheduled callerScope callerTail historyOrigin resources nonempty
              history goals binding tail landing landing.pullAux_exact⟩
      · exact .inr
          (.scheduled callerScope callerTail historyOrigin resources nonempty
            history falls (by
              simpa [PLeaTTa.pullAux] using falls.pullAux_eq)))
    (by
      intro support scope barrier canonical referenceBase current runtime right
        goals tail choices
      exact .inl
        ⟨goals, runtime, tail,
          .taskChoices support scope barrier canonical referenceBase current
            runtime right goals tail choices rfl⟩)
    (fun leafScope bindings resources alts =>
      .inr (.task leafScope bindings resources alts rfl))
    (by
      intro scope right leafScope bindings left next insideOrigin
        beforeResources afterResources regionResources beforeAlts afterAlts
        regionAlts insideAgreement regionAgreement insideIH regionIH
      rcases insideIH with ⟨goals, binding, rest, landing⟩ | insideFalls
      · exact .inl
          ⟨goals, binding, rest,
            .choiceInside scope right insideOrigin insideAgreement
              regionAgreement goals binding rest landing
              landing.pullAux_exact⟩
      · rcases regionIH with
          ⟨goals, binding, regionTail, regionLanding⟩ | regionEmpty
        · have pullExact :
              PLeaTTa.pullAux beforeAlts =
                some (.branch goals binding, regionTail ++ afterAlts) := by
            calc
              PLeaTTa.pullAux beforeAlts =
                  PLeaTTa.pullAux (regionAlts ++ afterAlts) :=
                insideFalls.pullAux_eq
              _ = some (.branch goals binding, regionTail ++ afterAlts) :=
                pullAux_append_of_some regionLanding.pullAux_exact
          exact .inl
            ⟨goals, binding, regionTail ++ afterAlts,
              .choiceRegion scope right insideOrigin insideAgreement
                regionAgreement goals binding regionTail insideFalls
                regionLanding pullExact⟩
        · have pullEq :
              PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts := by
            calc
              PLeaTTa.pullAux beforeAlts =
                  PLeaTTa.pullAux (regionAlts ++ afterAlts) :=
                insideFalls.pullAux_eq
              _ = PLeaTTa.pullAux afterAlts :=
                pullAux_append_of_none regionEmpty.pullAux_none
          exact .inr
            (.choice scope right insideOrigin insideAgreement regionAgreement
              insideFalls regionEmpty pullEq))
    (by
      intro scope leafScope bindings body next insideOrigin beforeResources
        afterResources beforeAlts afterAlts insideAgreement insideIH
      rcases insideIH with ⟨goals, binding, rest, landing⟩ | falls
      · exact .inl
          ⟨goals, binding, rest,
            .cutBoundary scope insideOrigin insideAgreement goals binding rest
              landing landing.pullAux_exact⟩
      · have pullEq :
            PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts := by
          calc
            PLeaTTa.pullAux beforeAlts =
                PLeaTTa.pullAux (.barrier :: afterAlts) :=
              falls.pullAux_eq
            _ = PLeaTTa.pullAux afterAlts := rfl
        exact .inr
          (.cutBoundary scope insideOrigin insideAgreement falls pullEq))
    agreement

end AnswerOriginResourceAgrees

/-! ## Four-way answer-pull outcome -/

/-- Exact landing of one eager executable answer pull relative to the source
origin zipper.

`events` is the observation trace the later source catch-up theorem must
produce: landing on any live branch is silent, while total exhaustion lets
exactly one completion escape.  This module classifies and fixes that trace;
it deliberately does not yet claim the corresponding `StepsN`. -/
inductive OriginPullOutcome
    (alpha : List (LogicVar × String))
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    List Observation → Prop where
  | localLive (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (landing : OriginPrefixLanding alpha agreement goals binding rest) :
      OriginPullOutcome alpha agreement []
  | baseLive (falls : OriginPrefixFallsThrough alpha agreement)
      (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (basePull :
        PLeaTTa.pullAux afterAlts = some (.branch goals binding, rest)) :
      OriginPullOutcome alpha agreement []
  | baseCatchResume (falls : OriginPrefixFallsThrough alpha agreement)
      (frame : PLeaTTa.CatchFrame) (protectedAlts rest : List PLeaTTa.Alt)
      (basePull :
        PLeaTTa.pullAux afterAlts =
          some (.catchResume frame protectedAlts, rest)) :
      OriginPullOutcome alpha agreement []
  | terminal (falls : OriginPrefixFallsThrough alpha agreement)
      (basePull : PLeaTTa.pullAux afterAlts = none) :
      OriginPullOutcome alpha agreement [.completed]

namespace AnswerOriginResourceAgrees

/-- Total classification for the real incoming alternative bank.

No caller chooses the case or the branch.  The local/base split comes from
`classifyPrefix`; only after every local region falls through is the literal
older suffix inspected for a branch versus exhaustion. -/
theorem classifyPull
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    ∃ events, OriginPullOutcome alpha agreement events := by
  rcases classifyPrefix agreement with
    ⟨goals, binding, rest, landing⟩ | falls
  · exact ⟨[], .localLive goals binding rest landing⟩
  · cases baseEq : PLeaTTa.pullAux afterAlts with
    | none => exact ⟨[.completed], .terminal falls baseEq⟩
    | some result =>
        rcases result with ⟨target, rest⟩
        cases target with
        | branch goals binding =>
            exact ⟨[], .baseLive falls goals binding rest baseEq⟩
        | catchResume frame protectedAlts =>
            exact
              ⟨[], .baseCatchResume falls frame protectedAlts rest baseEq⟩

end AnswerOriginResourceAgrees

namespace OriginPullOutcome

/-- The four-way source classification reconstructs exactly the existing
total executable pull classifier at the literal incoming bank. -/
theorem toPullOutcomeAgrees
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {events : List Observation}
    (outcome : OriginPullOutcome alpha agreement events) :
    (∃ goals binding rest,
        events = [] ∧
          PrologFindallAnswerResourceBridge.PullOutcomeAgrees beforeAlts
            (some (goals, binding)) rest) ∨
      (∃ frame protectedAlts rest,
        events = [] ∧
          PrologFindallAnswerResourceBridge.PullOutcomeAgrees beforeAlts none
            (protectedAlts ++ .catchActive frame :: rest)) ∨
        (events = [.completed] ∧
          PrologFindallAnswerResourceBridge.PullOutcomeAgrees beforeAlts none
            []) := by
  cases outcome with
  | localLive goals binding rest landing =>
      exact .inl
        ⟨goals, binding, rest, rfl,
          .selected (beforeAlts := beforeAlts) goals binding rest
            landing.pullAux_exact⟩
  | baseLive falls goals binding rest basePull =>
      have pullExact :
          PLeaTTa.pullAux beforeAlts =
            some (.branch goals binding, rest) :=
        falls.pullAux_eq.trans basePull
      exact .inl
        ⟨goals, binding, rest, rfl,
          .selected (beforeAlts := beforeAlts) goals binding rest pullExact⟩
  | baseCatchResume falls frame protectedAlts rest basePull =>
      have pullExact :
          PLeaTTa.pullAux beforeAlts =
            some (.catchResume frame protectedAlts, rest) :=
        falls.pullAux_eq.trans basePull
      exact .inr (.inl
        ⟨frame, protectedAlts, rest, rfl,
          .catchResumed (beforeAlts := beforeAlts) frame protectedAlts rest
            pullExact⟩)
  | terminal falls basePull =>
      have pullNone : PLeaTTa.pullAux beforeAlts = none :=
        falls.pullAux_eq.trans basePull
      exact .inr (.inr
        ⟨rfl, .exhausted (beforeAlts := beforeAlts) pullNone⟩)

/-- The classification fixes source-observation shape independently of any
later step-count proof. -/
theorem events_eq_live_or_completed
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId}
    {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {events : List Observation}
    (outcome : OriginPullOutcome alpha agreement events) :
    events = [] ∨ events = [.completed] := by
  cases outcome <;> simp

end OriginPullOutcome

/-! ## Active-answer consumer and anti-vacuity witnesses -/

namespace ActiveFindallAnswerResourceAgrees

/-- Every resource-certified active `findall` answer exposes the exact direct
producer origin and the pull classification for its literal incoming bank.

The transparent wrappers around the collector are erased only by the existing
`has_exactProducerResource` theorem.  The origin, resource zipper, and
classification remain tied to the same child source and successor.  Every
existential witness below is a projection of `answer`'s own direct producer;
none is an independently chosen compatible producer or origin. -/
theorem classifyOriginPull
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search next : Search}
    {cell : PrologFindallFrameZipperBridge.SourceCollectionCell}
    {answerBindings : OpenSubstitution.Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha before search childAfter next
        cell answerBindings beforeResources afterResources beforeAlts
        afterAlts) :
    ∃ childSource childNext leafScope,
      ∃ origin : AnswerOrigin leafScope answerBindings childSource childNext,
        ExactAnswerProducer before childAfter childSource childNext
            answerBindings ∧
          ∃ agreement :
              AnswerOriginResourceAgrees alpha origin beforeResources
                afterResources beforeAlts afterAlts,
            ∃ events, OriginPullOutcome alpha agreement events := by
  rcases answer.has_exactProducerResource with
    ⟨childSource, childNext, producer⟩
  rcases producer.originAgreement with ⟨leafScope, origin, agreement⟩
  rcases AnswerOriginResourceAgrees.classifyPull agreement with
    ⟨events, outcome⟩
  exact
    ⟨childSource, childNext, leafScope, origin, producer.producer,
      agreement, events, outcome⟩

end ActiveFindallAnswerResourceAgrees

/-- A genuinely owned resource with a live executable branch exists.  The
ownership and head equation are projected from the ranked outer-catch-up
witness, so no cursor well-formedness or scan result is assumed here. -/
theorem live_owned_region_is_inhabited :
    ∃ resource : RetainedAlternativeSegment,
      ∃ cursor : Resolver.PreparedCursor,
        ∃ goals binding tail,
          resource.HasIndexedOwnershipAt
            ([] : List (LogicVar × String)) cursor ∧
            resource.alts = .br goals binding :: tail := by
  obtain ⟨partition, _, _, _⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.two_crossed_then_live_partition_is_inhabited
  exact
    ⟨partition.first, partition.firstCursor, partition.goals,
      partition.binding, partition.tail, partition.firstOwnership,
      partition.firstHead⟩

/-- A genuinely owned source cursor whose conservative executable scan is
empty also exists.  Its source occurrence performs one ranked rejected pull;
the empty bank is therefore not a fabricated empty descriptor. -/
theorem empty_owned_region_is_inhabited :
    ∃ resource : RetainedAlternativeSegment,
      ∃ cursor : Resolver.PreparedCursor,
        resource.HasIndexedOwnershipAt
          ([] : List (LogicVar × String)) cursor ∧
          resource.alts = [] := by
  obtain
      ⟨resource, _, cursor, _, _, empty, _, _, ownership, _⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.one_rejected_crossed_frame_is_inhabited
  exact ⟨resource, cursor, ownership, empty⟩

/-- The first local right region can be the selected pull landing.  The owned
bank is concretely nonempty, and falling through to the empty base would
contradict its exact `pullAux` result. -/
theorem first_local_region_is_inhabited :
    ∃ (cursor : Resolver.PreparedCursor)
        (resource : RetainedAlternativeSegment)
        (origin :
          AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
            (.cutBoundary 1
              (.choice 1 (.task 1 [] []) (.clauses 1 cursor)))
            (.cutBoundary 1
              (.choice 1 .done (.clauses 1 cursor))))
        (agreement :
          AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
            [resource] [] (resource.alts ++ [.barrier]) []),
      resource.alts ≠ [] ∧
        ∃ goals binding rest,
          OriginPrefixLanding [] agreement goals binding rest ∧
            OriginPullOutcome [] agreement [] := by
  obtain ⟨resource, cursor, goals, binding, tail, ownership, head⟩ :=
    live_owned_region_is_inhabited
  let origin :
      AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
        (.cutBoundary 1
          (.choice 1 (.task 1 [] []) (.clauses 1 cursor)))
        (.cutBoundary 1
          (.choice 1 .done (.clauses 1 cursor))) :=
    .cutBoundary 1 (.choice 1 (.clauses 1 cursor) .task)
  have agreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
        [resource] [] (resource.alts ++ [.barrier]) [] := by
    rcases ownership with ⟨callStart, position, exactOwnership⟩
    simpa [origin] using
      (AnswerOriginResourceAgrees.active_call_exact_at
        (alpha := ([] : List (LogicVar × String))) 1
        ([] : OpenSubstitution.Substitution) callStart cursor position
        resource [] [] exactOwnership)
  have nonempty : resource.alts ≠ [] := by
    rw [head]
    simp
  refine ⟨cursor, resource, origin, agreement, nonempty, ?_⟩
  rcases AnswerOriginResourceAgrees.classifyPrefix agreement with
    ⟨selectedGoals, selectedBinding, rest, landing⟩ | falls
  · exact
      ⟨selectedGoals, selectedBinding, rest, landing,
        .localLive selectedGoals selectedBinding rest landing⟩
  · have selected :
        PLeaTTa.pullAux (resource.alts ++ [.barrier]) =
          some (.branch goals binding, tail ++ [.barrier]) := by
      apply pullAux_append_of_some
      rw [head]
      rfl
    have impossible := falls.pullAux_eq
    rw [selected] at impossible
    simp [PLeaTTa.pullAux] at impossible

/-- The second local right region is selected after a genuine first region
falls through.  Both ownership certificates are real; the first bank is
empty and the second bank has a literal branch. -/
theorem second_local_region_after_empty_is_inhabited :
    ∃ (emptyCursor liveCursor : Resolver.PreparedCursor)
        (emptyResource liveResource : RetainedAlternativeSegment)
        (origin :
          AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
            (.choice 2
              (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
              (.clauses 2 liveCursor))
            (.choice 2
              (.choice 1 .done (.clauses 1 emptyCursor))
              (.clauses 2 liveCursor)))
        (agreement :
          AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
            [emptyResource, liveResource] []
            (emptyResource.alts ++ liveResource.alts) []),
      emptyResource.alts = [] ∧ liveResource.alts ≠ [] ∧
        ∃ goals binding rest,
          OriginPrefixLanding [] agreement goals binding rest ∧
            OriginPullOutcome [] agreement [] := by
  obtain ⟨emptyResource, emptyCursor, emptyOwnership, emptyHead⟩ :=
    empty_owned_region_is_inhabited
  obtain
      ⟨liveResource, liveCursor, goals, binding, tail, liveOwnership,
        liveHead⟩ := live_owned_region_is_inhabited
  let leaf :
      AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
        (.task 1 [] []) .done := .task
  let innerOrigin :
      AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
        (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
        (.choice 1 .done (.clauses 1 emptyCursor)) :=
    .choice 1 (.clauses 1 emptyCursor) leaf
  let origin :
      AnswerOrigin 1 ([] : OpenSubstitution.Substitution)
        (.choice 2
          (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor))
        (.choice 2
          (.choice 1 .done (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor)) :=
    .choice 2 (.clauses 2 liveCursor) innerOrigin
  have leafAgreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) leaf
        [emptyResource, liveResource] [emptyResource, liveResource]
        (emptyResource.alts ++ liveResource.alts)
        (emptyResource.alts ++ liveResource.alts) :=
    .task 1 [] [emptyResource, liveResource]
      (emptyResource.alts ++ liveResource.alts)
  have emptyRegion :
      RightAlternativeRegionAgrees ([] : List (LogicVar × String))
        (.clauses 1 emptyCursor) [emptyResource] emptyResource.alts :=
    by
      rcases emptyOwnership with
        ⟨emptyCallStart, emptyPosition, exactEmptyOwnership⟩
      exact
        .clauses 1 emptyCallStart emptyCursor emptyPosition emptyResource
          exactEmptyOwnership
  have innerAgreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) innerOrigin
        [emptyResource, liveResource] [liveResource]
        (emptyResource.alts ++ liveResource.alts) liveResource.alts := by
    simpa [innerOrigin] using
      (AnswerOriginResourceAgrees.choice 1 (.clauses 1 emptyCursor) leaf
        leafAgreement emptyRegion)
  have liveRegion :
      RightAlternativeRegionAgrees ([] : List (LogicVar × String))
        (.clauses 2 liveCursor) [liveResource] liveResource.alts :=
    by
      rcases liveOwnership with
        ⟨liveCallStart, livePosition, exactLiveOwnership⟩
      exact
        .clauses 2 liveCallStart liveCursor livePosition liveResource
          exactLiveOwnership
  have innerAgreementForOuter :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) innerOrigin
        [emptyResource, liveResource] ([liveResource] ++ [])
        (emptyResource.alts ++ liveResource.alts)
        (liveResource.alts ++ []) := by
    simpa only [List.append_nil] using innerAgreement
  let agreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
        [emptyResource, liveResource] []
        (emptyResource.alts ++ liveResource.alts) [] :=
      (AnswerOriginResourceAgrees.choice 2 (.clauses 2 liveCursor) innerOrigin
        innerAgreementForOuter liveRegion)
  have selected :
      PLeaTTa.pullAux (emptyResource.alts ++ liveResource.alts) =
        some (.branch goals binding, tail) := by
    rw [emptyHead, liveHead]
    simp [PLeaTTa.pullAux]
  refine
    ⟨emptyCursor, liveCursor, emptyResource, liveResource, origin, agreement,
      emptyHead, ?_, ?_⟩
  · rw [liveHead]
    simp
  · rcases AnswerOriginResourceAgrees.classifyPrefix agreement with
      ⟨selectedGoals, selectedBinding, rest, landing⟩ | falls
    · exact
        ⟨selectedGoals, selectedBinding, rest, landing,
          .localLive selectedGoals selectedBinding rest landing⟩
    · have impossible := falls.pullAux_eq
      rw [selected] at impossible
      simp [PLeaTTa.pullAux] at impossible

/-- The older base-bank branch is a distinct live case: a task-only origin
consumes no local resource or alternative region. -/
theorem base_live_is_inhabited :
    let base : List PLeaTTa.Alt := [.br [] []]
    let origin :
        AnswerOrigin 0 ([] : OpenSubstitution.Substitution)
          (.task 0 [] []) .done := .task
    let agreement :
        AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
          [] [] base base := .task 0 [] [] base
    OriginPullOutcome [] agreement [] := by
  dsimp only
  exact
    .baseLive (.task 0 [] [] [.br [] []] rfl) [] [] [] rfl

/-- A marker-only older bank is exhausted rather than mistaken for an answer.
The completion event therefore belongs to the terminal case. -/
theorem marker_only_terminal_is_inhabited :
    let base : List PLeaTTa.Alt := [.barrier, .barrier]
    let origin :
        AnswerOrigin 0 ([] : OpenSubstitution.Substitution)
          (.task 0 [] []) .done := .task
    let agreement :
        AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
          [] [] base base := .task 0 [] [] base
    OriginPullOutcome [] agreement [.completed] := by
  dsimp only
  exact
    .terminal (.task 0 [] [] [.barrier, .barrier] rfl) rfl

/-- Leading and trailing predicate markers are skipped, never returned as a
synthetic answer.  The exact base-live result pins both the selected branch
and the residual trailing marker. -/
theorem barriers_are_skipped_not_selected :
    let base : List PLeaTTa.Alt :=
      [.barrier, .barrier, .br [] [], .barrier]
    let origin :
        AnswerOrigin 0 ([] : OpenSubstitution.Substitution)
          (.task 0 [] []) .done := .task
    let agreement :
        AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
          [] [] base base := .task 0 [] [] base
    PLeaTTa.pullAux base = some (.branch [] [], [.barrier]) ∧
      OriginPullOutcome [] agreement [] := by
  dsimp only
  exact
    ⟨rfl,
      .baseLive
        (.task 0 [] [] [.barrier, .barrier, .br [] [], .barrier] rfl)
        [] [] [.barrier] rfl⟩

/-- The classifier also has a genuine depth-two scheduled inhabitant.  The
carried historical origin owns two resources and exactly two predicate
markers, so recursion through the scheduled case cannot be replaced by a
singleton shortcut. -/
theorem depth_two_scheduled_classification_is_inhabited :
    ∃ next : Search,
      ∃ resources : List RetainedAlternativeSegment,
        ∃ segment : List PLeaTTa.Alt,
          ∃ _region :
              RightAlternativeRegionAgrees
                ([] : List (LogicVar × String)) (.product 4 next []) resources
                  segment,
            resources.length = 2 ∧
              PLeaTTa.barrierCount segment = 2 ∧
                ∃ (origin :
                    AnswerOrigin 5 ([] : OpenSubstitution.Substitution)
                      (.choice 5 (.task 5 [] []) (.product 4 next []))
                      (.choice 5 .done (.product 4 next [])))
                  (agreement :
                    AnswerOriginResourceAgrees
                      ([] : List (LogicVar × String)) origin resources []
                        segment []),
                  ∃ events, OriginPullOutcome [] agreement events := by
  obtain ⟨next, resources, segment, resourceCount, region, markerCount⟩ :=
    PLeaTTa.PrologAnswerResourceBridge.AnswerOriginResourceAgrees.two_resource_scheduled_region_is_inhabited
  let leaf :
      AnswerOrigin 5 ([] : OpenSubstitution.Substitution)
        (.task 5 [] []) .done := .task
  let origin :
      AnswerOrigin 5 ([] : OpenSubstitution.Substitution)
        (.choice 5 (.task 5 [] []) (.product 4 next []))
        (.choice 5 .done (.product 4 next [])) :=
    .choice 5 (.product 4 next []) leaf
  have leafAgreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) leaf
        resources resources segment segment :=
    .task 5 [] resources segment
  have leafAgreementForOuter :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) leaf
        resources (resources ++ []) segment (segment ++ []) := by
    simpa only [List.append_nil] using leafAgreement
  let agreement :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
        resources [] segment [] :=
      (AnswerOriginResourceAgrees.choice 5 (.product 4 next []) leaf
        leafAgreementForOuter region)
  rcases AnswerOriginResourceAgrees.classifyPull agreement with
    ⟨events, outcome⟩
  exact
    ⟨next, resources, segment, region, resourceCount, markerCount, origin,
      agreement, events, outcome⟩

end PLeaTTa.PrologAnswerPullClassificationBridge
