-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallCopyBridge
Purpose: Relate answer-time independent findall copies to the executable
  collector's later bounded copy phase without identifying allocator counters.
Trusted boundary: none
Main exports: RuntimeTermAgrees, DeferredCopyAgreesAt,
  CollectionCopyFrontier, CopyPaymentAgrees
-/
import PLeaTTa.Proofs.FindallCopy
import PLeaTTa.Proofs.PrologMguOpenAgreement
import PLeaTTa.Proofs.PrologMguVariantRenaming
import PLeaTTa.Proofs.PrologPrefilterBridge
import PLeaTTa.Proofs.PrologStateBridge

namespace PLeaTTa.PrologFindallCopyBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Copy
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguVariant
open PrologMguVariantRenaming
open PrologPrefilterBridge
open PrologStateBridge

/-!
# The private-copy timing seam

The independent search semantics copies a `findall/3` template as soon as its
generator answer is collected.  The executable macro stores the materialized
answer and its additive fine lane copies the completed bag later.  Neither
choice is observable before collection finishes, but their allocation
counters cannot be equated: nested calls may allocate between two answers.

The bridge below records an ordered *copy debt*.  Each independent copied term
is paired with the still-raw executable answer from which it arose.  Advancing
either allocator preserves the debt.  During the bounded executable copy
phase, one `BagCopyStep` pays exactly one entry and produces an explicit finite
alpha bijection for that value.  Thus the timing difference is represented in
the state relation rather than erased by an answer-list quotient or a
zero-step copy.
-/

/-- Independent targets chosen by the deterministic finite-term copier, in
stable first-occurrence order. -/
def termCopyReferenceTargets (firstFresh : Nat) (source : Term) :
    List LogicVar :=
  (copyVariables source).map (copyRename firstFresh source)

/-- Executable suffix targets for the same independently derived finite
support. -/
def termCopyExecutableTargets (suffix : String) (source : Term) :
    List String :=
  executableFreshTargets suffix (copyVariables source)

/-- The positional alpha graph used to compare the two actual copy
implementations. -/
def termCopyAlphaGraph (firstFresh : Nat) (suffix : String)
    (source : Term) : List (LogicVar × String) :=
  RuntimeAlpha.graph
    (termCopyReferenceTargets firstFresh source)
    (termCopyExecutableTargets suffix source)

private theorem eraseDups_nodup :
    ∀ support : List LogicVar, support.eraseDups.Nodup
  | [] => by
      simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup
          (tail.filter (fun identity => !identity == head))
termination_by support => support.length
decreasing_by
  have lengthBound :=
    List.length_filter_le (fun identity : LogicVar => !identity == head) tail
  simp only [List.length_cons]
  omega

private theorem copyVariables_nodup (source : Term) :
    (copyVariables source).Nodup := by
  exact eraseDups_nodup (termVariables source)

/-- The independent copier is injective on the variables that actually occur
in its finite source term. -/
theorem copyRename_injective_on (firstFresh : Nat) (source : Term)
    {left right : LogicVar}
    (leftMember : left ∈ copyVariables source)
    (_rightMember : right ∈ copyVariables source)
    (same :
      copyRename firstFresh source left =
        copyRename firstFresh source right) :
    left = right := by
  have sameIndex :
      (copyVariables source).idxOf left =
        (copyVariables source).idxOf right := by
    unfold copyRename at same
    injection same with generated
    omega
  exact (List.idxOf_inj leftMember).mp sameIndex

/-! ## Canonical renaming and source-denotation support

`RuntimeTermAgrees` is a Prolog-semantic relation.  Its independent side is
therefore compared through canonical tree denotation rather than raw list
presentation.  The lemmas in this section prove that the *actual* source
copier still induces exactly one canonical alpha-renaming: no variable is
invented, merged, or visited in a different order by denotation. -/

/-- Canonical list expansion commutes with one variable renaming. -/
theorem Tree.renameVariables_prologList (rename : LogicVar → LogicVar)
    (items : List Tree) (tail : Option Tree) :
    Tree.renameVariables rename (Tree.prologList items tail) =
      Tree.prologList (Trees.renameVariables rename items)
        (tail.map (Tree.renameVariables rename)) := by
  induction items with
  | nil =>
      cases tail <;> rfl
  | cons head items inductionHypothesis =>
      simp only [Tree.prologList, Tree.renameVariables,
        Trees.renameVariables]
      rw [inductionHypothesis]

mutual

/-- Source variable renaming and canonical denotation commute exactly. -/
theorem Term.denote_renameVariables (rename : LogicVar → LogicVar) :
    (term : Term) →
      Term.denote (term.renameVariables rename) =
        Tree.renameVariables rename (Term.denote term)
  | .variable identity => rfl
  | .atom name => rfl
  | .integer value => rfl
  | .float value => rfl
  | .string value => rfl
  | .compound functor arguments => by
      simp only [Term.renameVariables, Term.denote,
        Tree.renameVariables]
      rw [Terms.denote_renameVariables]
  | .list items none => by
      simp only [Term.renameVariables, Term.denote]
      rw [Tree.renameVariables_prologList,
        Terms.denote_renameVariables]
      rfl
  | .list items (some tail) => by
      simp only [Term.renameVariables, Term.denote]
      rw [Tree.renameVariables_prologList,
        Terms.denote_renameVariables, Term.denote_renameVariables]
      rfl

/-- Ordered source-term companion of `Term.denote_renameVariables`. -/
theorem Terms.denote_renameVariables (rename : LogicVar → LogicVar) :
    (terms : List Term) →
      Terms.denote (Terms.renameVariables rename terms) =
        Trees.renameVariables rename (Terms.denote terms)
  | [] => rfl
  | term :: terms => by
      simp only [Terms.renameVariables, Terms.denote,
        Trees.renameVariables]
      rw [Term.denote_renameVariables, Terms.denote_renameVariables]

end


/-- Canonical list expansion preserves every variable-support predicate. -/
private theorem treePrologList_variablesSatisfy
    {predicate : LogicVar → Prop} :
    ∀ {items : List Tree} {tail : Option Tree},
      TreesVariablesSatisfy predicate items →
      (match tail with
        | none => True
        | some finalTail => TreeVariablesSatisfy predicate finalTail) →
      TreeVariablesSatisfy predicate (Tree.prologList items tail)
  | [], none, _itemsSupported, _tailSupported => by
      trivial
  | [], some tail, _itemsSupported, tailSupported => by
      exact tailSupported
  | head :: items, tail, itemsSupported, tailSupported => by
      exact
        ⟨itemsSupported.1,
          ⟨treePrologList_variablesSatisfy
              itemsSupported.2 tailSupported, trivial⟩⟩

mutual

/-- Every variable in a denoted term comes from its source occurrence list. -/
theorem Term.denote_variablesSatisfy_of_occurrences
    {predicate : LogicVar → Prop} :
    (term : Term) →
      (∀ identity, identity ∈ termVariables term → predicate identity) →
      TreeVariablesSatisfy predicate (Term.denote term)
  | .variable identity, supported =>
      supported identity (by simp [termVariables])
  | .atom name, _supported => by
      trivial
  | .integer value, _supported => by
      trivial
  | .float value, _supported => by
      trivial
  | .string value, _supported => by
      trivial
  | .compound functor arguments, supported => by
      exact
        Terms.denote_variablesSatisfy_of_occurrences arguments
          (fun identity member =>
            supported identity (by simpa [termVariables] using member))
  | .list items none, supported => by
      exact treePrologList_variablesSatisfy
        (Terms.denote_variablesSatisfy_of_occurrences items
          (fun identity member =>
            supported identity (by simpa [termVariables] using member)))
        trivial
  | .list items (some tail), supported => by
      exact treePrologList_variablesSatisfy
        (Terms.denote_variablesSatisfy_of_occurrences items
          (fun identity member =>
            supported identity (by
              simp [termVariables, member])))
        (Term.denote_variablesSatisfy_of_occurrences tail
          (fun identity member =>
            supported identity (by
              simp [termVariables, member])))

/-- Ordered companion of
`Term.denote_variablesSatisfy_of_occurrences`. -/
theorem Terms.denote_variablesSatisfy_of_occurrences
    {predicate : LogicVar → Prop} :
    (terms : List Term) →
      (∀ identity, identity ∈ termsVariables terms → predicate identity) →
      TreesVariablesSatisfy predicate (Terms.denote terms)
  | [], _supported => by
      trivial
  | term :: terms, supported =>
      ⟨Term.denote_variablesSatisfy_of_occurrences term
          (fun identity member =>
            supported identity (by
              simp [termsVariables, member])),
        Terms.denote_variablesSatisfy_of_occurrences terms
          (fun identity member =>
            supported identity (by
              simp [termsVariables, member]))⟩

end


/-- Canonical/runtime agreement is stable under one finite alpha-renaming.
The support premise ensures the target graph need only cover variables that
actually occur in this value. -/
theorem canonicalRuntimeAgrees_alpha_rename
    {rename : LogicVar → LogicVar} {suffix : String}
    {domain : List LogicVar}
    {before after : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity name,
        (identity, name) ∈ before → identity ∈ domain →
          (rename identity, name ++ suffix) ∈ after)
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees before tree atom)
    (supported :
      TreeVariablesSatisfy (fun identity => identity ∈ domain) tree) :
    CanonicalRuntimeAgrees after
      (Tree.renameVariables rename tree)
      (renameAtomSuffix suffix atom) := by
  induction agreement with
  | «variable» linked =>
      simpa [Tree.renameVariables, renameAtomSuffix_var] using
        (CanonicalRuntimeAgrees.variable
          (variableAgreement _ _ linked supported))
  | atom notTrue notFalse =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_sym] using
        (CanonicalRuntimeAgrees.atom (alpha := after) notTrue notFalse)
  | trueAtom =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_sym] using
        (CanonicalRuntimeAgrees.trueAtom (alpha := after))
  | falseAtom =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_sym] using
        (CanonicalRuntimeAgrees.falseAtom (alpha := after))
  | integer value =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_gnd] using
        (CanonicalRuntimeAgrees.integer (alpha := after) value)
  | float value =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_gnd] using
        (CanonicalRuntimeAgrees.float (alpha := after) value)
  | string value =>
      simpa [Tree.renameVariables, Trees.renameVariables,
        renameAtomSuffix_gnd] using
        (CanonicalRuntimeAgrees.string (alpha := after) value)
  | partialValue arguments inductionHypothesis =>
      simpa [Tree.renameVariables, Trees.renameVariables, partialC,
        partialTagA, renameAtomSuffix_expr, renameAtomSuffix_chainOf,
        renameAtomSuffix_sym, renameAtomSuffix_gnd] using
        (CanonicalRuntimeAgrees.partialValue
          (inductionHypothesis supported.2.1))
  | nil =>
      simpa [Tree.renameVariables, Trees.renameVariables, nilA,
        renameAtomSuffix_gnd] using
        (CanonicalRuntimeAgrees.nil (alpha := after))
  | cons head tail headInduction tailInduction =>
      simpa [Tree.renameVariables, Trees.renameVariables, consC,
        renameAtomSuffix_expr, renameAtomSuffix_sym] using
        (CanonicalRuntimeAgrees.cons
          (headInduction supported.1)
          (tailInduction supported.2.1))

/-- The independent copy targets are injective on the complete finite source
support. -/
theorem termCopyReferenceTargets_nodup (firstFresh : Nat) (source : Term) :
    (termCopyReferenceTargets firstFresh source).Nodup := by
  apply (copyVariables_nodup source).map_on
  intro left leftMember right rightMember same
  exact copyRename_injective_on firstFresh source
    leftMember rightMember same

/-- The two target lists have the same independently determined cardinality
and are both injective under the already-explicit source/generated spelling
premise. -/
theorem termCopy_runtimeAlpha (firstFresh : Nat) (suffix : String)
    (source : Term) (encoding : EncodingInjectiveOn (copyVariables source)) :
    RuntimeAlpha
      (termCopyReferenceTargets firstFresh source)
      (termCopyExecutableTargets suffix source) := by
  constructor
  · simp [termCopyReferenceTargets, termCopyExecutableTargets,
      executableFreshTargets]
  · exact termCopyReferenceTargets_nodup firstFresh source
  · exact executableFreshTargets_nodup
      (copyVariables_nodup source) encoding suffix

private theorem termCopyAlphaGraph_eq_map (firstFresh : Nat)
    (suffix : String) (source : Term) :
    termCopyAlphaGraph firstFresh suffix source =
      (copyVariables source).map fun identity =>
        (copyRename firstFresh source identity,
          logicVarExecutableName identity ++ suffix) := by
  unfold termCopyAlphaGraph RuntimeAlpha.graph
  unfold termCopyReferenceTargets termCopyExecutableTargets
  unfold executableFreshTargets
  induction copyVariables source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.zip_cons_cons, inductionHypothesis]

/-- Every occurring source identity is linked to the two concrete targets at
its stable support position. -/
theorem termCopyAlphaGraph_member (firstFresh : Nat) (suffix : String)
    (source : Term) (identity : LogicVar)
    (member : identity ∈ termVariables source) :
    (copyRename firstFresh source identity,
      logicVarExecutableName identity ++ suffix) ∈
        termCopyAlphaGraph firstFresh suffix source := by
  rw [termCopyAlphaGraph_eq_map, List.mem_map]
  exact ⟨identity, List.mem_eraseDups.mpr member, rfl⟩

/-- Representation agreement is stable under an arbitrary independent
variable renaming and the executable's common-suffix renaming, provided the
same finite alpha graph links every variable in the independently supplied
domain. -/
theorem termAgrees_alpha_rename
    {rename : LogicVar → LogicVar} {suffix : String}
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        (rename identity, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {term : Term} {atom : Atom} (agreement : TermAgrees term atom)
    (supported : termVariablesIn domain term) :
    AlphaTermAgrees alpha
      (term.renameVariables rename)
      (renameAtomSuffix suffix atom) := by
  apply TermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        AlphaTermAgrees alpha
          (term.renameVariables rename)
          (renameAtomSuffix suffix atom))
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        AlphaProperListAgrees alpha
          (Terms.renameVariables rename terms)
          (renameAtomSuffix suffix atom))
  · intro name member
    simpa [Term.renameVariables, renameAtomSuffix_var,
      logicVarExecutableName] using
      (AlphaTermAgrees.variable
        (variableAgreement (.source name) member))
  · intro index member
    simpa [Term.renameVariables, renameAtomSuffix_var,
      logicVarExecutableName, generatedExecutableName,
      compilerGeneratedName] using
      (AlphaTermAgrees.variable
        (variableAgreement (.generated index) member))
  · intro name notTrue notFalse _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.atom (alpha := alpha) notTrue notFalse)
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.trueAtom (alpha := alpha))
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.falseAtom (alpha := alpha))
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.integer (alpha := alpha) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.float (alpha := alpha) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.string (alpha := alpha) value)
  · intro head terms encoded arguments inductionHypothesis support
    have termsSupport : termsVariablesIn domain terms := by
      simpa [termVariablesIn, termsVariablesIn] using support
    simpa [Term.renameVariables, Terms.renameVariables, partialC,
      partialTagA, renameAtomSuffix_expr, renameAtomSuffix_chainOf,
      renameAtomSuffix_sym, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.partialValue
        (inductionHypothesis termsSupport))
  · intro items encoded elements inductionHypothesis support
    have itemsSupport : termsVariablesIn domain items := by
      simpa [termVariablesIn] using support
    simpa [Term.renameVariables] using
      (AlphaTermAgrees.properList (inductionHypothesis itemsSupport))
  · intro _supported
    simpa [Terms.renameVariables, nilA, renameAtomSuffix_gnd] using
      (AlphaProperListAgrees.nil (alpha := alpha))
  · intro term atom terms tail head rest headInduction tailInduction support
    simpa [Terms.renameVariables, consC, renameAtomSuffix_expr,
      renameAtomSuffix_sym] using
      (AlphaProperListAgrees.cons
        (headInduction support.1) (tailInduction support.2))
  · exact agreement
  · exact supported

/-- Runtime-alpha agreement is stable under an arbitrary independent
renaming and the executable's common-suffix renaming when every occurring
old link is transported into the new graph.  Because the recursion follows
the term structure, repeated occurrences retain sharing and distinct
variables cannot be collapsed by the finite alpha. -/
theorem alphaTermAgrees_alpha_rename
    {rename : LogicVar → LogicVar} {suffix : String}
    {domain : List LogicVar}
    {before after : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity name,
        (identity, name) ∈ before →
        identity ∈ domain →
        (rename identity, name ++ suffix) ∈ after)
    {term : Term} {atom : Atom}
    (agreement : AlphaTermAgrees before term atom)
    (supported : termVariablesIn domain term) :
    AlphaTermAgrees after
      (term.renameVariables rename)
      (renameAtomSuffix suffix atom) := by
  apply AlphaTermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        AlphaTermAgrees after
          (term.renameVariables rename)
          (renameAtomSuffix suffix atom))
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        AlphaProperListAgrees after
          (Terms.renameVariables rename terms)
          (renameAtomSuffix suffix atom))
  · intro identity name linked member
    simpa [Term.renameVariables, renameAtomSuffix_var] using
      (AlphaTermAgrees.variable
        (variableAgreement identity name linked member))
  · intro name notTrue notFalse _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.atom (alpha := after) notTrue notFalse)
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.trueAtom (alpha := after))
  · intro _supported
    simpa [Term.renameVariables, renameAtomSuffix_sym] using
      (AlphaTermAgrees.falseAtom (alpha := after))
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.integer (alpha := after) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.float (alpha := after) value)
  · intro value _supported
    simpa [Term.renameVariables, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.string (alpha := after) value)
  · intro head terms encoded arguments inductionHypothesis support
    have termsSupport : termsVariablesIn domain terms := by
      simpa [termVariablesIn, termsVariablesIn] using support
    simpa [Term.renameVariables, Terms.renameVariables, partialC,
      partialTagA, renameAtomSuffix_expr, renameAtomSuffix_chainOf,
      renameAtomSuffix_sym, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.partialValue
        (inductionHypothesis termsSupport))
  · intro items encoded elements inductionHypothesis support
    have itemsSupport : termsVariablesIn domain items := by
      simpa [termVariablesIn] using support
    simpa [Term.renameVariables] using
      (AlphaTermAgrees.properList (inductionHypothesis itemsSupport))
  · intro _supported
    simpa [Terms.renameVariables, nilA, renameAtomSuffix_gnd] using
      (AlphaProperListAgrees.nil (alpha := after))
  · intro term atom terms tail head rest headInduction tailInduction support
    simpa [Terms.renameVariables, consC, renameAtomSuffix_expr,
      renameAtomSuffix_sym] using
      (AlphaProperListAgrees.cons
        (headInduction support.1) (tailInduction support.2))
  · exact agreement
  · exact supported

/-- Compiler-time exact agreement embeds into structural alpha agreement
whenever the supplied graph contains the canonical executable spelling of
every occurring independent variable. -/
theorem termAgrees_alpha
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        (identity, logicVarExecutableName identity) ∈ alpha)
    {term : Term} {atom : Atom} (agreement : TermAgrees term atom)
    (supported : termVariablesIn domain term) :
    AlphaTermAgrees alpha term atom := by
  apply TermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        AlphaTermAgrees alpha term atom)
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        AlphaProperListAgrees alpha terms atom)
  · intro name member
    exact
      AlphaTermAgrees.variable
        (variableAgreement (.source name) member)
  · intro index member
    exact
      AlphaTermAgrees.variable
        (variableAgreement (.generated index) member)
  · intro name notTrue notFalse _supported
    exact AlphaTermAgrees.atom notTrue notFalse
  · intro _supported
    exact .trueAtom
  · intro _supported
    exact .falseAtom
  · intro value _supported
    exact .integer value
  · intro value _supported
    exact .float value
  · intro value _supported
    exact .string value
  · intro head terms encoded arguments inductionHypothesis support
    exact .partialValue
      (inductionHypothesis (by
        simpa [termVariablesIn, termsVariablesIn] using support))
  · intro items encoded elements inductionHypothesis support
    exact .properList
      (inductionHypothesis (by
        simpa [termVariablesIn] using support))
  · intro _supported
    exact .nil
  · intro term atom terms tail head rest headInduction tailInduction support
    exact .cons (headInduction support.1) (tailInduction support.2)
  · exact agreement
  · exact supported

/-- The actual independent term copier and one executable suffix copy are
structurally alpha-related through the complete source support. -/
theorem copyTerm_renameAtomSuffix_alpha
    {source : Term} {raw : Atom} (agreement : TermAgrees source raw)
    (firstFresh : Nat) (suffix : String) :
    AlphaTermAgrees (termCopyAlphaGraph firstFresh suffix source)
      (copyTerm firstFresh source) (renameAtomSuffix suffix raw) := by
  unfold copyTerm
  apply termAgrees_alpha_rename
    (domain := copyVariables source)
    (alpha := termCopyAlphaGraph firstFresh suffix source)
  · intro identity member
    exact termCopyAlphaGraph_member firstFresh suffix source identity
      (List.mem_eraseDups.mp member)
  · exact agreement
  · exact termVariablesIn_of_occurrences (copyVariables source) source
      (fun _ member => List.mem_eraseDups.mpr member)

/-- Cross-runtime agreement for one copied Prolog value.  The supports are
explicit and form a finite bijection; the independent value is interpreted
through canonical Prolog denotation, so proper/dotted list presentation is
ignored while every rigid leaf tag and variable-sharing edge is retained. -/
def RuntimeTermAgrees (reference : Term) (executable : Atom) : Prop :=
  ∃ referenceSupport executableSupport,
    RuntimeAlpha referenceSupport executableSupport ∧
      CanonicalRuntimeAgrees
        (RuntimeAlpha.graph referenceSupport executableSupport)
        (Term.denote reference) executable

/-! ## Realizing one residual variant as a runtime alpha

The hidden cumulative representative used by executable substitution need
not spell its residual variables in the orientation chosen by the independent
ordered MGU.  Mutual finite instantiation proves that, on one observed value,
the two images differ by a genuine variable bijection.  The construction
below realizes that bijection with the runtime names already present in the
shared alpha graph. -/

/-- Select one runtime name only when coverage has already been proved.
The fallback is unreachable in every theorem below and prevents the choice
function from becoming a new premise or trusted classifier. -/
noncomputable def coveredRuntimeName
    (alpha : List (LogicVar × String)) (identity : LogicVar) : String := by
  classical
  exact
    if covered : AlphaCovers alpha identity then
      Classical.choose covered
    else
      ""

/-- The selected name is an actual member of the supplied alpha graph. -/
theorem coveredRuntimeName_linked
    {alpha : List (LogicVar × String)} {identity : LogicVar}
    (covered : AlphaCovers alpha identity) :
    (identity, coveredRuntimeName alpha identity) ∈ alpha := by
  simp only [coveredRuntimeName, dif_pos covered]
  exact Classical.choose_spec covered

/-- Choose the unique left identity paired with one right identity.  As with
`coveredRuntimeName`, the fallback never appears on a represented tree. -/
noncomputable def rightToLeftIdentity
    (pairs : List (LogicVar × LogicVar)) (rightIdentity : LogicVar) :
    LogicVar := by
  classical
  exact
    if linked : ∃ leftIdentity, (leftIdentity, rightIdentity) ∈ pairs then
      Classical.choose linked
    else
      rightIdentity

/-- Two-sided functionality makes the selected right-to-left map realize
every recorded pair exactly. -/
theorem rightToLeftIdentity_of_mem
    {pairs : List (LogicVar × LogicVar)}
    (shared : SharedTreeRenaming pairs)
    {leftIdentity rightIdentity : LogicVar}
    (member : (leftIdentity, rightIdentity) ∈ pairs) :
    rightToLeftIdentity pairs rightIdentity = leftIdentity := by
  have linked :
      ∃ candidateLeft, (candidateLeft, rightIdentity) ∈ pairs :=
    ⟨leftIdentity, member⟩
  rw [rightToLeftIdentity, dif_pos linked]
  exact shared.backward (Classical.choose_spec linked) member

/-- Minimal independent support for one observed residual-variant value. -/
def mutualInstanceReferenceSupport
    (pairs : List (LogicVar × LogicVar)) : List LogicVar :=
  pairs.eraseDups.map Prod.fst

/-- Runtime support selected pointwise from the representative side of the
same observed residual-variant value. -/
noncomputable def mutualInstanceExecutableSupport
    (alpha : List (LogicVar × String))
    (pairs : List (LogicVar × LogicVar)) : List String :=
  pairs.eraseDups.map fun pair => coveredRuntimeName alpha pair.2

/-- The induced runtime graph is exactly the duplicate-free occurrence graph
with its representative identities replaced by their existing runtime
names. -/
private theorem mutualInstance_graph_eq_map
    (alpha : List (LogicVar × String))
    (pairs : List (LogicVar × LogicVar)) :
    RuntimeAlpha.graph (mutualInstanceReferenceSupport pairs)
        (mutualInstanceExecutableSupport alpha pairs) =
      pairs.eraseDups.map fun pair =>
        (pair.1, coveredRuntimeName alpha pair.2) := by
  unfold mutualInstanceReferenceSupport mutualInstanceExecutableSupport
  unfold RuntimeAlpha.graph
  induction pairs.eraseDups with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.zip_cons_cons, inductionHypothesis]

/-- Every recorded occurrence pair enters the induced runtime graph at the
selected name of its representative identity. -/
theorem mutualInstance_graph_member
    {alpha : List (LogicVar × String)}
    {pairs : List (LogicVar × LogicVar)}
    {leftIdentity rightIdentity : LogicVar}
    (member : (leftIdentity, rightIdentity) ∈ pairs) :
    (leftIdentity, coveredRuntimeName alpha rightIdentity) ∈
      RuntimeAlpha.graph (mutualInstanceReferenceSupport pairs)
        (mutualInstanceExecutableSupport alpha pairs) := by
  rw [mutualInstance_graph_eq_map]
  exact List.mem_map.mpr
    ⟨(leftIdentity, rightIdentity),
      List.mem_eraseDups.mpr member, rfl⟩

/-- The occurrence-induced supports form a finite runtime bijection.  The
left projection is injective by residual-variant functionality; the runtime
projection is injective by representative functionality followed by the
shared alpha's inverse functionality. -/
theorem mutualInstance_runtimeAlpha
    {forward backward : TreeSubstitution}
    {pairs : List (LogicVar × LogicVar)} {left right : Tree}
    {alpha : List (LogicVar × String)} {executable : Atom}
    (witness :
      MutualInstanceRenaming forward backward pairs left right)
    (alphaShared : SharedRuntimeAlpha alpha)
    (runtime : CanonicalRuntimeAgrees alpha right executable) :
    RuntimeAlpha (mutualInstanceReferenceSupport pairs)
      (mutualInstanceExecutableSupport alpha pairs) := by
  have shared := witness.shared
  have rightSupported :=
    canonicalRuntimeAgrees_variablesSatisfy runtime
  have covered :
      ∀ {identity}, identity ∈ pairs.eraseDups.map Prod.snd →
        AlphaCovers alpha identity := by
    intro identity identityMember
    rcases List.mem_map.mp identityMember with
      ⟨⟨leftIdentity, rightIdentity⟩, pairMember, identityEq⟩
    simp only at identityEq
    subst rightIdentity
    exact witness.derivation.right_pair_satisfies rightSupported
      (List.mem_eraseDups.mp pairMember)
  constructor
  · simp [mutualInstanceReferenceSupport,
      mutualInstanceExecutableSupport]
  · exact shared.eraseDups_fst_nodup
  · unfold mutualInstanceExecutableSupport
    have selectedNamesNodup :=
      shared.eraseDups_snd_nodup.map_on
        (f := coveredRuntimeName alpha)
        (by
          intro first firstMember second secondMember sameName
          have firstLinked :=
            coveredRuntimeName_linked (covered firstMember)
          have secondLinked :=
            coveredRuntimeName_linked (covered secondMember)
          have secondLinkedAtFirstName :
              (second, coveredRuntimeName alpha first) ∈ alpha := by
            simpa only [sameName] using secondLinked
          exact alphaShared.backward firstLinked secondLinkedAtFirstName)
    change
      (pairs.eraseDups.map
        (coveredRuntimeName alpha ∘ Prod.snd)).Nodup
    rw [List.map_map] at selectedNamesNodup
    exact selectedNamesNodup

private theorem renameAtomSuffix_empty_local (atom : Atom) :
    renameAtomSuffix "" atom = atom := by
  induction atom using Metta.Atom.recAux with
  | sym name =>
      simp [renameAtomSuffix_sym]
  | var name =>
      simp [renameAtomSuffix_var]
  | gnd value =>
      simp [renameAtomSuffix_gnd]
  | expr atoms inductionHypothesis =>
      rw [renameAtomSuffix_expr]
      have mapped :
          atoms.map (renameAtomSuffix "") = atoms.map id :=
        List.map_congr_left fun child member =>
          inductionHypothesis child member
      rw [mapped, List.map_id]

/-- One structural mutual-instance witness transports a representative
canonical reading into a finite runtime-alpha reading of the other image. -/
theorem canonicalRuntimeAgrees_of_mutualInstanceRenaming
    {forward backward : TreeSubstitution}
    {pairs : List (LogicVar × LogicVar)} {left right : Tree}
    {alpha : List (LogicVar × String)} {executable : Atom}
    (witness :
      MutualInstanceRenaming forward backward pairs left right)
    (alphaShared : SharedRuntimeAlpha alpha)
    (runtime : CanonicalRuntimeAgrees alpha right executable) :
    CanonicalRuntimeAgrees
      (RuntimeAlpha.graph (mutualInstanceReferenceSupport pairs)
        (mutualInstanceExecutableSupport alpha pairs))
      left executable := by
  have shared := witness.shared
  have transported :=
    canonicalRuntimeAgrees_alpha_rename
      (rename := rightToLeftIdentity pairs)
      (suffix := "")
      (domain := pairs.eraseDups.map Prod.snd)
      (before := alpha)
      (after :=
        RuntimeAlpha.graph (mutualInstanceReferenceSupport pairs)
          (mutualInstanceExecutableSupport alpha pairs))
      (fun identity name linked identityMember => by
        rcases List.mem_map.mp identityMember with
          ⟨⟨leftIdentity, rightIdentity⟩, pairMember, identityEq⟩
        simp only at identityEq
        subst rightIdentity
        have originalMember := List.mem_eraseDups.mp pairMember
        have rightSupported :=
          canonicalRuntimeAgrees_variablesSatisfy runtime
        have covered : AlphaCovers alpha identity :=
          witness.derivation.right_pair_satisfies rightSupported
            originalMember
        have selectedLinked := coveredRuntimeName_linked covered
        have sameName := alphaShared.forward linked selectedLinked
        have selectedGraph :=
          mutualInstance_graph_member (alpha := alpha) originalMember
        have selectedLeft :=
          rightToLeftIdentity_of_mem shared originalMember
        simpa [selectedLeft, sameName] using selectedGraph)
      runtime witness.derivation.right_variables_in_unique_pairs
  rw [witness.derivation.left_eq_rename_right
    (rightToLeftIdentity pairs)
    (fun {_ _} member => rightToLeftIdentity_of_mem shared member)]
  simpa only [renameAtomSuffix_empty_local] using transported

/-- Residual substitution variants preserve the complete runtime meaning of
one observed finite source value, including rigid tags and variable sharing.
No MGU orientation, idempotence, or post-copy agreement is assumed. -/
theorem runtimeTermAgrees_of_variants
    {first second : TreeSubstitution} {tree : Tree}
    {source : Term} {alpha : List (LogicVar × String)} {executable : Atom}
    (sourceDenotes :
      Term.denote source = TreeSubstitution.apply first tree)
    (variants : TreeSubstitutionVariants first second)
    (alphaShared : SharedRuntimeAlpha alpha)
    (runtime :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply second tree) executable) :
    RuntimeTermAgrees source executable := by
  obtain ⟨forward, backward, pairs, witness⟩ :=
    PLeaTTa.PrologMguVariantRenaming.TreeSubstitutionVariants.apply_has_mutualInstanceRenaming
      variants tree
  refine
    ⟨mutualInstanceReferenceSupport pairs,
      mutualInstanceExecutableSupport alpha pairs,
      mutualInstance_runtimeAlpha witness alphaShared runtime, ?_⟩
  rw [sourceDenotes]
  exact canonicalRuntimeAgrees_of_mutualInstanceRenaming
    witness alphaShared runtime

/-- Canonical executable names for the complete finite support of one exact
compiler-time term. -/
def sourceEncodingExecutableSupport (source : Term) : List String :=
  (copyVariables source).map logicVarExecutableName

private theorem sourceEncoding_graph_eq_map (source : Term) :
    RuntimeAlpha.graph (copyVariables source)
        (sourceEncodingExecutableSupport source) =
      (copyVariables source).map fun identity =>
        (identity, logicVarExecutableName identity) := by
  unfold sourceEncodingExecutableSupport RuntimeAlpha.graph
  induction copyVariables source with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.zip_cons_cons, inductionHypothesis]

/-- The canonical source-name graph is a finite runtime alpha exactly under
the existing supported-source encoding-injectivity premise. -/
theorem sourceEncoding_runtimeAlpha (source : Term)
    (encoding : EncodingInjectiveOn (copyVariables source)) :
    RuntimeAlpha (copyVariables source)
      (sourceEncodingExecutableSupport source) := by
  constructor
  · simp [sourceEncodingExecutableSupport]
  · exact copyVariables_nodup source
  · unfold sourceEncodingExecutableSupport
    apply (copyVariables_nodup source).map_on
    intro left leftMember right rightMember same
    exact encoding leftMember rightMember same

private theorem sourceEncoding_graph_member
    (source : Term) {identity : LogicVar}
    (member : identity ∈ copyVariables source) :
    (identity, logicVarExecutableName identity) ∈
      RuntimeAlpha.graph (copyVariables source)
        (sourceEncodingExecutableSupport source) := by
  rw [sourceEncoding_graph_eq_map]
  exact List.mem_map.mpr ⟨identity, member, rfl⟩

/-- Exact compiler-time agreement embeds into runtime-alpha agreement.  This
compatibility theorem lets existing exact callers use the semantic copy
contract without duplicating the residual-variant proof. -/
theorem runtimeTermAgrees_of_termAgrees
    {source : Term} {raw : Atom}
    (agreement : TermAgrees source raw)
    (encoding : EncodingInjectiveOn (copyVariables source)) :
    RuntimeTermAgrees source raw := by
  refine
    ⟨copyVariables source, sourceEncodingExecutableSupport source,
      sourceEncoding_runtimeAlpha source encoding, ?_⟩
  exact AlphaTermAgrees.canonicalRuntimeAgrees
    (termAgrees_alpha
      (domain := copyVariables source)
      (alpha :=
        RuntimeAlpha.graph (copyVariables source)
          (sourceEncodingExecutableSupport source))
      (fun identity member => sourceEncoding_graph_member source member)
      agreement
      (termVariablesIn_of_occurrences (copyVariables source) source
        (fun _ member => List.mem_eraseDups.mpr member)))

/-- Restrict one runtime alpha graph to the independent variables that occur
in the value being copied.  Extra graph links remain useful to a surrounding
continuation but must not enter the copied value's fresh support. -/
def runtimeCopyActivePairs (source : Term)
    (referenceSupport : List LogicVar) (executableSupport : List String) :
    List (LogicVar × String) :=
  (RuntimeAlpha.graph referenceSupport executableSupport).filter fun pair =>
    (copyVariables source).contains pair.1

/-- Independent fresh targets induced by the active part of an existing
runtime alpha. -/
def runtimeCopyReferenceSupport (firstFresh : Nat) (source : Term)
    (referenceSupport : List LogicVar) (executableSupport : List String) :
    List LogicVar :=
  ((runtimeCopyActivePairs source referenceSupport executableSupport).map
    Prod.fst).map (copyRename firstFresh source)

/-- Executable fresh targets induced by the same active pairs and the one
suffix selected by the executable copier. -/
def runtimeCopyExecutableSupport (suffix : String) (source : Term)
    (referenceSupport : List LogicVar) (executableSupport : List String) :
    List String :=
  ((runtimeCopyActivePairs source referenceSupport executableSupport).map
    Prod.snd).map fun name => name ++ suffix

/-- The induced graph is exactly the pointwise transformation of the active
old graph. -/
private theorem runtimeCopy_graph_eq_map (firstFresh : Nat) (suffix : String)
    (source : Term) (referenceSupport : List LogicVar)
    (executableSupport : List String) :
    RuntimeAlpha.graph
        (runtimeCopyReferenceSupport firstFresh source
          referenceSupport executableSupport)
        (runtimeCopyExecutableSupport suffix source
          referenceSupport executableSupport) =
      (runtimeCopyActivePairs source referenceSupport executableSupport).map
        fun pair =>
          (copyRename firstFresh source pair.1, pair.2 ++ suffix) := by
  let active :=
    runtimeCopyActivePairs source referenceSupport executableSupport
  change
    ((active.map Prod.fst).map (copyRename firstFresh source)).zip
        ((active.map Prod.snd).map fun name => name ++ suffix) =
      active.map fun pair =>
        (copyRename firstFresh source pair.1, pair.2 ++ suffix)
  induction active with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.zip_cons_cons, inductionHypothesis]

private theorem runtimeAlpha_graph_fst_nodup
    {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport) :
    ((RuntimeAlpha.graph referenceSupport executableSupport).map
      Prod.fst).Nodup := by
  rw [agreement.graph_reference]
  exact agreement.referenceInjective

private theorem eq_of_project_eq_of_map_nodup
    {α β : Type} {project : α → β} :
    ∀ {values : List α} {left right : α},
      (values.map project).Nodup →
      left ∈ values →
      right ∈ values →
      project left = project right →
      left = right
  | [], _, _, _, leftMember, _, _ => by
      simp at leftMember
  | head :: tail, left, right, nodup, leftMember, rightMember, same => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exfalso
          exact nodup.1
            (List.mem_map.mpr ⟨right, rightMember, same.symm⟩)
      · rcases rightMember with rfl | rightMember
        · exfalso
          exact nodup.1
            (List.mem_map.mpr ⟨left, leftMember, same⟩)
        · exact
            eq_of_project_eq_of_map_nodup nodup.2
              leftMember rightMember same

/-- A finite runtime alpha graph is functional from independent identities to
executable names.  In particular, repeated source occurrences cannot be
related to two distinct runtime variables. -/
theorem runtimeAlpha_graph_left_unique
    {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport)
    {identity : LogicVar} {left right : String}
    (leftMember :
      (identity, left) ∈
        RuntimeAlpha.graph referenceSupport executableSupport)
    (rightMember :
      (identity, right) ∈
        RuntimeAlpha.graph referenceSupport executableSupport) :
    left = right := by
  have pairEq :
      (identity, left) = (identity, right) :=
    eq_of_project_eq_of_map_nodup
      (runtimeAlpha_graph_fst_nodup agreement)
      leftMember rightMember rfl
  exact congrArg Prod.snd pairEq

private theorem runtimeAlpha_graph_snd_nodup
    {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport) :
    ((RuntimeAlpha.graph referenceSupport executableSupport).map
      Prod.snd).Nodup := by
  rw [agreement.graph_executable]
  exact agreement.executableInjective

private theorem runtimeCopy_active_fst_nodup
    {source : Term} {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport) :
    ((runtimeCopyActivePairs source referenceSupport executableSupport).map
      Prod.fst).Nodup := by
  apply
    (List.filter_sublist
      (p := fun pair : LogicVar × String =>
        (copyVariables source).contains pair.1)
      (l := RuntimeAlpha.graph referenceSupport executableSupport)).map
      Prod.fst |>.nodup
  exact runtimeAlpha_graph_fst_nodup agreement

private theorem runtimeCopy_active_snd_nodup
    {source : Term} {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport) :
    ((runtimeCopyActivePairs source referenceSupport executableSupport).map
      Prod.snd).Nodup := by
  apply
    (List.filter_sublist
      (p := fun pair : LogicVar × String =>
        (copyVariables source).contains pair.1)
      (l := RuntimeAlpha.graph referenceSupport executableSupport)).map
      Prod.snd |>.nodup
  exact runtimeAlpha_graph_snd_nodup agreement

private theorem runtimeCopyActivePairs_fst_mem
    {source : Term} {referenceSupport : List LogicVar}
    {executableSupport : List String} {pair : LogicVar × String}
    (member :
      pair ∈
        runtimeCopyActivePairs source referenceSupport executableSupport) :
    pair.1 ∈ copyVariables source := by
  simpa [runtimeCopyActivePairs] using (List.mem_filter.mp member).2

/-- Restricting a finite runtime alpha to active source variables and applying
the two injective copier renamings yields another finite runtime alpha. -/
theorem runtimeCopy_runtimeAlpha
    {referenceSupport : List LogicVar}
    {executableSupport : List String}
    (agreement : RuntimeAlpha referenceSupport executableSupport)
    (firstFresh : Nat) (suffix : String) (source : Term) :
    RuntimeAlpha
      (runtimeCopyReferenceSupport firstFresh source
        referenceSupport executableSupport)
      (runtimeCopyExecutableSupport suffix source
        referenceSupport executableSupport) := by
  constructor
  · simp [runtimeCopyReferenceSupport, runtimeCopyExecutableSupport]
  · unfold runtimeCopyReferenceSupport
    apply (runtimeCopy_active_fst_nodup agreement).map_on
    intro left leftMember right rightMember same
    apply copyRename_injective_on firstFresh source
    · rcases List.mem_map.mp leftMember with
        ⟨leftPair, leftPairMember, rfl⟩
      exact runtimeCopyActivePairs_fst_mem leftPairMember
    · rcases List.mem_map.mp rightMember with
        ⟨rightPair, rightPairMember, rfl⟩
      exact runtimeCopyActivePairs_fst_mem rightPairMember
    · exact same
  · unfold runtimeCopyExecutableSupport
    exact
      (runtimeCopy_active_snd_nodup agreement).map
        (resolution_suffix_injective suffix)

/-- Every old alpha link used by the source survives in the induced copied
graph at the two concrete renamed targets. -/
theorem runtimeCopy_graph_member
    {referenceSupport : List LogicVar}
    {executableSupport : List String}
    {identity : LogicVar} {name : String}
    (linked :
      (identity, name) ∈
        RuntimeAlpha.graph referenceSupport executableSupport)
    (source : Term) (member : identity ∈ termVariables source)
    (firstFresh : Nat) (suffix : String) :
    (copyRename firstFresh source identity, name ++ suffix) ∈
      RuntimeAlpha.graph
        (runtimeCopyReferenceSupport firstFresh source
          referenceSupport executableSupport)
        (runtimeCopyExecutableSupport suffix source
          referenceSupport executableSupport) := by
  rw [runtimeCopy_graph_eq_map]
  apply List.mem_map.mpr
  refine ⟨(identity, name), ?_, rfl⟩
  have copyMember : identity ∈ copyVariables source :=
    List.mem_eraseDups.mpr member
  apply List.mem_filter.mpr
  exact ⟨linked, by simpa using copyMember⟩

/-- Copying both sides of one finite runtime-alpha-related value preserves
runtime agreement.  The old graph is restricted to variables occurring in
this value; the induced graph then pairs the independent copier's targets
with the executable copier's common-suffix targets. -/
theorem copyTerm_renameAtomSuffix_runtime_agrees
    {source : Term} {raw : Atom}
    (agreement : RuntimeTermAgrees source raw)
    (firstFresh : Nat) (suffix : String) :
    RuntimeTermAgrees (copyTerm firstFresh source)
      (renameAtomSuffix suffix raw) := by
  rcases agreement with
    ⟨referenceSupport, executableSupport, alpha, values⟩
  refine
    ⟨runtimeCopyReferenceSupport firstFresh source
        referenceSupport executableSupport,
      runtimeCopyExecutableSupport suffix source
        referenceSupport executableSupport,
      runtimeCopy_runtimeAlpha alpha firstFresh suffix source, ?_⟩
  rw [show
    Term.denote (copyTerm firstFresh source) =
      Tree.renameVariables (copyRename firstFresh source)
        (Term.denote source) by
      simp only [copyTerm, Term.denote_renameVariables]]
  apply canonicalRuntimeAgrees_alpha_rename
    (domain := copyVariables source)
    (before := RuntimeAlpha.graph referenceSupport executableSupport)
    (after :=
      RuntimeAlpha.graph
        (runtimeCopyReferenceSupport firstFresh source
          referenceSupport executableSupport)
        (runtimeCopyExecutableSupport suffix source
          referenceSupport executableSupport))
  · intro identity name linked member
    exact runtimeCopy_graph_member linked source
      (List.mem_eraseDups.mp member) firstFresh suffix
  · exact values
  · exact Term.denote_variablesSatisfy_of_occurrences source
      (fun _ member => List.mem_eraseDups.mpr member)

/-- Paying one copied value is valid from semantic runtime-alpha agreement,
not merely compiler-time exact spelling.  The counters remain independent:
the induced finite alpha absorbs both allocation offsets. -/
theorem copyTerm_copyFindallAtom_runtime_agrees_of_runtime
    {source : Term} {raw : Atom}
    (agreement : RuntimeTermAgrees source raw)
    (firstFresh counter : Nat) :
    RuntimeTermAgrees (copyTerm firstFresh source)
      (copyFindallAtom counter raw).value := by
  unfold copyFindallAtom
  split
  next closed =>
    let suffix := resolutionCompactSuffix counter
    have copied :=
      copyTerm_renameAtomSuffix_runtime_agrees
        agreement firstFresh suffix
    simpa [suffix,
      renameAtomSuffix_eq_self_of_resolutionAtomClosed suffix raw closed]
      using copied
  next _ =>
    exact
      copyTerm_renameAtomSuffix_runtime_agrees agreement firstFresh
        (resolutionCompactSuffix
          (advanceCounterPastAtoms counter [raw]))

/-- Paying one deferred entry at any later executable counter yields a
runtime-alpha-equivalent copied value.  The counter is universally
quantified: intervening executable allocations may change the chosen suffix
but cannot invalidate the debt. -/
theorem copyTerm_copyFindallAtom_runtime_agrees
    {source : Term} {raw : Atom} (agreement : TermAgrees source raw)
    (encoding : EncodingInjectiveOn (copyVariables source))
    (firstFresh counter : Nat) :
    RuntimeTermAgrees (copyTerm firstFresh source)
      (copyFindallAtom counter raw).value := by
  exact
    copyTerm_copyFindallAtom_runtime_agrees_of_runtime
      (runtimeTermAgrees_of_termAgrees agreement encoding)
      firstFresh counter

/-- Data and proof carried by one private independent copy paired with the raw
executable answer whose copy is still owed. -/
structure DeferredCopyWitness
    (referenceCopied : Term) (executableRaw : Atom) where
  source : Term
  firstFresh : Nat
  nextFresh : Nat
  sourceAgrees : RuntimeTermAgrees source executableRaw
  encoding : EncodingInjectiveOn (copyVariables source)
  copied :
    referenceCopied = copyTerm firstFresh source
  next :
    nextFresh = copyNextFresh firstFresh source

/-- One private independent copy paired with the raw executable answer whose
copy is still owed.  The reserved upper bound is below the current independent
frontier, while the executable counter is intentionally absent: payment is
valid at every later counter. -/
def DeferredCopyAgreesAt (referenceFrontier : Nat)
    (referenceCopied : Term) (executableRaw : Atom) : Prop :=
  ∃ witness : DeferredCopyWitness referenceCopied executableRaw,
    witness.nextFresh ≤ referenceFrontier

/-- A debt remains valid when the independent allocator advances. -/
theorem DeferredCopyAgreesAt.mono
    {before after : Nat} {referenceCopied : Term} {executableRaw : Atom}
    (agreement :
      DeferredCopyAgreesAt before referenceCopied executableRaw)
    (advance : before ≤ after) :
    DeferredCopyAgreesAt after referenceCopied executableRaw := by
  rcases agreement with ⟨witness, reserved⟩
  exact ⟨witness, Nat.le_trans reserved advance⟩

/-- One debt entry can be paid at any executable frontier. -/
theorem DeferredCopyAgreesAt.pay
    {referenceFrontier : Nat} {referenceCopied : Term}
    {executableRaw : Atom}
    (agreement :
      DeferredCopyAgreesAt referenceFrontier referenceCopied executableRaw)
    (counter : Nat) :
    RuntimeTermAgrees referenceCopied
      (copyFindallAtom counter executableRaw).value := by
  rcases agreement with ⟨witness, _reserved⟩
  rw [witness.copied]
  exact copyTerm_copyFindallAtom_runtime_agrees_of_runtime
    witness.sourceAgrees witness.firstFresh counter

/-- The real answer-time independent collector creates exactly one debt entry
against a related raw executable answer. -/
theorem collectTemplate_deferred
    (session : Session) (template : Term)
    (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      RuntimeTermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template))) :
    DeferredCopyAgreesAt
      (collectTemplate session template answerBindings).session.resolver.nextFresh
      (collectTemplate session template answerBindings).prepared.copied raw := by
  let collected := collectTemplate session template answerBindings
  refine ⟨
    { source := answerBindings.applyTerm template
      firstFresh := collected.prepared.firstFresh
      nextFresh := collected.prepared.nextFresh
      sourceAgrees := sourceAgrees
      encoding := encoding
      copied := ?_
      next := ?_ },
    Nat.le_refl _⟩
  · rfl
  · rfl

/-- Ordered reverse-discovery debt plus the honest allocator frontiers.  The
executable bound covers every still-raw answer variable; the independent
bound is carried per entry because its copied variables were allocated at
different answer times. -/
structure CollectionCopyFrontier
    (referenceFrontier executableFrontier : Nat)
    (referenceCopiedRev : List Term) (executableRawRev : List Atom) : Prop where
  debt :
    List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
      referenceCopiedRev executableRawRev
  executableBound :
    resolutionSeedHighWaterNames
      (executableRawRev.flatMap Atom.vars) ≤ executableFrontier

/-- Empty collectors relate at arbitrary, potentially unequal frontiers. -/
theorem CollectionCopyFrontier.empty
    (referenceFrontier executableFrontier : Nat) :
    CollectionCopyFrontier referenceFrontier executableFrontier [] [] := by
  exact ⟨.nil, by simp [resolutionSeedHighWaterNames]⟩

private theorem deferred_forall₂_mono
    {before after : Nat} (advance : before ≤ after) :
    ∀ {referenceCopied : List Term} {executableRaw : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt before)
          referenceCopied executableRaw →
        List.Forall₂ (DeferredCopyAgreesAt after)
          referenceCopied executableRaw
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (head.mono advance) (deferred_forall₂_mono advance tail)

/-- Advancing either allocator cannot invalidate an existing debt. -/
theorem CollectionCopyFrontier.advance
    {referenceBefore referenceAfter executableBefore executableAfter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceBefore executableBefore
        referenceCopiedRev executableRawRev)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    CollectionCopyFrontier referenceAfter executableAfter
      referenceCopiedRev executableRawRev := by
  constructor
  · exact deferred_forall₂_mono referenceMono agreement.debt
  · exact Nat.le_trans agreement.executableBound executableMono

/-- One answer-time independent copy extends the reverse-discovery debt,
while the executable lane keeps the corresponding materialized raw answer.
All older entries are lifted across the new independent high-water. -/
theorem CollectionCopyFrontier.collect
    {session : Session} {executableBefore executableAfter : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier session.resolver.nextFresh executableBefore
        referenceCopiedRev executableRawRev)
    (template : Term) (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      RuntimeTermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template)))
    (executableMono : executableBefore ≤ executableAfter)
    (rawBound :
      resolutionSeedHighWaterNames raw.vars ≤ executableAfter) :
    CollectionCopyFrontier
      (collectTemplate session template answerBindings).session.resolver.nextFresh
      executableAfter
      ((collectTemplate session template answerBindings).prepared.copied ::
        referenceCopiedRev)
      (raw :: executableRawRev) := by
  let collected := collectTemplate session template answerBindings
  have referenceMono :
      session.resolver.nextFresh ≤ collected.session.resolver.nextFresh :=
    collectTemplate_nextFresh_mono session template answerBindings
  constructor
  · exact .cons
      (collectTemplate_deferred session template answerBindings raw
        sourceAgrees encoding)
      (deferred_forall₂_mono referenceMono agreement.debt)
  · simpa only [List.flatMap_cons, resolutionSeedHighWaterNames_append,
      Nat.max_le] using
      And.intro rawBound
        (Nat.le_trans agreement.executableBound executableMono)

/-- The copy-debt frontier is a concrete, non-numeric instantiation of the
abstract persistent-state bridge. -/
def CopyDebtFrontier (referenceCopiedRev : List Term)
    (executableRawRev : List Atom) : FreshFrontierRelation :=
  fun referenceFrontier executableFrontier =>
    CollectionCopyFrontier referenceFrontier executableFrontier
      referenceCopiedRev executableRawRev

/-- Persistent database/world agreement equipped with the exact private
collector debt. -/
abbrev CollectionSessionRelates
    (referenceCopiedRev : List Term) (executableRawRev : List Atom)
    (session : Session) (persistent : DemandDrivenStep.Persistent) : Prop :=
  SessionRelatesPersistent
    (CopyDebtFrontier referenceCopiedRev executableRawRev)
    session persistent

/-- Pairing one real independent collection with one executable raw-answer
insertion preserves the full persistent bridge: database/world agreement is
unchanged, the independent allocator advances immediately, and the
executable allocator may advance independently while the new debt records
the pending copy. -/
theorem CollectionSessionRelates.collect
    {session : Session}
    {persistentBefore persistentAfter : DemandDrivenStep.Persistent}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionSessionRelates referenceCopiedRev executableRawRev
        session persistentBefore)
    (template : Term) (answerBindings : Substitution) (raw : Atom)
    (sourceAgrees :
      RuntimeTermAgrees (answerBindings.applyTerm template) raw)
    (encoding :
      EncodingInjectiveOn
        (copyVariables (answerBindings.applyTerm template)))
    (world : persistentAfter.world = persistentBefore.world)
    (counterMono : persistentBefore.counter ≤ persistentAfter.counter)
    (rawBound :
      resolutionSeedHighWaterNames raw.vars ≤ persistentAfter.counter) :
    CollectionSessionRelates
      ((collectTemplate session template answerBindings).prepared.copied ::
        referenceCopiedRev)
      (raw :: executableRawRev)
      (collectTemplate session template answerBindings).session
      persistentAfter := by
  constructor
  · rw [collectTemplate_database]
    simpa [world] using agreement.database
  · exact agreement.fresh.collect template answerBindings raw
      sourceAgrees encoding counterMono rawBound

private theorem deferred_forall₂_pay
    {referenceFrontier : Nat} :
    ∀ {referenceCopied : List Term} {executableRaw : List Atom},
      List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
          referenceCopied executableRaw →
        ∀ counter,
          List.Forall₂ RuntimeTermAgrees referenceCopied
            (copyFindallBag counter executableRaw).values
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, counter => by
      simp only [copyFindallBag]
      exact .cons (head.pay counter)
        (deferred_forall₂_pay tail
          (copyFindallAtom counter _).counter)

/-- A list-level copy debt can be paid after arbitrary intervening allocation:
the resulting executable bag agrees position-for-position with the independent
bag in source discovery order. -/
theorem CollectionCopyFrontier.pay
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    List.Forall₂ RuntimeTermAgrees referenceCopiedRev.reverse
      (copyFindallBag counter executableRawRev.reverse).values := by
  exact deferred_forall₂_pay (List.rel_reverse agreement.debt) counter

/-! ## Step-for-step debt payment

The relation below exposes the copy phase's intermediate prefixes.  Its
outstanding side is in source order; its paid side is reverse source order,
matching `BagCopyState.copiedRev`. -/

/-- Exact correspondence between outstanding/paid independent values and one
bounded executable copy state. -/
structure CopyPaymentAgrees (referenceFrontier : Nat)
    (referenceRemaining : List Term) (referencePaidRev : List Term)
    (phase : FindallCopy.BagCopyState) : Prop where
  outstanding :
    List.Forall₂ (DeferredCopyAgreesAt referenceFrontier)
      referenceRemaining phase.remaining
  paid :
    List.Forall₂ RuntimeTermAgrees referencePaidRev phase.copiedRev

/-- A reverse-discovery debt initializes the executable phase with every
entry outstanding and none paid. -/
theorem CollectionCopyFrontier.payment_initial
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    CopyPaymentAgrees referenceFrontier referenceCopiedRev.reverse []
      (FindallCopy.BagCopyState.initial counter executableRawRev.reverse) := by
  exact ⟨List.rel_reverse agreement.debt, .nil⟩

/-- The exact terminal state of the bounded executable payment phase.  Naming
this state prevents later composition proofs from maintaining a second,
independently reconstructed account of the copied bag or returned counter. -/
def paidCollectionCopyState (counter : Nat)
    (executableRawRev : List Atom) : FindallCopy.BagCopyState :=
  { remaining := []
    copiedRev :=
      (copyFindallBag counter executableRawRev.reverse).values.reverse
    counter :=
      (copyFindallBag counter executableRawRev.reverse).counter }

/-- The complete bounded phase reaches the literal macro-copy endpoint and
pays every debt there.  This strengthens the existential wrapper below: the
same `copyFindallBag` fold supplies both the microstep endpoint and all later
exit-counter/bag equations. -/
theorem CollectionCopyFrontier.payment_exact_target
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    FindallCopy.BagCopyStepsN executableRawRev.length
        (FindallCopy.BagCopyState.initial counter executableRawRev.reverse)
        (paidCollectionCopyState counter executableRawRev) ∧
      CopyPaymentAgrees referenceFrontier [] referenceCopiedRev
        (paidCollectionCopyState counter executableRawRev) := by
  constructor
  · simpa [paidCollectionCopyState] using
      (FindallCopy.BagCopyStepsN.run_initial
        counter executableRawRev.reverse)
  · have paidDiscovery := agreement.pay counter
    have paidReverse := List.rel_reverse paidDiscovery
    exact
      ⟨.nil, by
        simpa [paidCollectionCopyState] using paidReverse⟩

/-- The complete bounded phase pays every debt entry in exactly one
microstep, ends with no outstanding reference value, and leaves the private
reverse accumulators pointwise alpha-related. -/
theorem CollectionCopyFrontier.payment_exact
    {referenceFrontier executableFrontier : Nat}
    {referenceCopiedRev : List Term} {executableRawRev : List Atom}
    (agreement :
      CollectionCopyFrontier referenceFrontier executableFrontier
        referenceCopiedRev executableRawRev)
    (counter : Nat) :
    ∃ final,
      FindallCopy.BagCopyStepsN executableRawRev.length
        (FindallCopy.BagCopyState.initial counter executableRawRev.reverse)
        final ∧
      CopyPaymentAgrees referenceFrontier [] referenceCopiedRev final := by
  exact
    ⟨paidCollectionCopyState counter executableRawRev,
      (agreement.payment_exact_target counter).1,
      (agreement.payment_exact_target counter).2⟩

/-- One certified executable microstep pays exactly the head debt entry and
prepends exactly one alpha-related copied value. -/
theorem CopyPaymentAgrees.next
    {referenceFrontier : Nat} {reference : Term}
    {referenceRemaining referencePaidRev : List Term}
    {before after : FindallCopy.BagCopyState}
    (agreement :
      CopyPaymentAgrees referenceFrontier
        (reference :: referenceRemaining) referencePaidRev before)
    (step : FindallCopy.BagCopyStep before after) :
    CopyPaymentAgrees referenceFrontier referenceRemaining
      (reference :: referencePaidRev) after := by
  cases step with
  | next counter source remaining copiedRev =>
      cases agreement.outstanding with
      | cons head tail =>
          exact ⟨tail, .cons (head.pay counter) agreement.paid⟩

/-- Paying a debt is genuinely compatible with unequal allocation currencies:
one independent copied variable reserved at index ten relates to an
executable copy whose suffix allocation starts at zero. -/
theorem witness_copy_debt_frontiers_need_not_equal :
    ∃ referenceCopied raw,
      CollectionCopyFrontier 11 0 [referenceCopied] [raw] ∧
        (11 : Nat) ≠ 0 := by
  let source : Term := .variable (.source "x")
  let raw : Atom := .var "x"
  let referenceCopied := copyTerm 10 source
  have encoding : EncodingInjectiveOn (copyVariables source) := by
    intro left right leftMember rightMember same
    simp [source, copyVariables, termVariables] at leftMember rightMember
    simp [leftMember, rightMember]
  have deferred :
      DeferredCopyAgreesAt 11 referenceCopied raw := by
    refine ⟨
      { source := source
        firstFresh := 10
        nextFresh := 11
        sourceAgrees := ?_
        encoding := encoding
        copied := rfl
        next := ?_ },
      Nat.le_refl 11⟩
    · exact runtimeTermAgrees_of_termAgrees
        (TermAgrees.sourceVariable "x") encoding
    · change 11 =
        copyNextFresh 10 (.variable (.source "x"))
      decide
  refine ⟨referenceCopied, raw, ?_, by omega⟩
  constructor
  · exact .cons deferred .nil
  · dsimp [raw]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [Atom.vars, resolutionSeedHighWaterNames,
      resolutionSeedHighWaterName, terminalResolutionSeed?,
      terminalResolutionSeedRev]

end PLeaTTa.PrologFindallCopyBridge
