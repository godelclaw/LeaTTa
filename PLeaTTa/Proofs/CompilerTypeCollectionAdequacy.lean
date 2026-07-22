-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerTypeCollectionAdequacy
Purpose: Adequacy of pinned type-declaration collection and strict
  first-occurrence duplicate removal.
Trusted boundary: none
Main exports: collectTypeChains_sound, collectTypeChains_complete
-/
import PLeaTTa.Compile
import PLeaTTa.PeTTaSpec.PrologCore

namespace PLeaTTa.CompilerTypeCollectionAdequacy

open Metta (Atom)
open PLeaTTa.PeTTaSpec.PrologCore

/-- The executable declaration recognizer decides the independent matching
shape exactly. -/
theorem declaredTypeChain?_eq_some_iff {head : String}
    {declaration : Atom × Atom} {chain : List Atom} :
    declaredTypeChain? head declaration = some chain ↔
      DeclaresTypeChain head declaration chain := by
  constructor
  · intro recognized
    rcases declaration with ⟨subject, declaredType⟩
    simp only [declaredTypeChain?] at recognized
    split at recognized
    next equal =>
      cases subject with
      | sym name =>
          change (name == head) = true at equal
          have nameEq : name = head := beq_iff_eq.mp equal
          subst name
          cases declaredType with
          | sym _ => contradiction
          | var _ => contradiction
          | gnd _ => contradiction
          | expr items =>
              cases items with
              | nil => contradiction
              | cons first rest =>
                  cases first with
                  | sym arrow =>
                      by_cases arrowEq : arrow = "->"
                      · subst arrow
                        cases recognized
                        exact .arrow _
                      · simp [arrowEq] at recognized
                  | var _ => contradiction
                  | gnd _ => contradiction
                  | expr _ => contradiction
      | var _ =>
          change false = true at equal
          contradiction
      | gnd _ =>
          change false = true at equal
          contradiction
      | expr _ =>
          change false = true at equal
          contradiction
    next => contradiction
  · intro declares
    cases declares
    change (if head == head then some chain else none) = some chain
    simp

/-- The executable raw traversal is sound for ordered `findall/3`
collection. -/
theorem collectRawTypeChains_sound (declarations : List (Atom × Atom))
    (head : String) :
    CollectsRawTypeChains head declarations
      (collectRawTypeChains declarations head) := by
  induction declarations with
  | nil => exact .nil
  | cons declaration declarations inductionHypothesis =>
      simp only [collectRawTypeChains, List.filterMap_cons]
      cases recognized : declaredTypeChain? head declaration with
      | none =>
          apply CollectsRawTypeChains.skip
          · rintro ⟨chain, matchProof⟩
            have := (declaredTypeChain?_eq_some_iff).mpr matchProof
            rw [recognized] at this
            contradiction
          · simpa only [collectRawTypeChains] using inductionHypothesis
      | some chain =>
          exact CollectsRawTypeChains.keep
            ((declaredTypeChain?_eq_some_iff).mp recognized)
            (by simpa only [collectRawTypeChains] using inductionHypothesis)

/-- The ordered raw collection judgment determines the executable traversal. -/
theorem collectRawTypeChains_complete {declarations : List (Atom × Atom)}
    {head : String} {chains : List (List Atom)}
    (collection : CollectsRawTypeChains head declarations chains) :
    collectRawTypeChains declarations head = chains := by
  induction collection with
  | nil => rfl
  | keep matchProof _ inductionHypothesis =>
      simp only [collectRawTypeChains] at inductionHypothesis ⊢
      rw [List.filterMap_cons,
        (declaredTypeChain?_eq_some_iff).mpr matchProof,
        inductionHypothesis]
  | skip doesNotMatch tail inductionHypothesis =>
      rename_i skippedDeclaration tailDeclarations tailChains
      have absent : declaredTypeChain? head skippedDeclaration = none := by
        cases recognized : declaredTypeChain? head skippedDeclaration with
        | none => rfl
        | some chain =>
            exact False.elim
              (doesNotMatch ⟨chain,
                (declaredTypeChain?_eq_some_iff).mp recognized⟩)
      simp only [collectRawTypeChains] at inductionHypothesis ⊢
      rw [List.filterMap_cons, absent, inductionHypothesis]

/-- Boolean variable absence decides the independent closed-chain predicate. -/
theorem typeChainClosed_iff (chain : List Atom) :
    (chain.flatMap Atom.vars).isEmpty = true ↔ ClosedTypeChain chain := by
  simp [ClosedTypeChain]

/-- The executable comparison decides strict identity of separately copied
type-chain answers. -/
theorem sameCollectedTypeChain_eq_true_iff (left right : List Atom) :
    sameCollectedTypeChain left right = true ↔
      CopiedTypeChainsIdentical left right := by
  constructor
  · intro same
    simp only [sameCollectedTypeChain, Bool.and_eq_true] at same
    exact .closed ((typeChainClosed_iff left).mp same.1.1)
      ((typeChainClosed_iff right).mp same.1.2) same.2
  · intro same
    cases same with
    | closed leftClosed rightClosed sameSyntax =>
        simp [sameCollectedTypeChain,
          (typeChainClosed_iff left).mpr leftClosed,
          (typeChainClosed_iff right).mpr rightClosed, sameSyntax]

/-- Filtering later candidates by the executable strict-identity decision is
sound for the independent removal judgment. -/
theorem removeCopiedTypeChainDuplicates_sound (first : List Atom) :
    ∀ input : List (List Atom),
      RemovesCopiedTypeChainDuplicates first input
        (input.filter fun candidate =>
          decide (sameCollectedTypeChain candidate first = false))
  | [] => .nil
  | candidate :: input => by
      cases same : sameCollectedTypeChain candidate first with
      | false =>
          simpa [List.filter_cons, same] using
            (RemovesCopiedTypeChainDuplicates.keep
              (fun identical => by
                have := (sameCollectedTypeChain_eq_true_iff candidate first).mpr
                  identical
                simp [same] at this)
              (removeCopiedTypeChainDuplicates_sound first input))
      | true =>
          simpa [List.filter_cons, same] using
            (RemovesCopiedTypeChainDuplicates.drop
              ((sameCollectedTypeChain_eq_true_iff candidate first).mp same)
              (removeCopiedTypeChainDuplicates_sound first input))

/-- The independent removal judgment uniquely determines executable
filtering. -/
theorem removeCopiedTypeChainDuplicates_complete {first : List Atom}
    {input output : List (List Atom)}
    (removal : RemovesCopiedTypeChainDuplicates first input output) :
    input.filter (fun candidate =>
      decide (sameCollectedTypeChain candidate first = false)) = output := by
  induction removal with
  | nil => rfl
  | drop same tail inductionHypothesis =>
      rename_i removedCandidate tailInput tailOutput
      have decision :=
        (sameCollectedTypeChain_eq_true_iff removedCandidate first).mpr same
      simp only [List.filter_cons]
      rw [decision]
      simpa using inductionHypothesis
  | keep different tail inductionHypothesis =>
      rename_i retainedCandidate tailInput tailOutput
      have decision : sameCollectedTypeChain retainedCandidate first = false := by
        cases same : sameCollectedTypeChain retainedCandidate first with
        | false => rfl
        | true =>
            exact False.elim
              (different ((sameCollectedTypeChain_eq_true_iff _ _).mp same))
      simp only [List.filter_cons]
      rw [decision]
      simpa using inductionHypothesis

/-- Executable first-occurrence removal is sound for pinned strict duplicate
removal. -/
theorem eraseDupsTypeChains_sound : ∀ raw : List (List Atom),
    DedupsTypeChains raw (raw.eraseDupsBy sameCollectedTypeChain)
  | [] => .nil
  | first :: input => by
      rw [List.eraseDupsBy_cons]
      exact .cons (removeCopiedTypeChainDuplicates_sound first input)
        (eraseDupsTypeChains_sound
          (input.filter fun candidate =>
            decide (sameCollectedTypeChain candidate first = false)))
termination_by raw => raw.length
decreasing_by
  simpa [Nat.succ_eq_add_one] using
    Nat.lt_succ_of_le (List.length_filter_le
      (fun candidate =>
        decide (sameCollectedTypeChain candidate first = false)) input)

/-- The independent strict-duplicate judgment uniquely determines executable
first-occurrence removal. -/
theorem eraseDupsTypeChains_complete {raw unique : List (List Atom)}
    (deduplication : DedupsTypeChains raw unique) :
    raw.eraseDupsBy sameCollectedTypeChain = unique := by
  induction deduplication with
  | nil => rfl
  | cons removes _ inductionHypothesis =>
      rw [List.eraseDupsBy_cons]
      rw [removeCopiedTypeChainDuplicates_complete removes]
      rw [inductionHypothesis]

/-- Executable collection is sound for independent pinned `findall/3` plus
`list_to_set/2` semantics. -/
theorem collectTypeChains_sound {declarations : List (Atom × Atom)}
    {head : String} {chains : List (List Atom)}
    (collected : collectTypeChains declarations head = chains) :
    CollectsTypeChains declarations head chains := by
  subst chains
  exact ⟨collectRawTypeChains declarations head,
    collectRawTypeChains_sound declarations head,
    eraseDupsTypeChains_sound _⟩

/-- Independent pinned collection completely determines the executable
result. -/
theorem collectTypeChains_complete {declarations : List (Atom × Atom)}
    {head : String} {chains : List (List Atom)}
    (collection : CollectsTypeChains declarations head chains) :
    collectTypeChains declarations head = chains := by
  rcases collection with ⟨raw, collected, deduplicated⟩
  simp only [collectTypeChains]
  rw [collectRawTypeChains_complete collected]
  exact eraseDupsTypeChains_complete deduplicated

/-- Identical closed declarations collapse to their first occurrence. -/
example :
    collectTypeChains
      [(.sym "f", .expr [.sym "->", .sym "Number", .sym "Number"]),
       (.sym "f", .expr [.sym "->", .sym "Number", .sym "Number"])]
      "f" = [[.sym "Number", .sym "Number"]] := by
  let closed : List Atom := [.sym "Number", .sym "Number"]
  have recognized : declaredTypeChain? "f"
      (.sym "f", .expr (.sym "->" :: closed)) = some closed := by rfl
  have duplicate : sameCollectedTypeChain closed closed = true := by
    simp only [closed, sameCollectedTypeChain, Atom.vars,
      List.flatMap_cons, List.flatMap_nil, List.nil_append,
      List.isEmpty_nil, Bool.true_and]
    change Atom.beqList [.sym "Number", .sym "Number"]
      [.sym "Number", .sym "Number"] = true
    rfl
  have filtered : List.filter
      (fun candidate =>
        decide (sameCollectedTypeChain candidate closed = false))
      [closed] = [] := by
    simp [duplicate]
  change collectTypeChains
      [(.sym "f", .expr (.sym "->" :: closed)),
       (.sym "f", .expr (.sym "->" :: closed))] "f" = [closed]
  simp only [collectTypeChains, collectRawTypeChains, List.filterMap_cons,
    List.filterMap_nil, recognized, List.eraseDupsBy_cons, filtered]
  rfl

/-- Identical source spelling does not collapse declaration-local variables. -/
example :
    collectTypeChains
      [(.sym "f", .expr [.sym "->", .var "a", .var "a"]),
       (.sym "f", .expr [.sym "->", .var "a", .var "a"])]
      "f" =
        [[.var "a", .var "a"], [.var "a", .var "a"]] := by
  let openChain : List Atom := [.var "a", .var "a"]
  have recognized : declaredTypeChain? "f"
      (.sym "f", .expr (.sym "->" :: openChain)) = some openChain := by rfl
  have distinct : sameCollectedTypeChain openChain openChain = false := by
    simp only [openChain, sameCollectedTypeChain, Atom.vars,
      List.flatMap_cons, List.flatMap_nil]
    rfl
  have filtered : List.filter
      (fun candidate =>
        decide (sameCollectedTypeChain candidate openChain = false))
      [openChain] = [openChain] := by
    simp [distinct]
  change collectTypeChains
      [(.sym "f", .expr (.sym "->" :: openChain)),
       (.sym "f", .expr (.sym "->" :: openChain))] "f" =
        [openChain, openChain]
  simp only [collectTypeChains, collectRawTypeChains, List.filterMap_cons,
    List.filterMap_nil, recognized, List.eraseDupsBy_cons, filtered]
  rfl

end PLeaTTa.CompilerTypeCollectionAdequacy
