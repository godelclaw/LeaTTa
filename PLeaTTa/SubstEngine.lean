import PLeaTTa.PersistentSubst

namespace PLeaTTa

open Metta (Atom Subst)

/-- A prepared atom whose cached metadata is intrinsically certified. -/
abbrev CertifiedPreparedAtom :=
  { prepared : PersistentSubst.PreparedAtom // prepared.Valid }

/-- Groundness read from certified cached variable metadata. -/
def certifiedPreparedGround (prepared : CertifiedPreparedAtom) : Bool :=
  prepared.1.variables.isEmpty

theorem certifiedPreparedGround_eq (prepared : CertifiedPreparedAtom) :
    certifiedPreparedGround prepared = Metta.isGround prepared.1.atom := by
  unfold certifiedPreparedGround Metta.isGround Metta.freeVars
  rw [prepared.2.variables_eq]
  cases prepared.1.atom.vars <;> rfl

/-- Batch groundness without rescanning the erased atom trees. -/
def preparedAtomsAllGround (atoms : List CertifiedPreparedAtom) : Bool :=
  atoms.all certifiedPreparedGround

theorem preparedAtomsAllGround_eq
    (atoms : List CertifiedPreparedAtom) :
    preparedAtomsAllGround atoms =
      atoms.all (fun prepared => Metta.isGround prepared.1.atom) := by
  induction atoms with
  | nil => rfl
  | cons head rest _ =>
      simp [preparedAtomsAllGround, certifiedPreparedGround_eq]

theorem preparedAtomsAllGround_map (atoms : List CertifiedPreparedAtom) :
    preparedAtomsAllGround atoms =
      (atoms.map (fun prepared => prepared.1.atom)).all Metta.isGround := by
  rw [preparedAtomsAllGround_eq]
  induction atoms with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.all_cons, List.map_cons]
      rw [ih]

theorem certifiedAtoms_eq (atoms : List CertifiedPreparedAtom) :
    atoms.unattach.map PersistentSubst.PreparedAtom.atom =
      atoms.map (fun prepared => prepared.1.atom) := by
  simp [List.unattach, -List.map_subtype, List.map_map,
    Function.comp_def]

/-- Advance the resolution-name counter from a certified prepared singleton
without rescanning its atom tree.  Structural identity is checked before the
cache is used; every other shape takes the ordinary exact path. -/
def advanceCounterPastPreparedResult (counter : Nat)
    (prepared : Option CertifiedPreparedAtom) (results : List Atom) : Nat :=
  match prepared, results with
  | some cached, [atom] =>
      if cached.1.sameAtom atom then
        max counter (resolutionSeedHighWaterNames cached.1.variables)
      else
        advanceCounterPastAtoms counter results
  | _, _ => advanceCounterPastAtoms counter results

@[simp] theorem advanceCounterPastPreparedResult_eq (counter : Nat)
    (prepared : Option CertifiedPreparedAtom) (results : List Atom) :
    advanceCounterPastPreparedResult counter prepared results =
      advanceCounterPastAtoms counter results := by
  cases prepared with
  | none => rfl
  | some cached =>
      cases results with
      | nil => rfl
      | cons atom rest =>
          cases rest with
          | cons next tail => rfl
          | nil =>
              unfold advanceCounterPastPreparedResult
              by_cases equal : cached.1.sameAtom atom = true
              · simp only [equal, if_true]
                have atomEq :=
                  PersistentSubst.PreparedAtom.sameAtom_eq_true equal
                subst atom
                rw [cached.2.variables_eq]
                simp [advanceCounterPastAtoms, resolutionSeedHighWaterAtoms,
                  resolutionSeedHighWaterAtom]
              · simp [equal]

@[simp] theorem advanceCounterPastPreparedResult_fun (counter : Nat)
    (prepared : Option CertifiedPreparedAtom) :
    advanceCounterPastPreparedResult counter prepared =
      advanceCounterPastAtoms counter := by
  funext results
  exact advanceCounterPastPreparedResult_eq counter prepared results

/-- The substitution operations used by the operational machine, together
with the denotational laws needed to instantiate the same machine over a
reference list or a persistent executable state. Reads are state-threaded so
the executable instance can retain path-local cache refreshes. -/
structure SubstEngine where
  State : Type
  empty : State
  ofDenote : Subst → State
  denote : State → Subst
  Valid : State → Prop
  subst : State → Atom → Atom × State
  substMany : State → List Atom → List Atom × State
  /-- Batch substitution that retains proof-carrying prepared roots. -/
  substManyCertified : State → List Atom →
    List CertifiedPreparedAtom × State
  substPrepared : State → Atom → PersistentSubst.PreparedAtom × State
  /-- Retain a prepared value for the immediately following operation. -/
  rememberRecent : State → (prepared : PersistentSubst.PreparedAtom) →
    prepared.Valid → State
  /-- Retain a valid prepared value as representation-only metadata. -/
  rememberPrepared : State → (prepared : PersistentSubst.PreparedAtom) →
    prepared.Valid → State
  /-- Prepared substitution used at persistent-world insertion boundaries.
  Checked engines retain the certified result for later indexed matching. -/
  substPreparedRemembered : State → Atom →
    PersistentSubst.PreparedAtom × State
  preparedExactKey : State → PersistentSubst.PreparedAtom →
    Option PersistentSubst.AtomExactKey
  rememberClosed : State → PersistentSubst.ClosedRoot → State
  compose : State → Subst → State
  composePrepared : State →
    (generated : PersistentSubst.PreparedAtom.PreparedSubst) →
    generated.Valid → State
  unify : State → Atom → Atom → Option State
  trimFor : State → List Goal → Atom → State
  empty_valid : Valid empty
  denote_empty : denote empty = []
  ofDenote_valid : ∀ entries, Valid (ofDenote entries)
  denote_ofDenote : ∀ entries, denote (ofDenote entries) = entries
  subst_value : ∀ state atom, Valid state →
    (subst state atom).1 = PLeaTTa.subst (denote state) atom
  subst_valid : ∀ state atom, Valid state → Valid (subst state atom).2
  subst_denote : ∀ state atom, Valid state →
    denote (subst state atom).2 = denote state
  substMany_value : ∀ state atoms, Valid state →
    (substMany state atoms).1 = atoms.map (PLeaTTa.subst (denote state))
  substMany_valid : ∀ state atoms, Valid state →
    Valid (substMany state atoms).2
  substMany_denote : ∀ state atoms, Valid state →
    denote (substMany state atoms).2 = denote state
  substManyCertified_value : ∀ state atoms,
    (substManyCertified state atoms).1.map
        (fun prepared => prepared.1.atom) =
      atoms.map (PLeaTTa.subst (denote state))
  substManyCertified_valid : ∀ state atoms, Valid state →
    Valid (substManyCertified state atoms).2
  substManyCertified_denote : ∀ state atoms,
    denote (substManyCertified state atoms).2 = denote state
  substPrepared_value : ∀ state atom, Valid state →
    (substPrepared state atom).1.atom =
      PLeaTTa.subst (denote state) atom
  substPrepared_metadata : ∀ state atom, Valid state →
    (substPrepared state atom).1.Valid
  substPrepared_valid : ∀ state atom, Valid state →
    Valid (substPrepared state atom).2
  substPrepared_denote : ∀ state atom, Valid state →
    denote (substPrepared state atom).2 = denote state
  rememberRecent_valid : ∀ state prepared preparedValid, Valid state →
    Valid (rememberRecent state prepared preparedValid)
  rememberRecent_denote : ∀ state prepared preparedValid,
    denote (rememberRecent state prepared preparedValid) = denote state
  rememberPrepared_valid : ∀ state prepared preparedValid, Valid state →
    Valid (rememberPrepared state prepared preparedValid)
  rememberPrepared_denote : ∀ state prepared preparedValid,
    denote (rememberPrepared state prepared preparedValid) = denote state
  substPreparedRemembered_value : ∀ state atom, Valid state →
    (substPreparedRemembered state atom).1.atom =
      PLeaTTa.subst (denote state) atom
  substPreparedRemembered_metadata : ∀ state atom, Valid state →
    (substPreparedRemembered state atom).1.Valid
  substPreparedRemembered_valid : ∀ state atom, Valid state →
    Valid (substPreparedRemembered state atom).2
  substPreparedRemembered_denote : ∀ state atom, Valid state →
    denote (substPreparedRemembered state atom).2 = denote state
  preparedExactKey_value : ∀ state prepared,
    preparedExactKey state prepared =
      PersistentSubst.atomExactKey prepared.atom
  rememberClosed_valid : ∀ state root, Valid state →
    Valid (rememberClosed state root)
  rememberClosed_denote : ∀ state root,
    denote (rememberClosed state root) = denote state
  compose_valid : ∀ state generated, Valid state →
    Valid (compose state generated)
  compose_denote : ∀ state generated,
    denote (compose state generated) =
      Metta.Subst.compose generated (denote state)
  composePrepared_valid : ∀ state generated generatedValid, Valid state →
    Valid (composePrepared state generated generatedValid)
  composePrepared_denote : ∀ state generated generatedValid,
    denote (composePrepared state generated generatedValid) =
      Metta.Subst.compose
        (PersistentSubst.PreparedAtom.eraseSubst generated) (denote state)
  unify_valid : ∀ state left right, Valid state →
    ∀ next, unify state left right = some next → Valid next
  unify_denote : ∀ state left right, Valid state →
    (unify state left right).map denote =
      PLeaTTa.unifyB (denote state) left right
  trim_valid : ∀ state goals qterm, Valid state →
    Valid (trimFor state goals qterm)
  trim_denote : ∀ state goals qterm,
    denote (trimFor state goals qterm) =
      PLeaTTa.trimFor goals qterm (denote state)

namespace SubstEngine

@[simp] theorem substManyCertified_allGround (engine : SubstEngine)
    (state : engine.State) (atoms : List Atom) :
    preparedAtomsAllGround (engine.substManyCertified state atoms).1 =
      (atoms.map (PLeaTTa.subst (engine.denote state))).all
        Metta.isGround := by
  rw [preparedAtomsAllGround_map, engine.substManyCertified_value]

def mapAlt {Source Target : Type} (f : Source → Target) :
    Alt Source → Alt Target
  | .br goals state => .br goals (f state)
  | .barrier => .barrier

def mapConf {Source Target : Type} (f : Source → Target)
    (conf : Conf Source) : Conf Target :=
  { cur := conf.cur.map (fun branch => (branch.1, f branch.2))
    alts := conf.alts.map (mapAlt f)
    world := conf.world
    counter := conf.counter
    qterm := conf.qterm
    answers := conf.answers
    answerKeys := conf.answerKeys
    answerKeys_sound := conf.answerKeys_sound
    barriers := conf.barriers }

def erase (engine : SubstEngine) (conf : Conf engine.State) : Conf :=
  mapConf engine.denote conf

def lift (engine : SubstEngine) (conf : Conf) : Conf engine.State :=
  mapConf engine.ofDenote conf

def AltValid (engine : SubstEngine) : Alt engine.State → Prop
  | .br _ state => engine.Valid state
  | .barrier => True

def ConfValid (engine : SubstEngine) (conf : Conf engine.State) : Prop :=
  (∀ goals state, conf.cur = some (goals, state) → engine.Valid state) ∧
    ∀ alt ∈ conf.alts, AltValid engine alt

@[simp] theorem mapAlt_id (alt : Alt) : mapAlt id alt = alt := by
  cases alt <;> rfl

theorem mapAlt_comp {A B C : Type} (f : A → B) (g : B → C)
    (alt : Alt A) :
    mapAlt g (mapAlt f alt) = mapAlt (g ∘ f) alt := by
  cases alt <;> rfl

theorem mapConf_comp {A B C : Type} (f : A → B) (g : B → C)
    (conf : Conf A) :
    mapConf g (mapConf f conf) = mapConf (g ∘ f) conf := by
  cases conf
  simp [mapConf, mapAlt_comp, Function.comp_def]

@[simp] theorem erase_lift (engine : SubstEngine) (conf : Conf) :
    erase engine (lift engine conf) = conf := by
  rw [erase, lift, mapConf_comp]
  have hfunction : engine.denote ∘ engine.ofDenote = id := by
    funext entries
    exact engine.denote_ofDenote entries
  rw [hfunction]
  cases conf with
  | mk cur alts world counter qterm answers answerKeys answerKeys_sound barriers =>
      simp only [mapConf, id_eq]
      congr 1
      · cases cur <;> simp
      · induction alts with
        | nil => rfl
        | cons alt rest ih =>
            cases alt <;> simp [mapAlt, ih]

theorem lift_valid (engine : SubstEngine) (conf : Conf) :
    ConfValid engine (lift engine conf) := by
  constructor
  · intro goals state hcur
    unfold lift mapConf at hcur
    cases sourceCur : conf.cur with
    | none => simp [sourceCur] at hcur
    | some branch =>
        rcases branch with ⟨sourceGoals, sourceState⟩
        simp only [sourceCur, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact engine.ofDenote_valid sourceState
  · intro alt halt
    unfold lift mapConf at halt
    rw [List.mem_map] at halt
    rcases halt with ⟨sourceAlt, hsource, rfl⟩
    cases sourceAlt with
    | barrier => trivial
    | br goals sourceState => exact engine.ofDenote_valid sourceState

def referenceSubst (state : Subst) (atom : Atom) : Atom × Subst :=
  (PLeaTTa.subst state atom, state)

def referenceSubstMany (state : Subst) (atoms : List Atom) :
    List Atom × Subst :=
  (atoms.map (PLeaTTa.subst state), state)

def referenceSubstPrepared (state : Subst) (atom : Atom) :
    PersistentSubst.PreparedAtom × Subst :=
  (PersistentSubst.PreparedAtom.ofAtom (PLeaTTa.subst state atom), state)

def referenceSubstManyCertified (state : Subst) (atoms : List Atom) :
    List CertifiedPreparedAtom × Subst :=
  (atoms.map fun atom =>
    let value := PLeaTTa.subst state atom
    ⟨PersistentSubst.PreparedAtom.ofAtom value,
      PersistentSubst.PreparedAtom.ofAtom_valid value⟩,
    state)

def persistentSubstManyCertified (state : PersistentSubst.Scoped)
    (atoms : List Atom) : List CertifiedPreparedAtom × PersistentSubst.Scoped :=
  (atoms.map fun atom =>
    let value := PLeaTTa.subst state.denote atom
    ⟨PersistentSubst.PreparedAtom.ofAtom value,
      PersistentSubst.PreparedAtom.ofAtom_valid value⟩,
    state)

def reference : SubstEngine where
  State := Subst
  empty := []
  ofDenote := id
  denote := id
  Valid := fun _ => True
  subst := referenceSubst
  substMany := referenceSubstMany
  substManyCertified := referenceSubstManyCertified
  substPrepared := referenceSubstPrepared
  rememberRecent := fun state _ _ => state
  rememberPrepared := fun state _ _ => state
  substPreparedRemembered := referenceSubstPrepared
  preparedExactKey := fun _ prepared => prepared.exactValue
  rememberClosed := fun state _ => state
  compose := fun state generated => Metta.Subst.compose generated state
  composePrepared := fun state generated _ =>
    Metta.Subst.compose
      (PersistentSubst.PreparedAtom.eraseSubst generated) state
  unify := PLeaTTa.unifyB
  trimFor := fun state goals qterm => PLeaTTa.trimFor goals qterm state
  empty_valid := True.intro
  denote_empty := rfl
  ofDenote_valid := by intros; trivial
  denote_ofDenote := by intros; rfl
  subst_value := by intros; rfl
  subst_valid := by intros; trivial
  subst_denote := by intros; rfl
  substMany_value := by intros; rfl
  substMany_valid := by intros; trivial
  substMany_denote := by intros; rfl
  substManyCertified_value := by
    intros
    simp [referenceSubstManyCertified, List.map_map, Function.comp_def]
  substManyCertified_valid := by intros; trivial
  substManyCertified_denote := by intros; rfl
  substPrepared_value := by intros; rfl
  substPrepared_metadata := by
    intros
    exact PersistentSubst.PreparedAtom.ofAtom_valid _
  substPrepared_valid := by intros; trivial
  substPrepared_denote := by intros; rfl
  rememberRecent_valid := by intros; trivial
  rememberRecent_denote := by intros; rfl
  rememberPrepared_valid := by intros; trivial
  rememberPrepared_denote := by intros; rfl
  substPreparedRemembered_value := by intros; rfl
  substPreparedRemembered_metadata := by
    intros
    exact PersistentSubst.PreparedAtom.ofAtom_valid _
  substPreparedRemembered_valid := by intros; trivial
  substPreparedRemembered_denote := by intros; rfl
  preparedExactKey_value := by intros; simp
  rememberClosed_valid := by intros; trivial
  rememberClosed_denote := by intros; rfl
  compose_valid := by intros; trivial
  compose_denote := by intros; rfl
  composePrepared_valid := by intros; trivial
  composePrepared_denote := by intros; rfl
  unify_valid := by intros; trivial
  unify_denote := by intros; simp
  trim_valid := by intros; trivial
  trim_denote := by intros; rfl

@[simp] theorem reference_substManyCertified_values (state : Subst)
    (atoms : List Atom) :
    (reference.substManyCertified state atoms).1.map
        (fun prepared => prepared.1.atom) =
      atoms.map (PLeaTTa.subst state) := by
  exact reference.substManyCertified_value state atoms

@[simp] theorem reference_substManyCertified_atoms (state : Subst)
    (atoms : List Atom) :
    (reference.substManyCertified state atoms).1.unattach.map
        PersistentSubst.PreparedAtom.atom =
      atoms.map (PLeaTTa.subst state) := by
  simp [reference, referenceSubstManyCertified, List.unattach,
    -List.map_subtype, List.map_map, Function.comp_def]

@[simp] theorem reference_substManyCertified_state (state : Subst)
    (atoms : List Atom) :
    (reference.substManyCertified state atoms).2 = state := by
  rfl

@[simp] theorem reference_substManyCertified_length (state : Subst)
    (atoms : List Atom) :
    (reference.substManyCertified state atoms).1.length = atoms.length := by
  simp [reference, referenceSubstManyCertified]

def persistent : SubstEngine where
  State := PersistentSubst.Scoped
  empty := PersistentSubst.Scoped.empty
  ofDenote := PersistentSubst.Scoped.ofList
  denote := PersistentSubst.Scoped.denote
  Valid := PersistentSubst.Scoped.Coherent
  subst := PersistentSubst.Scoped.subst
  substMany := PersistentSubst.Scoped.substMany
  substManyCertified := persistentSubstManyCertified
  substPrepared := PersistentSubst.Scoped.substPrepared
  rememberRecent := PersistentSubst.Scoped.rememberRecent
  rememberPrepared := PersistentSubst.Scoped.rememberPrepared
  substPreparedRemembered := PersistentSubst.Scoped.substPrepared
  preparedExactKey := PersistentSubst.Scoped.preparedExactKey
  rememberClosed := PersistentSubst.Scoped.selectClosedRoot
  compose := PersistentSubst.Scoped.compose
  composePrepared := fun state generated valid =>
    state.composePrepared generated valid
  unify := PersistentSubst.Scoped.unifyB
  trimFor := PersistentSubst.Scoped.trimFor
  empty_valid := PersistentSubst.Scoped.ofList_coherent []
  denote_empty := PersistentSubst.Memo.denote_ofList []
  ofDenote_valid := PersistentSubst.Scoped.ofList_coherent
  denote_ofDenote := PersistentSubst.Memo.denote_ofList
  subst_value := by
    intro state atom valid
    exact (PersistentSubst.Scoped.subst_eq_reference state atom valid).1
  subst_valid := by
    intro state atom valid
    exact (PersistentSubst.Scoped.subst_eq_reference state atom valid).2.1
  subst_denote := by
    intro state atom valid
    exact (PersistentSubst.Scoped.subst_eq_reference state atom valid).2.2
  substMany_value := by
    intro state atoms valid
    exact (PersistentSubst.Scoped.substMany_eq_reference state atoms valid).1
  substMany_valid := by
    intro state atoms valid
    exact (PersistentSubst.Scoped.substMany_eq_reference state atoms valid).2.1
  substMany_denote := by
    intro state atoms valid
    exact (PersistentSubst.Scoped.substMany_eq_reference
      state atoms valid).2.2
  substManyCertified_value := by
    intros
    simp [persistentSubstManyCertified, List.map_map, Function.comp_def]
  substManyCertified_valid := by intros; assumption
  substManyCertified_denote := by intros; rfl
  substPrepared_value := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).1
  substPrepared_metadata := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.1
  substPrepared_valid := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.2.1
  substPrepared_denote := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.2.2
  rememberRecent_valid := PersistentSubst.Scoped.rememberRecent_coherent
  rememberRecent_denote := PersistentSubst.Scoped.denote_rememberRecent
  rememberPrepared_valid := PersistentSubst.Scoped.rememberPrepared_coherent
  rememberPrepared_denote := PersistentSubst.Scoped.denote_rememberPrepared
  substPreparedRemembered_value := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).1
  substPreparedRemembered_metadata := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.1
  substPreparedRemembered_valid := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.2.1
  substPreparedRemembered_denote := by
    intro state atom valid
    exact (PersistentSubst.Scoped.substPrepared_eq_reference
      state atom valid).2.2.2
  preparedExactKey_value := PersistentSubst.Scoped.preparedExactKey_eq
  rememberClosed_valid := by
    intro state root valid
    exact PersistentSubst.Scoped.selectClosedRoot_coherent state root valid
  rememberClosed_denote := PersistentSubst.Scoped.denote_selectClosedRoot
  compose_valid := PersistentSubst.Scoped.compose_coherent
  compose_denote := PersistentSubst.Scoped.denote_compose
  composePrepared_valid := PersistentSubst.Scoped.composePrepared_coherent
  composePrepared_denote := PersistentSubst.Scoped.denote_composePrepared
  unify_valid := PersistentSubst.Scoped.unifyB_coherent
  unify_denote := PersistentSubst.Scoped.unifyB_map_denote
  trim_valid := PersistentSubst.Scoped.trimFor_coherent
  trim_denote := PersistentSubst.Scoped.denote_trimFor

/-- A substitution state paired with the engine invariant that justifies all
denotational laws. The proof component is erased by code generation; at the
Lean level it makes an incoherent executable state unrepresentable. -/
def CheckedState (engine : SubstEngine) :=
  { state : engine.State // engine.Valid state }

def checkedSubst (engine : SubstEngine) (state : CheckedState engine)
    (atom : Atom) : Atom × CheckedState engine :=
  let result := engine.subst state.1 atom
  (result.1, ⟨result.2, engine.subst_valid state.1 atom state.2⟩)

def checkedSubstMany (engine : SubstEngine) (state : CheckedState engine)
    (atoms : List Atom) : List Atom × CheckedState engine :=
  let result := engine.substMany state.1 atoms
  (result.1, ⟨result.2, engine.substMany_valid state.1 atoms state.2⟩)

/-- Preserve certified prepared roots while threading cache refreshes across a
batch.  The proof component is erased; the executable receives the prepared
trees produced by the coherent underlying engine. -/
def checkedSubstManyCertified (engine : SubstEngine) :
    CheckedState engine → List Atom →
      List CertifiedPreparedAtom × CheckedState engine
  | state, [] => ([], state)
  | state, atom :: rest =>
      let head := engine.substPrepared state.1 atom
      let headCertified : CertifiedPreparedAtom :=
        ⟨head.1, engine.substPrepared_metadata state.1 atom state.2⟩
      let next : CheckedState engine :=
        ⟨head.2, engine.substPrepared_valid state.1 atom state.2⟩
      let tail := checkedSubstManyCertified engine next rest
      (headCertified :: tail.1, tail.2)

theorem checkedSubstManyCertified_value (engine : SubstEngine)
    (state : CheckedState engine) (atoms : List Atom) :
    (checkedSubstManyCertified engine state atoms).1.map
        (fun prepared => prepared.1.atom) =
      atoms.map (PLeaTTa.subst (engine.denote state.1)) := by
  induction atoms generalizing state with
  | nil => rfl
  | cons atom rest ih =>
      let head := engine.substPrepared state.1 atom
      let next : CheckedState engine :=
        ⟨head.2, engine.substPrepared_valid state.1 atom state.2⟩
      have headValue := engine.substPrepared_value state.1 atom state.2
      have headDenote := engine.substPrepared_denote state.1 atom state.2
      have tailValue := ih next
      simp only [checkedSubstManyCertified, List.map_cons]
      change head.1.atom ::
          (checkedSubstManyCertified engine next rest).1.map
            (fun prepared => prepared.1.atom) =
        PLeaTTa.subst (engine.denote state.1) atom ::
          rest.map (PLeaTTa.subst (engine.denote state.1))
      rw [headValue, tailValue]
      simpa [next] using congrArg
        (fun denotation => rest.map (PLeaTTa.subst denotation)) headDenote

theorem checkedSubstManyCertified_denote (engine : SubstEngine)
    (state : CheckedState engine) (atoms : List Atom) :
    engine.denote (checkedSubstManyCertified engine state atoms).2.1 =
      engine.denote state.1 := by
  induction atoms generalizing state with
  | nil => rfl
  | cons atom rest ih =>
      let head := engine.substPrepared state.1 atom
      let next : CheckedState engine :=
        ⟨head.2, engine.substPrepared_valid state.1 atom state.2⟩
      have tailDenote := ih next
      have headDenote := engine.substPrepared_denote state.1 atom state.2
      change engine.denote
          (checkedSubstManyCertified engine next rest).2.1 =
        engine.denote state.1
      rw [tailDenote]
      exact headDenote

def checkedSubstPrepared (engine : SubstEngine)
    (state : CheckedState engine) (atom : Atom) :
    PersistentSubst.PreparedAtom × CheckedState engine :=
  let result := engine.substPrepared state.1 atom
  (result.1, ⟨result.2, engine.substPrepared_valid state.1 atom state.2⟩)

def checkedRememberRecent (engine : SubstEngine)
    (state : CheckedState engine)
    (prepared : PersistentSubst.PreparedAtom) (valid : prepared.Valid) :
    CheckedState engine :=
  ⟨engine.rememberRecent state.1 prepared valid,
    engine.rememberRecent_valid state.1 prepared valid state.2⟩

def checkedRememberPrepared (engine : SubstEngine)
    (state : CheckedState engine)
    (prepared : PersistentSubst.PreparedAtom) (valid : prepared.Valid) :
    CheckedState engine :=
  ⟨engine.rememberPrepared state.1 prepared valid,
    engine.rememberPrepared_valid state.1 prepared valid state.2⟩

/-- At an insertion boundary the checked state supplies the erased validity
proof needed to retain the exact prepared tree in the underlying engine. -/
def checkedSubstPreparedRemembered (engine : SubstEngine)
    (state : CheckedState engine) (atom : Atom) :
    PersistentSubst.PreparedAtom × CheckedState engine :=
  let result := engine.substPrepared state.1 atom
  let preparedValid := engine.substPrepared_metadata state.1 atom state.2
  let nextValid := engine.substPrepared_valid state.1 atom state.2
  (result.1,
    ⟨engine.rememberPrepared result.2 result.1 preparedValid,
      engine.rememberPrepared_valid result.2 result.1 preparedValid
        nextValid⟩)

def checkedPreparedExactKey (engine : SubstEngine)
    (state : CheckedState engine) (prepared : PersistentSubst.PreparedAtom) :
    Option PersistentSubst.AtomExactKey :=
  engine.preparedExactKey state.1 prepared

def checkedRememberClosed (engine : SubstEngine)
    (state : CheckedState engine) (root : PersistentSubst.ClosedRoot) :
    CheckedState engine :=
  ⟨engine.rememberClosed state.1 root,
    engine.rememberClosed_valid state.1 root state.2⟩

def checkedCompose (engine : SubstEngine) (state : CheckedState engine)
    (generated : Subst) : CheckedState engine :=
  ⟨engine.compose state.1 generated,
    engine.compose_valid state.1 generated state.2⟩

def checkedComposePrepared (engine : SubstEngine)
    (state : CheckedState engine)
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (generatedValid : generated.Valid) : CheckedState engine :=
  ⟨engine.composePrepared state.1 generated generatedValid,
    engine.composePrepared_valid state.1 generated generatedValid state.2⟩

def checkedUnify (engine : SubstEngine) (state : CheckedState engine)
    (left right : Atom) : Option (CheckedState engine) :=
  match result : engine.unify state.1 left right with
  | none => none
  | some next =>
      some ⟨next, engine.unify_valid state.1 left right state.2 next result⟩

def checkedTrimFor (engine : SubstEngine) (state : CheckedState engine)
    (goals : List Goal) (qterm : Atom) : CheckedState engine :=
  ⟨engine.trimFor state.1 goals qterm,
    engine.trim_valid state.1 goals qterm state.2⟩

/-- Refine an engine so every carried state contains its actual invariant
proof. `Valid` is then structurally true because coherence has moved into the
state type, not because the invariant was discarded. -/
def checked (engine : SubstEngine) : SubstEngine where
  State := CheckedState engine
  empty := ⟨engine.empty, engine.empty_valid⟩
  ofDenote := fun entries =>
    ⟨engine.ofDenote entries, engine.ofDenote_valid entries⟩
  denote := fun state => engine.denote state.1
  Valid := fun _ => True
  subst := checkedSubst engine
  substMany := checkedSubstMany engine
  substManyCertified := checkedSubstManyCertified engine
  substPrepared := checkedSubstPrepared engine
  rememberRecent := checkedRememberRecent engine
  rememberPrepared := checkedRememberPrepared engine
  substPreparedRemembered := checkedSubstPreparedRemembered engine
  preparedExactKey := checkedPreparedExactKey engine
  rememberClosed := checkedRememberClosed engine
  compose := checkedCompose engine
  composePrepared := checkedComposePrepared engine
  unify := checkedUnify engine
  trimFor := checkedTrimFor engine
  empty_valid := True.intro
  denote_empty := engine.denote_empty
  ofDenote_valid := by intros; trivial
  denote_ofDenote := engine.denote_ofDenote
  subst_value := by
    intro state atom _
    unfold checkedSubst
    exact engine.subst_value state.1 atom state.2
  subst_valid := by intros; trivial
  subst_denote := by
    intro state atom _
    unfold checkedSubst
    exact engine.subst_denote state.1 atom state.2
  substMany_value := by
    intro state atoms _
    unfold checkedSubstMany
    exact engine.substMany_value state.1 atoms state.2
  substMany_valid := by intros; trivial
  substMany_denote := by
    intro state atoms _
    unfold checkedSubstMany
    exact engine.substMany_denote state.1 atoms state.2
  substManyCertified_value := by
    intro state atoms
    exact checkedSubstManyCertified_value engine state atoms
  substManyCertified_valid := by intros; trivial
  substManyCertified_denote := by
    intro state atoms
    exact checkedSubstManyCertified_denote engine state atoms
  substPrepared_value := by
    intro state atom _
    unfold checkedSubstPrepared
    exact engine.substPrepared_value state.1 atom state.2
  substPrepared_metadata := by
    intro state atom _
    unfold checkedSubstPrepared
    exact engine.substPrepared_metadata state.1 atom state.2
  substPrepared_valid := by intros; trivial
  substPrepared_denote := by
    intro state atom _
    unfold checkedSubstPrepared
    exact engine.substPrepared_denote state.1 atom state.2
  rememberRecent_valid := by intros; trivial
  rememberRecent_denote := by
    intro state prepared preparedValid
    unfold checkedRememberRecent
    exact engine.rememberRecent_denote state.1 prepared preparedValid
  rememberPrepared_valid := by intros; trivial
  rememberPrepared_denote := by
    intro state prepared preparedValid
    unfold checkedRememberPrepared
    exact engine.rememberPrepared_denote state.1 prepared preparedValid
  substPreparedRemembered_value := by
    intro state atom _
    unfold checkedSubstPreparedRemembered
    exact engine.substPrepared_value state.1 atom state.2
  substPreparedRemembered_metadata := by
    intro state atom _
    unfold checkedSubstPreparedRemembered
    exact engine.substPrepared_metadata state.1 atom state.2
  substPreparedRemembered_valid := by intros; trivial
  substPreparedRemembered_denote := by
    intro state atom _
    unfold checkedSubstPreparedRemembered
    rw [engine.rememberPrepared_denote]
    exact engine.substPrepared_denote state.1 atom state.2
  preparedExactKey_value := by
    intro state prepared
    unfold checkedPreparedExactKey
    exact engine.preparedExactKey_value state.1 prepared
  rememberClosed_valid := by intros; trivial
  rememberClosed_denote := by
    intro state root
    unfold checkedRememberClosed
    exact engine.rememberClosed_denote state.1 root
  compose_valid := by intros; trivial
  compose_denote := by
    intro state generated
    unfold checkedCompose
    exact engine.compose_denote state.1 generated
  composePrepared_valid := by intros; trivial
  composePrepared_denote := by
    intro state generated generatedValid
    unfold checkedComposePrepared
    exact engine.composePrepared_denote state.1 generated generatedValid
  unify_valid := by intros; trivial
  unify_denote := by
    intro state left right _
    have denotation := engine.unify_denote state.1 left right state.2
    unfold checkedUnify
    split <;> simp_all
  trim_valid := by intros; trivial
  trim_denote := by
    intro state goals qterm
    unfold checkedTrimFor
    exact engine.trim_denote state.1 goals qterm

theorem checked_confValid (engine : SubstEngine)
    (conf : Conf (checked engine).State) :
    ConfValid (checked engine) conf := by
  constructor
  · intro goals state equality
    trivial
  · intro alt member
    cases alt <;> trivial

namespace PreparedUnify

abbrev Constraint := String × PersistentSubst.PreparedAtom
abbrev Constraints := List Constraint

def eraseConstraints (constraints : Constraints) : Subst :=
  constraints.map fun constraint =>
    (constraint.1, constraint.2.atom)

def prepareConstraints (constraints : Subst) : Constraints :=
  constraints.map fun constraint =>
    (constraint.1, PersistentSubst.PreparedAtom.ofAtom constraint.2)

def decomposeShallow (left right : PersistentSubst.PreparedAtom) :
    Option Constraints :=
  match left.atom, right.atom with
  | .var x, .var y =>
      if x == y then some [] else some [(x, right)]
  | .var x, _ => some [(x, right)]
  | _, .var x => some [(x, left)]
  | .sym a, .sym b => if a == b then some [] else none
  | .gnd a, .gnd b => if Metta.Ground.equiv a b then some [] else none
  | .expr left, .expr right =>
      (Metta.Unify.decomposeList left right).map prepareConstraints
  | _, _ => none

/-- Build a raw child view without rescanning it when its prepared parent
has already certified that the whole expression is closed. -/
def prepareRawAtom (closed : Bool) (atom : Atom) :
    PersistentSubst.PreparedAtom :=
  if closed then PersistentSubst.PreparedAtom.ofClosed atom
  else PersistentSubst.PreparedAtom.ofAtom atom

mutual
/-- Recursively decompose a raw subtree against a prepared subtree.  When the
    prepared side has children, descend through them rather than converting
    the next expression level back to raw constraints. -/
def decomposeRawPrepared (closed : Bool) : Atom →
    PersistentSubst.PreparedAtom → Option Constraints
  | .expr left, .expr _ rightChildren _ _ _ =>
      decomposeRawPreparedList closed left rightChildren
  | left, right => decomposeShallow (prepareRawAtom closed left) right

def decomposeRawPreparedList (closed : Bool) : List Atom →
    List PersistentSubst.PreparedAtom → Option Constraints
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match decomposeRawPrepared closed left right,
          decomposeRawPreparedList closed leftRest rightRest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none
  | _, _ => none
end

mutual
/-- Symmetric recursive prepared/raw decomposition. -/
def decomposePreparedRaw (closed : Bool) :
    PersistentSubst.PreparedAtom → Atom → Option Constraints
  | .expr _ leftChildren _ _ _, .expr right =>
      decomposePreparedRawList closed leftChildren right
  | left, right => decomposeShallow left (prepareRawAtom closed right)

def decomposePreparedRawList (closed : Bool) :
    List PersistentSubst.PreparedAtom →
    List Atom → Option Constraints
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match decomposePreparedRaw closed left right,
          decomposePreparedRawList closed leftRest rightRest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none
  | _, _ => none
end

mutual

/-- Recursively decompose two raw subtrees while retaining closedness
certified by their prepared summaries.  A closed side wraps every visited
child in O(1), avoiding reconstruction of a large variable-free subtree. -/
def decomposeRawRaw (leftClosed rightClosed : Bool) :
    Atom → Atom → Option Constraints
  | .expr left, .expr right =>
      decomposeRawRawList leftClosed rightClosed left right
  | left, right =>
      decomposeShallow (prepareRawAtom leftClosed left)
        (prepareRawAtom rightClosed right)

def decomposeRawRawList (leftClosed rightClosed : Bool) :
    List Atom → List Atom → Option Constraints
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match decomposeRawRaw leftClosed rightClosed left right,
          decomposeRawRawList leftClosed rightClosed leftRest rightRest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none
  | _, _ => none
end

mutual

/-- Structurally decompose prepared atoms while retaining cached targets. -/
def decompose : PersistentSubst.PreparedAtom →
    PersistentSubst.PreparedAtom → Option Constraints
  | left@(.expr _ leftChildren _ _ _), right =>
      match right with
      | .expr _ rightChildren _ _ _ =>
          decomposeList leftChildren rightChildren
      | .summary (.expr rightAtoms) rightVariables _ _ =>
          decomposePreparedRawList rightVariables.isEmpty leftChildren
            rightAtoms
      | _ => decomposeShallow left right
  | left@(.summary (.expr leftAtoms) leftVariables _ _), right =>
      match right with
      | .expr _ rightChildren _ _ _ =>
          decomposeRawPreparedList leftVariables.isEmpty leftAtoms
            rightChildren
      | .summary (.expr rightAtoms) rightVariables _ _ =>
          decomposeRawRawList leftVariables.isEmpty rightVariables.isEmpty
            leftAtoms rightAtoms
      | _ => decomposeShallow left right
  | left, right => decomposeShallow left right

/-- Pointwise prepared decomposition, mirroring the reference unifier. -/
def decomposeList : List PersistentSubst.PreparedAtom →
    List PersistentSubst.PreparedAtom → Option Constraints
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match decompose left right, decomposeList leftRest rightRest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none
  | _, _ => none

end

def independent (constraints : Constraints) : Bool :=
  let names := constraints.map Prod.fst
  constraints.all (fun constraint =>
      constraint.2.variables.all fun name => !names.contains name) &&
    decide names.Nodup

def ConstraintsValid (constraints : Constraints) : Prop :=
  ∀ constraint ∈ constraints, constraint.2.Valid

/-- Elimination order sufficient for a decomposition batch to remain
unchanged round-for-round: each source is fresh in its own target, every
later target, and every later source.  Earlier targets may reference later
sources, which is common in compiled relation heads. -/
def RawEliminationOrdered : List (String × Atom) → Prop
  | [] => True
  | (source, target) :: rest =>
      source ∉ target.vars ∧
      (∀ constraint ∈ rest, source ∉ constraint.2.vars) ∧
      source ∉ rest.map Prod.fst ∧
      RawEliminationOrdered rest

/-- Cached checker for `RawEliminationOrdered`; atom bodies are never
rescanned. -/
def eliminationOrdered : Constraints → Bool
  | [] => true
  | (source, target) :: rest =>
      !target.variables.contains source &&
      rest.all (fun constraint =>
        !constraint.2.variables.contains source) &&
      !(rest.map Prod.fst).contains source &&
      eliminationOrdered rest

/-- Apply one prepared binding.  Cached variable absence makes substitution
into a large unaffected term O(1); affected prepared expressions preserve
their child structure. -/
def substituteAtomPrepared (source : String)
    (replacement : PersistentSubst.PreparedAtom) :
    Atom → PersistentSubst.PreparedAtom
  | .var name =>
      if name == source then replacement
      else PersistentSubst.PreparedAtom.ofAtom (.var name)
  | .expr children =>
      PersistentSubst.PreparedAtom.mkExpr
        (children.map (substituteAtomPrepared source replacement))
  | atom => PersistentSubst.PreparedAtom.ofAtom atom

def substituteOne (source : String)
    (replacement : PersistentSubst.PreparedAtom) :
    PersistentSubst.PreparedAtom → PersistentSubst.PreparedAtom
  | .summary atom cachedVariables exact exactSound =>
      if cachedVariables.contains source then
        substituteAtomPrepared source replacement atom
      else
        .summary atom cachedVariables exact exactSound
  | .expr atom children cachedVariables exact exactSound =>
      if cachedVariables.contains source then
        PersistentSubst.PreparedAtom.mkExpr
          (children.map (substituteOne source replacement))
      else
        .expr atom children cachedVariables exact exactSound

abbrev Equation :=
  PersistentSubst.PreparedAtom × PersistentSubst.PreparedAtom
abbrev Equations := List Equation

def EquationsValid (equations : Equations) : Prop :=
  ∀ equation ∈ equations, equation.1.Valid ∧ equation.2.Valid

def eraseEquation (equation : Equation) : Atom × Atom :=
  (equation.1.atom, equation.2.atom)

def eraseEquations (equations : Equations) : List (Atom × Atom) :=
  equations.map eraseEquation

def constraintEquationsPrepared (constraints : Constraints) : Equations :=
  constraints.map fun constraint =>
    (PersistentSubst.PreparedAtom.ofAtom (Atom.var constraint.1),
      constraint.2)

def applyOneEquation (source : String)
    (replacement : PersistentSubst.PreparedAtom)
    (equation : Equation) : Equation :=
  (substituteOne source replacement equation.1,
    substituteOne source replacement equation.2)

def erasePreparedSource
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (source : String) : PersistentSubst.PreparedAtom.PreparedSubst :=
  generated.filter fun binding => binding.1 != source

def extendPrepared
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (source : String) (target : PersistentSubst.PreparedAtom) :
    PersistentSubst.PreparedAtom.PreparedSubst :=
  (source, target) :: erasePreparedSource generated source

def decomposeAll : Equations → Option Constraints
  | [] => some []
  | equation :: rest =>
      match decompose equation.1 equation.2, decomposeAll rest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none

def unifyRounds : Nat → Equations →
    PersistentSubst.PreparedAtom.PreparedSubst →
    Option PersistentSubst.PreparedAtom.PreparedSubst
  | 0, equations, generated =>
      match decomposeAll equations with
      | none => none
      | some [] => some generated
      | some (_ :: _) => none
  | fuel + 1, equations, generated =>
      match decomposeAll equations with
      | none => none
      | some [] => some generated
      | some ((source, target) :: rest) =>
          if target.variables.contains source then none
          else
            let singletonEquations := constraintEquationsPrepared rest
            let nextEquations := singletonEquations.map
              (applyOneEquation source target)
            unifyRounds fuel nextEquations
              (extendPrepared generated source target)

def unifyTopGeneral (left right : PersistentSubst.PreparedAtom) :
    Option PersistentSubst.PreparedAtom.PreparedSubst :=
  unifyRounds (left.atom.size + right.atom.size) [(left, right)] []

@[simp] theorem eraseConstraints_prepareConstraints (constraints : Subst) :
    eraseConstraints (prepareConstraints constraints) = constraints := by
  simp [eraseConstraints, prepareConstraints, Function.comp_def]

@[simp] theorem prepareConstraints_valid (constraints : Subst) :
    ConstraintsValid (prepareConstraints constraints) := by
  intro constraint member
  simp only [prepareConstraints, List.mem_map] at member
  rcases member with ⟨raw, rawMember, rfl⟩
  exact PersistentSubst.PreparedAtom.ofAtom_valid raw.2

theorem decomposeShallow_erase (left right : PersistentSubst.PreparedAtom) :
    (decomposeShallow left right).map eraseConstraints =
      Metta.Unify.decomposeEq left.atom right.atom := by
  unfold decomposeShallow
  cases hleft : left.atom <;> cases hright : right.atom <;>
    simp [hleft, hright, Metta.Unify.decomposeEq, eraseConstraints,
      prepareConstraints, Function.comp_def]
  all_goals split <;> simp_all [eraseConstraints]

theorem decomposeShallow_valid (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid)
    (constraints : Constraints)
    (decomposed : decomposeShallow left right = some constraints) :
    ConstraintsValid constraints := by
  unfold decomposeShallow at decomposed
  cases hleft : left.atom <;> cases hright : right.atom <;>
    try simp_all [ConstraintsValid]
  case sym.var | gnd.var | expr.var =>
    subst constraints
    intro source target member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      at member
    rcases member with ⟨rfl, rfl⟩
    exact leftValid
  case var.sym | var.gnd | var.expr =>
    subst constraints
    intro source target member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      at member
    rcases member with ⟨rfl, rfl⟩
    exact rightValid
  case var.var =>
    split at decomposed
    · simp only [Option.some.injEq] at decomposed
      subst constraints
      simp
    · simp only [Option.some.injEq] at decomposed
      subst constraints
      intro source target member
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
        at member
      rcases member with ⟨rfl, rfl⟩
      exact rightValid
  case expr.expr =>
    rcases decomposed with ⟨raw, rawResult, rfl⟩
    intro source target member
    exact prepareConstraints_valid raw (source, target) member

theorem decomposeShallow_sound (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid)
    (constraints : Constraints)
    (decomposed : decomposeShallow left right = some constraints) :
    Metta.Unify.decomposeEq left.atom right.atom =
        some (eraseConstraints constraints) ∧
      ConstraintsValid constraints := by
  have erased := decomposeShallow_erase left right
  rw [decomposed] at erased
  simp only [Option.map_some] at erased
  exact ⟨erased.symm, decomposeShallow_valid left right leftValid rightValid
    constraints decomposed⟩

@[simp] theorem prepareRawAtom_atom (closed : Bool) (atom : Atom) :
    (prepareRawAtom closed atom).atom = atom := by
  cases closed <;> rfl

theorem prepareRawAtom_valid (closed : Bool) (atom : Atom)
    (closedAtom : closed = true → atom.vars = []) :
    (prepareRawAtom closed atom).Valid := by
  cases closed with
  | false => exact PersistentSubst.PreparedAtom.ofAtom_valid atom
  | true =>
      exact PersistentSubst.PreparedAtom.ofClosed_valid atom
        (closedAtom rfl)

theorem child_vars_nil_of_expr_isEmpty (atoms : List Atom)
    (empty : (Atom.expr atoms).vars.isEmpty = true) :
    ∀ atom ∈ atoms, atom.vars = [] := by
  have wholeNil : (Atom.expr atoms).vars = [] := by
    cases equality : (Atom.expr atoms).vars with
    | nil => rfl
    | cons head tail => simp [equality] at empty
  simp only [Atom.vars] at wholeNil
  rw [List.flatten_eq_nil_iff] at wholeNil
  intro atom member
  exact wholeNil atom.vars (List.mem_map_of_mem member)

mutual

theorem decomposeRawPrepared_sound (closed : Bool) (left : Atom)
    (right : PersistentSubst.PreparedAtom) (constraints : Constraints)
    (rawValid : closed = true → left.vars = [])
    (rightValid : right.Valid)
    (decomposed : decomposeRawPrepared closed left right = some constraints) :
    Metta.Unify.decomposeEq left right.atom =
        some (eraseConstraints constraints) ∧
      ConstraintsValid constraints := by
  cases left with
  | expr leftAtoms =>
      cases right with
      | expr rightAtom rightChildren rightVariables rightExact
          rightExactSound =>
          cases rightValid with
          | expr _ rightChildrenValid =>
              have leftChildren : closed = true →
                  ∀ atom ∈ leftAtoms, atom.vars = [] := by
                intro equality
                apply child_vars_nil_of_expr_isEmpty leftAtoms
                rw [rawValid equality]
                rfl
              have sound := decomposeRawPreparedList_sound closed leftAtoms
                rightChildren constraints leftChildren rightChildrenValid
                (by simpa [decomposeRawPrepared,
                  PersistentSubst.PreparedAtom.mkExpr] using decomposed)
              simpa [PersistentSubst.PreparedAtom.mkExpr,
                PersistentSubst.PreparedAtom.atom,
                Metta.Unify.decomposeEq] using sound
      | summary rightAtom rightVariables rightExact rightExactSound =>
          have sound := decomposeShallow_sound
            (prepareRawAtom closed (.expr leftAtoms))
            (.summary rightAtom rightVariables rightExact rightExactSound)
            (prepareRawAtom_valid closed (.expr leftAtoms) rawValid)
            rightValid constraints (by
              simpa [decomposeRawPrepared] using decomposed)
          simpa using sound
  | sym symbol | var symbol | gnd symbol =>
      have sound := decomposeShallow_sound
        (prepareRawAtom closed _) right
        (prepareRawAtom_valid closed _ rawValid) rightValid constraints
        (by simpa [decomposeRawPrepared] using decomposed)
      simpa using sound

theorem decomposeRawPreparedList_sound :
    ∀ (closed : Bool) (left : List Atom)
      (right : List PersistentSubst.PreparedAtom) (constraints : Constraints),
      (closed = true → ∀ atom ∈ left, atom.vars = []) →
      (∀ atom ∈ right, atom.Valid) →
      decomposeRawPreparedList closed left right = some constraints →
      Metta.Unify.decomposeList left
          (right.map PersistentSubst.PreparedAtom.atom) =
          some (eraseConstraints constraints) ∧
        ConstraintsValid constraints
  | _, [], [], constraints, _, _, decomposed => by
      simp [decomposeRawPreparedList] at decomposed
      subst constraints
      simp [Metta.Unify.decomposeList, eraseConstraints, ConstraintsValid]
  | _, [], _ :: _, _, _, _, decomposed => by
      simp [decomposeRawPreparedList] at decomposed
  | _, _ :: _, [], _, _, _, decomposed => by
      simp [decomposeRawPreparedList] at decomposed
  | closed, left :: leftRest, right :: rightRest, constraints,
      rawValid, rightValid, decomposed => by
      simp only [decomposeRawPreparedList] at decomposed
      cases hhead : decomposeRawPrepared closed left right with
      | none => simp [hhead] at decomposed
      | some head =>
          cases htail : decomposeRawPreparedList closed leftRest rightRest with
          | none => simp [hhead, htail] at decomposed
          | some tail =>
              simp only [hhead, htail, Option.some.injEq] at decomposed
              subst constraints
              have headSound := decomposeRawPrepared_sound closed left right
                head (fun equality => rawValid equality left (by simp))
                (rightValid right (by simp)) hhead
              have tailSound := decomposeRawPreparedList_sound closed leftRest
                rightRest tail
                (fun equality atom member =>
                  rawValid equality atom (by simp [member]))
                (fun atom member => rightValid atom (by simp [member])) htail
              constructor
              · simp only [List.map_cons, Metta.Unify.decomposeList,
                  headSound.1, tailSound.1, eraseConstraints,
                  List.map_append]
              · intro constraint member
                rcases List.mem_append.mp member with member | member
                · exact headSound.2 constraint member
                · exact tailSound.2 constraint member

end

mutual

theorem decomposePreparedRaw_sound (closed : Bool)
    (left : PersistentSubst.PreparedAtom) (right : Atom)
    (constraints : Constraints) (leftValid : left.Valid)
    (rawValid : closed = true → right.vars = [])
    (decomposed : decomposePreparedRaw closed left right = some constraints) :
    Metta.Unify.decomposeEq left.atom right =
        some (eraseConstraints constraints) ∧
      ConstraintsValid constraints := by
  cases left with
  | expr leftAtom leftChildren leftVariables leftExact leftExactSound =>
      cases leftValid with
      | expr _ leftChildrenValid =>
          cases right with
          | expr rightAtoms =>
              have rightChildren : closed = true →
                  ∀ atom ∈ rightAtoms, atom.vars = [] := by
                intro equality
                apply child_vars_nil_of_expr_isEmpty rightAtoms
                rw [rawValid equality]
                rfl
              have sound := decomposePreparedRawList_sound closed leftChildren
                rightAtoms constraints leftChildrenValid rightChildren
                (by simpa [decomposePreparedRaw,
                  PersistentSubst.PreparedAtom.mkExpr] using decomposed)
              simpa [PersistentSubst.PreparedAtom.mkExpr,
                PersistentSubst.PreparedAtom.atom,
                Metta.Unify.decomposeEq] using sound
          | sym symbol | var symbol | gnd symbol =>
              have sound := decomposeShallow_sound
                _ (prepareRawAtom closed _)
                (.expr leftChildren leftChildrenValid)
                (prepareRawAtom_valid closed _ rawValid) constraints (by
                  simpa [decomposePreparedRaw,
                    PersistentSubst.PreparedAtom.mkExpr] using decomposed)
              simpa [PersistentSubst.PreparedAtom.mkExpr] using sound
  | summary leftAtom leftVariables leftExact leftExactSound =>
      have sound := decomposeShallow_sound
        (.summary leftAtom leftVariables leftExact leftExactSound)
        (prepareRawAtom closed right) leftValid
        (prepareRawAtom_valid closed right rawValid) constraints
        (by simpa [decomposePreparedRaw] using decomposed)
      simpa using sound

theorem decomposePreparedRawList_sound :
    ∀ (closed : Bool) (left : List PersistentSubst.PreparedAtom)
      (right : List Atom) (constraints : Constraints),
      (∀ atom ∈ left, atom.Valid) →
      (closed = true → ∀ atom ∈ right, atom.vars = []) →
      decomposePreparedRawList closed left right = some constraints →
      Metta.Unify.decomposeList
          (left.map PersistentSubst.PreparedAtom.atom) right =
          some (eraseConstraints constraints) ∧
        ConstraintsValid constraints
  | _, [], [], constraints, _, _, decomposed => by
      simp [decomposePreparedRawList] at decomposed
      subst constraints
      simp [Metta.Unify.decomposeList, eraseConstraints, ConstraintsValid]
  | _, [], _ :: _, _, _, _, decomposed => by
      simp [decomposePreparedRawList] at decomposed
  | _, _ :: _, [], _, _, _, decomposed => by
      simp [decomposePreparedRawList] at decomposed
  | closed, left :: leftRest, right :: rightRest, constraints,
      leftValid, rawValid, decomposed => by
      simp only [decomposePreparedRawList] at decomposed
      cases hhead : decomposePreparedRaw closed left right with
      | none => simp [hhead] at decomposed
      | some head =>
          cases htail : decomposePreparedRawList closed leftRest rightRest with
          | none => simp [hhead, htail] at decomposed
          | some tail =>
              simp only [hhead, htail, Option.some.injEq] at decomposed
              subst constraints
              have headSound := decomposePreparedRaw_sound closed left right
                head (leftValid left (by simp))
                (fun equality => rawValid equality right (by simp)) hhead
              have tailSound := decomposePreparedRawList_sound closed leftRest
                rightRest tail
                (fun atom member => leftValid atom (by simp [member]))
                (fun equality atom member =>
                  rawValid equality atom (by simp [member])) htail
              constructor
              · simp only [List.map_cons, Metta.Unify.decomposeList,
                  headSound.1, tailSound.1, eraseConstraints,
                  List.map_append]
              · intro constraint member
                rcases List.mem_append.mp member with member | member
                · exact headSound.2 constraint member
                · exact tailSound.2 constraint member

end

mutual

theorem decomposeRawRaw_sound :
    ∀ (leftClosed rightClosed : Bool) (left right : Atom)
      (constraints : Constraints),
      (leftClosed = true → left.vars = []) →
      (rightClosed = true → right.vars = []) →
      decomposeRawRaw leftClosed rightClosed left right = some constraints →
      Metta.Unify.decomposeEq left right =
          some (eraseConstraints constraints) ∧
        ConstraintsValid constraints
  | leftClosed, rightClosed, .expr left, .expr right, constraints,
      leftValid, rightValid, decomposed => by
      simp only [decomposeRawRaw] at decomposed
      have leftChildren : leftClosed = true →
          ∀ atom ∈ left, atom.vars = [] := by
        intro equality
        apply child_vars_nil_of_expr_isEmpty left
        rw [leftValid equality]
        rfl
      have rightChildren : rightClosed = true →
          ∀ atom ∈ right, atom.vars = [] := by
        intro equality
        apply child_vars_nil_of_expr_isEmpty right
        rw [rightValid equality]
        rfl
      simpa [Metta.Unify.decomposeEq] using
        decomposeRawRawList_sound leftClosed rightClosed left right
          constraints leftChildren rightChildren decomposed
  | leftClosed, rightClosed, left, right, constraints, leftValid,
      rightValid, decomposed => by
      cases left <;> cases right
      case expr.expr left right =>
        simp only [decomposeRawRaw] at decomposed
        have leftChildren : leftClosed = true →
            ∀ atom ∈ left, atom.vars = [] := by
          intro equality
          apply child_vars_nil_of_expr_isEmpty left
          rw [leftValid equality]
          rfl
        have rightChildren : rightClosed = true →
            ∀ atom ∈ right, atom.vars = [] := by
          intro equality
          apply child_vars_nil_of_expr_isEmpty right
          rw [rightValid equality]
          rfl
        simpa [Metta.Unify.decomposeEq] using
          decomposeRawRawList_sound leftClosed rightClosed left right
            constraints leftChildren rightChildren decomposed
      all_goals
        simp only [decomposeRawRaw] at decomposed
      all_goals
        have sound := decomposeShallow_sound
          (prepareRawAtom leftClosed _) (prepareRawAtom rightClosed _)
          (prepareRawAtom_valid leftClosed _ leftValid)
          (prepareRawAtom_valid rightClosed _ rightValid)
          constraints decomposed
      all_goals
        simpa using sound

theorem decomposeRawRawList_sound :
    ∀ (leftClosed rightClosed : Bool) (left right : List Atom)
      (constraints : Constraints),
      (leftClosed = true → ∀ atom ∈ left, atom.vars = []) →
      (rightClosed = true → ∀ atom ∈ right, atom.vars = []) →
      decomposeRawRawList leftClosed rightClosed left right =
          some constraints →
      Metta.Unify.decomposeList left right =
          some (eraseConstraints constraints) ∧
        ConstraintsValid constraints
  | _, _, [], [], constraints, _, _, decomposed => by
      simp [decomposeRawRawList] at decomposed
      subst constraints
      simp [Metta.Unify.decomposeList, eraseConstraints, ConstraintsValid]
  | _, _, [], _ :: _, _, _, _, decomposed => by
      simp [decomposeRawRawList] at decomposed
  | _, _, _ :: _, [], _, _, _, decomposed => by
      simp [decomposeRawRawList] at decomposed
  | leftClosed, rightClosed, left :: leftRest, right :: rightRest,
      constraints, leftValid, rightValid, decomposed => by
      simp only [decomposeRawRawList] at decomposed
      cases hhead : decomposeRawRaw leftClosed rightClosed left right with
      | none => simp [hhead] at decomposed
      | some head =>
          cases htail : decomposeRawRawList leftClosed rightClosed leftRest
              rightRest with
          | none => simp [hhead, htail] at decomposed
          | some tail =>
              simp only [hhead, htail, Option.some.injEq] at decomposed
              subst constraints
              have headSound := decomposeRawRaw_sound leftClosed rightClosed
                left right head
                (fun equality => leftValid equality left (by simp))
                (fun equality => rightValid equality right (by simp)) hhead
              have tailSound := decomposeRawRawList_sound leftClosed
                rightClosed leftRest rightRest tail
                (fun equality atom member =>
                  leftValid equality atom (by simp [member]))
                (fun equality atom member =>
                  rightValid equality atom (by simp [member])) htail
              constructor
              · simp only [Metta.Unify.decomposeList, headSound.1,
                  tailSound.1, eraseConstraints, List.map_append]
              · intro constraint member
                rcases List.mem_append.mp member with member | member
                · exact headSound.2 constraint member
                · exact tailSound.2 constraint member

end

mutual

theorem decomposeList_sound :
    ∀ (left right : List PersistentSubst.PreparedAtom)
      (constraints : Constraints),
      (∀ atom ∈ left, atom.Valid) →
      (∀ atom ∈ right, atom.Valid) →
      decomposeList left right = some constraints →
      Metta.Unify.decomposeList (left.map PersistentSubst.PreparedAtom.atom)
          (right.map PersistentSubst.PreparedAtom.atom) =
          some (eraseConstraints constraints) ∧
        ConstraintsValid constraints
  | [], [], constraints, _, _, decomposed => by
      simp [decomposeList] at decomposed
      subst constraints
      simp [Metta.Unify.decomposeList, eraseConstraints, ConstraintsValid]
  | [], _ :: _, _, _, _, decomposed => by
      simp [decomposeList] at decomposed
  | _ :: _, [], _, _, _, decomposed => by
      simp [decomposeList] at decomposed
  | left :: leftRest, right :: rightRest, constraints,
      leftValid, rightValid, decomposed => by
      simp only [decomposeList] at decomposed
      cases hhead : decompose left right with
      | none => simp [hhead] at decomposed
      | some head =>
          cases htail : decomposeList leftRest rightRest with
          | none => simp [hhead, htail] at decomposed
          | some tail =>
              simp only [hhead, htail, Option.some.injEq] at decomposed
              subst constraints
              have headSound := decompose_sound left right
                (leftValid left (by simp)) (rightValid right (by simp))
                head hhead
              have tailSound := decomposeList_sound leftRest rightRest tail
                (fun atom member => leftValid atom (by simp [member]))
                (fun atom member => rightValid atom (by simp [member]))
                htail
              constructor
              · simp only [List.map_cons, Metta.Unify.decomposeList,
                  headSound.1, tailSound.1, eraseConstraints,
                  List.map_append]
              · intro constraint member
                rcases List.mem_append.mp member with member | member
                · exact headSound.2 constraint member
                · exact tailSound.2 constraint member

theorem decompose_sound (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid)
    (constraints : Constraints)
    (decomposed : decompose left right = some constraints) :
    Metta.Unify.decomposeEq left.atom right.atom =
        some (eraseConstraints constraints) ∧
      ConstraintsValid constraints := by
  cases left with
  | summary leftAtom leftVariables leftExact leftExactSound =>
      have leftVariablesSound := leftValid.variables_eq
      simp only [PersistentSubst.PreparedAtom.variables,
        PersistentSubst.PreparedAtom.atom] at leftVariablesSound
      cases right with
      | summary rightAtom rightVariables rightExact rightExactSound =>
          have rightVariablesSound := rightValid.variables_eq
          simp only [PersistentSubst.PreparedAtom.variables,
            PersistentSubst.PreparedAtom.atom] at rightVariablesSound
          cases leftAtom with
          | expr leftAtoms =>
              cases rightAtom with
              | expr rightAtoms =>
                  have sound := decomposeRawRawList_sound
                    leftVariables.isEmpty rightVariables.isEmpty leftAtoms
                    rightAtoms constraints
                    (fun empty => child_vars_nil_of_expr_isEmpty leftAtoms (by
                      rw [← leftVariablesSound]
                      exact empty))
                    (fun empty => child_vars_nil_of_expr_isEmpty rightAtoms (by
                      rw [← rightVariablesSound]
                      exact empty)) (by
                      simpa [decompose] using decomposed)
                  simpa [PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using sound
              | sym symbol | var symbol | gnd symbol =>
                  exact decomposeShallow_sound _ _ leftValid rightValid
                    constraints (by simpa [decompose] using decomposed)
          | sym symbol | var symbol | gnd symbol =>
              exact decomposeShallow_sound _ _ leftValid rightValid
                constraints (by simpa [decompose] using decomposed)
      | expr rightAtom rightChildren rightVariables rightExact
          rightExactSound =>
          cases rightValid with
          | expr _ rightChildrenValid =>
              cases leftAtom with
              | expr leftAtoms =>
                  have sound := decomposeRawPreparedList_sound
                    leftVariables.isEmpty leftAtoms rightChildren constraints
                    (fun empty => child_vars_nil_of_expr_isEmpty leftAtoms (by
                      rw [← leftVariablesSound]
                      exact empty))
                    rightChildrenValid (by
                      simpa [decompose,
                        PersistentSubst.PreparedAtom.mkExpr] using decomposed)
                  simpa [PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using sound
              | sym symbol | var symbol | gnd symbol =>
                  exact decomposeShallow_sound _ _ leftValid
                    (.expr rightChildren rightChildrenValid) constraints (by
                      simpa [decompose,
                        PersistentSubst.PreparedAtom.mkExpr] using decomposed)
  | expr leftAtom leftChildren leftVariables leftExact leftExactSound =>
      cases leftValid with
      | expr _ leftChildrenValid =>
          cases right with
          | summary rightAtom rightVariables rightExact rightExactSound =>
              have rightVariablesSound := rightValid.variables_eq
              simp only [PersistentSubst.PreparedAtom.variables,
                PersistentSubst.PreparedAtom.atom] at rightVariablesSound
              cases rightAtom with
              | expr rightAtoms =>
                  have sound := decomposePreparedRawList_sound
                    rightVariables.isEmpty leftChildren rightAtoms constraints
                    leftChildrenValid
                    (fun empty =>
                      child_vars_nil_of_expr_isEmpty rightAtoms (by
                        rw [← rightVariablesSound]
                        exact empty)) (by
                      simpa [decompose,
                        PersistentSubst.PreparedAtom.mkExpr] using decomposed)
                  simpa [PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using sound
              | sym symbol | var symbol | gnd symbol =>
                  exact decomposeShallow_sound _ _
                    (.expr leftChildren leftChildrenValid) rightValid
                    constraints (by simpa [decompose,
                      PersistentSubst.PreparedAtom.mkExpr] using decomposed)
          | expr rightAtom rightChildren rightVariables rightExact
              rightExactSound =>
              cases rightValid with
              | expr _ rightChildrenValid =>
                  have sound := decomposeList_sound leftChildren rightChildren
                    constraints leftChildrenValid rightChildrenValid (by
                      simpa [decompose,
                        PersistentSubst.PreparedAtom.mkExpr] using decomposed)
                  simpa [PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using sound

end

mutual

theorem decomposeRawPrepared_erase (closed : Bool) (left : Atom)
    (right : PersistentSubst.PreparedAtom) (rightValid : right.Valid) :
    (decomposeRawPrepared closed left right).map eraseConstraints =
      Metta.Unify.decomposeEq left right.atom := by
  cases left with
  | expr leftAtoms =>
      cases right with
      | expr rightAtom rightChildren rightVariables rightExact
          rightExactSound =>
          cases rightValid with
          | expr _ rightChildrenValid =>
              simpa [decomposeRawPrepared,
                PersistentSubst.PreparedAtom.mkExpr,
                PersistentSubst.PreparedAtom.atom,
                Metta.Unify.decomposeEq] using
                decomposeRawPreparedList_erase closed leftAtoms rightChildren
                  rightChildrenValid
      | summary rightAtom rightVariables rightExact rightExactSound =>
          simpa [decomposeRawPrepared] using decomposeShallow_erase
            (prepareRawAtom closed (.expr leftAtoms))
            (.summary rightAtom rightVariables rightExact rightExactSound)
  | sym symbol | var symbol | gnd symbol =>
      simpa [decomposeRawPrepared] using decomposeShallow_erase
        (prepareRawAtom closed _) right

theorem decomposeRawPreparedList_erase :
    ∀ (closed : Bool) (left : List Atom)
      (right : List PersistentSubst.PreparedAtom),
      (∀ atom ∈ right, atom.Valid) →
      (decomposeRawPreparedList closed left right).map eraseConstraints =
        Metta.Unify.decomposeList left
          (right.map PersistentSubst.PreparedAtom.atom)
  | _, [], [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, _ :: _, [], _ => rfl
  | closed, left :: leftRest, right :: rightRest, rightValid => by
      have headErased := decomposeRawPrepared_erase closed left right
        (rightValid right (by simp))
      have tailErased := decomposeRawPreparedList_erase closed leftRest rightRest
        (fun atom member => rightValid atom (by simp [member]))
      cases headResult : decomposeRawPrepared closed left right <;>
        cases tailResult : decomposeRawPreparedList closed leftRest rightRest <;>
        simp only [decomposeRawPreparedList, headResult, tailResult,
          List.map_cons, Metta.Unify.decomposeList]
      all_goals
        simp only [headResult, tailResult, Option.map_none, Option.map_some]
          at headErased tailErased
        rw [← headErased, ← tailErased]
        simp [eraseConstraints]

end


mutual

theorem decomposePreparedRaw_erase (closed : Bool)
    (left : PersistentSubst.PreparedAtom) (right : Atom)
    (leftValid : left.Valid) :
    (decomposePreparedRaw closed left right).map eraseConstraints =
      Metta.Unify.decomposeEq left.atom right := by
  cases left with
  | expr leftAtom leftChildren leftVariables leftExact leftExactSound =>
      cases leftValid with
      | expr _ leftChildrenValid =>
          cases right with
          | expr rightAtoms =>
              simpa [decomposePreparedRaw,
                PersistentSubst.PreparedAtom.mkExpr,
                PersistentSubst.PreparedAtom.atom,
                Metta.Unify.decomposeEq] using
                decomposePreparedRawList_erase closed leftChildren rightAtoms
                  leftChildrenValid
          | sym symbol | var symbol | gnd symbol =>
              simpa [decomposePreparedRaw,
                PersistentSubst.PreparedAtom.mkExpr] using
                decomposeShallow_erase _ (prepareRawAtom closed _)
  | summary leftAtom leftVariables leftExact leftExactSound =>
      simpa [decomposePreparedRaw] using decomposeShallow_erase
        (.summary leftAtom leftVariables leftExact leftExactSound)
        (prepareRawAtom closed right)

theorem decomposePreparedRawList_erase :
    ∀ (closed : Bool) (left : List PersistentSubst.PreparedAtom)
      (right : List Atom),
      (∀ atom ∈ left, atom.Valid) →
      (decomposePreparedRawList closed left right).map eraseConstraints =
        Metta.Unify.decomposeList
          (left.map PersistentSubst.PreparedAtom.atom) right
  | _, [], [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, _ :: _, [], _ => rfl
  | closed, left :: leftRest, right :: rightRest, leftValid => by
      have headErased := decomposePreparedRaw_erase closed left right
        (leftValid left (by simp))
      have tailErased := decomposePreparedRawList_erase closed leftRest rightRest
        (fun atom member => leftValid atom (by simp [member]))
      cases headResult : decomposePreparedRaw closed left right <;>
        cases tailResult : decomposePreparedRawList closed leftRest rightRest <;>
        simp only [decomposePreparedRawList, headResult, tailResult,
          List.map_cons, Metta.Unify.decomposeList]
      all_goals
        simp only [headResult, tailResult, Option.map_none, Option.map_some]
          at headErased tailErased
        rw [← headErased, ← tailErased]
        simp [eraseConstraints]

end

mutual

theorem decomposeRawRaw_erase :
    ∀ (leftClosed rightClosed : Bool) (left right : Atom),
      (decomposeRawRaw leftClosed rightClosed left right).map
          eraseConstraints =
        Metta.Unify.decomposeEq left right
  | leftClosed, rightClosed, .expr left, .expr right => by
      simpa [decomposeRawRaw, Metta.Unify.decomposeEq] using
        decomposeRawRawList_erase leftClosed rightClosed left right
  | leftClosed, rightClosed, left, right => by
      cases left <;> cases right
      case expr.expr left right =>
        simpa [decomposeRawRaw, Metta.Unify.decomposeEq] using
          decomposeRawRawList_erase leftClosed rightClosed left right
      all_goals
        simpa [decomposeRawRaw] using decomposeShallow_erase
          (prepareRawAtom leftClosed _) (prepareRawAtom rightClosed _)

theorem decomposeRawRawList_erase :
    ∀ (leftClosed rightClosed : Bool) (left right : List Atom),
      (decomposeRawRawList leftClosed rightClosed left right).map
          eraseConstraints =
        Metta.Unify.decomposeList left right
  | _, _, [], [] => rfl
  | _, _, [], _ :: _ => rfl
  | _, _, _ :: _, [] => rfl
  | leftClosed, rightClosed, left :: leftRest, right :: rightRest => by
      have headErased := decomposeRawRaw_erase leftClosed rightClosed
        left right
      have tailErased := decomposeRawRawList_erase leftClosed rightClosed
        leftRest rightRest
      cases headResult : decomposeRawRaw leftClosed rightClosed left right <;>
        cases tailResult : decomposeRawRawList leftClosed rightClosed
          leftRest rightRest <;>
        simp only [decomposeRawRawList, headResult, tailResult,
          Metta.Unify.decomposeList]
      all_goals
        simp only [headResult, tailResult, Option.map_none, Option.map_some]
          at headErased tailErased
        rw [← headErased, ← tailErased]
        simp [eraseConstraints, List.map_append]

end

mutual

theorem decomposeList_erase :
    ∀ (left right : List PersistentSubst.PreparedAtom),
      (∀ atom ∈ left, atom.Valid) →
      (∀ atom ∈ right, atom.Valid) →
      (decomposeList left right).map eraseConstraints =
        Metta.Unify.decomposeList
          (left.map PersistentSubst.PreparedAtom.atom)
          (right.map PersistentSubst.PreparedAtom.atom)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | left :: leftRest, right :: rightRest, leftValid, rightValid => by
      have headErased := decompose_erase left right
        (leftValid left (by simp)) (rightValid right (by simp))
      have tailErased := decomposeList_erase leftRest rightRest
        (fun atom member => leftValid atom (by simp [member]))
        (fun atom member => rightValid atom (by simp [member]))
      cases headResult : decompose left right <;>
        cases tailResult : decomposeList leftRest rightRest <;>
        simp only [decomposeList, headResult, tailResult,
          List.map_cons, Metta.Unify.decomposeList]
      all_goals
        simp only [headResult, tailResult, Option.map_none, Option.map_some]
          at headErased tailErased
        rw [← headErased, ← tailErased]
        simp [eraseConstraints, List.map_append]

theorem decompose_erase (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    (decompose left right).map eraseConstraints =
      Metta.Unify.decomposeEq left.atom right.atom := by
  cases left with
  | summary leftAtom leftVariables leftExact leftExactSound =>
      cases right with
      | summary rightAtom rightVariables rightExact rightExactSound =>
          cases leftAtom with
          | expr leftAtoms =>
              cases rightAtom with
              | expr rightAtoms =>
                  simpa [decompose, PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using
                    decomposeRawRawList_erase leftVariables.isEmpty
                      rightVariables.isEmpty leftAtoms rightAtoms
              | sym _ | var _ | gnd _ =>
                  simpa [decompose] using decomposeShallow_erase _ _
          | sym _ | var _ | gnd _ =>
              simpa [decompose] using decomposeShallow_erase _ _
      | expr rightAtom rightChildren rightVariables rightExact
          rightExactSound =>
          cases rightValid with
          | expr _ rightChildrenValid =>
              cases leftAtom with
              | expr leftAtoms =>
                  simpa [decompose, PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using
                    decomposeRawPreparedList_erase leftVariables.isEmpty
                      leftAtoms rightChildren rightChildrenValid
              | sym _ | var _ | gnd _ =>
                  simpa [decompose,
                    PersistentSubst.PreparedAtom.mkExpr] using
                    decomposeShallow_erase _ _
  | expr leftAtom leftChildren leftVariables leftExact leftExactSound =>
      cases leftValid with
      | expr _ leftChildrenValid =>
          cases right with
          | summary rightAtom rightVariables rightExact rightExactSound =>
              cases rightAtom with
              | expr rightAtoms =>
                  simpa [decompose, PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using
                    decomposePreparedRawList_erase rightVariables.isEmpty
                      leftChildren rightAtoms leftChildrenValid
              | sym _ | var _ | gnd _ =>
                  simpa [decompose,
                    PersistentSubst.PreparedAtom.mkExpr] using
                    decomposeShallow_erase _ _
          | expr rightAtom rightChildren rightVariables rightExact
              rightExactSound =>
              cases rightValid with
              | expr _ rightChildrenValid =>
                  simpa [decompose, PersistentSubst.PreparedAtom.mkExpr,
                    PersistentSubst.PreparedAtom.atom,
                    Metta.Unify.decomposeEq] using
                    decomposeList_erase leftChildren rightChildren
                      leftChildrenValid rightChildrenValid

end

theorem substituteAtomPrepared_valid (source : String)
    (replacement : PersistentSubst.PreparedAtom)
    (replacementValid : replacement.Valid) :
    ∀ atom, (substituteAtomPrepared source replacement atom).Valid := by
  intro atom
  induction atom with
  | sym symbol =>
      simp only [substituteAtomPrepared]
      exact PersistentSubst.PreparedAtom.ofAtom_valid _
  | var name =>
      simp only [substituteAtomPrepared]
      split
      · exact replacementValid
      · exact PersistentSubst.PreparedAtom.ofAtom_valid _
  | gnd ground =>
      simp only [substituteAtomPrepared]
      exact PersistentSubst.PreparedAtom.ofAtom_valid _
  | expr children ih =>
      simp only [substituteAtomPrepared]
      apply PersistentSubst.PreparedAtom.mkExpr_valid
      intro prepared member
      rcases List.mem_map.mp member with ⟨child, childMember, rfl⟩
      exact ih child childMember

theorem substituteAtomPrepared_atom (source : String)
    (replacement : PersistentSubst.PreparedAtom) : ∀ atom,
    (substituteAtomPrepared source replacement atom).atom =
      Metta.Subst.apply [(source, replacement.atom)] atom := by
  intro atom
  induction atom with
  | sym symbol => simp [substituteAtomPrepared, Metta.Subst.apply]
  | var name =>
      by_cases equal : name = source <;>
        simp [substituteAtomPrepared, Metta.Subst.apply, Metta.Subst.lookup,
          equal]
  | gnd ground => simp [substituteAtomPrepared, Metta.Subst.apply]
  | expr children ih =>
      simp only [substituteAtomPrepared,
        PersistentSubst.PreparedAtom.atom_mkExpr, Metta.Subst.apply,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro child member
      exact ih child member

theorem substituteOne_valid (source : String)
    (replacement prepared : PersistentSubst.PreparedAtom)
    (replacementValid : replacement.Valid) (preparedValid : prepared.Valid) :
    (substituteOne source replacement prepared).Valid := by
  induction preparedValid with
  | summary atom =>
      simp only [substituteOne]
      split
      · exact substituteAtomPrepared_valid source replacement
          replacementValid atom
      · exact .summary atom
  | cached atom cachedVariables exact exactSound variablesSound =>
      simp only [substituteOne]
      split
      · exact substituteAtomPrepared_valid source replacement
          replacementValid atom
      · exact .cached atom cachedVariables exact exactSound variablesSound
  | expr children valid ih =>
      simp only [PersistentSubst.PreparedAtom.mkExpr, substituteOne]
      split
      · apply PersistentSubst.PreparedAtom.mkExpr_valid
        intro mapped mappedMember
        rcases List.mem_map.mp mappedMember with ⟨child, childMember, rfl⟩
        exact ih child childMember
      · exact .expr children valid

theorem substituteOne_atom (source : String)
    (replacement prepared : PersistentSubst.PreparedAtom)
    (preparedValid : prepared.Valid) :
    (substituteOne source replacement prepared).atom =
      Metta.Subst.apply [(source, replacement.atom)] prepared.atom := by
  induction preparedValid with
  | summary atom =>
      simp only [substituteOne]
      split
      · exact substituteAtomPrepared_atom source replacement atom
      · rename_i absent
        have sourceAbsent : source ∉ atom.vars := by
          simpa using absent
        exact (apply_singleton_eq_self_of_not_mem source replacement.atom
          atom sourceAbsent).symm
  | cached atom cachedVariables exact exactSound variablesSound =>
      simp only [substituteOne]
      split
      · exact substituteAtomPrepared_atom source replacement atom
      · rename_i absent
        have sourceAbsent : source ∉ atom.vars := by
          rw [← variablesSound]
          simpa using absent
        exact (apply_singleton_eq_self_of_not_mem source replacement.atom
          atom sourceAbsent).symm
  | expr children valid ih =>
      simp only [PersistentSubst.PreparedAtom.mkExpr, substituteOne]
      split
      · simp only [PersistentSubst.PreparedAtom.atom, Metta.Subst.apply,
          List.map_map]
        congr 1
        apply List.map_congr_left
        intro child member
        exact ih child member
      · rename_i absent
        have wholeValid :
            (PersistentSubst.PreparedAtom.mkExpr children).Valid :=
          .expr children valid
        have sourceAbsent : source ∉
            (PersistentSubst.PreparedAtom.mkExpr children).atom.vars := by
          rw [← wholeValid.variables_eq]
          simpa using absent
        exact (apply_singleton_eq_self_of_not_mem source replacement.atom
          (PersistentSubst.PreparedAtom.mkExpr children).atom
          sourceAbsent).symm

theorem applyOneEquation_valid (source : String)
    (replacement : PersistentSubst.PreparedAtom) (equation : Equation)
    (replacementValid : replacement.Valid)
    (valid : equation.1.Valid ∧ equation.2.Valid) :
    (applyOneEquation source replacement equation).1.Valid ∧
      (applyOneEquation source replacement equation).2.Valid := by
  exact ⟨substituteOne_valid source replacement equation.1 replacementValid
      valid.1,
    substituteOne_valid source replacement equation.2 replacementValid valid.2⟩

theorem eraseEquation_applyOneEquation (source : String)
    (replacement : PersistentSubst.PreparedAtom) (equation : Equation)
    (valid : equation.1.Valid ∧ equation.2.Valid) :
    eraseEquation (applyOneEquation source replacement equation) =
      (Metta.Subst.apply [(source, replacement.atom)] equation.1.atom,
        Metta.Subst.apply [(source, replacement.atom)] equation.2.atom) := by
  apply Prod.ext
  · exact substituteOne_atom source replacement equation.1 valid.1
  · exact substituteOne_atom source replacement equation.2 valid.2

theorem constraintEquationsPrepared_valid (constraints : Constraints)
    (valid : ConstraintsValid constraints) :
    EquationsValid (constraintEquationsPrepared constraints) := by
  intro equation member
  simp only [constraintEquationsPrepared, List.mem_map] at member
  rcases member with ⟨constraint, constraintMember, rfl⟩
  exact ⟨PersistentSubst.PreparedAtom.ofAtom_valid _,
    valid constraint constraintMember⟩

theorem constraintEquationsPrepared_erase (constraints : Constraints) :
    eraseEquations (constraintEquationsPrepared constraints) =
      (eraseConstraints constraints).map fun constraint =>
        (Atom.var constraint.1, constraint.2) := by
  simp [eraseEquations, constraintEquationsPrepared, eraseConstraints,
    eraseEquation, Function.comp_def]

theorem map_applyOneEquation_valid (source : String)
    (replacement : PersistentSubst.PreparedAtom) (equations : Equations)
    (replacementValid : replacement.Valid)
    (valid : EquationsValid equations) :
    EquationsValid (equations.map (applyOneEquation source replacement)) := by
  intro equation member
  simp only [List.mem_map] at member
  rcases member with ⟨original, originalMember, rfl⟩
  exact applyOneEquation_valid source replacement original replacementValid
    (valid original originalMember)

theorem map_applyOneEquation_erase (source : String)
    (replacement : PersistentSubst.PreparedAtom) (equations : Equations)
    (valid : EquationsValid equations) :
    eraseEquations (equations.map (applyOneEquation source replacement)) =
      (eraseEquations equations).map fun equation =>
        (Metta.Subst.apply [(source, replacement.atom)] equation.1,
          Metta.Subst.apply [(source, replacement.atom)] equation.2) := by
  simp only [eraseEquations, List.map_map]
  apply List.map_congr_left
  intro equation member
  exact eraseEquation_applyOneEquation source replacement equation
    (valid equation member)

theorem nextEquations_valid (source : String)
    (target : PersistentSubst.PreparedAtom) (constraints : Constraints)
    (targetValid : target.Valid)
    (valid : ConstraintsValid constraints) :
    EquationsValid
      ((constraintEquationsPrepared constraints).map
        (applyOneEquation source target)) :=
  map_applyOneEquation_valid source target
    (constraintEquationsPrepared constraints) targetValid
    (constraintEquationsPrepared_valid constraints valid)

theorem nextEquations_erase (source : String)
    (target : PersistentSubst.PreparedAtom) (constraints : Constraints)
    (valid : ConstraintsValid constraints) :
    eraseEquations
        ((constraintEquationsPrepared constraints).map
          (applyOneEquation source target)) =
      (eraseConstraints constraints).map fun constraint =>
        (Metta.Subst.apply [(source, target.atom)]
            (Atom.var constraint.1),
          Metta.Subst.apply [(source, target.atom)] constraint.2) := by
  rw [map_applyOneEquation_erase source target
    (constraintEquationsPrepared constraints)
    (constraintEquationsPrepared_valid constraints valid)]
  simp [constraintEquationsPrepared_erase, eraseConstraints,
    Function.comp_def]

theorem erasePreparedSource_erase
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (source : String) :
    PersistentSubst.PreparedAtom.eraseSubst
        (erasePreparedSource generated source) =
      Metta.Subst.erase
        (PersistentSubst.PreparedAtom.eraseSubst generated) source := by
  unfold erasePreparedSource Metta.Subst.erase
  induction generated with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, target⟩
      simp only [List.filter_cons,
        PersistentSubst.PreparedAtom.eraseSubst, List.map_cons]
      by_cases keep : name != source
      · simp only [keep, if_true]
        simpa [PersistentSubst.PreparedAtom.eraseSubst] using ih
      · simp only [keep]
        simpa [PersistentSubst.PreparedAtom.eraseSubst] using ih

theorem extendPrepared_erase
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (source : String) (target : PersistentSubst.PreparedAtom) :
    PersistentSubst.PreparedAtom.eraseSubst
        (extendPrepared generated source target) =
      Metta.Subst.extend
        (PersistentSubst.PreparedAtom.eraseSubst generated) source
        target.atom := by
  unfold extendPrepared Metta.Subst.extend
  simp only [PersistentSubst.PreparedAtom.eraseSubst, List.map_cons]
  apply congrArg ((source, target.atom) :: ·)
  simpa [PersistentSubst.PreparedAtom.eraseSubst] using
    erasePreparedSource_erase generated source

theorem erasePreparedSource_valid
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (valid : generated.Valid) (source : String) :
    (erasePreparedSource generated source).Valid := by
  intro binding member
  simp only [erasePreparedSource, List.mem_filter] at member
  exact valid binding member.1

theorem extendPrepared_valid
    (generated : PersistentSubst.PreparedAtom.PreparedSubst)
    (valid : generated.Valid) (source : String)
    (target : PersistentSubst.PreparedAtom) (targetValid : target.Valid) :
    (extendPrepared generated source target).Valid := by
  intro binding member
  rcases List.mem_cons.mp member with rfl | member
  · exact targetValid
  · exact erasePreparedSource_valid generated valid source binding member

theorem decomposeAll_sound (equations : Equations)
    (valid : EquationsValid equations) (constraints : Constraints)
    (decomposed : decomposeAll equations = some constraints) :
    Metta.Unify.decomposeAll (eraseEquations equations) =
        some (eraseConstraints constraints) ∧
      ConstraintsValid constraints := by
  induction equations generalizing constraints with
  | nil =>
      simp [decomposeAll] at decomposed
      subst constraints
      simp [Metta.Unify.decomposeAll, eraseEquations, eraseConstraints,
        ConstraintsValid]
  | cons equation rest ih =>
      have equationValid := valid equation (by simp)
      have restValid : EquationsValid rest :=
        fun entry member => valid entry (by simp [member])
      simp only [decomposeAll] at decomposed
      cases headResult : decompose equation.1 equation.2 with
      | none => simp [headResult] at decomposed
      | some head =>
          cases tailResult : decomposeAll rest with
          | none => simp [headResult, tailResult] at decomposed
          | some tail =>
              simp only [headResult, tailResult, Option.some.injEq]
                at decomposed
              subst constraints
              have headSound := decompose_sound equation.1 equation.2
                equationValid.1 equationValid.2 head headResult
              have tailSound := ih restValid tail tailResult
              constructor
              · simp only [eraseEquations, List.map_cons,
                  Metta.Unify.decomposeAll]
                change
                  (match Metta.Unify.decomposeEq equation.1.atom
                      equation.2.atom,
                      Metta.Unify.decomposeAll (eraseEquations rest) with
                    | some head, some tail => some (head ++ tail)
                    | _, _ => none) = _
                rw [headSound.1, tailSound.1]
                simp [eraseConstraints]
              · intro constraint member
                rcases List.mem_append.mp member with member | member
                · exact headSound.2 constraint member
                · exact tailSound.2 constraint member

theorem decomposeAll_erase (equations : Equations)
    (valid : EquationsValid equations) :
    (decomposeAll equations).map eraseConstraints =
      Metta.Unify.decomposeAll (eraseEquations equations) := by
  induction equations with
  | nil => rfl
  | cons equation rest ih =>
      have equationValid := valid equation (by simp)
      have restValid : EquationsValid rest :=
        fun entry member => valid entry (by simp [member])
      have headErased := decompose_erase equation.1 equation.2
        equationValid.1 equationValid.2
      have tailErased := ih restValid
      cases headResult : decompose equation.1 equation.2 <;>
        cases tailResult : decomposeAll rest <;>
        simp only [decomposeAll, headResult, tailResult, eraseEquations,
          List.map_cons, Metta.Unify.decomposeAll]
      all_goals
        simp only [headResult, tailResult, Option.map_none, Option.map_some]
          at headErased tailErased
        change _ =
          (match Metta.Unify.decomposeEq equation.1.atom equation.2.atom,
              Metta.Unify.decomposeAll (eraseEquations rest) with
            | some head, some tail => some (head ++ tail)
            | _, _ => none)
        rw [← headErased, ← tailErased]
        simp [eraseConstraints, List.map_append]

private theorem not_mem_vars_of_occurs_eq_false (name : String) (atom : Atom)
    (occursFalse : Metta.Subst.occurs name atom = false) :
    name ∉ atom.vars := by
  induction atom with
  | sym symbol => simp [Atom.vars]
  | var source =>
      simpa [Metta.Subst.occurs, Atom.vars] using occursFalse
  | gnd ground => simp [Atom.vars]
  | expr atoms ih =>
      simp only [Metta.Subst.occurs] at occursFalse
      simp only [Atom.vars, List.mem_flatten, List.mem_map]
      intro member
      rcases member with ⟨_variableNames, ⟨child, childMember, rfl⟩,
        nameMember⟩
      have childFalse : Metta.Subst.occurs name child = false := by
        have allFalse := List.any_eq_false.mp occursFalse
        simpa only [Bool.not_eq_true] using
          (allFalse ⟨child, childMember⟩ (by simp))
      exact ih child childMember childFalse nameMember

theorem contains_variables_eq_occurs (source : String)
    (target : PersistentSubst.PreparedAtom) (valid : target.Valid) :
    target.variables.contains source =
      Metta.Subst.occurs source target.atom := by
  rw [valid.variables_eq]
  by_cases member : source ∈ target.atom.vars
  · have contained : target.atom.vars.contains source = true := by
      simpa using member
    have occursTrue : Metta.Subst.occurs source target.atom = true := by
      cases occursResult : Metta.Subst.occurs source target.atom with
      | false =>
          exfalso
          exact not_mem_vars_of_occurs_eq_false source target.atom
            occursResult member
      | true => rfl
    exact contained.trans occursTrue.symm
  · have contained : target.atom.vars.contains source = false := by
      simpa using member
    have occursFalse := occurs_eq_false_of_not_mem_vars source target.atom
      member
    exact contained.trans occursFalse.symm

theorem unifyRounds_erase :
    ∀ (fuel : Nat) (equations : Equations)
      (generated : PersistentSubst.PreparedAtom.PreparedSubst),
      EquationsValid equations → generated.Valid →
      (unifyRounds fuel equations generated).map
          PersistentSubst.PreparedAtom.eraseSubst =
        Metta.Unify.unifyRounds fuel (eraseEquations equations)
          (PersistentSubst.PreparedAtom.eraseSubst generated) := by
  intro fuel
  induction fuel with
  | zero =>
      intro equations generated equationsValid generatedValid
      have decomposed := decomposeAll_erase equations equationsValid
      unfold PreparedUnify.unifyRounds Metta.Unify.unifyRounds
      cases preparedResult : decomposeAll equations with
      | none =>
          simp only [preparedResult, Option.map_none] at decomposed
          rw [← decomposed]
          simp
      | some constraints =>
          simp only [preparedResult, Option.map_some] at decomposed
          rw [← decomposed]
          cases constraints <;> rfl
  | succ fuel ih =>
      intro equations generated equationsValid generatedValid
      have decomposed := decomposeAll_erase equations equationsValid
      unfold PreparedUnify.unifyRounds Metta.Unify.unifyRounds
      cases preparedResult : decomposeAll equations with
      | none =>
          simp only [preparedResult, Option.map_none] at decomposed
          rw [← decomposed]
          simp
      | some constraints =>
          simp only [preparedResult, Option.map_some] at decomposed
          rw [← decomposed]
          cases constraints with
          | nil => rfl
          | cons binding rest =>
              rcases binding with ⟨source, target⟩
              have sound := decomposeAll_sound equations equationsValid
                ((source, target) :: rest) preparedResult
              have targetValid : target.Valid :=
                sound.2 (source, target) (by simp)
              have restValid : ConstraintsValid rest :=
                fun constraint member => sound.2 constraint (by simp [member])
              have occursEqual := contains_variables_eq_occurs source target
                targetValid
              cases cachedOccurs : target.variables.contains source with
              | true =>
                  have rawOccurs :
                      Metta.Subst.occurs source target.atom = true := by
                    rw [← occursEqual]
                    exact cachedOccurs
                  have sourceMember : source ∈ target.variables := by
                    simpa using cachedOccurs
                  simp [sourceMember, rawOccurs, eraseConstraints]
              | false =>
                  have rawOccurs :
                      Metta.Subst.occurs source target.atom = false := by
                    rw [← occursEqual]
                    exact cachedOccurs
                  have sourceAbsent : source ∉ target.variables := by
                    simpa using cachedOccurs
                  have nextValid := nextEquations_valid source target rest
                    targetValid restValid
                  have extendedValid := extendPrepared_valid generated
                    generatedValid source target targetValid
                  have recursive := ih
                    ((constraintEquationsPrepared rest).map
                      (applyOneEquation source target))
                    (extendPrepared generated source target) nextValid
                    extendedValid
                  rw [nextEquations_erase source target rest restValid,
                    extendPrepared_erase generated source target] at recursive
                  simpa [sourceAbsent, rawOccurs, eraseConstraints]
                    using recursive

theorem unifyRounds_valid :
    ∀ (fuel : Nat) (equations : Equations)
      (generated result : PersistentSubst.PreparedAtom.PreparedSubst),
      EquationsValid equations → generated.Valid →
      unifyRounds fuel equations generated = some result →
      result.Valid := by
  intro fuel
  induction fuel with
  | zero =>
      intro equations generated result equationsValid generatedValid unified
      unfold PreparedUnify.unifyRounds at unified
      cases decomposed : decomposeAll equations with
      | none => simp [decomposed] at unified
      | some constraints =>
          cases constraints with
          | nil =>
              simp only [decomposed, Option.some.injEq] at unified
              subst result
              exact generatedValid
          | cons binding rest => simp [decomposed] at unified
  | succ fuel ih =>
      intro equations generated result equationsValid generatedValid unified
      unfold PreparedUnify.unifyRounds at unified
      cases decomposed : decomposeAll equations with
      | none => simp [decomposed] at unified
      | some constraints =>
          cases constraints with
          | nil =>
              simp only [decomposed, Option.some.injEq] at unified
              subst result
              exact generatedValid
          | cons binding rest =>
              rcases binding with ⟨source, target⟩
              have sound := decomposeAll_sound equations equationsValid
                ((source, target) :: rest) decomposed
              have targetValid : target.Valid :=
                sound.2 (source, target) (by simp)
              have restValid : ConstraintsValid rest :=
                fun constraint member => sound.2 constraint (by simp [member])
              by_cases sourceMember : source ∈ target.variables
              · simp [decomposed, sourceMember] at unified
              · have cachedFalse :
                    target.variables.contains source = false := by
                  simpa using sourceMember
                simp only [decomposed, cachedFalse, Bool.false_eq_true,
                  if_false] at unified
                exact ih
                  ((constraintEquationsPrepared rest).map
                    (applyOneEquation source target))
                  (extendPrepared generated source target) result
                  (nextEquations_valid source target rest targetValid restValid)
                  (extendPrepared_valid generated generatedValid source target
                    targetValid)
                  unified

theorem unifyTopGeneral_erase (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    (unifyTopGeneral left right).map
        PersistentSubst.PreparedAtom.eraseSubst =
      Metta.Unify.unifyTop left.atom right.atom := by
  unfold unifyTopGeneral Metta.Unify.unifyTop
  apply unifyRounds_erase
  · intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst equation
    exact ⟨leftValid, rightValid⟩
  · intro binding member
    simp at member

theorem unifyTopGeneral_valid (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid)
    (result : PersistentSubst.PreparedAtom.PreparedSubst)
    (unified : unifyTopGeneral left right = some result) :
    result.Valid := by
  unfold unifyTopGeneral at unified
  apply unifyRounds_valid (left.atom.size + right.atom.size) [(left, right)]
    [] result
  · intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst equation
    exact ⟨leftValid, rightValid⟩
  · intro binding member
    simp at member
  · exact unified

theorem eliminationOrdered_sound (constraints : Constraints)
    (valid : ConstraintsValid constraints)
    (checked : eliminationOrdered constraints = true) :
    RawEliminationOrdered (eraseConstraints constraints) := by
  induction constraints with
  | nil => trivial
  | cons entry rest ih =>
      rcases entry with ⟨source, target⟩
      have targetValid : target.Valid := valid (source, target) (by simp)
      have restValid : ConstraintsValid rest :=
        fun constraint member => valid constraint (by simp [member])
      have parts :
          ((source ∉ target.variables ∧
            (∀ constraint ∈ rest,
              source ∉ constraint.2.variables)) ∧
            source ∉ rest.map Prod.fst) ∧
          eliminationOrdered rest = true := by
        simpa [eliminationOrdered, Bool.and_eq_true] using checked
      simp only [eraseConstraints, List.map_cons, RawEliminationOrdered]
      constructor
      · rw [← targetValid.variables_eq]
        exact parts.1.1.1
      constructor
      · intro constraint member
        simp only [List.mem_map] at member
        rcases member with ⟨prepared, preparedMember, rfl⟩
        have preparedValid := restValid prepared preparedMember
        rw [← preparedValid.variables_eq]
        exact parts.1.1.2 prepared preparedMember
      constructor
      · simpa [eraseConstraints, List.map_map, Function.comp_def]
          using parts.1.2
      · exact ih restValid parts.2

end PreparedUnify

mutual
def atomAvoidsNames (names : List String) : Atom → Bool
  | .var name => !names.contains name
  | .expr atoms => atomsAvoidNames names atoms
  | _ => true
termination_by atom => 2 * atom.size
decreasing_by
  simp [Atom.size]
  omega

def atomsAvoidNames (names : List String) : List Atom → Bool
  | [] => true
  | atom :: rest => atomAvoidsNames names atom && atomsAvoidNames names rest
termination_by atoms => 2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals
    simp only [List.map_cons, List.sum_cons]
    have hsize : 0 < atom.size := by
      cases atom <;> simp [Atom.size]
    omega
end

/-- Independent constraints have distinct source names and no target refers
to any source name in the same elimination batch. -/
def IndependentConstraints (constraints : List (String × Atom)) : Prop :=
  (∀ constraint ∈ constraints, ∀ name ∈ constraints.map Prod.fst,
    name ∉ constraint.2.vars) ∧
  (constraints.map Prod.fst).Nodup

def independentConstraints (constraints : List (String × Atom)) : Bool :=
  let names := constraints.map Prod.fst
  constraints.all (fun constraint => atomAvoidsNames names constraint.2) &&
    decide names.Nodup

private theorem atomAvoidsNames_of_mem (names : List String)
    (atoms : List Atom) (avoids : atomsAvoidNames names atoms = true) :
    ∀ atom ∈ atoms, atomAvoidsNames names atom = true := by
  induction atoms with
  | nil => simp
  | cons head tail ih =>
      simp only [atomsAvoidNames, Bool.and_eq_true] at avoids
      intro atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact avoids.1
      · exact ih avoids.2 atom member

private theorem atomAvoidsNames_not_mem_vars (names : List String)
    (atom : Atom) (avoids : atomAvoidsNames names atom = true) :
    ∀ name ∈ names, name ∉ atom.vars := by
  induction atom with
  | sym symbol => simp [Atom.vars]
  | var source =>
      have sourceAbsent : source ∉ names := by
        simpa [atomAvoidsNames] using avoids
      intro name member
      have different : name ≠ source := by
        intro equality
        apply sourceAbsent
        simpa [equality] using member
      simpa [Atom.vars] using different
  | gnd ground => simp [Atom.vars]
  | expr atoms ih =>
      have atomsAvoid : atomsAvoidNames names atoms = true := by
        simpa only [atomAvoidsNames] using avoids
      intro name member present
      simp only [Atom.vars, List.mem_flatten, List.mem_map] at present
      rcases present with ⟨vars, ⟨child, childMember, rfl⟩, nameMember⟩
      exact ih child childMember
        (atomAvoidsNames_of_mem names atoms atomsAvoid child childMember)
        name member nameMember

theorem independentConstraints_sound (constraints : List (String × Atom))
    (checked : independentConstraints constraints = true) :
    IndependentConstraints constraints := by
  have parts :
      constraints.all (fun constraint =>
          atomAvoidsNames (constraints.map Prod.fst) constraint.2) = true ∧
        decide (constraints.map Prod.fst).Nodup = true := by
    simpa [independentConstraints, Bool.and_eq_true] using checked
  constructor
  · intro constraint member name nameMember
    exact atomAvoidsNames_not_mem_vars (constraints.map Prod.fst)
      constraint.2 (List.all_eq_true.mp parts.1 constraint member)
      name nameMember
  · exact of_decide_eq_true parts.2

theorem PreparedUnify.independent_sound (constraints : Constraints)
    (valid : ConstraintsValid constraints)
    (checked : independent constraints = true) :
    IndependentConstraints (eraseConstraints constraints) := by
  have parts :
      constraints.all (fun constraint =>
          constraint.2.variables.all fun name =>
            !(constraints.map Prod.fst).contains name) = true ∧
        decide (constraints.map Prod.fst).Nodup = true := by
    simpa [independent, Bool.and_eq_true] using checked
  have namesEq :
      (eraseConstraints constraints).map Prod.fst =
        constraints.map Prod.fst := by
    simp [eraseConstraints, List.map_map, Function.comp_def]
  constructor
  · intro erased erasedMember name nameMember targetMember
    simp only [eraseConstraints, List.mem_map] at erasedMember
    rcases erasedMember with ⟨constraint, constraintMember, rfl⟩
    have constraintValid := valid constraint constraintMember
    have variableMember : name ∈ constraint.2.variables := by
      rw [constraintValid.variables_eq]
      exact targetMember
    have avoids := List.all_eq_true.mp
      (List.all_eq_true.mp parts.1 constraint constraintMember)
      name variableMember
    have absent : name ∉ constraints.map Prod.fst := by
      simpa using avoids
    rw [namesEq] at nameMember
    exact absent nameMember
  · rw [namesEq]
    exact of_decide_eq_true parts.2

private def constraintEquations
    (constraints : List (String × Atom)) : List (Atom × Atom) :=
  constraints.map fun constraint =>
    (Atom.var constraint.1, constraint.2)

private theorem decomposeList_length_le_of_each (left : List Atom)
    (each : ∀ atom ∈ left, ∀ right constraints,
      Metta.Unify.decomposeEq atom right = some constraints →
        constraints.length ≤ atom.size) :
    ∀ right constraints,
      Metta.Unify.decomposeList left right = some constraints →
        constraints.length ≤ (left.map Atom.size).sum := by
  induction left with
  | nil =>
      intro right constraints decomposed
      cases right with
      | nil =>
          simp [Metta.Unify.decomposeList] at decomposed
          subst constraints
          simp
      | cons head tail =>
          simp [Metta.Unify.decomposeList] at decomposed
  | cons head tail ih =>
      intro right constraints decomposed
      cases right with
      | nil => simp [Metta.Unify.decomposeList] at decomposed
      | cons rightHead rightTail =>
          simp only [Metta.Unify.decomposeList] at decomposed
          cases headResult : Metta.Unify.decomposeEq head rightHead with
          | none => simp [headResult] at decomposed
          | some headConstraints =>
              cases tailResult :
                  Metta.Unify.decomposeList tail rightTail with
              | none => simp [headResult, tailResult] at decomposed
              | some tailConstraints =>
                  simp only [headResult, tailResult, Option.some.injEq]
                    at decomposed
                  subst constraints
                  have headBound := each head (by simp) rightHead
                    headConstraints headResult
                  have tailEach : ∀ atom ∈ tail, ∀ right constraints,
                      Metta.Unify.decomposeEq atom right = some constraints →
                        constraints.length ≤ atom.size := by
                    intro atom member
                    exact each atom (by simp [member])
                  have tailBound := ih tailEach rightTail tailConstraints
                    tailResult
                  simp only [List.length_append, List.map_cons,
                    List.sum_cons]
                  omega

private theorem decomposeEq_length_le_left (left : Atom) :
    ∀ right constraints,
      Metta.Unify.decomposeEq left right = some constraints →
        constraints.length ≤ left.size := by
  induction left with
  | sym symbol =>
      intro right constraints decomposed
      cases right with
      | sym other =>
          simp [Metta.Unify.decomposeEq] at decomposed
          rcases decomposed with ⟨_, rfl⟩
          simp [Atom.size]
      | var name =>
          simp [Metta.Unify.decomposeEq] at decomposed
          subst constraints
          simp [Atom.size]
      | gnd ground => simp [Metta.Unify.decomposeEq] at decomposed
      | expr atoms => simp [Metta.Unify.decomposeEq] at decomposed
  | var name =>
      intro right constraints decomposed
      cases right with
      | sym symbol | gnd ground | expr atoms =>
          simp [Metta.Unify.decomposeEq] at decomposed
          subst constraints
          simp [Atom.size]
      | var source =>
          by_cases equal : name = source
          · simp [Metta.Unify.decomposeEq, equal] at decomposed
            subst constraints
            simp [Atom.size]
          · simp [Metta.Unify.decomposeEq, equal] at decomposed
            subst constraints
            simp [Atom.size]
  | gnd ground =>
      intro right constraints decomposed
      cases right with
      | sym symbol => simp [Metta.Unify.decomposeEq] at decomposed
      | var name =>
          simp [Metta.Unify.decomposeEq] at decomposed
          subst constraints
          simp [Atom.size]
      | gnd other =>
          simp [Metta.Unify.decomposeEq] at decomposed
          rcases decomposed with ⟨_, rfl⟩
          simp [Atom.size]
      | expr atoms => simp [Metta.Unify.decomposeEq] at decomposed
  | expr atoms ih =>
      intro right constraints decomposed
      cases right with
      | sym symbol => simp [Metta.Unify.decomposeEq] at decomposed
      | var name =>
          simp [Metta.Unify.decomposeEq] at decomposed
          subst constraints
          simp [Atom.size]
      | gnd ground => simp [Metta.Unify.decomposeEq] at decomposed
      | expr rightAtoms =>
          have listBound := decomposeList_length_le_of_each atoms ih
            rightAtoms constraints decomposed
          simp only [Atom.size]
          omega

/-- Unification fast paths for zero or one constraint and for any number of
independent closed constraints. The general unifier would traverse both input
atoms to manufacture fuel and then repeatedly rebuild already-ground targets. -/
def unifyTopFast (left right : Atom) : Option Subst :=
  match Metta.Unify.decomposeEq left right with
  | none => none
  | some [] => some []
  | some [(name, target)] =>
      if Metta.Subst.occurs name target then none
      else some [(name, target)]
  | some (first :: second :: rest) =>
      let constraints := first :: second :: rest
      if independentConstraints constraints then
        some constraints.reverse
      else
        Metta.Unify.unifyTop left right

private theorem atomSizeSum_ne_zero (left right : Atom) :
    left.size + right.size ≠ 0 := by
  cases left <;> simp only [Atom.size] <;> omega

private theorem atomSizeSum_two_le (left right : Atom) :
    2 ≤ left.size + right.size := by
  have hleft : 1 ≤ left.size := by
    cases left <;> simp only [Atom.size] <;> omega
  have hright : 1 ≤ right.size := by
    cases right <;> simp only [Atom.size] <;> omega
  omega

private theorem occurs_eq_false_of_atomClosed (name : String) (atom : Atom)
    (closed : PersistentSubst.atomClosed atom = true) :
    Metta.Subst.occurs name atom = false := by
  apply occurs_eq_false_of_not_mem_vars name atom
  rw [(PersistentSubst.atomClosed_eq_true_iff_vars_nil atom).mp closed]
  simp

private theorem decomposeEq_var_of_atomClosed (name : String) (atom : Atom)
    (closed : PersistentSubst.atomClosed atom = true) :
    Metta.Unify.decomposeEq (Atom.var name) atom = some [(name, atom)] := by
  cases atom with
  | sym symbol => simp [Metta.Unify.decomposeEq]
  | var source => simp [PersistentSubst.atomClosed] at closed
  | gnd ground => simp [Metta.Unify.decomposeEq]
  | expr atoms => simp [Metta.Unify.decomposeEq]

private theorem decomposeEq_var_of_not_mem_vars (name : String) (atom : Atom)
    (absent : name ∉ atom.vars) :
    Metta.Unify.decomposeEq (Atom.var name) atom = some [(name, atom)] := by
  cases atom with
  | sym symbol => simp [Metta.Unify.decomposeEq]
  | var source =>
      have different : name ≠ source := by
        simpa [Atom.vars] using absent
      simp [Metta.Unify.decomposeEq, different]
  | gnd ground => simp [Metta.Unify.decomposeEq]
  | expr atoms => simp [Metta.Unify.decomposeEq]

private theorem substApply_of_vars_nil (subst : Subst) :
    ∀ atom : Atom, atom.vars = [] → Metta.Subst.apply subst atom = atom := by
  intro atom
  induction atom with
  | var name => intro closed; simp [Atom.vars] at closed
  | expr atoms ih =>
      intro closed
      simp only [Atom.vars] at closed
      rw [List.flatten_eq_nil_iff] at closed
      simp only [Metta.Subst.apply]
      have hchildren : ∀ child ∈ atoms,
          Metta.Subst.apply subst child = child := fun child member =>
        ih child member
          (closed (Atom.vars child) (List.mem_map_of_mem member))
      rw [List.map_congr_left hchildren]
      simp
  | _ => intro _; simp [Metta.Subst.apply]

private theorem substErase_eq_self_of_name_not_mem (entries : Subst)
    (name : String) (absent : name ∉ entries.map Prod.fst) :
    Metta.Subst.erase entries name = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      have keep : (key != name) = true := by
        simp [Ne.symm absent.1]
      simp only [Metta.Subst.erase, List.filter_cons, keep, if_true]
      congr 1
      exact ih absent.2

private theorem decomposeAll_constraintEquations
    (constraints : List (String × Atom))
    (independent : ∀ constraint ∈ constraints,
      constraint.1 ∉ constraint.2.vars) :
    Metta.Unify.decomposeAll (constraintEquations constraints) =
      some constraints := by
  induction constraints with
  | nil => rfl
  | cons constraint rest ih =>
      rcases constraint with ⟨name, target⟩
      have headIndependent := independent (name, target) (by simp)
      have tailIndependent : ∀ constraint ∈ rest,
          constraint.1 ∉ constraint.2.vars := by
        intro constraint member
        exact independent constraint (by simp [member])
      simp only [constraintEquations, List.map_cons,
        Metta.Unify.decomposeAll]
      rw [decomposeEq_var_of_not_mem_vars name target headIndependent]
      have tailDecomposed :
          Metta.Unify.decomposeAll
              (rest.map fun constraint =>
                (Atom.var constraint.1, constraint.2)) = some rest := by
        simpa [constraintEquations] using ih tailIndependent
      rw [tailDecomposed]
      rfl

private theorem mapIndependentConstraints_eq_constraintEquations
    (name : String) (target : Atom)
    (constraints : List (String × Atom))
    (independent : ∀ constraint ∈ constraints,
      name ∉ constraint.2.vars)
    (fresh : name ∉ constraints.map Prod.fst) :
    constraints.map (fun constraint =>
        (Metta.Subst.apply [(name, target)] (Atom.var constraint.1),
          Metta.Subst.apply [(name, target)] constraint.2)) =
      constraintEquations constraints := by
  unfold constraintEquations
  apply List.map_congr_left
  intro constraint member
  rcases constraint with ⟨source, value⟩
  have sourceMember : source ∈ constraints.map Prod.fst := by
    exact List.mem_map_of_mem member
  have sourceNe : source ≠ name := by
    intro equality
    apply fresh
    simpa [equality] using sourceMember
  have valueFixed : Metta.Subst.apply [(name, target)] value = value := by
    exact apply_singleton_eq_self_of_not_mem name target value
      (independent (source, value) member)
  change
    (Metta.Subst.apply [(name, target)] (Atom.var source),
        Metta.Subst.apply [(name, target)] value) =
      (Atom.var source, value)
  rw [valueFixed]
  simp [Metta.Subst.apply, Metta.Subst.lookup, sourceNe]

private theorem unifyRounds_independent
    (constraints : List (String × Atom)) :
    ∀ (fuel : Nat) (equations : List (Atom × Atom))
      (generated : Subst),
      Metta.Unify.decomposeAll equations = some constraints →
      IndependentConstraints constraints →
      (∀ name ∈ constraints.map Prod.fst,
        name ∉ generated.map Prod.fst) →
      constraints.length ≤ fuel →
      Metta.Unify.unifyRounds fuel equations generated =
        some (constraints.reverse ++ generated) := by
  induction constraints with
  | nil =>
      intro fuel equations generated decomposed _ _ _
      cases fuel <;>
        simp [Metta.Unify.unifyRounds, decomposed]
  | cons constraint rest ih =>
      intro fuel equations generated decomposed independent disjoint bound
      rcases constraint with ⟨name, target⟩
      have headIndependent : name ∉ target.vars :=
        independent.1 (name, target) (by simp) name (by simp)
      have tailIndependent : IndependentConstraints rest := by
        constructor
        · intro constraint member source sourceMember
          exact independent.1 constraint (by simp [member]) source
            (by simp [sourceMember])
        · have namesNodup : (name :: rest.map Prod.fst).Nodup := by
            simpa using independent.2
          exact (List.nodup_cons.mp namesNodup).2
      have namesNodup : (name :: rest.map Prod.fst).Nodup := by
        simpa using independent.2
      have nameFreshTail := (List.nodup_cons.mp namesNodup).1
      cases fuel with
      | zero => simp at bound
      | succ fuel =>
          have occursFalse := occurs_eq_false_of_not_mem_vars name target
            headIndependent
          have tailAvoidsName : ∀ constraint ∈ rest,
              name ∉ constraint.2.vars := by
            intro constraint member
            exact independent.1 constraint (by simp [member]) name (by simp)
          have mapped := mapIndependentConstraints_eq_constraintEquations
            name target rest tailAvoidsName nameFreshTail
          have nameFreshGenerated : name ∉ generated.map Prod.fst := by
            exact disjoint name (by simp)
          have extendEq :
              Metta.Subst.extend generated name target =
                (name, target) :: generated := by
            simp [Metta.Subst.extend,
              substErase_eq_self_of_name_not_mem generated name
                nameFreshGenerated]
          have tailDisjoint : ∀ source ∈ rest.map Prod.fst,
              source ∉ ((name, target) :: generated).map Prod.fst := by
            intro source sourceMember
            have sourceNe : source ≠ name := by
              intro equality
              apply nameFreshTail
              simpa [equality] using sourceMember
            have sourceFreshGenerated := disjoint source (by
              simp [sourceMember])
            simpa [sourceNe] using sourceFreshGenerated
          have tailBound : rest.length ≤ fuel := by
            simp only [List.length_cons] at bound
            omega
          have tailDecomposed := decomposeAll_constraintEquations rest (by
            intro constraint member
            exact tailIndependent.1 constraint member constraint.1
              (List.mem_map_of_mem member))
          have tailResult := ih fuel (constraintEquations rest)
            ((name, target) :: generated) tailDecomposed
            tailIndependent tailDisjoint tailBound
          simp only [Metta.Unify.unifyRounds, decomposed, occursFalse,
            Bool.false_eq_true, if_false]
          rw [mapped, extendEq, tailResult]
          simp [List.reverse_cons, List.append_assoc]

private theorem eliminationOrdered_selfAbsent
    (constraints : List (String × Atom))
    (ordered : PreparedUnify.RawEliminationOrdered constraints) :
    ∀ constraint ∈ constraints, constraint.1 ∉ constraint.2.vars := by
  induction constraints with
  | nil => simp
  | cons entry rest ih =>
      rcases entry with ⟨source, target⟩
      intro constraint member
      rcases List.mem_cons.mp member with rfl | member
      · exact ordered.1
      · exact ih ordered.2.2.2 constraint member

private theorem unifyRounds_eliminationOrdered
    (constraints : List (String × Atom)) :
    ∀ (fuel : Nat) (equations : List (Atom × Atom))
      (generated : Subst),
      Metta.Unify.decomposeAll equations = some constraints →
      PreparedUnify.RawEliminationOrdered constraints →
      (∀ name ∈ constraints.map Prod.fst,
        name ∉ generated.map Prod.fst) →
      constraints.length ≤ fuel →
      Metta.Unify.unifyRounds fuel equations generated =
        some (constraints.reverse ++ generated) := by
  induction constraints with
  | nil =>
      intro fuel equations generated decomposed _ _ _
      cases fuel <;>
        simp [Metta.Unify.unifyRounds, decomposed]
  | cons constraint rest ih =>
      intro fuel equations generated decomposed ordered disjoint bound
      rcases constraint with ⟨name, target⟩
      have headIndependent : name ∉ target.vars := ordered.1
      have tailAvoidsName : ∀ constraint ∈ rest,
          name ∉ constraint.2.vars := ordered.2.1
      have nameFreshTail : name ∉ rest.map Prod.fst := ordered.2.2.1
      have tailOrdered :
          PreparedUnify.RawEliminationOrdered rest := ordered.2.2.2
      cases fuel with
      | zero => simp at bound
      | succ fuel =>
          have occursFalse := occurs_eq_false_of_not_mem_vars name target
            headIndependent
          have mapped := mapIndependentConstraints_eq_constraintEquations
            name target rest tailAvoidsName nameFreshTail
          have nameFreshGenerated : name ∉ generated.map Prod.fst := by
            exact disjoint name (by simp)
          have extendEq :
              Metta.Subst.extend generated name target =
                (name, target) :: generated := by
            simp [Metta.Subst.extend,
              substErase_eq_self_of_name_not_mem generated name
                nameFreshGenerated]
          have tailDisjoint : ∀ source ∈ rest.map Prod.fst,
              source ∉ ((name, target) :: generated).map Prod.fst := by
            intro source sourceMember
            have sourceNe : source ≠ name := by
              intro equality
              apply nameFreshTail
              simpa [equality] using sourceMember
            have sourceFreshGenerated := disjoint source (by
              simp [sourceMember])
            simpa [sourceNe] using sourceFreshGenerated
          have tailBound : rest.length ≤ fuel := by
            simp only [List.length_cons] at bound
            omega
          have tailDecomposed := decomposeAll_constraintEquations rest
            (eliminationOrdered_selfAbsent rest tailOrdered)
          have tailResult := ih fuel (constraintEquations rest)
            ((name, target) :: generated) tailDecomposed tailOrdered
            tailDisjoint tailBound
          simp only [Metta.Unify.unifyRounds, decomposed, occursFalse,
            Bool.false_eq_true, if_false]
          rw [mapped, extendEq, tailResult]
          simp [List.reverse_cons, List.append_assoc]

/-- The single-constraint shortcut is extensionally the reference unifier. -/
theorem unifyTopFast_eq (left right : Atom) :
    unifyTopFast left right = Metta.Unify.unifyTop left right := by
  cases hdecompose : Metta.Unify.decomposeEq left right with
  | none =>
      obtain ⟨fuel, hfuel⟩ :=
        Nat.exists_eq_succ_of_ne_zero (atomSizeSum_ne_zero left right)
      simp [unifyTopFast, hdecompose, Metta.Unify.unifyTop, hfuel,
        Metta.Unify.unifyRounds, Metta.Unify.decomposeAll]
  | some constraints =>
      cases constraints with
      | nil =>
          obtain ⟨fuel, hfuel⟩ :=
            Nat.exists_eq_succ_of_ne_zero (atomSizeSum_ne_zero left right)
          simp [unifyTopFast, hdecompose, Metta.Unify.unifyTop, hfuel,
            Metta.Unify.unifyRounds, Metta.Unify.decomposeAll]
      | cons binding rest =>
          cases rest with
          | nil =>
              rcases binding with ⟨name, target⟩
              obtain ⟨fuel, hfuel⟩ :=
                Nat.exists_eq_succ_of_ne_zero
                  (atomSizeSum_ne_zero left right)
              simp only [unifyTopFast, hdecompose, Metta.Unify.unifyTop,
                hfuel, Metta.Unify.unifyRounds,
                Metta.Unify.decomposeAll, List.append_nil]
              by_cases hoccurs : Metta.Subst.occurs name target
              · simp [hoccurs]
              · simp only [hoccurs, Bool.false_eq_true, ↓reduceIte]
                cases fuel <;> rfl
          | cons next tail =>
              let constraintsBatch := binding :: next :: tail
              cases fast : independentConstraints constraintsBatch with
              | false =>
                  simp only [unifyTopFast, hdecompose]
                  have notFast : ¬ independentConstraints constraintsBatch =
                      true := by
                    intro equality
                    rw [fast] at equality
                    contradiction
                  rw [if_neg notFast]
              | true =>
                  have independent :
                      IndependentConstraints constraintsBatch :=
                    independentConstraints_sound constraintsBatch fast
                  have leftBound : constraintsBatch.length ≤ left.size :=
                    decomposeEq_length_le_left left right constraintsBatch
                      hdecompose
                  have lengthBound : constraintsBatch.length ≤
                      left.size + right.size := by
                    omega
                  have decomposed :
                      Metta.Unify.decomposeAll [(left, right)] =
                        some constraintsBatch := by
                    simp [Metta.Unify.decomposeAll, hdecompose,
                      constraintsBatch]
                  have result := unifyRounds_independent
                    constraintsBatch (left.size + right.size)
                    [(left, right)] [] decomposed independent (by simp)
                    lengthBound
                  have unified : Metta.Unify.unifyTop left right =
                      some constraintsBatch.reverse := by
                    unfold Metta.Unify.unifyTop
                    simpa using result
                  simp [unifyTopFast, hdecompose, unified,
                    constraintsBatch]

/-- Prepared unification consumes variable summaries assembled by
substitution.  It accelerates elimination-ordered multi-binding applications
and falls back to the verified raw unifier for every other shape. -/
def unifyTopPrepared (left right : PersistentSubst.PreparedAtom) :
    Option Subst :=
  match PreparedUnify.decompose left right with
  | some [] => some []
  | some [(name, target)] =>
      if !target.variables.contains name then
        some [(name, target.atom)]
      else
        unifyTopFast left.atom right.atom
  | some (first :: second :: rest) =>
      let constraints := first :: second :: rest
      if PreparedUnify.eliminationOrdered constraints then
        some (PreparedUnify.eraseConstraints constraints.reverse)
      else
        unifyTopFast left.atom right.atom
  | _ => unifyTopFast left.atom right.atom

theorem unifyTopPrepared_eq (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    unifyTopPrepared left right =
      Metta.Unify.unifyTop left.atom right.atom := by
  cases hdecompose : PreparedUnify.decompose left right with
  | none =>
      simp [unifyTopPrepared, hdecompose, unifyTopFast_eq]
  | some constraints =>
      cases constraints with
      | nil =>
          have sound := PreparedUnify.decompose_sound left right leftValid
            rightValid [] hdecompose
          have raw : Metta.Unify.decomposeEq left.atom right.atom =
              some [] := by
            simpa [PreparedUnify.eraseConstraints] using sound.1
          have fast : unifyTopFast left.atom right.atom = some [] := by
            simp [unifyTopFast, raw]
          rw [← unifyTopFast_eq]
          unfold unifyTopPrepared
          rw [hdecompose]
          exact fast.symm
      | cons first rest =>
          cases rest with
          | nil =>
              rcases first with ⟨name, target⟩
              cases checked : !target.variables.contains name with
              | false =>
                  unfold unifyTopPrepared
                  rw [hdecompose]
                  change
                    (if !target.variables.contains name then
                      some [(name, target.atom)]
                    else unifyTopFast left.atom right.atom) =
                      Metta.Unify.unifyTop left.atom right.atom
                  rw [checked]
                  exact unifyTopFast_eq left.atom right.atom
              | true =>
                  have sound := PreparedUnify.decompose_sound left right
                    leftValid rightValid [(name, target)] hdecompose
                  have targetValid : target.Valid :=
                    sound.2 (name, target) (by simp)
                  have absent : name ∉ target.atom.vars := by
                    rw [← targetValid.variables_eq]
                    simpa using checked
                  have occursFalse := occurs_eq_false_of_not_mem_vars name
                    target.atom absent
                  have raw : Metta.Unify.decomposeEq left.atom right.atom =
                      some [(name, target.atom)] := by
                    simpa [PreparedUnify.eraseConstraints] using sound.1
                  have fast : unifyTopFast left.atom right.atom =
                      some [(name, target.atom)] := by
                    simp [unifyTopFast, raw, occursFalse]
                  rw [← unifyTopFast_eq]
                  unfold unifyTopPrepared
                  rw [hdecompose]
                  change
                    (if !target.variables.contains name then
                      some [(name, target.atom)]
                    else unifyTopFast left.atom right.atom) =
                      unifyTopFast left.atom right.atom
                  rw [checked]
                  exact fast.symm
          | cons second rest =>
              let constraints := first :: second :: rest
              cases checked : PreparedUnify.eliminationOrdered constraints with
              | false =>
                  simp [unifyTopPrepared, hdecompose, constraints, checked,
                    unifyTopFast_eq]
              | true =>
                  have sound := PreparedUnify.decompose_sound left right
                    leftValid rightValid constraints (by
                      simpa [constraints] using hdecompose)
                  have ordered : PreparedUnify.RawEliminationOrdered
                      (PreparedUnify.eraseConstraints constraints) :=
                    PreparedUnify.eliminationOrdered_sound constraints
                      sound.2 checked
                  have leftBound :
                      (PreparedUnify.eraseConstraints constraints).length ≤
                        left.atom.size :=
                    decomposeEq_length_le_left left.atom right.atom
                      (PreparedUnify.eraseConstraints constraints) sound.1
                  have lengthBound :
                      (PreparedUnify.eraseConstraints constraints).length ≤
                        left.atom.size + right.atom.size := by
                    omega
                  have decomposed :
                      Metta.Unify.decomposeAll [(left.atom, right.atom)] =
                        some (PreparedUnify.eraseConstraints constraints) := by
                    simp [Metta.Unify.decomposeAll, sound.1]
                  have result := unifyRounds_eliminationOrdered
                    (PreparedUnify.eraseConstraints constraints)
                    (left.atom.size + right.atom.size)
                    [(left.atom, right.atom)] [] decomposed ordered
                    (by simp) lengthBound
                  have unified :
                      Metta.Unify.unifyTop left.atom right.atom =
                        some
                          (PreparedUnify.eraseConstraints constraints).reverse := by
                    unfold Metta.Unify.unifyTop
                    simpa using result
                  have eraseReverse :
                      PreparedUnify.eraseConstraints constraints.reverse =
                        (PreparedUnify.eraseConstraints constraints).reverse := by
                    simp [PreparedUnify.eraseConstraints]
                  unfold unifyTopPrepared
                  rw [hdecompose]
                  change
                    (if PreparedUnify.eliminationOrdered constraints then
                      some (PreparedUnify.eraseConstraints
                        constraints.reverse)
                    else unifyTopFast left.atom right.atom) =
                      Metta.Unify.unifyTop left.atom right.atom
                  rw [checked]
                  simp only [if_true]
                  rw [eraseReverse, unified]

/-- PeTTa-facing prepared unification retains the prepared fast path while
rejecting the integer/float constructor equivalence admitted by the shared
Hyperon unifier. -/
def unifyTopPreparedExact (left right : PersistentSubst.PreparedAtom) :
    Option Subst :=
  match unifyTopPrepared left right with
  | some generated =>
      if pettaUnifyCompatible (PLeaTTa.subst generated left.atom)
          (PLeaTTa.subst generated right.atom) then
        some generated
      else none
  | none => none

theorem unifyTopPreparedExact_eq
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    unifyTopPreparedExact left right =
      PLeaTTa.unifyTopExact left.atom right.atom := by
  unfold unifyTopPreparedExact PLeaTTa.unifyTopExact
  rw [unifyTopPrepared_eq left right leftValid rightValid]
  rfl

/-- A unifier batch distinguishes cached prepared constraints from the
verified raw fallback. -/
inductive PreparedUnify.Result where
  | raw (entries : Subst)
  | prepared (entries : Constraints)

def PreparedUnify.Result.erase : PreparedUnify.Result → Subst
  | .raw entries => entries
  | .prepared entries => eraseConstraints entries

def PreparedUnify.Result.Valid : PreparedUnify.Result → Prop
  | .raw _ => True
  | .prepared entries => ConstraintsValid entries

theorem PreparedUnify.constraintsValid_reverse (constraints : Constraints)
    (valid : ConstraintsValid constraints) :
    ConstraintsValid constraints.reverse := by
  intro constraint member
  exact valid constraint (List.mem_reverse.mp member)

/-- Preserve prepared constraints through both the fast paths and the general
elimination loop. -/
def unifyTopPreparedResult (left right : PersistentSubst.PreparedAtom) :
    Option PreparedUnify.Result :=
  match PreparedUnify.decompose left right with
  | some [] => some (.prepared [])
  | some [(name, target)] =>
      if !target.variables.contains name then
        some (.prepared [(name, target)])
      else
        (PreparedUnify.unifyTopGeneral left right).map .prepared
  | some (first :: second :: rest) =>
      let constraints := first :: second :: rest
      if PreparedUnify.eliminationOrdered constraints then
        some (.prepared constraints.reverse)
      else
        (PreparedUnify.unifyTopGeneral left right).map .prepared
  | _ => (PreparedUnify.unifyTopGeneral left right).map .prepared

theorem unifyTopPreparedResult_valid
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    ∀ result, unifyTopPreparedResult left right = some result →
      result.Valid := by
  intro result hresult
  cases hdecompose : PreparedUnify.decompose left right with
  | none =>
      cases hunify : PreparedUnify.unifyTopGeneral left right with
      | none =>
          simp [unifyTopPreparedResult, hdecompose, hunify] at hresult
      | some entries =>
          simp [unifyTopPreparedResult, hdecompose, hunify] at hresult
          subst result
          exact PreparedUnify.unifyTopGeneral_valid left right leftValid
            rightValid entries hunify
  | some constraints =>
      have sound := PreparedUnify.decompose_sound left right leftValid
        rightValid constraints hdecompose
      cases constraints with
      | nil =>
          simp [unifyTopPreparedResult, hdecompose] at hresult
          subst result
          exact sound.2
      | cons first rest =>
          cases rest with
          | nil =>
              rcases first with ⟨name, target⟩
              by_cases hmem : name ∈ target.variables
              · cases hunify : PreparedUnify.unifyTopGeneral left right with
                | none =>
                    simp [unifyTopPreparedResult, hdecompose, hmem, hunify]
                      at hresult
                | some entries =>
                    simp [unifyTopPreparedResult, hdecompose, hmem, hunify]
                      at hresult
                    subst result
                    exact PreparedUnify.unifyTopGeneral_valid left right
                      leftValid rightValid entries hunify
              · simp [unifyTopPreparedResult, hdecompose, hmem] at hresult
                subst result
                exact sound.2
          | cons second rest =>
              let constraints := first :: second :: rest
              cases hordered : PreparedUnify.eliminationOrdered constraints with
              | false =>
                  cases hunify : PreparedUnify.unifyTopGeneral left right with
                  | none =>
                      simp [unifyTopPreparedResult, hdecompose, constraints,
                        hordered, hunify] at hresult
                  | some entries =>
                      simp [unifyTopPreparedResult, hdecompose, constraints,
                        hordered, hunify] at hresult
                      subst result
                      exact PreparedUnify.unifyTopGeneral_valid left right
                        leftValid rightValid entries hunify
              | true =>
                  simp [unifyTopPreparedResult, hdecompose, constraints,
                    hordered] at hresult
                  subst result
                  have reverseValid :=
                    PreparedUnify.constraintsValid_reverse constraints (by
                      simpa [constraints] using sound.2)
                  simpa [PreparedUnify.Result.Valid, constraints] using
                    reverseValid

def unifyTopPreparedCertified
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    Option { result : PreparedUnify.Result // result.Valid } :=
  match equality : unifyTopPreparedResult left right with
  | none => none
  | some result =>
      some ⟨result, unifyTopPreparedResult_valid left right leftValid
        rightValid result equality⟩

theorem unifyTopPreparedCertified_value
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    (unifyTopPreparedCertified left right leftValid rightValid).map
        Subtype.val =
      unifyTopPreparedResult left right := by
  unfold unifyTopPreparedCertified
  split <;> simp_all

theorem unifyTopPreparedResult_erase
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    (unifyTopPreparedResult left right).map
        PreparedUnify.Result.erase =
      unifyTopPrepared left right := by
  have generalErased := PreparedUnify.unifyTopGeneral_erase left right
    leftValid rightValid
  have fallback :
      (PreparedUnify.unifyTopGeneral left right).map
          PreparedUnify.eraseConstraints =
        unifyTopFast left.atom right.atom :=
    generalErased.trans (unifyTopFast_eq left.atom right.atom).symm
  cases hdecompose : PreparedUnify.decompose left right with
  | none =>
      simpa [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
        PreparedUnify.Result.erase, Function.comp_def] using fallback
  | some constraints =>
      cases constraints with
      | nil =>
          simp [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
            PreparedUnify.Result.erase, PreparedUnify.eraseConstraints]
      | cons first rest =>
          cases rest with
          | nil =>
              rcases first with ⟨name, target⟩
              by_cases hmem : name ∈ target.variables
              · simpa [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
                  hmem, PreparedUnify.Result.erase,
                  Function.comp_def]
                  using fallback
              · simp [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
                  hmem, PreparedUnify.Result.erase,
                  PreparedUnify.eraseConstraints]
          | cons second rest =>
              cases hordered : PreparedUnify.eliminationOrdered
                  (first :: second :: rest) with
              | false =>
                  simpa [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
                    hordered, PreparedUnify.Result.erase,
                    Function.comp_def] using fallback
              | true =>
                  simp [unifyTopPreparedResult, unifyTopPrepared, hdecompose,
                    hordered, PreparedUnify.Result.erase]

/-- Shared engine-level unification. Both instances substitute operands in
the same order, invoke the same unifier, and differ only in representation
of the resulting composition. -/
def unifyB (engine : SubstEngine) (state : engine.State)
    (left right : Atom) : Option engine.State :=
  let leftResult := engine.substPrepared state left
  let rightResult := engine.substPrepared leftResult.2 right
  match unifyTopPreparedExact leftResult.1 rightResult.1 with
  | none => none
  | some [] => some rightResult.2
  | some generated => some (engine.compose rightResult.2 generated)

theorem unifyB_map_denote (engine : SubstEngine) (state : engine.State)
    (left right : Atom) (valid : engine.Valid state) :
    (engine.unifyB state left right).map engine.denote =
      PLeaTTa.unifyB (engine.denote state) left right := by
  have hleftValue := engine.substPrepared_value state left valid
  have hleftMetadata := engine.substPrepared_metadata state left valid
  have hleftValid := engine.substPrepared_valid state left valid
  have hleftDenote := engine.substPrepared_denote state left valid
  cases hleft : engine.substPrepared state left with
  | mk leftValue leftState =>
      simp only [hleft] at hleftValue hleftMetadata hleftValid hleftDenote
      have hrightValue := engine.substPrepared_value leftState right
        hleftValid
      have hrightMetadata := engine.substPrepared_metadata leftState right
        hleftValid
      have hrightValid := engine.substPrepared_valid leftState right
        hleftValid
      have hrightDenote := engine.substPrepared_denote leftState right
        hleftValid
      cases hright : engine.substPrepared leftState right with
      | mk rightValue rightState =>
          simp only [hright] at hrightValue hrightMetadata hrightValid hrightDenote
          unfold unifyB PLeaTTa.unifyB
          rw [hleft]
          dsimp only
          rw [hright]
          dsimp only
          rw [unifyTopPreparedExact_eq leftValue rightValue hleftMetadata
            hrightMetadata]
          rw [hleftValue, hrightValue, hleftDenote]
          cases hunify : PLeaTTa.unifyTopExact
              (PLeaTTa.subst (engine.denote state) left)
              (PLeaTTa.subst (engine.denote state) right) with
          | none => rfl
          | some generated =>
              cases generated with
              | nil => simp [hrightDenote, hleftDenote]
              | cons binding rest =>
                  simp [engine.compose_denote, hrightDenote, hleftDenote]

theorem unifyB_valid (engine : SubstEngine) (state : engine.State)
    (left right : Atom) (valid : engine.Valid state) :
    ∀ next, engine.unifyB state left right = some next →
      engine.Valid next := by
  intro next hnext
  have hleftValid := engine.substPrepared_valid state left valid
  cases hleft : engine.substPrepared state left with
  | mk leftValue leftState =>
      simp only [hleft] at hleftValid
      have hrightValid := engine.substPrepared_valid leftState right
        hleftValid
      cases hright : engine.substPrepared leftState right with
      | mk rightValue rightState =>
          simp only [hright] at hrightValid
          unfold unifyB at hnext
          rw [hleft] at hnext
          dsimp only at hnext
          rw [hright] at hnext
          dsimp only at hnext
          cases hunify : unifyTopPreparedExact leftValue rightValue with
          | none => simp [hunify] at hnext
          | some generated =>
              cases generated with
              | nil =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact hrightValid
              | cons binding rest =>
                  simp only [hunify, Option.some.injEq] at hnext
                  subst next
                  exact engine.compose_valid rightState (binding :: rest)
                    hrightValid

/-- Apply one raw unifier batch, treating the empty batch as the identity. -/
def composeRawResult (engine : SubstEngine) (state : engine.State) :
    Subst → engine.State
  | [] => state
  | binding :: rest => engine.compose state (binding :: rest)

/-- Compose one certified unifier result into a checked state. -/
def checkedComposeUnifierResult (engine : SubstEngine)
    (state : engine.State) (stateValid : engine.Valid state)
    (result : PreparedUnify.Result) (resultValid : result.Valid) :
    CheckedState engine :=
  match result with
  | .raw [] => ⟨state, stateValid⟩
  | .raw (binding :: rest) =>
      checkedCompose engine ⟨state, stateValid⟩ (binding :: rest)
  | .prepared [] => ⟨state, stateValid⟩
  | .prepared (binding :: rest) =>
      checkedComposePrepared engine ⟨state, stateValid⟩
        (binding :: rest) resultValid

def checkedUnifyPreparedValues (engine : SubstEngine)
    (state : engine.State) (stateValid : engine.Valid state)
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    Option (CheckedState engine) :=
  match unifyTopPreparedCertified left right leftValid rightValid with
  | none => none
  | some result =>
      if pettaUnifyCompatible
          (PLeaTTa.subst result.1.erase left.atom)
          (PLeaTTa.subst result.1.erase right.atom) then
        some (checkedComposeUnifierResult engine state stateValid
          result.1 result.2)
      else none

/-- Proof-carrying unification for a checked state.  Prepared constraints
flow directly into prepared composition; unsupported shapes retain the raw
verified path. -/
def checkedUnifyPrepared (engine : SubstEngine)
    (state : CheckedState engine) (left right : Atom) :
    Option (CheckedState engine) :=
  let leftResult := engine.substPrepared state.1 left
  let leftMetadata := engine.substPrepared_metadata state.1 left state.2
  let leftStateValid := engine.substPrepared_valid state.1 left state.2
  let rightResult := engine.substPrepared leftResult.2 right
  let rightMetadata := engine.substPrepared_metadata leftResult.2 right
    leftStateValid
  let rightStateValid := engine.substPrepared_valid leftResult.2 right
    leftStateValid
  checkedUnifyPreparedValues engine rightResult.2 rightStateValid
    leftResult.1 rightResult.1 leftMetadata rightMetadata

theorem checkedComposeUnifierResult_denote (engine : SubstEngine)
    (state : engine.State) (stateValid : engine.Valid state)
    (result : PreparedUnify.Result) (resultValid : result.Valid) :
    engine.denote
        (checkedComposeUnifierResult engine state stateValid result
          resultValid).1 =
      engine.denote (composeRawResult engine state result.erase) := by
  cases result with
  | raw entries =>
      cases entries <;> rfl
  | prepared entries =>
      cases entries with
      | nil => rfl
      | cons binding rest =>
          have preparedDenote := engine.composePrepared_denote state
            (binding :: rest) resultValid
          have rawDenote := engine.compose_denote state
            (PreparedUnify.eraseConstraints (binding :: rest))
          change engine.denote
              (engine.composePrepared state (binding :: rest) resultValid) =
            engine.denote (engine.compose state
              (PreparedUnify.eraseConstraints (binding :: rest)))
          rw [preparedDenote, rawDenote]
          rfl

theorem checkedUnifyPreparedValues_denote_raw (engine : SubstEngine)
    (state : engine.State) (stateValid : engine.Valid state)
    (left right : PersistentSubst.PreparedAtom)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    (checkedUnifyPreparedValues engine state stateValid left right
        leftValid rightValid).map (fun next => engine.denote next.1) =
      (match unifyTopPreparedExact left right with
       | none => none
       | some generated => some (composeRawResult engine state generated)).map
        engine.denote := by
  have certifiedValue := unifyTopPreparedCertified_value left right
    leftValid rightValid
  have erased := unifyTopPreparedResult_erase left right leftValid rightValid
  cases hcertified : unifyTopPreparedCertified left right leftValid
      rightValid with
  | none =>
      simp only [hcertified, Option.map_none] at certifiedValue
      rw [← certifiedValue] at erased
      simp only [Option.map_none] at erased
      simp [checkedUnifyPreparedValues, hcertified,
        unifyTopPreparedExact, ← erased]
  | some certified =>
      rcases certified with ⟨result, resultValid⟩
      simp only [hcertified, Option.map_some] at certifiedValue
      rw [← certifiedValue] at erased
      simp only [Option.map_some] at erased
      cases compatible : pettaUnifyCompatible
          (PLeaTTa.subst result.erase left.atom)
          (PLeaTTa.subst result.erase right.atom) with
      | false =>
          simp [checkedUnifyPreparedValues, hcertified, compatible,
            unifyTopPreparedExact, ← erased]
      | true =>
          have composed := checkedComposeUnifierResult_denote engine state
            stateValid result resultValid
          simpa [checkedUnifyPreparedValues, hcertified, compatible,
            unifyTopPreparedExact, ← erased] using congrArg some composed

theorem checkedUnifyPrepared_denote_raw (engine : SubstEngine)
    (state : CheckedState engine) (left right : Atom) :
    (checkedUnifyPrepared engine state left right).map
        (fun next => engine.denote next.1) =
      (unifyB engine state.1 left right).map engine.denote := by
  have hleftMetadata := engine.substPrepared_metadata state.1 left state.2
  have hleftValid := engine.substPrepared_valid state.1 left state.2
  cases hleft : engine.substPrepared state.1 left with
  | mk leftValue leftState =>
      simp only [hleft] at hleftMetadata hleftValid
      have hrightMetadata := engine.substPrepared_metadata leftState right
        hleftValid
      have hrightValid := engine.substPrepared_valid leftState right hleftValid
      cases hright : engine.substPrepared leftState right with
      | mk rightValue rightState =>
          simp only [hright] at hrightMetadata hrightValid
          have helper := checkedUnifyPreparedValues_denote_raw engine
            rightState hrightValid leftValue rightValue hleftMetadata
              hrightMetadata
          have shapes :
              (match unifyTopPreparedExact leftValue rightValue with
               | none => none
               | some generated =>
                   some (composeRawResult engine rightState generated)).map
                  engine.denote =
                (match unifyTopPreparedExact leftValue rightValue with
                 | none => none
                 | some [] => some rightState
                 | some generated =>
                     some (engine.compose rightState generated)).map
                  engine.denote := by
            cases hunify : unifyTopPreparedExact leftValue rightValue with
            | none => rfl
            | some generated => cases generated <;> rfl
          have combined := helper.trans shapes
          simpa [checkedUnifyPrepared, unifyB, hleft, hright] using combined

/-- A checked engine whose unification operation preserves prepared
constraints through composition.  All other operations are inherited from
the ordinary proof-carrying wrapper. -/
def preparedChecked (engine : SubstEngine) : SubstEngine :=
{ checked engine with
  unify := checkedUnifyPrepared engine
  unify_valid := by intros; trivial
  unify_denote := by
    intro state left right _
    have prepared := checkedUnifyPrepared_denote_raw engine state left right
    have reference := unifyB_map_denote engine state.1 left right state.2
    exact prepared.trans reference }

/-- Executable persistent substitution engine.  The outer checked wrapper
lets the existing generic machine simulation consume the optimized inner
engine without a second proof path. -/
def executablePersistent : SubstEngine :=
  checked (preparedChecked persistent)

end SubstEngine

end PLeaTTa
