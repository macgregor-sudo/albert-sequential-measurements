module

public import DefaultChoiModel

/-! Locally defined finite menus extend without compatibility choices.
Only unused labels receive arbitrary normalized defaults. Every word on the
original menu has exactly the same unnormalized state and probability.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

def includeMenuWord {X : Type*} {A : X → Type*} (xs : Finset X)
    (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) : InstrumentWord A :=
  w.map (fun a => ⟨a.1.val, a.2⟩)

def extendFiniteMenuModel {d : ℕ} (hd : 0 < d) {P X : Type*} {A : X → Type*}
    [∀ x, Nonempty (A x)] (ps : Finset P) (xs : Finset X)
    (r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val)) :
    RawFiniteCPModel d P X A := by
  classical
  exact (fun p => if hp : p ∈ ps then r.1 ⟨p, hp⟩ else coordinateDensity ⟨0, hd⟩,
    fun x => if hx : x ∈ xs then r.2 ⟨x, hx⟩ else defaultChoiInstrument d (A x))

theorem extendFiniteMenuModel_normalized {d : ℕ} (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (ps : Finset P) (xs : Finset X)
    (r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val))
    (hr : IsNormalizedFiniteCPModel r) :
    IsNormalizedFiniteCPModel (extendFiniteMenuModel hd ps xs r) := by
  classical
  constructor
  · intro p
    by_cases hp : p ∈ ps
    · simpa only [extendFiniteMenuModel, dite_eq_left hp] using hr.1 ⟨p, hp⟩
    · simpa only [extendFiniteMenuModel, dite_eq_right hp] using
        coordinateDensity_isDensity (⟨0, hd⟩ : Fin d)
  · constructor
    · intro x a
      by_cases hx : x ∈ xs
      · simpa only [extendFiniteMenuModel, dite_eq_left hx] using hr.2.1 ⟨x, hx⟩ a
      · simpa only [extendFiniteMenuModel, dite_eq_right hx] using
          (defaultChoiInstrument_normalized d (A x)).1 a
    · intro x
      by_cases hx : x ∈ xs
      · simpa only [extendFiniteMenuModel, dite_eq_left hx] using hr.2.2 ⟨x, hx⟩
      · simpa only [extendFiniteMenuModel, dite_eq_right hx] using
          (defaultChoiInstrument_normalized d (A x)).2

theorem finiteMenuExtension_wordState {d : ℕ} (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Nonempty (A x)]
    (ps : Finset P) (xs : Finset X)
    (r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val))
    (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) :
    finiteCPWordState (extendFiniteMenuModel hd ps xs r) p.val (includeMenuWord xs w) =
      finiteCPWordState r p w := by
  classical
  induction w using List.reverseRecOn with
  | nil => simp only [includeMenuWord, List.map_nil, finiteCPWordState, List.foldl_nil,
      extendFiniteMenuModel, dite_eq_left p.property]
  | append_singleton w a ih =>
      simpa only [includeMenuWord, List.map_append, List.map_cons, List.map_nil,
        finiteCPWordState, List.foldl_append, List.foldl_cons, List.foldl_nil,
        extendFiniteMenuModel, dite_eq_left p.property, dite_eq_left a.1.property] using
        congrArg (choiAction (r.2 a.1 a.2)) ih

theorem finiteMenuExtension_wordProbability {d : ℕ} (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Nonempty (A x)]
    (ps : Finset P) (xs : Finset X)
    (r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val))
    (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) :
    finiteCPWordProbability (extendFiniteMenuModel hd ps xs r) p.val (includeMenuWord xs w) =
      finiteCPWordProbability r p w := by
  unfold finiteCPWordProbability
  rw [finiteMenuExtension_wordState]

def restrictFiniteMenuModel {d : ℕ} {P X : Type*} {A : X → Type*}
    (ps : Finset P) (xs : Finset X) (r : RawFiniteCPModel d P X A) :
    RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val) :=
  (fun p => r.1 p.val, fun x => r.2 x.val)

theorem restrictFiniteMenuModel_normalized {d : ℕ}
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (ps : Finset P) (xs : Finset X) (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) :
    IsNormalizedFiniteCPModel (restrictFiniteMenuModel ps xs r) :=
  ⟨fun p => hr.1 p.val, fun x a => hr.2.1 x.val a, fun x => hr.2.2 x.val⟩

theorem finiteMenuRestriction_wordState {d : ℕ}
    {P X : Type*} {A : X → Type*} (ps : Finset P) (xs : Finset X)
    (r : RawFiniteCPModel d P X A) (p : {p // p ∈ ps})
    (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) :
    finiteCPWordState (restrictFiniteMenuModel ps xs r) p w =
      finiteCPWordState r p.val (includeMenuWord xs w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      simpa only [restrictFiniteMenuModel, includeMenuWord, List.map_append,
        List.map_cons, List.map_nil, finiteCPWordState, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using
        congrArg (choiAction (r.2 a.1.val a.2)) ih

theorem includeMenuWord_members {X : Type*} {A : X → Type*} (xs : Finset X)
    (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) :
    ∀ a ∈ includeMenuWord xs w, a.1 ∈ xs := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact b.1.property

theorem exists_localMenuWord {X : Type*} {A : X → Type*} (xs : Finset X)
    (w : InstrumentWord A) (hw : ∀ a ∈ w, a.1 ∈ xs) :
    ∃ v : InstrumentWord (fun x : {x // x ∈ xs} => A x.val), includeMenuWord xs v = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
      have ha : a.1 ∈ xs := hw a List.mem_cons_self
      obtain ⟨v, hv⟩ := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
      refine ⟨⟨⟨a.1, ha⟩, a.2⟩ :: v, ?_⟩
      simpa only [includeMenuWord, List.map_cons] using congrArg (List.cons a) hv

theorem finiteMenu_globalData_iff_localData {d : ℕ} (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (ps : Finset P) (xs : Finset X) (t : P → InstrumentWord A → ℝ) :
    (∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesFiniteMenu r t ps xs) ↔
    (∃ r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val),
      IsNormalizedFiniteCPModel r ∧ ∀ p w,
        finiteCPWordProbability r p w = t p.val (includeMenuWord xs w)) := by
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨restrictFiniteMenuModel ps xs r, restrictFiniteMenuModel_normalized ps xs r hr,
      fun p w => ?_⟩
    unfold finiteCPWordProbability
    rw [finiteMenuRestriction_wordState]
    exact hm p.val p.property (includeMenuWord xs w) (includeMenuWord_members xs w)
  · rintro ⟨r, hr, hm⟩
    refine ⟨extendFiniteMenuModel hd ps xs r, extendFiniteMenuModel_normalized hd ps xs r hr,
      fun p hp w hw => ?_⟩
    obtain ⟨v, hv⟩ := exists_localMenuWord xs w hw
    rw [← hv]
    exact (finiteMenuExtension_wordProbability hd ps xs r ⟨p, hp⟩ v).trans (hm ⟨p, hp⟩ v)

end AlbertSequential
