module

public import FixedDimensionCompactness
public import FiniteMenuExtension
public import StationaryKrausSemantics

/-! Paper-facing fixed-dimensional compactness using actual stationary finite
Kraus instruments and genuinely local finite-menu models. This theorem supplies
neither an Albert no-go nor continuous/equivariant/affine choices in labels.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def HasStationaryKrausRealization (d : ℕ) {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (t : P → InstrumentWord A → ℝ) : Prop :=
  ∃ (rho : P → ComplexMatrix d) (K : (x : X) → A x → List (ComplexMatrix d)),
    (∀ p, IsMatrixDensity (rho p)) ∧
    (∀ x, ∑ a, krausEffect (K x a) = 1) ∧
    ∀ p w, finiteKrausWordProbability rho K p w = t p w

theorem stationaryKrausRealization_iff_choi {d : ℕ}
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (t : P → InstrumentWord A → ℝ) :
    HasStationaryKrausRealization d t ↔
      ∃ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t := by
  constructor
  · rintro ⟨rho, K, hrho, hKn, ht⟩
    let r := stationaryKrausToChoi rho K
    have hact : ∀ x a Y, choiAction (r.2 x a) Y = krausAction (K x a) Y :=
      fun x a Y => krausChoi_action (K x a) Y
    refine ⟨r, stationaryKrausToChoi_normalized rho K hrho hKn, fun p w => ?_⟩
    exact (choiWordProbability_eq_krausWordProbability r K hact p w).trans (ht p w)
  · rintro ⟨r, hr, ht⟩
    obtain ⟨K, hKn, _, hwords⟩ := normalizedChoiModel_has_stationaryKraus r hr
    exact ⟨r.1, K, hr.1, hKn, fun p w => (hwords p w).symm.trans (ht p w)⟩

theorem stationaryKraus_global_iff_local_finite_menus (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) :
    HasStationaryKrausRealization d t ↔
      ∀ (ps : Finset P) (xs : Finset X),
        HasStationaryKrausRealization d
          (fun (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) =>
            t p.val (includeMenuWord xs w)) := by
  constructor
  · intro h ps xs
    have hchoi := (stationaryKrausRealization_iff_choi t).mp h
    have hmenu := ((fixedDimensionCompactness d P X A).finite_menu_iff hd t).mp hchoi ps xs
    have hlocal := (finiteMenu_globalData_iff_localData hd ps xs t).mp hmenu
    exact (stationaryKrausRealization_iff_choi _).mpr hlocal
  · intro h
    have hmenus : ∀ (ps : Finset P) (xs : Finset X),
        ∃ r : RawFiniteCPModel d P X A,
          IsNormalizedFiniteCPModel r ∧ MatchesFiniteMenu r t ps xs := by
      intro ps xs
      have hlocal := (stationaryKrausRealization_iff_choi _).mp (h ps xs)
      exact (finiteMenu_globalData_iff_localData hd ps xs t).mpr hlocal
    apply (stationaryKrausRealization_iff_choi t).mpr
    exact ((fixedDimensionCompactness d P X A).finite_menu_iff hd t).mpr hmenus

theorem stationaryKraus_finite_positive_error_gap (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) (hnone : ¬ HasStationaryKrausRealization d t) :
    ∃ (F : Finset (P × InstrumentWord A)) (δ : ℝ), 0 < δ ∧
      ∀ (rho : P → ComplexMatrix d) (K : (x : X) → A x → List (ComplexMatrix d)),
        (∀ p, IsMatrixDensity (rho p)) →
        (∀ x, ∑ a, krausEffect (K x a) = 1) →
        ∃ q ∈ F, δ ≤ |finiteKrausWordProbability rho K q.1 q.2 - t q.1 q.2| := by
  have hnchoi : ¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t :=
    fun h => hnone ((stationaryKrausRealization_iff_choi t).mpr h)
  obtain ⟨F, δ, hδ, hF⟩ := (fixedDimensionCompactness d P X A).finite_error_gap hd t hnchoi
  refine ⟨F, δ, hδ, fun rho K hrho hKn => ?_⟩
  let r := stationaryKrausToChoi rho K
  obtain ⟨q, hq, herr⟩ := hF r (stationaryKrausToChoi_normalized rho K hrho hKn)
  refine ⟨q, hq, ?_⟩
  have hact : ∀ x a Y, choiAction (r.2 x a) Y = krausAction (K x a) Y :=
    fun x a Y => krausChoi_action (K x a) Y
  rwa [choiWordProbability_eq_krausWordProbability r K hact] at herr

end AlbertSequential
