module

public import FixedDimensionCompactness
public import FiniteMenuExtension
public import LocalFiniteErrorGap
public import CPWordProbabilities

/-! Exact paper-facing fixed-dimensional compactness: arbitrary complex-linear
CP instruments, arbitrary labels, finite nonempty outcomes, all chronological
unconditional words, and complex trace equality to the real target. The error
gap applies to intrinsically local finite-menu models, not only global data.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

def HasStationaryCPRealization (d : ℕ) {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (t : P → InstrumentWord A → ℝ) : Prop :=
  ∃ r : RawStationaryLinearCPModel d P X A,
    IsNormalizedStationaryLinearCPModel r ∧
    ∀ p w, Matrix.trace (stationaryLinearCPWordState r p w) = (t p w : ℂ)

theorem stationaryCPRealization_iff_choi {d : ℕ}
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (t : P → InstrumentWord A → ℝ) :
    HasStationaryCPRealization d t ↔
      ∃ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t := by
  constructor
  · rintro ⟨r, hr, ht⟩
    refine ⟨linearCPModelToChoi r, linearCPModelToChoi_normalized r hr, fun p w => ?_⟩
    rw [linearCPModelToChoi_wordProbability]
    have hp := congrArg Complex.re (ht p w)
    exact hp
  · rintro ⟨r, hr, ht⟩
    let s := choiModelToLinearCP r
    have hs : IsNormalizedStationaryLinearCPModel s := choiModelToLinearCP_normalized r hr
    refine ⟨s, hs, fun p w => ?_⟩
    calc
      Matrix.trace (stationaryLinearCPWordState s p w) =
          (stationaryLinearCPWordProbability s p w : ℂ) :=
        stationaryLinearCPWord_trace_eq_probability s hs p w
      _ = (t p w : ℂ) := by rw [choiModelToLinearCP_wordProbability, ht p w]

theorem stationaryCP_global_iff_local_finite_menus (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) :
    HasStationaryCPRealization d t ↔
      ∀ (ps : Finset P) (xs : Finset X), HasStationaryCPRealization d
        (fun (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) =>
          t p.val (includeMenuWord xs w)) := by
  constructor
  · intro h ps xs
    have hglobal := (stationaryCPRealization_iff_choi t).mp h
    have hmenu := ((fixedDimensionCompactness d P X A).finite_menu_iff hd t).mp hglobal ps xs
    exact (stationaryCPRealization_iff_choi _).mpr
      ((finiteMenu_globalData_iff_localData hd ps xs t).mp hmenu)
  · intro h
    apply (stationaryCPRealization_iff_choi t).mpr
    apply ((fixedDimensionCompactness d P X A).finite_menu_iff hd t).mpr
    intro ps xs
    exact (finiteMenu_globalData_iff_localData hd ps xs t).mpr
      ((stationaryCPRealization_iff_choi _).mp (h ps xs))

theorem stationaryCP_local_finite_positive_error_gap (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) (hnone : ¬ HasStationaryCPRealization d t) :
    ∃ (ps : Finset P) (xs : Finset X)
      (F : Finset ({p // p ∈ ps} × InstrumentWord (fun x : {x // x ∈ xs} => A x.val)))
      (δ : ℝ), 0 < δ ∧
      ∀ r : RawStationaryLinearCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val),
        IsNormalizedStationaryLinearCPModel r →
        ∃ q ∈ F, δ ≤ |stationaryLinearCPWordProbability r q.1 q.2 -
          t q.1.val (includeMenuWord xs q.2)| := by
  have hnchoi : ¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t :=
    fun h => hnone ((stationaryCPRealization_iff_choi t).mpr h)
  obtain ⟨ps, xs, F, δ, hδ, hF⟩ := finite_positive_error_gap_on_local_menu d hd t hnchoi
  refine ⟨ps, xs, F, δ, hδ, fun r hr => ?_⟩
  obtain ⟨q, hq, herr⟩ := hF (linearCPModelToChoi r) (linearCPModelToChoi_normalized r hr)
  exact ⟨q, hq, by simpa only [linearCPModelToChoi_wordProbability] using herr⟩

/-- Literal finite-maximum form of the paper's error-gap assertion. The witness
set is nonempty because the local normalized model space is explicitly inhabited.
There is no numerical value of the gap and no linear-inequality conclusion. -/
theorem stationaryCP_local_finite_maximum_error_gap (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) (hnone : ¬ HasStationaryCPRealization d t) :
    ∃ (ps : Finset P) (xs : Finset X)
      (F : Finset ({p // p ∈ ps} × InstrumentWord (fun x : {x // x ∈ xs} => A x.val)))
      (hF : F.Nonempty) (δ : ℝ), 0 < δ ∧
      ∀ r : RawStationaryLinearCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val),
        IsNormalizedStationaryLinearCPModel r →
        δ ≤ F.sup' hF (fun q => |stationaryLinearCPWordProbability r q.1 q.2 -
          t q.1.val (includeMenuWord xs q.2)|) := by
  classical
  obtain ⟨ps, xs, F, δ, hδ, hgap⟩ := stationaryCP_local_finite_positive_error_gap d hd t hnone
  have hF : F.Nonempty := by
    let c := defaultFiniteCPModel d hd {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val)
    have hc : IsNormalizedFiniteCPModel c := defaultFiniteCPModel_normalized d hd _ _ _
    obtain ⟨q, hq, _⟩ := hgap (choiModelToLinearCP c) (choiModelToLinearCP_normalized c hc)
    exact ⟨q, hq⟩
  refine ⟨ps, xs, F, hF, δ, hδ, fun r hr => ?_⟩
  obtain ⟨q, hq, herr⟩ := hgap r hr
  exact herr.trans (Finset.le_sup'
    (fun q => |stationaryLinearCPWordProbability r q.1 q.2 - t q.1.val (includeMenuWord xs q.2)|) hq)

end AlbertSequential
