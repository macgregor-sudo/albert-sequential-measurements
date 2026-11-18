module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Lattice

/-! Compact closed constraints and finite positive discrepancy witnesses.
This generic topology module contains no CP interpretation or assumed target.
Its application to stationary Choi models is implemented separately.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

open Set

theorem exists_mem_of_finite_constraints
    {Z I : Type*} [TopologicalSpace Z] {K : Set Z} (hK : IsCompact K)
    (E : I → Set Z) (hE : ∀ i, IsClosed (E i))
    (hfinite : ∀ F : Finset I, ∃ z ∈ K, ∀ i ∈ F, z ∈ E i) :
    ∃ z ∈ K, ∀ i, z ∈ E i := by
  classical
  by_contra! hnone
  have hd : Disjoint K (⋂ i, E i) := by
    rw [Set.disjoint_left]
    intro z hz he
    obtain ⟨i, hi⟩ := hnone z hz
    exact hi (Set.mem_iInter.mp he i)
  obtain ⟨F, hF⟩ := hK.elim_finite_subfamily_closed E hE hd
  obtain ⟨z, hz, he⟩ := hfinite F
  exact Set.disjoint_left.mp hF hz (by simpa using he)

/-- If continuous coordinates cannot all match, a finite collection has a
strictly positive error gap on the compact parameter set. This is a maximum
absolute-error conclusion, with no linear-separation or quantitative claim. -/
theorem exists_finite_positive_error_gap
    {Z I : Type*} [TopologicalSpace Z] {K : Set Z} (hK : IsCompact K)
    (f : I → Z → ℝ) (hf : ∀ i, Continuous (f i)) (t : I → ℝ)
    (hnone : ¬ ∃ z ∈ K, ∀ i, f i z = t i) :
    ∃ (F : Finset I) (δ : ℝ), 0 < δ ∧
      ∀ z ∈ K, ∃ i ∈ F, δ ≤ |f i z - t i| := by
  classical
  by_cases hne : K.Nonempty
  · have hd : Disjoint K (⋂ i, {z | f i z = t i}) := by
      rw [Set.disjoint_left]
      intro z hz he
      exact hnone ⟨z, hz, by simpa using he⟩
    obtain ⟨F, hF⟩ := hK.elim_finite_subfamily_closed
      (fun i => {z | f i z = t i}) (fun i => isClosed_eq (hf i) continuous_const) hd
    have hFne : F.Nonempty := by
      by_contra hempty
      have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      obtain ⟨z, hz⟩ := hne
      exact Set.disjoint_left.mp hF hz (by simp [hFe])
    let err : Z → ℝ := fun z => F.sup' hFne (fun i => |f i z - t i|)
    have herr : Continuous err :=
      Continuous.finset_sup'_apply hFne (fun i _ => ((hf i).sub continuous_const).abs)
    have hpos : ∀ z ∈ K, 0 < err z := by
      intro z hz
      have hnot : ¬ ∀ i ∈ F, f i z = t i := by
        intro hall
        exact Set.disjoint_left.mp hF hz (by simpa using hall)
      push Not at hnot
      obtain ⟨i, hi, hineq⟩ := hnot
      change 0 < F.sup' hFne (fun i => |f i z - t i|)
      exact (abs_pos.mpr (sub_ne_zero.mpr hineq)).trans_le
        (Finset.le_sup' (fun i => |f i z - t i|) hi)
    obtain ⟨δ, hδ, hlower⟩ := hK.exists_forall_le' herr.continuousOn hpos
    refine ⟨F, δ, hδ, fun z hz => ?_⟩
    exact (Finset.le_sup'_iff hFne).mp (hlower z hz)
  · refine ⟨∅, 1, zero_lt_one, fun z hz => ?_⟩
    exact (hne ⟨z, hz⟩).elim

end AlbertSequential
