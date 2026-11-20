/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralRadial
public import WindowProbabilitySpectralFlagSectors

/-! The trace-simplex Jacobian on the ordered positive eigenvalue chamber. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped ENNReal

/-- The two free coordinates of the normalized eigenvalues. -/
def spectrumSimplexProjection (x : Fin 3 → ℝ) : ℝ × ℝ :=
  (x 0 / (∑ i, x i), x 1 / (∑ i, x i))

/-- The positive simplex in the descending eigenvalue chamber. -/
def orderedEigenvalueSimplex : Set (ℝ × ℝ) :=
  positiveEigenvalueSimplex ∩ {p | p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2}

private theorem measurableSet_simplexOrder : MeasurableSet {p : ℝ × ℝ | p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2} :=
  (isOpen_lt continuous_snd continuous_fst).measurableSet.inter
    (isOpen_lt ((continuous_const.sub continuous_fst).sub continuous_snd) continuous_snd).measurableSet

private theorem simplexProjection_order_iff {x : Fin 3 → ℝ} (hx : x ∈ positiveEigenvalueOrthant) :
    spectrumSimplexProjection x ∈ {p | p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2} ↔ StrictAnti x := by
  let r := ∑ i, x i
  have hr : 0 < r := Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty
  have hlast : 1 - x 0 / r - x 1 / r = x 2 / r := by
    field_simp [hr.ne']
    rw [show r = x 0 + x 1 + x 2 by simp [r, Fin.sum_univ_three]]
    ring
  change x 1 / r < x 0 / r ∧ 1 - x 0 / r - x 1 / r < x 1 / r ↔ _
  rw [hlast, div_lt_div_iff_of_pos_right hr, div_lt_div_iff_of_pos_right hr, strictAnti_fin3_iff]

/-- A trace-simplex integration formula over the full positive orthant restricts to the descending chamber. -/
theorem restrict_traceSimplex_integral_to_order
    (W : (Fin 3 → ℝ) → ℝ≥0∞) (V : ℝ × ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (H : ∀ φ : ℝ × ℝ → ℝ≥0∞, Measurable φ →
      (∫⁻ x in positiveEigenvalueOrthant, W x * φ (spectrumSimplexProjection x)) =
        C * ∫⁻ p in positiveEigenvalueSimplex, V p * φ p)
    (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in spectralPositiveChamber, W x * φ (spectrumSimplexProjection x)) =
      C * ∫⁻ p in orderedEigenvalueSimplex, V p * φ p := by
  let O : Set (ℝ × ℝ) := {p | p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2}
  have h := H (O.indicator φ) (hφ.indicator measurableSet_simplexOrder)
  have hL : (∫⁻ x in positiveEigenvalueOrthant, W x * O.indicator φ (spectrumSimplexProjection x)) =
      ∫⁻ x in spectralPositiveChamber, W x * φ (spectrumSimplexProjection x) := by
    have hSub : spectralPositiveChamber ⊆ positiveEigenvalueOrthant := fun _ hx => hx.2
    have hSet : MeasurableSet positiveEigenvalueOrthant := by
      have he : positiveEigenvalueOrthant = ⋂ i : Fin 3, {x | 0 < x i} := by ext x; simp [positiveEigenvalueOrthant]
      rw [he]
      exact MeasurableSet.iInter fun i => (isOpen_lt continuous_const (continuous_apply i)).measurableSet
    rw [← Set.inter_eq_left.mpr hSub, ← setLIntegral_indicator isOpen_spectralPositiveChamber.measurableSet]
    apply setLIntegral_congr_fun hSet
    intro x hx
    change W x * O.indicator φ (spectrumSimplexProjection x) = _
    have he : spectrumSimplexProjection x ∈ O ↔ x ∈ spectralPositiveChamber :=
      (simplexProjection_order_iff hx).trans ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
    by_cases hp : x ∈ spectralPositiveChamber
    · rw [indicator_of_mem (he.mpr hp), indicator_of_mem hp]
    · rw [indicator_of_notMem (fun h => hp (he.mp h)), indicator_of_notMem hp, mul_zero]
  have hR : (∫⁻ p in positiveEigenvalueSimplex, V p * O.indicator φ p) =
      ∫⁻ p in orderedEigenvalueSimplex, V p * φ p := by
    change _ = ∫⁻ p in positiveEigenvalueSimplex ∩ O, V p * φ p
    rw [Set.inter_comm, ← setLIntegral_indicator measurableSet_simplexOrder]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ O
    · rw [indicator_of_mem hp, indicator_of_mem hp]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, mul_zero]
  exact hL.symm.trans (h.trans (congrArg (fun a => C * a) hR))

/-- The exact real radial substitution restricted to the ordered chamber. -/
theorem fourColumnEigenvalueWeight_orderedSimplex_integral (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in spectralPositiveChamber,
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x) * φ (spectrumSimplexProjection x)) =
      ENNReal.ofReal (Nat.factorial 11 : ℝ) * ∫⁻ p in orderedEigenvalueSimplex,
        ENNReal.ofReal (fourColumnEigenvalueWeight ![p.1, p.2, 1 - p.1 - p.2]) * φ p := by
  exact restrict_traceSimplex_integral_to_order _ _ _
    (fun ψ hψ => fourColumnEigenvalueWeight_simplex_integral ψ hψ) φ hφ

end AlbertSequential.WindowProbability
