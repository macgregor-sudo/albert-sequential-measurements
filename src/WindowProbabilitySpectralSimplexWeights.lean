/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralSimplexPermutations

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Function ENNReal


/-- The symmetric simplex polynomial in its two free real coordinates. -/
def spectralSimplexWeight (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fourColumnEigenvalueWeight ![p.1, p.2, 1 - p.1 - p.2])

theorem measurable_spectralSimplexWeight : Measurable spectralSimplexWeight := by
  unfold spectralSimplexWeight fourColumnEigenvalueWeight
  simp
  fun_prop

theorem spectralSimplexWeight_relabel (i : Fin 6) (p : ℝ × ℝ) :
    spectralSimplexWeight (simplexRelabel i p) = spectralSimplexWeight p := by
  rw [simplexRelabel_apply]
  fin_cases i <;> simp [spectralSimplexWeight, fourColumnEigenvalueWeight] <;> congr 1 <;> ring

private theorem spectralSimplexWeight_zero_outside_chambers {p : ℝ × ℝ}
    (hp : p ∈ positiveEigenvalueSimplex) (h : p ∉ ⋃ i, labelledEigenvalueSimplex i) :
    spectralSimplexWeight p = 0 := by
  by_cases h₁ : p.1 = p.2
  · simp [spectralSimplexWeight, fourColumnEigenvalueWeight, h₁]
  by_cases h₂ : p.1 = 1 - p.1 - p.2
  · unfold spectralSimplexWeight fourColumnEigenvalueWeight
    have he : (p.1 - (1 - p.1 - p.2)) ^ 2 = 0 := by rw [sub_eq_zero.mpr h₂]; norm_num
    simp [he]
  by_cases h₃ : p.2 = 1 - p.1 - p.2
  · unfold spectralSimplexWeight fourColumnEigenvalueWeight
    have he : (p.2 - (1 - p.1 - p.2)) ^ 2 = 0 := by rw [sub_eq_zero.mpr h₃]; norm_num
    simp [he]
  exact (h (mem_iUnion_labelledEigenvalueSimplex hp h₁ h₂ h₃)).elim

/-- Integrating the symmetric polynomial on the whole simplex is exactly the sum of
the six volume-preserving relabelled integrals on the descending chamber. -/
theorem lintegral_spectralSimplexWeight_partition (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p in positiveEigenvalueSimplex, spectralSimplexWeight p * g p) =
      ∑ i : Fin 6, ∫⁻ p in orderedSimplexInTwoCoordinates, spectralSimplexWeight p * g (simplexRelabel i p) := by
  let U : Set (ℝ × ℝ) := ⋃ i, labelledEigenvalueSimplex i
  have hU : MeasurableSet U := MeasurableSet.iUnion labelledEigenvalueSimplex_measurable
  have hS : MeasurableSet positiveEigenvalueSimplex :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const).measurableSet)
  have hUs : U ⊆ positiveEigenvalueSimplex := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ((mem_labelledEigenvalueSimplex_iff i p).mp hi).1
  have hCover : (∫⁻ p in positiveEigenvalueSimplex, spectralSimplexWeight p * g p) =
      ∫⁻ p in U, spectralSimplexWeight p * g p := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hU]
    apply lintegral_congr
    intro p
    by_cases h : p ∈ U
    · simp [h, hUs h]
    · by_cases hp : p ∈ positiveEigenvalueSimplex
      · simp [h,hp,spectralSimplexWeight_zero_outside_chambers hp h]
      · simp [h,hp]
  rw [hCover]
  change (∫⁻ p in ⋃ i, labelledEigenvalueSimplex i, spectralSimplexWeight p * g p) = _
  rw [lintegral_iUnion labelledEigenvalueSimplex_measurable labelledEigenvalueSimplex_disjoint, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  let E := simplexRelabel i
  have hMap : (volume.restrict orderedSimplexInTwoCoordinates).map E = volume.restrict (labelledEigenvalueSimplex i) := by
    have h := E.restrict_map (volume : Measure (ℝ × ℝ)) (E '' orderedSimplexInTwoCoordinates)
    rw [Set.preimage_image_eq _ E.injective, (measurePreserving_simplexRelabel i).map_eq] at h
    exact h.symm
  have hProduct : Measurable (fun p => spectralSimplexWeight p * g p) :=
    measurable_spectralSimplexWeight.mul hg
  rw [← hMap, lintegral_map hProduct E.measurable]
  apply lintegral_congr
  intro p
  rw [show E = simplexRelabel i from rfl, spectralSimplexWeight_relabel]

theorem spectralSimplexWeight_mass :
    (∫⁻ p in positiveEigenvalueSimplex, spectralSimplexWeight p) =
      (6 : ℝ≥0∞) * ∫⁻ p in orderedSimplexInTwoCoordinates, spectralSimplexWeight p := by
  have he := lintegral_spectralSimplexWeight_partition (fun _ => 1) measurable_const
  simpa [Finset.sum_const, nsmul_eq_mul] using he

/-- The normalized printed polynomial density on the whole simplex. -/
def normalizedFourColumnSymmetricSimplexDensity : Measure (ℝ × ℝ) :=
  (∫⁻ p in positiveEigenvalueSimplex, spectralSimplexWeight p)⁻¹ •
    (volume.restrict positiveEigenvalueSimplex).withDensity spectralSimplexWeight

/-- Uniform relabelling of the normalized descending-chamber density gives the symmetric density. -/
theorem relabelled_orderedSimplexDensity_eq_symmetricDensity :
    let μ := (∫⁻ p in orderedSimplexInTwoCoordinates, spectralSimplexWeight p)⁻¹ •
      (volume.restrict orderedSimplexInTwoCoordinates).withDensity spectralSimplexWeight
    (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6, μ.map (simplexRelabel i) = normalizedFourColumnSymmetricSimplexDensity := by
  dsimp only
  apply Measure.ext_of_lintegral
  intro g hg
  let mass := ∫⁻ p in orderedSimplexInTwoCoordinates, spectralSimplexWeight p
  let μ := mass⁻¹ • (volume.restrict orderedSimplexInTwoCoordinates).withDensity spectralSimplexWeight
  have hTerm (i : Fin 6) : (∫⁻ p, g p ∂(μ.map (simplexRelabel i))) =
      mass⁻¹ * ∫⁻ p in orderedSimplexInTwoCoordinates, spectralSimplexWeight p * g (simplexRelabel i p) := by
    have hgRelabelled : Measurable (fun p => g (simplexRelabel i p)) :=
      hg.comp (simplexRelabel i).measurable
    dsimp only [μ]
    rw [lintegral_map hg (simplexRelabel i).measurable, lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ measurable_spectralSimplexWeight hgRelabelled]
    rfl
  change (∫⁻ p, g p ∂((6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6, μ.map (simplexRelabel i))) = _
  rw [normalizedFourColumnSymmetricSimplexDensity, lintegral_smul_measure,
    lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ measurable_spectralSimplexWeight hg]
  simp_rw [smul_eq_mul, Pi.mul_apply, hTerm]
  rw [← Finset.mul_sum, spectralSimplexWeight_mass, lintegral_spectralSimplexWeight_partition g hg]
  change (6 : ℝ≥0∞)⁻¹ * (mass⁻¹ * _) = (6 * mass)⁻¹ * _
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (6 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (6 : ℝ≥0∞) ≠ ∞)), mul_assoc]

end AlbertSequential.WindowProbability
