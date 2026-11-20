/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralSimplexPermutations
public import WindowProbabilitySpectralPowerPublished

/-! Extend the descending ordered density to the literal symmetric simplex weight. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Function ENNReal


private theorem measurable_powerSimplexWeight (m : ℕ) : Measurable (powerSimplexWeight m) := by
  unfold powerSimplexWeight powerEigenvaluePolynomial
  simp
  fun_prop

theorem powerSimplexWeight_relabel (m : ℕ) (i : Fin 6) (p : ℝ × ℝ) :
    powerSimplexWeight m (simplexRelabel i p) = powerSimplexWeight m p := by
  rw [simplexRelabel_apply]
  fin_cases i <;> simp [powerSimplexWeight, powerEigenvaluePolynomial] <;> congr 1 <;> ring

private theorem powerSimplexWeight_zero_outside_chambers (m : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ positiveEigenvalueSimplex) (h : p ∉ ⋃ i, labelledEigenvalueSimplex i) :
    powerSimplexWeight m p = 0 := by
  by_cases h₁ : p.1 = p.2
  · simp [powerSimplexWeight, powerEigenvaluePolynomial, h₁]
  by_cases h₂ : p.1 = 1 - p.1 - p.2
  · unfold powerSimplexWeight powerEigenvaluePolynomial
    have he : (p.1 - (1 - p.1 - p.2)) ^ 2 = 0 := by rw [sub_eq_zero.mpr h₂]; norm_num
    simp [he]
  by_cases h₃ : p.2 = 1 - p.1 - p.2
  · unfold powerSimplexWeight powerEigenvaluePolynomial
    have he : (p.2 - (1 - p.1 - p.2)) ^ 2 = 0 := by rw [sub_eq_zero.mpr h₃]; norm_num
    simp [he]
  exact (h (mem_iUnion_labelledEigenvalueSimplex hp h₁ h₂ h₃)).elim

/-- Integrating the symmetric polynomial on the whole simplex is exactly the sum of
the six volume-preserving relabelled integrals on the descending chamber. -/
theorem lintegral_powerSimplexWeight_partition (m : ℕ) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p * g p) =
      ∑ i : Fin 6, ∫⁻ p in orderedSimplexInTwoCoordinates, powerSimplexWeight m p * g (simplexRelabel i p) := by
  let U : Set (ℝ × ℝ) := ⋃ i, labelledEigenvalueSimplex i
  have hU : MeasurableSet U := MeasurableSet.iUnion labelledEigenvalueSimplex_measurable
  have hUs : U ⊆ positiveEigenvalueSimplex := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ((mem_labelledEigenvalueSimplex_iff i p).mp hi).1
  have hCover : (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p * g p) =
      ∫⁻ p in U, powerSimplexWeight m p * g p := by
    rw [← lintegral_indicator measurableSet_positiveEigenvalueSimplex, ← lintegral_indicator hU]
    apply lintegral_congr
    intro p
    by_cases h : p ∈ U
    · simp [h, hUs h]
    · by_cases hp : p ∈ positiveEigenvalueSimplex
      · simp [h,hp,powerSimplexWeight_zero_outside_chambers m hp h]
      · simp [h,hp]
  rw [hCover]
  change (∫⁻ p in ⋃ i, labelledEigenvalueSimplex i, powerSimplexWeight m p * g p) = _
  rw [lintegral_iUnion labelledEigenvalueSimplex_measurable labelledEigenvalueSimplex_disjoint, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  let E := simplexRelabel i
  have hMap : (volume.restrict orderedSimplexInTwoCoordinates).map E = volume.restrict (labelledEigenvalueSimplex i) := by
    have h := E.restrict_map (volume : Measure (ℝ × ℝ)) (E '' orderedSimplexInTwoCoordinates)
    rw [Set.preimage_image_eq _ E.injective, (measurePreserving_simplexRelabel i).map_eq] at h
    exact h.symm
  have hProduct : Measurable (fun p => powerSimplexWeight m p * g p) :=
    (measurable_powerSimplexWeight m).mul hg
  rw [← hMap, lintegral_map hProduct E.measurable]
  apply lintegral_congr
  intro p
  rw [show E = simplexRelabel i from rfl, powerSimplexWeight_relabel]

theorem powerSimplexWeight_mass (m : ℕ) :
    (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p) =
      (6 : ℝ≥0∞) * ∫⁻ p in orderedSimplexInTwoCoordinates, powerSimplexWeight m p := by
  have he := lintegral_powerSimplexWeight_partition m (fun _ => 1) measurable_const
  simpa [Finset.sum_const, nsmul_eq_mul] using he

/-- The normalized printed polynomial density on the whole simplex. -/
def normalizedPowerSymmetricSimplexDensity (m : ℕ) : Measure (ℝ × ℝ) :=
  (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p)⁻¹ •
    (volume.restrict positiveEigenvalueSimplex).withDensity (powerSimplexWeight m)

/-- Uniform relabelling of the normalized descending-chamber density gives the symmetric density. -/
theorem relabelled_powerOrderedSimplexDensity_eq_symmetricDensity (m : ℕ) :
    let μ := (∫⁻ p in orderedSimplexInTwoCoordinates, powerSimplexWeight m p)⁻¹ •
      (volume.restrict orderedSimplexInTwoCoordinates).withDensity (powerSimplexWeight m)
    (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6, μ.map (simplexRelabel i) = normalizedPowerSymmetricSimplexDensity m := by
  dsimp only
  apply Measure.ext_of_lintegral
  intro g hg
  let mass := ∫⁻ p in orderedSimplexInTwoCoordinates, powerSimplexWeight m p
  let μ := mass⁻¹ • (volume.restrict orderedSimplexInTwoCoordinates).withDensity (powerSimplexWeight m)
  have hTerm (i : Fin 6) : (∫⁻ p, g p ∂(μ.map (simplexRelabel i))) =
      mass⁻¹ * ∫⁻ p in orderedSimplexInTwoCoordinates, powerSimplexWeight m p * g (simplexRelabel i p) := by
    have hgRelabelled : Measurable (fun p => g (simplexRelabel i p)) :=
      hg.comp (simplexRelabel i).measurable
    dsimp only [μ]
    rw [lintegral_map hg (simplexRelabel i).measurable, lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_powerSimplexWeight m) hgRelabelled]
    rfl
  change (∫⁻ p, g p ∂((6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6, μ.map (simplexRelabel i))) = _
  rw [normalizedPowerSymmetricSimplexDensity, lintegral_smul_measure,
    lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_powerSimplexWeight m) hg]
  simp_rw [smul_eq_mul, Pi.mul_apply, hTerm]
  rw [← Finset.mul_sum, powerSimplexWeight_mass m, lintegral_powerSimplexWeight_partition m g hg]
  change (6 : ℝ≥0∞)⁻¹ * (mass⁻¹ * _) = (6 * mass)⁻¹ * _
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (6 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (6 : ℝ≥0∞) ≠ ∞)), mul_assoc]

/-- The law after a uniform independent relabelling of the three actual normalized Gram eigenvalues. -/
def uniformlyRelabelledGramEigenvalueLaw (k : ℕ) : Measure (ℝ × ℝ) :=
  (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6,
    ((standardComplexGaussianMatrix k).map (normalizedGramEigenvaluePair k)).map (simplexRelabel i)

/-- The printed symmetric eigenvalue density on the positive simplex for every `k ≥ 3`. -/
theorem uniformlyRelabelledGramEigenvalueLaw_eq_density (k : ℕ) (hk : 3 ≤ k) :
    uniformlyRelabelledGramEigenvalueLaw k = normalizedPowerSymmetricSimplexDensity (k - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, (Nat.sub_add_cancel hk).symm⟩
  rw [Nat.add_sub_cancel, uniformlyRelabelledGramEigenvalueLaw, normalizedGramEigenvaluePair_law_eq_density]
  exact relabelled_powerOrderedSimplexDensity_eq_symmetricDensity m

end AlbertSequential.WindowProbability
