module

import WindowProbabilitySpectralWindowDensity

open AlbertSequential AlbertSequential.WindowProbability
open MeasureTheory Set
open scoped ENNReal

noncomputable section

example (i : Fin 6) (p : ℝ × ℝ) : simplexRelabel i p =
    ![p, (p.1, 1 - p.1 - p.2), (p.2, p.1), (1 - p.1 - p.2, p.1),
      (p.2, 1 - p.1 - p.2), (1 - p.1 - p.2, p.2)] i := simplexRelabel_apply i p

example (i : Fin 6) : MeasurePreserving (simplexRelabel i)
    (volume : Measure (ℝ × ℝ)) volume := measurePreserving_simplexRelabel i

example (p : ℝ × ℝ) :
    spectralSimplexWeight p =
      ENNReal.ofReal (p.1 * p.2 * (1 - p.1 - p.2) *
        ((p.1 - p.2)^2 * (p.1 - (1 - p.1 - p.2))^2 * (p.2 - (1 - p.1 - p.2))^2)) := rfl

def closedEigenvalueSimplex : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

private theorem weight_zero_on_boundary {p : ℝ × ℝ} (hc : p ∈ closedEigenvalueSimplex)
    (ho : p ∉ positiveEigenvalueSimplex) : spectralSimplexWeight p = 0 := by
  obtain ⟨ha,hb,hs⟩ := hc
  by_cases h₁ : p.1 = 0
  · simp [spectralSimplexWeight, fourColumnEigenvalueWeight, h₁]
  by_cases h₂ : p.2 = 0
  · simp [spectralSimplexWeight, fourColumnEigenvalueWeight, h₂]
  have h₃ : 1 - p.1 - p.2 = 0 := by
    have h : ¬ p.1 + p.2 < 1 := fun h => ho ⟨lt_of_le_of_ne ha (Ne.symm h₁),lt_of_le_of_ne hb (Ne.symm h₂),h⟩
    linarith
  unfold spectralSimplexWeight fourColumnEigenvalueWeight
  have hthird : (![p.1, p.2, 1 - p.1 - p.2] : Fin 3 → ℝ) 2 = 0 := h₃
  rw [hthird]
  simp

private theorem lintegral_weight_closedSimplex (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in positiveEigenvalueSimplex, spectralSimplexWeight p * g p) =
      ∫⁻ p in closedEigenvalueSimplex, spectralSimplexWeight p * g p := by
  have ho : MeasurableSet positiveEigenvalueSimplex := by
    have h₁ : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
      (isOpen_lt continuous_const continuous_fst).measurableSet
    have h₂ : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
      (isOpen_lt continuous_const continuous_snd).measurableSet
    have h₃ : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 < 1} :=
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const).measurableSet
    exact h₁.inter (h₂.inter h₃)
  have hc : MeasurableSet closedEigenvalueSimplex :=
    (isClosed_le continuous_const continuous_fst).measurableSet.inter
      ((isClosed_le continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet))
  rw [← lintegral_indicator ho, ← lintegral_indicator hc]
  apply lintegral_congr
  intro p
  by_cases h : p ∈ positiveEigenvalueSimplex
  · rcases h with ⟨h₁,h₂,h₃⟩
    have hc' : p ∈ closedEigenvalueSimplex := ⟨h₁.le,h₂.le,h₃.le⟩
    have ho' : p ∈ positiveEigenvalueSimplex := ⟨h₁,h₂,h₃⟩
    rw [indicator_of_mem ho', indicator_of_mem hc']
  · rw [indicator_of_notMem h]
    by_cases hc' : p ∈ closedEigenvalueSimplex
    · rw [indicator_of_mem hc', weight_zero_on_boundary hc' h, zero_mul]
    · rw [indicator_of_notMem hc']

theorem checkedSymmetricDensity_closedSimplex :
    normalizedFourColumnSymmetricSimplexDensity =
      (∫⁻ p in closedEigenvalueSimplex, spectralSimplexWeight p)⁻¹ •
        (volume.restrict closedEigenvalueSimplex).withDensity spectralSimplexWeight := by
  apply Measure.ext_of_lintegral
  intro g hg
  unfold normalizedFourColumnSymmetricSimplexDensity
  rw [lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul, lintegral_withDensity_eq_lintegral_mul _ measurable_spectralSimplexWeight hg, Pi.mul_apply]
  rw [lintegral_weight_closedSimplex g]
  have hmass := lintegral_weight_closedSimplex (fun _ => 1)
  simp only [mul_one] at hmass
  rw [hmass]

section Projection

variable (W : ComplexWindow) (μ : Measure Albert) [IsProbabilityMeasure μ]
  (hu : ∀ᵐ p ∂μ, IsAtom p)
  (hi : ∀ f : Albert ≃ₗ[ℝ] Albert,
    (∀ x y, f (jordanMul x y) = jordanMul (f x) (f y)) →
    f albertUnit = albertUnit → μ.map f = μ)

example (M : ComplexMatrix3) (hM : M.IsHermitian) :
    orderedMatrixEigenvaluePair M = (sortedHermitianSpectrum hM 0, sortedHermitianSpectrum hM 1) :=
  orderedMatrixEigenvaluePair_of_isHermitian M hM

example (p : Albert) :
    orderedMatrixEigenvaluePair (projectedMatrix W p) =
      (sortedHermitianSpectrum (windowProj W p).property 0,
        sortedHermitianSpectrum (windowProj W p).property 1) :=
  orderedMatrixEigenvaluePair_of_isHermitian _ (windowProj W p).property

example :
    μ.map (orderedMatrixEigenvaluePair ∘ projectedMatrix W) =
      normalizedFourColumnOrderedSimplexDensity :=
  projectedAlbertAtom_orderedEigenvalueLaw_eq_density W μ hu hi

example :
    (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6,
      (μ.map (orderedMatrixEigenvaluePair ∘ projectedMatrix W)).map (simplexRelabel i) =
      (∫⁻ p in closedEigenvalueSimplex, spectralSimplexWeight p)⁻¹ •
        (volume.restrict closedEigenvalueSimplex).withDensity spectralSimplexWeight :=
  (projectedAlbertAtom_uniformlyRelabelledEigenvalueLaw_eq_density W μ hu hi).trans
    checkedSymmetricDensity_closedSimplex

end Projection

#print axioms simplexRelabel_apply
#print axioms measurePreserving_simplexRelabel
#print axioms labelledEigenvalueSimplex_disjoint
#print axioms spectralSimplexWeight_relabel
#print axioms lintegral_spectralSimplexWeight_partition
#print axioms spectralSimplexWeight_mass
#print axioms uniformlyRelabelledFourColumnEigenvalueLaw_eq_density
#print axioms aemeasurable_orderedMatrixEigenvaluePair_four
#print axioms projectedAlbertAtom_orderedEigenvalueLaw_eq_density
#print axioms projectedAlbertAtom_uniformlyRelabelledEigenvalueLaw_eq_density
#print axioms checkedSymmetricDensity_closedSimplex
