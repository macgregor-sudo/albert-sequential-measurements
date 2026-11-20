/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilityAlbertWindowLaw
public import WindowProbabilitySpectralSimplexSymmetricLaw

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped AlbertSequential.WindowProbability ENNReal

/-- The first two entries of the ordered spectrum, using the nine real Hermitian coordinates. -/
def orderedMatrixEigenvaluePair (M : ComplexMatrix3) : ℝ × ℝ :=
  let c := sortedSpectrumAtCoords (hermitianMatrixRealCoordinates M)
  (c 0, c 1)

theorem orderedMatrixEigenvaluePair_of_isHermitian (M : ComplexMatrix3) (hM : M.IsHermitian) :
    orderedMatrixEigenvaluePair M = (sortedHermitianSpectrum hM 0, sortedHermitianSpectrum hM 1) := by
  let X : Hermitian3 := ⟨M, hM⟩
  have hs : sortedSpectrumAtCoords (hermitianMatrixRealCoordinates M) = sortedHermitianSpectrum hM := by
    change sortedSpectrumOfHermitian (hermitianMatrixRealCoordinateEquiv.symm
      (hermitianMatrixRealCoordinateEquiv X)) = _
    rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply]
    rfl
  unfold orderedMatrixEigenvaluePair
  rw [hs]

private theorem measurable_hermitianMatrixRealCoordinates : Measurable hermitianMatrixRealCoordinates := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> simp [hermitianMatrixRealCoordinates] <;> fun_prop

theorem aemeasurable_orderedMatrixEigenvaluePair_four :
    AEMeasurable orderedMatrixEigenvaluePair (inducedComplexStateLaw 4) := by
  let Ω : Set (Fin 3 → ℝ) := {c | StrictAnti c}
  have hΩ : MeasurableSet Ω := isOpen_strictAnti_fin3.measurableSet
  have hs : ∀ c ∈ Ω, StrictAnti c := fun _ hc => hc
  have hRegion : ∀ᵐ x ∂(inducedComplexStateLaw 4).map hermitianMatrixRealCoordinates,
      x ∈ spectralFlagCoordinateRegion Ω := by
    refine (ae_map_iff measurable_hermitianMatrixRealCoordinates.aemeasurable
      (measurableSet_spectralFlagCoordinateRegion Ω hΩ hs)).mpr ?_
    filter_upwards [ae_inducedComplexStateLaw_four_distinct_eigenvalues] with M hM
    obtain ⟨hHerm, hSimple⟩ := hM
    obtain ⟨c, F, hc, he⟩ := exists_spectralFlagEvaluate_of_simple M hHerm hSimple
    exact ⟨(c, F), ⟨hc, mem_univ _⟩, congrArg hermitianMatrixRealCoordinates he⟩
  have ha := (aemeasurable_sortedSpectrumAtCoords_of_ae_mem Ω hΩ hs _ hRegion).comp_measurable
    measurable_hermitianMatrixRealCoordinates
  exact (measurable_pi_apply 0 |>.comp_aemeasurable ha).prodMk
    (measurable_pi_apply 1 |>.comp_aemeasurable ha)

theorem orderedMatrixEigenvaluePair_inducedFour_law_eq_density :
    (inducedComplexStateLaw 4).map orderedMatrixEigenvaluePair = normalizedFourColumnOrderedSimplexDensity := by
  have hMap : (inducedComplexStateLaw 4).map orderedMatrixEigenvaluePair =
      (standardComplexGaussianMatrix 4).map (orderedMatrixEigenvaluePair ∘ normalizedComplexGram 4) :=
    aemeasurable_orderedMatrixEigenvaluePair_four.map_map_of_aemeasurable
      (measurable_normalizedComplexGram 4).aemeasurable
  rw [hMap]
  have hEq : orderedMatrixEigenvaluePair ∘ normalizedComplexGram 4 = normalizedFourColumnEigenvaluePair := by
    funext Z
    exact orderedMatrixEigenvaluePair_of_isHermitian _ (normalizedComplexGram_isHermitian 4 Z)
  rw [hEq, normalizedFourColumnEigenvaluePair_law_eq_density]

/-- The ordered eigenvalues of the actual projected invariant Albert atom have the ordered density. -/
theorem projectedAlbertAtom_orderedEigenvalueLaw_eq_density (W : ComplexWindow)
    (μ : Measure Albert) [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, IsAtom p)
    (hinv : ∀ (f : Albert ≃ₗ[ℝ] Albert),
      (∀ x y, f (jordanMul x y) = jordanMul (f x) (f y)) →
      f albertUnit = albertUnit → μ.map f = μ) :
    μ.map (orderedMatrixEigenvaluePair ∘ projectedMatrix W) = normalizedFourColumnOrderedSimplexDensity := by
  have hW := albert_complexWindow_probability_law_of_invariant W μ hμ hinv
  have hSpec : AEMeasurable orderedMatrixEigenvaluePair (μ.map (projectedMatrix W)) :=
    hW.symm ▸ aemeasurable_orderedMatrixEigenvaluePair_four
  rw [← hSpec.map_map_of_aemeasurable (measurable_projectedMatrix W).aemeasurable,
    hW, orderedMatrixEigenvaluePair_inducedFour_law_eq_density]

/-- Relabelling the actual projected spectrum uniformly gives the density on the whole simplex. -/
theorem projectedAlbertAtom_uniformlyRelabelledEigenvalueLaw_eq_density (W : ComplexWindow)
    (μ : Measure Albert) [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, IsAtom p)
    (hinv : ∀ (f : Albert ≃ₗ[ℝ] Albert),
      (∀ x y, f (jordanMul x y) = jordanMul (f x) (f y)) →
      f albertUnit = albertUnit → μ.map f = μ) :
    (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6,
      (μ.map (orderedMatrixEigenvaluePair ∘ projectedMatrix W)).map (simplexRelabel i) =
      normalizedFourColumnSymmetricSimplexDensity := by
  rw [projectedAlbertAtom_orderedEigenvalueLaw_eq_density W μ hμ hinv]
  exact relabelled_orderedSimplexDensity_eq_symmetricDensity

end AlbertSequential.WindowProbability
