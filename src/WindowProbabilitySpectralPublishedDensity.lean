/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralSimplexLaw

/-! Identify the printed simplex law with the actual normalized Gaussian Gram matrix. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped Matrix ENNReal

/-- The first two ordered eigenvalues of the literal normalized complex Gram matrix. -/
def normalizedFourColumnEigenvaluePair (Z : Matrix (Fin 3) (Fin 4) ℂ) : ℝ × ℝ :=
  let x := sortedHermitianSpectrum (normalizedComplexGram_isHermitian 4 Z)
  (x 0, x 1)

private theorem sortedGramSpectrum_evaluate (x : Fin 3 → ℝ) (hx : StrictAnti x) (F : SpectralFlag) :
    sortedGramSpectrum ⟨spectralFlagEvaluate x F, spectralFlagEvaluate_isHermitian x F⟩ = x := by
  let M : Hermitian3 := ⟨spectralFlagEvaluate x F, spectralFlagEvaluate_isHermitian x F⟩
  have h := sortedSpectrumAtCoords_evaluate x hx F
  change sortedSpectrumAtCoords (hermitianMatrixRealCoordinateEquiv M) = x at h
  unfold sortedSpectrumAtCoords at h
  rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply] at h
  exact h

private theorem normalizedFourColumnEigenvaluePair_eq_of_chart
    (Z : Matrix (Fin 3) (Fin 4) ℂ)
    (hZ : hermitianMatrixRealCoordinateEquiv (rawFourColumnHermitianGram Z) ∈
      spectralFlagCoordinateRegion spectralPositiveChamber) :
    normalizedFourColumnEigenvaluePair Z = spectrumSimplexProjection (sortedGramSpectrum (rawFourColumnHermitianGram Z)) := by
  obtain ⟨⟨x,F⟩, ⟨hx,_⟩, hcoord⟩ := hZ
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
  let M := rawFourColumnHermitianGram Z
  let D := spectralDiagonal x
  let C := Unitary.conjStarAlgAut ℂ ComplexMatrix3 U
  let N : Hermitian3 := ⟨spectralFlagEvaluate x (spectralFlagOfUnitary U),
    spectralFlagEvaluate_isHermitian x (spectralFlagOfUnitary U)⟩
  have hN : N.val = C D := spectralFlagEvaluate_unitary x U
  have he : N = M := hermitianMatrixRealCoordinateEquiv.injective hcoord
  have hs : sortedGramSpectrum M = x := he ▸ sortedGramSpectrum_evaluate x hx.1 (spectralFlagOfUnitary U)
  let t := ∑ i, x i
  have ht : 0 < t := Finset.sum_pos (fun j _ => hx.2 j) Finset.univ_nonempty
  have htr : M.val.trace = (t : ℂ) := by
    rw [← he, hN, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      Matrix.one_mul]
    dsimp [D, spectralDiagonal, t]
    rw [Matrix.trace_diagonal, Complex.ofReal_sum]
  let y : Fin 3 → ℝ := fun i => x i / t
  have hy : StrictAnti y := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right ht).mpr (hx.1 hij)
  have hn : normalizedComplexGram 4 Z = spectralConjugate U y := by
    change M.val.trace⁻¹ • M.val = C (spectralDiagonal y)
    rw [htr, ← he, hN, ← map_smul]
    congr 1
    change ((t : ℂ)⁻¹ • Matrix.diagonal (fun i => (x i : ℂ))) =
      Matrix.diagonal (fun i => ((x i / t : ℝ) : ℂ))
    ext i j
    by_cases hij : i = j
    · subst j
      simp [div_eq_mul_inv, mul_comm]
    · simp [hij]
  have hNrm : sortedHermitianSpectrum (normalizedComplexGram_isHermitian 4 Z) = y := by
    let Mnorm : Hermitian3 := ⟨normalizedComplexGram 4 Z, normalizedComplexGram_isHermitian 4 Z⟩
    let Nnorm : Hermitian3 := ⟨spectralFlagEvaluate y (spectralFlagOfUnitary U),
      spectralFlagEvaluate_isHermitian y (spectralFlagOfUnitary U)⟩
    have eh : Nnorm.val = spectralConjugate U y := spectralFlagEvaluate_unitary y U
    have hm : Mnorm = Nnorm := Subtype.ext (hn.trans eh.symm)
    change sortedGramSpectrum Mnorm = y
    rw [hm]
    exact sortedGramSpectrum_evaluate y hy (spectralFlagOfUnitary U)
  unfold normalizedFourColumnEigenvaluePair
  rw [hNrm, hs]
  rfl

theorem aemeasurable_normalizedFourColumnEigenvaluePair :
    AEMeasurable normalizedFourColumnEigenvaluePair (standardComplexGaussianMatrix 4) := by
  have hp : Measurable spectrumSimplexProjection := by unfold spectrumSimplexProjection; fun_prop
  have hm := (hp.comp_aemeasurable aemeasurable_sortedGramSpectrum).comp_measurable
    measurable_rawFourColumnHermitianGram
  apply hm.congr
  have he := ae_of_ae_map measurable_rawFourColumnHermitianGram.aemeasurable ae_rawFourColumnGramSpectralRegion
  filter_upwards [he] with Z hZ
  exact (normalizedFourColumnEigenvaluePair_eq_of_chart Z hZ).symm

/-- The actual normalized matrix's ordered simplex spectrum has the printed density. -/
theorem lintegral_normalizedFourColumnEigenvaluePair_eq_weight (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ Z, g (normalizedFourColumnEigenvaluePair Z) ∂standardComplexGaussianMatrix 4) =
      (∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p)⁻¹ *
        ∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p * g p := by
  have hp : Measurable spectrumSimplexProjection := by
    unfold spectrumSimplexProjection
    fun_prop
  have he := ae_of_ae_map measurable_rawFourColumnHermitianGram.aemeasurable ae_rawFourColumnGramSpectralRegion
  calc
    _ = ∫⁻ Z, g (spectrumSimplexProjection (sortedGramSpectrum (rawFourColumnHermitianGram Z)))
        ∂standardComplexGaussianMatrix 4 := by
      apply lintegral_congr_ae
      filter_upwards [he] with Z hZ
      rw [normalizedFourColumnEigenvaluePair_eq_of_chart Z hZ]
    _ = ∫⁻ M, g (spectrumSimplexProjection (sortedGramSpectrum M)) ∂rawFourColumnHermitianGramLaw := by
      have hm := (hg.comp hp).comp_aemeasurable aemeasurable_sortedGramSpectrum
      exact (lintegral_map' hm measurable_rawFourColumnHermitianGram.aemeasurable).symm
    _ = _ := lintegral_traceNormalizedFourColumnSpectrum_eq_weight g hg

/-- The normalized printed eigenvalue density as a Borel measure on the ordered simplex. -/
def normalizedFourColumnOrderedSimplexDensity : Measure (ℝ × ℝ) :=
  (∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p)⁻¹ •
    (volume.restrict orderedEigenvalueSimplex).withDensity fourColumnOrderedSimplexWeight

/-- Exact equality of the actual normalized Gram spectrum law and the printed density. -/
theorem normalizedFourColumnEigenvaluePair_law_eq_density :
    (standardComplexGaussianMatrix 4).map normalizedFourColumnEigenvaluePair =
      normalizedFourColumnOrderedSimplexDensity := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map' hg.aemeasurable aemeasurable_normalizedFourColumnEigenvaluePair,
    lintegral_normalizedFourColumnEigenvaluePair_eq_weight g hg]
  have hw : Measurable fourColumnOrderedSimplexWeight := by
    unfold fourColumnOrderedSimplexWeight fourColumnEigenvalueWeight
    fun_prop
  rw [normalizedFourColumnOrderedSimplexDensity, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ hw hg]
  rfl

end AlbertSequential.WindowProbability
