/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralPowerSimplex

/-! Identify the printed generic density with the actual normalized Gaussian Gram matrix. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped Matrix ENNReal

/-- The first two ordered eigenvalues of the literal normalized complex Gram matrix. -/
def normalizedGramEigenvaluePair (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) : ℝ × ℝ :=
  let x := sortedHermitianSpectrum (normalizedComplexGram_isHermitian k Z)
  (x 0, x 1)

private theorem sortedGramSpectrum_evaluate (x : Fin 3 → ℝ) (hx : StrictAnti x) (F : SpectralFlag) :
    sortedGramSpectrum ⟨spectralFlagEvaluate x F, spectralFlagEvaluate_isHermitian x F⟩ = x := by
  let M : Hermitian3 := ⟨spectralFlagEvaluate x F, spectralFlagEvaluate_isHermitian x F⟩
  have h := sortedSpectrumAtCoords_evaluate x hx F
  change sortedSpectrumAtCoords (hermitianMatrixRealCoordinateEquiv M) = x at h
  unfold sortedSpectrumAtCoords at h
  rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply] at h
  exact h

private theorem normalizedGramEigenvaluePair_eq_of_chart (m : ℕ)
    (Z : Matrix (Fin 3) (Fin (m + 3)) ℂ)
    (hZ : hermitianMatrixRealCoordinateEquiv (rawPowerHermitianGram m Z) ∈
      spectralFlagCoordinateRegion spectralPositiveChamber) :
    normalizedGramEigenvaluePair (m + 3) Z = spectrumSimplexProjection (sortedGramSpectrum (rawPowerHermitianGram m Z)) := by
  obtain ⟨⟨x,F⟩, ⟨hx,_⟩, hcoord⟩ := hZ
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
  let M := rawPowerHermitianGram m Z
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
  have hn : normalizedComplexGram (m + 3) Z = spectralConjugate U y := by
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
  have hNrm : sortedHermitianSpectrum (normalizedComplexGram_isHermitian (m + 3) Z) = y := by
    let Mnorm : Hermitian3 := ⟨normalizedComplexGram (m + 3) Z, normalizedComplexGram_isHermitian (m + 3) Z⟩
    let Nnorm : Hermitian3 := ⟨spectralFlagEvaluate y (spectralFlagOfUnitary U),
      spectralFlagEvaluate_isHermitian y (spectralFlagOfUnitary U)⟩
    have eh : Nnorm.val = spectralConjugate U y := spectralFlagEvaluate_unitary y U
    have hm : Mnorm = Nnorm := Subtype.ext (hn.trans eh.symm)
    change sortedGramSpectrum Mnorm = y
    rw [hm]
    exact sortedGramSpectrum_evaluate y hy (spectralFlagOfUnitary U)
  unfold normalizedGramEigenvaluePair
  rw [hNrm, hs]
  rfl

theorem aemeasurable_normalizedGramEigenvaluePair (m : ℕ) :
    AEMeasurable (normalizedGramEigenvaluePair (m + 3)) (standardComplexGaussianMatrix (m + 3)) := by
  have hp : Measurable spectrumSimplexProjection := by unfold spectrumSimplexProjection; fun_prop
  have hsort := aemeasurable_sortedGramSpectrum.mono_ac (rawPowerHermitianGramLaw_absolutelyContinuous_four m)
  have hm := (hp.comp_aemeasurable hsort).comp_measurable (measurable_rawPowerHermitianGram m)
  apply hm.congr
  have hstratum := ae_rawFourColumnGramSpectralRegion.filter_mono
    (rawPowerHermitianGramLaw_absolutelyContinuous_four m).ae_le
  have he := ae_of_ae_map (measurable_rawPowerHermitianGram m).aemeasurable hstratum
  filter_upwards [he] with Z hZ
  exact (normalizedGramEigenvaluePair_eq_of_chart m Z hZ).symm

/-- The actual normalized matrix's ordered simplex spectrum has the printed density. -/
theorem lintegral_normalizedGramEigenvaluePair_eq_weight (m : ℕ) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ Z, g (normalizedGramEigenvaluePair (m + 3) Z) ∂standardComplexGaussianMatrix (m + 3)) =
      (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p)⁻¹ *
        ∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p * g p := by
  have hp : Measurable spectrumSimplexProjection := by
    unfold spectrumSimplexProjection
    fun_prop
  have hstratum := ae_rawFourColumnGramSpectralRegion.filter_mono
    (rawPowerHermitianGramLaw_absolutelyContinuous_four m).ae_le
  have he := ae_of_ae_map (measurable_rawPowerHermitianGram m).aemeasurable hstratum
  calc
    _ = ∫⁻ Z, g (spectrumSimplexProjection (sortedGramSpectrum (rawPowerHermitianGram m Z)))
        ∂standardComplexGaussianMatrix (m + 3) := by
      apply lintegral_congr_ae
      filter_upwards [he] with Z hZ
      rw [normalizedGramEigenvaluePair_eq_of_chart m Z hZ]
    _ = ∫⁻ M, g (spectrumSimplexProjection (sortedGramSpectrum M)) ∂rawPowerHermitianGramLaw m := by
      have hsort := aemeasurable_sortedGramSpectrum.mono_ac (rawPowerHermitianGramLaw_absolutelyContinuous_four m)
      have hm := (hg.comp hp).comp_aemeasurable hsort
      exact (lintegral_map' hm (measurable_rawPowerHermitianGram m).aemeasurable).symm
    _ = _ := lintegral_traceNormalizedPowerSpectrum_eq_weight m g hg

/-- The normalized printed eigenvalue density as a Borel measure on the ordered simplex. -/
def normalizedPowerOrderedSimplexDensity (m : ℕ) : Measure (ℝ × ℝ) :=
  (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p)⁻¹ •
    (volume.restrict orderedEigenvalueSimplex).withDensity (powerSimplexWeight m)

/-- Exact equality of the actual normalized Gram spectrum law and the printed density. -/
theorem normalizedGramEigenvaluePair_law_eq_density (m : ℕ) :
    (standardComplexGaussianMatrix (m + 3)).map (normalizedGramEigenvaluePair (m + 3)) =
      normalizedPowerOrderedSimplexDensity m := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map' hg.aemeasurable (aemeasurable_normalizedGramEigenvaluePair m),
    lintegral_normalizedGramEigenvaluePair_eq_weight m g hg]
  have hw : Measurable (powerSimplexWeight m) := by
    unfold powerSimplexWeight powerEigenvaluePolynomial
    fun_prop
  rw [normalizedPowerOrderedSimplexDensity, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ hw hg]
  rfl

end AlbertSequential.WindowProbability
