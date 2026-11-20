/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralSectorIntegrals
public import WindowProbabilitySpectralFlagProjection

/-! The global ordered eigenvalue marginal of the actual four-column Gram probability. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter Set MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The sorted spectrum of the exact native Hermitian draw. -/
def sortedGramSpectrum (M : Hermitian3) : Fin 3 → ℝ :=
  sortedHermitianSpectrum (show M.val.IsHermitian from M.property)

private theorem lintegral_gramSpectralPartition {C : SpectralAngularChart} (A : SpectralAngularPartition C)
    (g : (Fin 3 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in spectralFlagCoordinateRegion spectralPositiveChamber,
      ENNReal.ofReal (complexFourColumnGramWeight (hermitianMatrixRealCoordinateEquiv.symm y)) *
        g (sortedSpectrumAtCoords y)) =
      (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * g x) *
        ∑ i : Fin A.count, ∫⁻ v in A.domain i, spectralAngularWeight v := by
  rw [A.lintegral_coordinateSector_partition spectralPositiveChamber
    isOpen_spectralPositiveChamber.measurableSet (fun _ hx => hx.1) volume]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  refine lintegral_gramSpectralSector A i (fun y => g (sortedSpectrumAtCoords y)) g hg ?_
  intro x hx v _
  rw [sortedSpectrumAtCoords_angularCoordinateBlock (A.translate i) x hx.1 v]

/-- The raw Gram probability is carried by the coordinates covered by the actual spectral atlas. -/
theorem ae_rawFourColumnGramSpectralRegion :
    ∀ᵐ M ∂rawFourColumnHermitianGramLaw,
      hermitianMatrixRealCoordinateEquiv M ∈ spectralFlagCoordinateRegion spectralPositiveChamber := by
  rw [rawFourColumnHermitianGramLaw_eq_density spectralHermitianVolume]
  filter_upwards [ae_complexFourColumnGramDensityMeasure_posDef_simple spectralHermitianVolume] with M hM
  exact posDef_discriminant_mem_spectralFlagCoordinateRegion M.val hM.1 hM.2

/-- The ordered eigenvalue coordinates are measurable for the actual raw draw. -/
theorem aemeasurable_sortedGramSpectrum : AEMeasurable sortedGramSpectrum rawFourColumnHermitianGramLaw := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  let e := hermitianMatrixRealCoordinateEquiv.toContinuousLinearEquiv
  let R := spectralFlagCoordinateRegion spectralPositiveChamber
  have hR : MeasurableSet R := measurableSet_spectralFlagCoordinateRegion spectralPositiveChamber
    isOpen_spectralPositiveChamber.measurableSet (fun _ hx => hx.1)
  have hEmb := MeasurableEmbedding.subtype_coe hR
  let f : R → Fin 3 → ℝ := fun x => sortedSpectrumAtCoords x.val
  have hf : Measurable f := measurable_sortedSpectrumAtCoords_on_region spectralPositiveChamber
    isOpen_spectralPositiveChamber.measurableSet (fun _ hx => hx.1)
  obtain ⟨g, hg, h⟩ := hEmb.exists_measurable_extend hf (fun _ => inferInstance)
  refine ⟨g ∘ e, hg.comp e.continuous.measurable, ?_⟩
  filter_upwards [ae_rawFourColumnGramSpectralRegion] with M hM
  have he := congrFun h (⟨e M, hM⟩ : R)
  change sortedGramSpectrum M = g (e M)
  rw [show g (e M) = sortedSpectrumAtCoords (e M) from he]
  change sortedGramSpectrum M = sortedGramSpectrum (hermitianMatrixRealCoordinateEquiv.symm
    (hermitianMatrixRealCoordinateEquiv M))
  rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply]

private theorem lintegral_rawFourColumnSpectrum_eq_chart (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    (∫⁻ M, g (sortedGramSpectrum M) ∂rawFourColumnHermitianGramLaw) =
      (∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂spectralHermitianVolume)⁻¹ *
        ∫⁻ y in spectralFlagCoordinateRegion spectralPositiveChamber,
          ENNReal.ofReal (complexFourColumnGramWeight (hermitianMatrixRealCoordinateEquiv.symm y)) *
            g (sortedSpectrumAtCoords y) := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  let e := hermitianMatrixRealCoordinateEquiv.toContinuousLinearEquiv
  let μ := spectralHermitianVolume
  let ρ := complexFourColumnGramDensityMeasure μ
  let R := spectralFlagCoordinateRegion spectralPositiveChamber
  let S := e ⁻¹' R
  let w (M : Hermitian3) := ENNReal.ofReal (complexFourColumnGramWeight M)
  let m := ∫⁻ M, w M ∂μ
  have hR : MeasurableSet R := measurableSet_spectralFlagCoordinateRegion spectralPositiveChamber
    isOpen_spectralPositiveChamber.measurableSet (fun _ hx => hx.1)
  have hS : MeasurableSet S := e.continuous.measurable hR
  have hae : ∀ᵐ M ∂ρ, M ∈ S := by
    change ∀ᵐ M ∂complexFourColumnGramDensityMeasure μ, M ∈ S
    rw [← rawFourColumnHermitianGramLaw_eq_density μ]
    exact ae_rawFourColumnGramSpectralRegion
  have hρ : ρ.restrict S = ρ := Measure.restrict_eq_self_of_ae_mem hae
  rw [rawFourColumnHermitianGramLaw_eq_density μ]
  change (∫⁻ M, g (sortedGramSpectrum M) ∂ρ) = _
  have he : (∫⁻ M, g (sortedGramSpectrum M) ∂ρ) = ∫⁻ M in S, g (sortedGramSpectrum M) ∂ρ := by
    rw [hρ]
  rw [he]
  change (∫⁻ M in S, g (sortedGramSpectrum M) ∂(m⁻¹ • μ.withDensity w)) =
    m⁻¹ * ∫⁻ y in R, _
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable μ
      measurable_complexFourColumnGramWeight.ennreal_ofReal _ hS
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  change (∫⁻ M in S, w M * g (sortedGramSpectrum M) ∂μ) =
    ∫⁻ y in R, w (e.symm y) * g (sortedSpectrumAtCoords y)
  change (∫⁻ M in S, w M * g (sortedGramSpectrum M) ∂(volume.map e.symm)) = _
  have hR' : e.symm ⁻¹' S = R := by ext y; simp [S]
  rw [Measure.restrict_map e.symm.continuous.measurable hS, hR']
  have hEmb : MeasurableEmbedding (e.symm : (Fin 9 → ℝ) → Hermitian3) :=
    e.symm.toHomeomorph.measurableEmbedding
  exact hEmb.lintegral_map (fun M => w M * g (sortedGramSpectrum M))

/-- The ordered unnormalized eigenvalues of the actual complex four-column Gram law
have the exact normalized squared-Vandermonde weight on the positive chamber. -/
theorem lintegral_rawFourColumnSpectrum_eq_weight (g : (Fin 3 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ M, g (sortedGramSpectrum M) ∂rawFourColumnHermitianGramLaw) =
      (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x)⁻¹ *
        ∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * g x := by
  obtain ⟨C⟩ := exists_spectralAngularChart
  obtain ⟨A⟩ := exists_spectralAngularPartition C
  let m := ∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂spectralHermitianVolume
  let a := ∑ i : Fin A.count, ∫⁻ v in A.domain i, spectralAngularWeight v
  let b := ∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x
  have hprod (f : (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ M, f (sortedGramSpectrum M) ∂rawFourColumnHermitianGramLaw) =
        (m⁻¹ * a) * ∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * f x := by
    rw [lintegral_rawFourColumnSpectrum_eq_chart, lintegral_gramSpectralPartition A f hf]
    change m⁻¹ * ((∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * f x) * a) =
      (m⁻¹ * a) * (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * f x)
    ac_rfl
  have hprob : IsProbabilityMeasure rawFourColumnHermitianGramLaw := by
    rw [rawFourColumnHermitianGramLaw_eq_density spectralHermitianVolume]
    infer_instance
  have hOne : 1 = (m⁻¹ * a) * b := by
    simpa [b] using hprod (fun _ => 1) measurable_const
  have hb0 : b ≠ 0 := by intro h; rw [h, mul_zero] at hOne; exact one_ne_zero hOne
  have hbT : b ≠ ∞ := by
    intro h
    by_cases hc : m⁻¹ * a = 0
    · rw [hc, zero_mul] at hOne
      exact one_ne_zero hOne
    · rw [h, ENNReal.mul_top hc] at hOne
      exact ENNReal.one_ne_top hOne
  have hc : m⁻¹ * a = b⁻¹ := by
    calc
      _ = (m⁻¹ * a) * b * b⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hb0 hbT, mul_one]
      _ = _ := by rw [← hOne, one_mul]
  rw [hprod g hg, hc]

end AlbertSequential.WindowProbability
