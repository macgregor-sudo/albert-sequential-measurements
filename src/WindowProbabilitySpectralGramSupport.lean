/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramLaw
public import WindowProbabilitySpectralRegularity

/-! Place the raw Gram probability on the native Hermitian space and
realize its Haar measure by the exact nine spectral coordinates. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The native Hermitian value of the actual rectangular Gaussian draw. -/
def rawFourColumnHermitianGram (Z : Matrix (Fin 3) (Fin 4) ℂ) : Hermitian3 :=
  ⟨Z * Z.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self Z⟩

/-- Unnormalized four-column Gaussian Gram law carried on the Hermitian space itself. -/
def rawFourColumnHermitianGramLaw : Measure Hermitian3 :=
  (standardComplexGaussianMatrix 4).map rawFourColumnHermitianGram

theorem measurable_rawFourColumnHermitianGram : Measurable rawFourColumnHermitianGram := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  fun_prop

/-- In the native Hermitian space, the actual raw Gaussian Gram law is the normalized Haar density. -/
theorem rawFourColumnHermitianGramLaw_eq_density (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    rawFourColumnHermitianGramLaw = complexFourColumnGramDensityMeasure μ := by
  have hc : IsClosed (selfAdjoint ComplexMatrix3 : Set ComplexMatrix3) := by
    change IsClosed {M : ComplexMatrix3 | star M = M}
    exact isClosed_eq continuous_star continuous_id
  have h := (MeasurableEmbedding.subtype_coe hc.measurableSet).map_injective
  apply h
  have hg : Measurable (Subtype.val : Hermitian3 → ComplexMatrix3) := measurable_subtype_coe
  exact (Measure.map_map hg measurable_rawFourColumnHermitianGram).trans
    (fourColumnGaussianGram_eq_density μ)

/-- The Hermitian Haar density occupies the simple positive definite stratum almost surely. -/
theorem ae_complexFourColumnGramDensityMeasure_posDef_simple (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    ∀ᵐ M ∂complexFourColumnGramDensityMeasure μ,
      M.val.PosDef ∧ cubicMatrixDiscriminant (1 / 2 : ℂ) M.val ≠ 0 := by
  rw [← rawFourColumnHermitianGramLaw_eq_density μ]
  have hm : MeasurableSet {M : Hermitian3 |
      M.val.PosDef ∧ cubicMatrixDiscriminant (1 / 2 : ℂ) M.val ≠ 0} :=
    measurableSet_complexPositiveDefiniteCone.inter
      (isClosed_eq (continuous_cubicMatrixDiscriminant.comp continuous_subtype_val)
        continuous_const).isOpen_compl.measurableSet
  change ∀ᵐ M ∂((standardComplexGaussianMatrix 4).map rawFourColumnHermitianGram),
    M.val.PosDef ∧ cubicMatrixDiscriminant (1 / 2 : ℂ) M.val ≠ 0
  rw [ae_map_iff measurable_rawFourColumnHermitianGram.aemeasurable hm]
  filter_upwards [ae_fourColumnGram_posDef, ae_cubicMatrixDiscriminant_complexGaussianGram_four_ne_zero] with Z hP hS
  exact ⟨hP, hS⟩

/-- Hermitian volume in the explicit nine real spectral coordinates. -/
def spectralHermitianVolume : Measure Hermitian3 :=
  volume.map hermitianMatrixRealCoordinateEquiv.symm

instance : spectralHermitianVolume.IsAddHaarMeasure := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  exact hermitianMatrixRealCoordinateEquiv.toContinuousLinearEquiv.symm.isAddHaarMeasure_map volume

/-- Hermitian volume is literally the transport of coordinate Lebesgue measure. -/
theorem measurePreserving_hermitianMatrixRealCoordinateEquiv :
    MeasurePreserving hermitianMatrixRealCoordinateEquiv spectralHermitianVolume volume := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  let e := hermitianMatrixRealCoordinateEquiv.toContinuousLinearEquiv
  refine ⟨e.continuous.measurable, ?_⟩
  change ((volume : Measure (Fin 9 → ℝ)).map e.symm).map e = volume
  rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
  exact congrArg (fun f : (Fin 9 → ℝ) → (Fin 9 → ℝ) => volume.map f)
    (funext e.apply_symm_apply) |>.trans Measure.map_id

/-- Native Hermitian unitary conjugation has unit absolute real determinant. -/
theorem abs_det_native_unitaryConjugation (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    |LinearMap.det (hermitianUnitaryConjugate U).toLinearMap| = 1 := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  let e := hermitianUnitaryConjugate U
  have he := measurePreserving_hermitianUnitaryConjugate μ U
  let r := LinearMap.det e.toLinearMap
  have hm := μ.map_linearMap_addHaar_eq_smul_addHaar e.isUnit_det'.ne_zero
  change μ.map (hermitianUnitaryConjugate U) = ENNReal.ofReal |r⁻¹| • μ at hm
  rw [he.map_eq] at hm
  let B := Metric.ball (0 : Hermitian3) 1
  have hB : 0 < μ B := Metric.isOpen_ball.measure_pos μ ⟨0, Metric.mem_ball_self zero_lt_one⟩
  have hBT : μ B ≠ ∞ := measure_ball_lt_top.ne
  have h := congrArg (fun ν : Measure Hermitian3 => ν B) hm
  rw [smul_apply, smul_eq_mul] at h
  have hscale : 1 = ENNReal.ofReal |r⁻¹| :=
    (ENNReal.mul_left_inj hB.ne' hBT).mp ((one_mul _).trans h)
  have hr := ENNReal.ofReal_eq_one.mp hscale.symm
  rw [abs_inv] at hr
  exact inv_eq_one.mp hr

end AlbertSequential.WindowProbability
