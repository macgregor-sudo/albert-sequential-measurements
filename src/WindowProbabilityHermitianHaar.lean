/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityComplexAmbient
public import WindowProbabilityGaussianRank
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Almost sure positive definiteness of the four-column Gram matrix and
unitary invariance of additive Haar measure in the native Hermitian space. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder

private theorem measurePreserving_realLinearIsometryEquiv_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e μ μ := by
  let c := ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹|
  have hm : μ.map e = c • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ e.toLinearEquiv.isUnit_det'.ne_zero
  let B := Metric.ball (0 : E) 1
  have hB : IsOpen B := Metric.isOpen_ball
  have hp : 0 < μ B := hB.measure_pos μ ⟨0, Metric.mem_ball_self zero_lt_one⟩
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hf : μ B ≠ ∞ := measure_ball_lt_top.ne
  have hpre : e ⁻¹' B = B := by
    ext x
    change dist (e x) 0 < 1 ↔ dist x 0 < 1
    have hd := e.isometry.dist_eq x 0
    rw [e.map_zero] at hd
    rw [hd]
  have h := congrArg (fun ν : Measure E => ν B) hm
  rw [Measure.map_apply e.continuous.measurable hB.measurableSet, hpre,
    smul_apply, smul_eq_mul] at h
  have hc : 1 = c := (ENNReal.mul_left_inj hp.ne' hf).mp ((one_mul (μ B)).trans h)
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hm, ← hc, one_smul]

/-- Conjugation by a unitary preserves additive Haar measure on Hermitian matrices. -/
theorem measurePreserving_hermitianUnitaryConjugate
    (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    MeasurePreserving (hermitianUnitaryConjugate U) μ μ := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  let e : Hermitian3 ≃ₗᵢ[ℝ] Hermitian3 :=
    { hermitianUnitaryConjugate U with
      norm_map' := fun M => by
        change ‖Unitary.conjStarAlgAut ℂ ComplexMatrix3 U M.val‖ = ‖M.val‖
        rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
          CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul] }
  exact measurePreserving_realLinearIsometryEquiv_haar μ e

/-- The actual unnormalized four-column Gaussian law occupies the positive definite cone. -/
theorem ae_fourColumnGram_posDef :
    ∀ᵐ Z ∂(standardComplexGaussianMatrix 4), (Z * Z.conjTranspose).PosDef := by
  filter_upwards [ae_rank_normalizedComplexGram 4] with Z hZ
  have hr : (Z * Z.conjTranspose).rank = Fintype.card (Fin 3) := by
    rw [Matrix.rank_self_mul_conjTranspose, ← rank_normalizedComplexGram 4 Z, hZ]
    decide
  exact (Matrix.posSemidef_self_mul_conjTranspose Z).posDef_iff_det_ne_zero.mpr
    ((complexMatrix_rank_eq_card_iff_det_ne_zero _).mp hr)

end AlbertSequential.WindowProbability
