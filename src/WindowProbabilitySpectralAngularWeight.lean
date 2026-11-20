/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralJacobianFactor

/-! The angular Jacobian factor used by the finite spectral atlas. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open NormedSpace
open scoped Matrix Matrix.Norms.Frobenius

private theorem continuous_spectralSkewMatrix : Continuous spectralSkewMatrix := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralSkewMatrix, mkHerm3Matrix, Matrix.smul_apply] <;> fun_prop

private theorem continuous_spectralAngularMatrixDerivative_apply (w : Fin 9 → ℝ) :
    Continuous (fun v => spectralAngularMatrixDerivative v w) := by
  let E := (ContinuousLinearMap.snd ℝ ComplexMatrix3 ComplexMatrix3).comp spectralChartInputs
  have he : ContDiff ℝ 1 (fun M : ComplexMatrix3 => exp M) :=
    contDiff_iff_contDiffAt.mpr fun M => (exp_analytic (𝕂 := ℝ) M).contDiffAt
  have hA := (he.continuous_fderiv one_ne_zero).comp continuous_spectralSkewMatrix
  have hE : Continuous (fun v => (fderiv ℝ (fun M : ComplexMatrix3 => exp M) (spectralSkewMatrix v)) (E w)) :=
    hA.clm_apply continuous_const
  have hU : Continuous (fun v => (spectralExpUnitary v : ComplexMatrix3)) :=
    continuous_subtype_val.comp continuous_spectralExpUnitary
  exact hU.star.mul hE

/-- The angular factor is continuous, so it is bounded on any compact angular neighborhood. -/
theorem continuous_spectralAngularJacobian :
    Continuous (fun v => |(spectralAngularRealDerivative v).det|) := by
  have hc : Continuous (fun v => LinearMap.toMatrix' (spectralAngularRealDerivative v).toLinearMap) := by
    apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    let w : Fin 9 → ℝ := Pi.single j 1
    change Continuous (fun v => if i.val < 3 then w i else spectralMatrixOutput (spectralAngularMatrixDerivative v w) i)
    by_cases h : i.val < 3
    · simp only [ite_eq_left h]
      exact continuous_const
    · simp only [ite_eq_right h]
      exact (continuous_apply i).comp (spectralMatrixOutput.continuous.comp
        (continuous_spectralAngularMatrixDerivative_apply w))
  have hd := hc.matrix_det
  exact continuous_abs.comp (by simpa only [LinearMap.det_toMatrix'] using hd)

/-- The normalized angular derivative at the chart center is the identity. -/
theorem spectralAngularRealDerivative_zero : spectralAngularRealDerivative 0 = 1 := by
  have hK : spectralSkewMatrix 0 = 0 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [spectralSkewMatrix, mkHerm3Matrix, Matrix.smul_apply] <;> rfl
  have hU : (spectralExpUnitary 0 : ComplexMatrix3) = 1 := by
    rw [spectralExpUnitary_val, hK, exp_zero]
  have hA (q : Fin 9 → ℝ) : spectralAngularMatrixDerivative 0 q = spectralSkewMatrix (spectralOrbitOffsets q) := by
    have he : fderiv ℝ (fun A : ComplexMatrix3 => exp A) 0 = 1 :=
      (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ComplexMatrix3)).fderiv
    dsimp only [spectralAngularMatrixDerivative]
    rw [hU, hK, he, Matrix.conjTranspose_one, one_smul]
    rfl
  apply ContinuousLinearMap.ext
  intro q
  funext i
  change (if i.val < 3 then q i else spectralMatrixOutput (spectralAngularMatrixDerivative 0 q) i) = q i
  rw [hA]
  fin_cases i <;> simp [spectralMatrixOutput, hermitianMatrixRealCoordinates, spectralSkewMatrix,
    mkHerm3Matrix, spectralOrbitOffsets, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

end AlbertSequential.WindowProbability
