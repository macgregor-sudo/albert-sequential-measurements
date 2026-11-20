/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Local inverse for the actual spectral chart at a diagonal with distinct eigenvalues. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open NormedSpace
open scoped Matrix Matrix.Norms.Frobenius

/-- Eigenvalue variations in the first three real spectral coordinates. -/
def spectralVariations (q : Fin 9 → ℝ) : Fin 3 → ℝ := ![q 0, q 1, q 2]

/-- The three complex upper entries of the infinitesimal angular parameter. -/
def spectralOrbitOffsets (q : Fin 9 → ℝ) : Fin 3 → ℂ :=
  ![⟨q 3, q 4⟩, ⟨q 5, q 6⟩, ⟨q 7, q 8⟩]

/-- Exponentiating the zero-diagonal skew-Hermitian generator gives an actual unitary. -/
def spectralExpUnitary (v : Fin 3 → ℂ) : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨exp (spectralSkewMatrix v), exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.mem_iff.mpr (spectralSkewMatrix_conjTranspose v))⟩

theorem spectralExpUnitary_val (v : Fin 3 → ℂ) :
    (spectralExpUnitary v : ComplexMatrix3) = exp (spectralSkewMatrix v) := rfl

theorem spectralExpUnitary_star_val (v : Fin 3 → ℂ) :
    star (spectralExpUnitary v : ComplexMatrix3) = exp (-spectralSkewMatrix v) := by
  rw [spectralExpUnitary_val, star_exp, Matrix.star_eq_conjTranspose, spectralSkewMatrix_conjTranspose]

theorem continuous_spectralExpUnitary : Continuous spectralExpUnitary := by
  apply Continuous.subtype_mk _ _
  apply exp_continuous.comp
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralSkewMatrix, mkHerm3Matrix, Matrix.smul_apply] <;> fun_prop

/-- Pack the real spectral-coordinate variations as a diagonal and an angular generator. -/
def spectralChartInputs : (Fin 9 → ℝ) →L[ℝ] ComplexMatrix3 × ComplexMatrix3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => (Matrix.diagonal (fun i => (spectralVariations q i : ℂ)),
        spectralSkewMatrix (spectralOrbitOffsets q))
      map_add' := by
        intro q r
        apply Prod.ext
        · ext i j
          fin_cases i <;> fin_cases j <;> simp [spectralVariations]
        · ext i j
          fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
            simp [spectralSkewMatrix, spectralOrbitOffsets, mkHerm3Matrix, Matrix.smul_apply,
              Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring
      map_smul' := by
        intro x q
        apply Prod.ext
        · ext i j
          fin_cases i <;> fin_cases j <;> simp [spectralVariations, Complex.real_smul]
        · ext i j
          fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
            simp [spectralSkewMatrix, spectralOrbitOffsets, mkHerm3Matrix, Matrix.smul_apply,
              Complex.real_smul, Complex.mul_re, Complex.mul_im] }

/-- Read the real Hermitian matrix coordinates as a continuous linear map on matrices. -/
def spectralMatrixOutput : ComplexMatrix3 →L[ℝ] (Fin 9 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hermitianMatrixRealCoordinates
      map_add' := by
        intro M N
        funext i
        fin_cases i <;> simp [hermitianMatrixRealCoordinates, Matrix.add_apply, Complex.add_re, Complex.add_im]
      map_smul' := by
        intro c M
        funext i
        fin_cases i <;> simp [hermitianMatrixRealCoordinates, Matrix.smul_apply, Complex.real_smul,
          Complex.mul_re, Complex.mul_im] }

/-- The ambient-matrix exponential chart before imposing the Hermitian coordinate restrictions. -/
def spectralMatrixExpChart (s : Fin 3 → ℝ) (p : ComplexMatrix3 × ComplexMatrix3) : ComplexMatrix3 :=
  let D : ComplexMatrix3 := Matrix.diagonal fun i => (s i : ℂ)
  exp p.2 * (D + p.1) * exp (-p.2)

/-- Nine real coordinates of the literal unitary exponential conjugation chart,
with the first three coordinates varying the eigenvalues around the base diagonal. -/
def spectralExpChart (s : Fin 3 → ℝ) (q : Fin 9 → ℝ) : Fin 9 → ℝ :=
  spectralMatrixOutput (spectralMatrixExpChart s (spectralChartInputs q))

theorem spectralExpChart_apply (s : Fin 3 → ℝ) (q : Fin 9 → ℝ) :
    spectralExpChart s q = hermitianMatrixRealCoordinates
      (exp (spectralSkewMatrix (spectralOrbitOffsets q)) *
        Matrix.diagonal (fun i => ((s i + spectralVariations q i : ℝ) : ℂ)) *
        exp (-spectralSkewMatrix (spectralOrbitOffsets q))) := by
  change hermitianMatrixRealCoordinates (_ * (Matrix.diagonal (fun i => (s i : ℂ)) +
    Matrix.diagonal (fun i => (spectralVariations q i : ℂ))) * _) = _
  have hK : (spectralChartInputs q).2 = spectralSkewMatrix (spectralOrbitOffsets q) := rfl
  rw [Matrix.diagonal_add, hK]
  simp only [Complex.ofReal_add]

private theorem contDiff_spectralMatrixExpChart (s : Fin 3 → ℝ) :
    ContDiff ℝ 1 (spectralMatrixExpChart s) := by
  have he : ContDiff ℝ 1 (fun M : ComplexMatrix3 => exp M) :=
    contDiff_iff_contDiffAt.mpr fun M => (exp_analytic (𝕂 := ℝ) M).contDiffAt
  unfold spectralMatrixExpChart
  exact ((he.comp contDiff_snd).mul (contDiff_const.add contDiff_fst)).mul
    (he.comp contDiff_snd.neg)

/-- The actual spectral exponential chart is continuously differentiable on all its coordinates. -/
theorem contDiff_spectralExpChart (s : Fin 3 → ℝ) : ContDiff ℝ 1 (spectralExpChart s) :=
  spectralMatrixOutput.contDiff.comp ((contDiff_spectralMatrixExpChart s).comp spectralChartInputs.contDiff)

/-- The genuine local map has the displayed nine-variable derivative at its base point. -/
theorem fderiv_spectralExpChart_zero (s : Fin 3 → ℝ) :
    fderiv ℝ (spectralExpChart s) 0 =
      (Matrix.diagonal (spectralLinearizationWeights s)).mulVecLin.toContinuousLinearMap := by
  let F := spectralMatrixExpChart s
  have h0 : spectralChartInputs (0 : Fin 9 → ℝ) = 0 := spectralChartInputs.map_zero
  have hF : HasFDerivAt F (fderiv ℝ F (0 : ComplexMatrix3 × ComplexMatrix3)) 0 :=
    ((contDiff_spectralMatrixExpChart s).differentiable one_ne_zero 0).hasFDerivAt
  have hF' : HasFDerivAt F (fderiv ℝ F (0 : ComplexMatrix3 × ComplexMatrix3))
      (spectralChartInputs (0 : Fin 9 → ℝ)) := by rw [h0]; exact hF
  have hp := hF'.comp (0 : Fin 9 → ℝ) spectralChartInputs.hasFDerivAt
  have h := (spectralMatrixOutput.hasFDerivAt.comp (0 : Fin 9 → ℝ) hp).fderiv
  rw [show spectralExpChart s = spectralMatrixOutput ∘ F ∘ spectralChartInputs by rfl]
  rw [h]
  ext q i
  change hermitianMatrixRealCoordinates (fderiv ℝ F 0 (spectralChartInputs q)) i = _
  have hl := spectralExpConjugation_derivative_coordinates s (spectralVariations q) (spectralOrbitOffsets q)
  change hermitianMatrixRealCoordinates (fderiv ℝ F 0 (spectralChartInputs q)) = _ at hl
  have hv : ![spectralVariations q 0, spectralVariations q 1, spectralVariations q 2,
      (spectralOrbitOffsets q 0).re, (spectralOrbitOffsets q 0).im,
      (spectralOrbitOffsets q 1).re, (spectralOrbitOffsets q 1).im,
      (spectralOrbitOffsets q 2).re, (spectralOrbitOffsets q 2).im] = q := by
    funext j
    fin_cases j <;> rfl
  rw [hl, hv]
  rfl

/-- At each simple diagonal the actual exponential spectral map is locally invertible. -/
theorem spectralExpChart_localHomeomorph (s : Fin 3 → ℝ) (hs : Function.Injective s) :
    ∃ e : OpenPartialHomeomorph (Fin 9 → ℝ) (Fin 9 → ℝ),
      0 ∈ e.source ∧ (e : (Fin 9 → ℝ) → Fin 9 → ℝ) = spectralExpChart s := by
  let L := (Matrix.diagonal (spectralLinearizationWeights s)).mulVecLin.toContinuousLinearMap
  have hdet : L.det ≠ 0 := by
    change LinearMap.det (Matrix.diagonal (spectralLinearizationWeights s)).mulVecLin ≠ 0
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin', spectralLinearization_det]
    have h01 : (1 : Fin 3) ≠ 0 := by decide
    have h02 : (2 : Fin 3) ≠ 0 := by decide
    have h12 : (2 : Fin 3) ≠ 1 := by decide
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (fun h => h01 (hs h))))
      (pow_ne_zero 2 (sub_ne_zero.mpr (fun h => h02 (hs h)))))
      (pow_ne_zero 2 (sub_ne_zero.mpr (fun h => h12 (hs h))))
  let e := L.toContinuousLinearEquivOfDetNeZero hdet
  have hd : ContDiffAt ℝ 1 (spectralExpChart s) 0 := (contDiff_spectralExpChart s).contDiffAt
  have hL : fderiv ℝ (spectralExpChart s) 0 = L := fderiv_spectralExpChart_zero s
  have hf : HasFDerivAt (spectralExpChart s) (e : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ)) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, ← hL]
    exact ((contDiff_spectralExpChart s).differentiable one_ne_zero 0).hasFDerivAt
  exact ⟨hd.toOpenPartialHomeomorph _ hf one_ne_zero,
    hd.mem_toOpenPartialHomeomorph_source hf one_ne_zero, rfl⟩

end AlbertSequential.WindowProbability
