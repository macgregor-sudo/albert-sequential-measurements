/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramCandidate
public import WindowProbabilitySpectralDerivative

/-! Exact Haar scaling under diagonal Hermitian congruence. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The real diagonal, then real and imaginary upper entries, in spectral order. -/
def hermitianMatrixRealCoordinateEquiv : Hermitian3 ≃ₗ[ℝ] (Fin 9 → ℝ) where
  toFun M := hermitianMatrixRealCoordinates M.val
  invFun x := hermitian3Equiv.symm
    (![x 0, x 1, x 2], ![⟨x 3, x 4⟩, ⟨x 5, x 6⟩, ⟨x 7, x 8⟩])
  left_inv M := by
    apply hermitian3Equiv.injective
    rw [hermitian3Equiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> apply Complex.ext <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> simp [hermitianMatrixRealCoordinates, hermitian3Equiv, mkHerm3Matrix]
  map_add' M N := by
    funext i
    fin_cases i <;> simp [hermitianMatrixRealCoordinates, Matrix.add_apply, Complex.add_re, Complex.add_im]
  map_smul' c M := by
    funext i
    fin_cases i <;> simp [hermitianMatrixRealCoordinates, Matrix.smul_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im]

/-- Real diagonal congruence acting on the native Hermitian space. -/
def hermitianDiagonalCongruence (d : Fin 3 → ℝ) : Hermitian3 →ₗ[ℝ] Hermitian3 :=
  hermitianMatrixRealCoordinateEquiv.symm.toLinearMap.comp
    ((Matrix.diagonal (hermitianDiagonalCongruenceWeights d)).mulVecLin.comp
      hermitianMatrixRealCoordinateEquiv.toLinearMap)

/-- The coordinate-linear map is precisely the matrix congruence. -/
theorem hermitianDiagonalCongruence_apply (d : Fin 3 → ℝ) (M : Hermitian3) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    (hermitianDiagonalCongruence d M).val = D * M.val * D := by
  intro D
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (fun _ => by simp [IsSelfAdjoint])
  let N : Hermitian3 := ⟨D * M.val * D, by
    have h := Matrix.isHermitian_mul_mul_conjTranspose D M.property
    rw [hD.eq] at h
    exact h⟩
  have hEq : hermitianDiagonalCongruence d M = N := by
    apply hermitianMatrixRealCoordinateEquiv.injective
    change hermitianMatrixRealCoordinateEquiv (hermitianMatrixRealCoordinateEquiv.symm _) = _
    rw [hermitianMatrixRealCoordinateEquiv.apply_symm_apply]
    exact (hermitianDiagonalCongruence_coordinates d M.val).symm
  exact congrArg Subtype.val hEq

/-- The Haar scaling factor uses the determinant of the actual congruence map. -/
theorem map_hermitianDiagonalCongruence_haar (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) :
    μ.map (hermitianDiagonalCongruence d) = ENNReal.ofReal ((d 0 * d 1 * d 2) ^ 6)⁻¹ • μ := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  have hdet : LinearMap.det (hermitianDiagonalCongruence d) = (d 0 * d 1 * d 2) ^ 6 := by
    have h := LinearMap.det_conj ((Matrix.diagonal (hermitianDiagonalCongruenceWeights d)).mulVecLin)
      hermitianMatrixRealCoordinateEquiv.symm
    simp only [LinearEquiv.symm_symm] at h
    rw [hermitianDiagonalCongruence]
    rw [h, ← Matrix.toLin'_apply', LinearMap.det_toLin', hermitianDiagonalCongruence_det]
  have hpos := pow_pos (mul_pos (mul_pos (hd 0) (hd 1)) (hd 2)) 6
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (hdet.symm ▸ hpos.ne'), hdet,
    abs_of_pos (inv_pos.mpr hpos)]

end AlbertSequential.WindowProbability
