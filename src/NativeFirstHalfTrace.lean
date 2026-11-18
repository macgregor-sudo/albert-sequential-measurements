/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfMatrixLaws

/-! The trace constant is eight, calculated from the two actual octonion slots.
This is a symbolic coordinate proof, not an external computed certificate. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace AlbertSequential.NativeAnalysis

theorem jordanMul_upper01 (x y : Albert) :
    (jordanMul x y).2 0 = (1/2 : ℝ) •
      ((x.1 0 + x.1 1) • y.2 0 + (y.1 0 + y.1 1) • x.2 0 +
        octonionMul (x.2 1) (octonionConj (y.2 2)) +
        octonionMul (y.2 1) (octonionConj (x.2 2))) := by
  have h := Glennie.jordan_o01 (recoveredCoordinateEquiv x) (recoveredCoordinateEquiv y)
  rw [← recoveredCoordinateEquiv_jordanMul] at h
  exact h

theorem jordanMul_upper02 (x y : Albert) :
    (jordanMul x y).2 1 = (1/2 : ℝ) •
      ((x.1 0 + x.1 2) • y.2 1 + (y.1 0 + y.1 2) • x.2 1 +
        octonionMul (x.2 0) (y.2 2) + octonionMul (y.2 0) (x.2 2)) := by
  have h := Glennie.jordan_o02 (recoveredCoordinateEquiv x) (recoveredCoordinateEquiv y)
  rw [← recoveredCoordinateEquiv_jordanMul] at h
  exact h

theorem firstHalf_product_first (x : Albert) (u : Octonion) :
    (firstHalfReadout ((2 : ℝ) • jordanMul x (firstHalfInclusion (u,0)))).1 =
      (x.1 0 + x.1 1) • u := by
  change (2 : ℝ) • (jordanMul x (firstHalfInclusion (u,0))).2 0 = _
  rw [jordanMul_upper01]
  change (2 : ℝ) • ((1/2 : ℝ) •
    ((x.1 0 + x.1 1) • u + (0 + 0 : ℝ) • x.2 0 +
      octonionMul (x.2 1) (octonionConj 0) + octonionMul 0 (octonionConj (x.2 2)))) = _
  simp [octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right, smul_smul]

theorem firstHalf_product_second (x : Albert) (u : Octonion) :
    (firstHalfReadout ((2 : ℝ) • jordanMul x (firstHalfInclusion (0,u)))).2 =
      (x.1 0 + x.1 2) • u := by
  change (2 : ℝ) • (jordanMul x (firstHalfInclusion (0,u))).2 1 = _
  rw [jordanMul_upper02]
  change (2 : ℝ) • ((1/2 : ℝ) •
    ((x.1 0 + x.1 2) • u + (0 + 0 : ℝ) • x.2 1 +
      octonionMul (x.2 0) 0 + octonionMul 0 (x.2 2))) = _
  simp [octonionMul_zero_left, octonionMul_zero_right, smul_smul]

def firstHalfMatrix (x : Albert) : Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  LinearMap.toMatrix' (octonionPairCoordinates.toLinearMap.comp
    (firstHalfReadout.comp (((2 : ℝ) • nativeMultiplicationOperator x).comp
      (firstHalfInclusion.comp octonionPairCoordinates.symm.toLinearMap))))

theorem octonionPairCoordinates_single_first (i : OctonionCoordinate) :
    octonionPairCoordinates.symm (Pi.single (0,i) 1) =
      (octonionRealCoordinates.symm (Pi.single i 1), 0) := by
  apply octonionPairCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rcases j with ⟨a,b⟩
  fin_cases a
  · change (Pi.single (0,i) 1 : SpinorCoordinate → ℝ) (0,b) =
      octonionRealCoordinates (octonionRealCoordinates.symm (Pi.single i 1)) b
    rw [LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply]
  · change (Pi.single (0,i) 1 : SpinorCoordinate → ℝ) (1,b) = octonionRealCoordinates 0 b
    rw [map_zero]
    simp [Pi.single_apply]

theorem octonionPairCoordinates_single_second (i : OctonionCoordinate) :
    octonionPairCoordinates.symm (Pi.single (1,i) 1) =
      (0, octonionRealCoordinates.symm (Pi.single i 1)) := by
  apply octonionPairCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rcases j with ⟨a,b⟩
  fin_cases a
  · change (Pi.single (1,i) 1 : SpinorCoordinate → ℝ) (0,b) = octonionRealCoordinates 0 b
    rw [map_zero]
    simp [Pi.single_apply]
  · change (Pi.single (1,i) 1 : SpinorCoordinate → ℝ) (1,b) =
      octonionRealCoordinates (octonionRealCoordinates.symm (Pi.single i 1)) b
    rw [LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply]

theorem firstHalfMatrix_diagonal (x : Albert) (i : SpinorCoordinate) :
    firstHalfMatrix x i i = if i.1 = 0 then x.1 0 + x.1 1 else x.1 0 + x.1 2 := by
  rcases i with ⟨a,b⟩
  fin_cases a
  · change octonionRealCoordinates
      (firstHalfReadout ((2 : ℝ) • jordanMul x
        (firstHalfInclusion (octonionPairCoordinates.symm (Pi.single (0,b) 1))))).1 b = _
    rw [octonionPairCoordinates_single_first, firstHalf_product_first]
    change (octonionRealCoordinates ((x.1 0 + x.1 1) •
      octonionRealCoordinates.symm (Pi.single b 1))) b = x.1 0 + x.1 1
    rw [map_smul, LinearEquiv.apply_symm_apply]
    simp
  · change octonionRealCoordinates
      (firstHalfReadout ((2 : ℝ) • jordanMul x
        (firstHalfInclusion (octonionPairCoordinates.symm (Pi.single (1,b) 1))))).2 b = _
    rw [octonionPairCoordinates_single_second, firstHalf_product_second]
    change (octonionRealCoordinates ((x.1 0 + x.1 2) •
      octonionRealCoordinates.symm (Pi.single b 1))) b = x.1 0 + x.1 2
    rw [map_smul, LinearEquiv.apply_symm_apply]
    simp

theorem firstHalfMatrix_trace (x : Albert) :
    Matrix.trace (firstHalfMatrix x) = 8 * (2 * x.1 0 + x.1 1 + x.1 2) := by
  simp only [Matrix.trace, Matrix.diag, firstHalfMatrix_diagonal,
    Fintype.sum_prod_type, Fin.sum_univ_two, ↓reduceIte, one_ne_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end AlbertSequential.NativeAnalysis
