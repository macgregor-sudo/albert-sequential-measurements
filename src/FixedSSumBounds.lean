/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCubicLowerBounds
public import FixedSCornerConditions

/-! Conceptual all-state mass bound from the trace and monic cubic of the
literal sum of four fixed-S atoms. Only the sum is diagonalized. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators

def fixedSAtomSum : Albert := ∑ i : Fin 4, fixedS i

theorem fixedSAtomSum_positive : IsPositive fixedSAtomSum := by
  simpa only [fixedSAtomSum, Fin.sum_univ_four] using
    isPositive_add _ _ (isPositive_add _ _ (isPositive_add _ _
      (isPositive_idempotent _ (fixedS_isAtom 0).1)
      (isPositive_idempotent _ (fixedS_isAtom 1).1))
      (isPositive_idempotent _ (fixedS_isAtom 2).1))
      (isPositive_idempotent _ (fixedS_isAtom 3).1)

theorem fixedSAtomSum_trace : albertTrace fixedSAtomSum = 4 := by
  simp only [fixedSAtomSum, Fin.sum_univ_four, albertTrace_add,
    (fixedS_isAtom 0).2, (fixedS_isAtom 1).2, (fixedS_isAtom 2).2, (fixedS_isAtom 3).2]
  norm_num

theorem fixedSAtomSum_trace_square :
    albertTrace (jordanMul fixedSAtomSum fixedSAtomSum) = 25 / 3 := by
  have ho (i j : Fin 4) : tracePairing (fixedS i) (fixedS j) =
      if i = j then 1 else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 / 2 else 1 / 3 :=
    nativeOverlaps_fixedS_eq i j
  change tracePairing fixedSAtomSum fixedSAtomSum = _
  simp only [fixedSAtomSum, Fin.sum_univ_four, tracePairing_add_left, tracePairing_add_right, ho]
  norm_num

theorem fixedSAtomSum_trace_cube :
    albertTrace (jordanMul fixedSAtomSum (jordanMul fixedSAtomSum fixedSAtomSum)) = 61 / 3 := by
  have hr (i j k : Fin 4) : tracePairing (fixedS i) (jordanMul (fixedS j) (fixedS k)) =
      fixedSTriangleVal i j k := nativeTriangles_fixedS_eq i j k
  change tracePairing fixedSAtomSum (jordanMul fixedSAtomSum fixedSAtomSum) = _
  simp only [fixedSAtomSum, Fin.sum_univ_four, jordanMul_add_left, jordanMul_add_right,
    tracePairing_add_left, tracePairing_add_right, hr]
  norm_num [fixedSTriangleVal, nativeOverlaps_fixedS_eq]

theorem fixedSAtomSum_cubic :
    jordanMul fixedSAtomSum (jordanMul fixedSAtomSum fixedSAtomSum) -
      (4 : ℝ) • jordanMul fixedSAtomSum fixedSAtomSum +
      (23 / 6 : ℝ) • fixedSAtomSum - (7 / 9 : ℝ) • albertUnit = 0 := by
  have h := cubic_characteristic_identity fixedSAtomSum
  rw [fixedSAtomSum_trace, fixedSAtomSum_trace_square, fixedSAtomSum_trace_cube] at h
  norm_num at h
  rw [h]
  module

theorem fixedSAtomSum_lower : IsPositive (fixedSAtomSum - (14 / 69 : ℝ) • albertUnit) := by
  have h := native_positive_lower_of_monicCubic fixedSAtomSum fixedSAtomSum_positive
    4 (23 / 6) (7 / 9) fixedSAtomSum_trace (by norm_num) fixedSAtomSum_cubic
  norm_num at h ⊢
  exact h

theorem fixedSAtomSum_density_mass (ρ : Albert) (hρ : IsDensity ρ) :
    (14 / 69 : ℝ) ≤ tracePairing ρ fixedSAtomSum := by
  have h := tracePairing_positive_nonnegative ρ _ hρ.1 fixedSAtomSum_lower
  rw [tracePairing_sub_right, tracePairing_smul_right, tracePairing_unit_right, hρ.2] at h
  linarith

end AlbertSequential
