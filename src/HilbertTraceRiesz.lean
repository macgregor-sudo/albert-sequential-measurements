/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! Riesz representation of the real bounded form used to construct an effect. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem bilinear_bound_of_diagonal
    (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (hmin : ∀ x, 0 ≤ B x x) (hmax : ∀ x, B x x ≤ ‖x‖ ^ 2) (x y : H) :
    ‖B x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  have hdisc : discrim (B x x) (2 * B x y) (B y y) ≤ 0 := by
    apply discrim_le_zero
    intro t
    have ht := hmin (t • x + y)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at ht
    rw [hB y x] at ht
    nlinarith
  have hs : (B x y) ^ 2 ≤ B x x * B y y := by
    unfold discrim at hdisc
    nlinarith
  have hxy : B x x * B y y ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 :=
    mul_le_mul (hmax x) (hmax y) (hmin y) (sq_nonneg _)
  have hsq : (B x y) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]
    exact hs.trans hxy
  simpa only [Real.norm_eq_abs, one_mul] using
    abs_le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A symmetric real bilinear form bounded between zero and the norm-square on its diagonal is
the actual quadratic form of a positive contraction. -/
theorem exists_positiveContraction_of_diagonal_bilinear
    (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (hmin : ∀ x, 0 ≤ B x x) (hmax : ∀ x, B x x ≤ ‖x‖ ^ 2) :
    ∃ A : H →L[ℝ] H, A.IsPositive ∧ (1 - A).IsPositive ∧ ∀ x y, ⟪A x, y⟫_ℝ = B x y := by
  let C := B.mkContinuous₂ 1 (bilinear_bound_of_diagonal B hB hmin hmax)
  let A := InnerProductSpace.continuousLinearMapOfBilin C
  have hA (x y : H) : ⟪A x, y⟫_ℝ = B x y := InnerProductSpace.continuousLinearMapOfBilin_apply C x y
  have hs : IsSelfAdjoint A := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by
    intro x y
    change ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ
    calc
      _ = B x y := hA x y
      _ = B y x := hB x y
      _ = ⟪A y, x⟫_ℝ := (hA y x).symm
      _ = _ := real_inner_comm _ _)
  have hs1 : IsSelfAdjoint (1 : H →L[ℝ] H) := ContinuousLinearMap.isPositive_one.isSelfAdjoint
  refine ⟨A, ContinuousLinearMap.isPositive_def'.mpr ⟨hs, ?_⟩,
    ContinuousLinearMap.isPositive_def'.mpr ⟨hs1.sub hs, ?_⟩, hA⟩
  · intro x
    change 0 ≤ ⟪A x, x⟫_ℝ
    rw [hA]
    exact hmin x
  · intro x
    change 0 ≤ ⟪(1 - A) x, x⟫_ℝ
    rw [sub_apply, one_apply_eq_self, inner_sub_left, real_inner_self_eq_norm_sq, hA]
    exact sub_nonneg.mpr (hmax x)

end AlbertSequential.HilbertTrace
