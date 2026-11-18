/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicOperatorAlgebra
public import Mathlib.Analysis.Quaternion

/-! Native right-Hilbert source data, over the actual Quaternion ℝ carrier.
These fields are ordinary scalar/inner-product laws, never a realization or
word-probability assumption. The underlying complete real norm is unchanged. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

def quaternionI : Quaternion ℝ := ⟨0,1,0,0⟩
def quaternionJ : Quaternion ℝ := ⟨0,0,1,0⟩
def quaternionK : Quaternion ℝ := ⟨0,0,0,1⟩

theorem quaternionI_sq : quaternionI * quaternionI = -1 := by
  ext <;> norm_num [quaternionI, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

theorem quaternionJ_sq : quaternionJ * quaternionJ = -1 := by
  ext <;> norm_num [quaternionJ, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

theorem quaternionI_mul_quaternionJ : quaternionI * quaternionJ = quaternionK := by
  ext <;> norm_num [quaternionI, quaternionJ, quaternionK, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem quaternionJ_mul_quaternionI : quaternionJ * quaternionI = -quaternionK := by
  ext <;> norm_num [quaternionI, quaternionJ, quaternionK, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem star_quaternionI : star quaternionI = -quaternionI := by
  ext <;> norm_num [quaternionI]

theorem star_quaternionJ : star quaternionJ = -quaternionJ := by
  ext <;> norm_num [quaternionJ]

theorem quaternion_real_part_mul_comm (q r : Quaternion ℝ) :
    (q*r).re = (r*q).re := by
  simp only [Quaternion.re_mul]
  ring

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

/-- A complete right quaternionic Hilbert structure on the same complete real
Hilbert carrier. Right scalar multiplication is bounded real-linear for each
scalar, and real-linear in that scalar. No dimension or state premise appears. -/
structure RightQuaternionicHilbertStructure where
  rightScalar : Quaternion ℝ →ₗ[ℝ] (H →L[ℝ] H)
  right_one : rightScalar 1 = 1
  right_mul : ∀ q r, rightScalar (q*r) = rightScalar r * rightScalar q
  quaternionInner : H → H → Quaternion ℝ
  inner_add_right : ∀ x y z, quaternionInner x (y+z) =
    quaternionInner x y + quaternionInner x z
  inner_right_scalar : ∀ x y q, quaternionInner x (rightScalar q y) =
    quaternionInner x y * q
  inner_symm : ∀ x y, quaternionInner y x = star (quaternionInner x y)
  inner_re : ∀ x y, (quaternionInner x y).re = inner ℝ x y

namespace RightQuaternionicHilbertStructure
variable {H}

theorem adjoint_rightScalar (S : RightQuaternionicHilbertStructure H) (q : Quaternion ℝ) :
    ContinuousLinearMap.adjoint (S.rightScalar q) = S.rightScalar (star q) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have hleft : S.quaternionInner (S.rightScalar (star q) x) y =
      q * S.quaternionInner x y := by
    rw [S.inner_symm y (S.rightScalar (star q) x), S.inner_right_scalar,
      star_mul, star_star, ← S.inner_symm y x]
  calc
    inner ℝ (S.rightScalar (star q) x) y =
        (S.quaternionInner (S.rightScalar (star q) x) y).re := (S.inner_re _ _).symm
    _ = (q * S.quaternionInner x y).re := congrArg (fun q : Quaternion ℝ => q.re) hleft
    _ = (S.quaternionInner x y * q).re := quaternion_real_part_mul_comm _ _
    _ = (S.quaternionInner x (S.rightScalar q y)).re :=
      congrArg (fun q : Quaternion ℝ => q.re) (S.inner_right_scalar x y q).symm
    _ = inner ℝ x (S.rightScalar q y) := S.inner_re _ _

def toOperatorStructure (S : RightQuaternionicHilbertStructure H) :
    QuaternionicOperatorStructure H where
  rightI := S.rightScalar quaternionI
  rightJ := S.rightScalar quaternionJ
  rightI_sq := by
    rw [← S.right_mul, quaternionI_sq, map_neg, S.right_one]
  rightJ_sq := by
    rw [← S.right_mul, quaternionJ_sq, map_neg, S.right_one]
  anticommute := by
    rw [← S.right_mul, ← S.right_mul, quaternionJ_mul_quaternionI,
      quaternionI_mul_quaternionJ, map_neg]
  star_rightI := by
    change ContinuousLinearMap.adjoint (S.rightScalar quaternionI) = _
    rw [S.adjoint_rightScalar, star_quaternionI, map_neg]
  star_rightJ := by
    change ContinuousLinearMap.adjoint (S.rightScalar quaternionJ) = _
    rw [S.adjoint_rightScalar, star_quaternionJ, map_neg]

theorem rightScalar_quaternionK (S : RightQuaternionicHilbertStructure H) :
    S.rightScalar quaternionK = S.toOperatorStructure.rightK := by
  rw [← quaternionI_mul_quaternionJ, S.right_mul]
  rfl

/-- Every source quaternionic inner product is recovered from its real part
and the ACTUAL right scalar action; the three minus signs are not optional. -/
theorem quaternionInner_reconstruction (S : RightQuaternionicHilbertStructure H) (x y : H) :
    S.quaternionInner x y =
      ⟨inner ℝ x y, -inner ℝ x (S.rightScalar quaternionI y),
        -inner ℝ x (S.rightScalar quaternionJ y),
        -inner ℝ x (S.rightScalar quaternionK y)⟩ := by
  have hi := congrArg (fun q : Quaternion ℝ => q.re) (S.inner_right_scalar x y quaternionI)
  have hj := congrArg (fun q : Quaternion ℝ => q.re) (S.inner_right_scalar x y quaternionJ)
  have hk := congrArg (fun q : Quaternion ℝ => q.re) (S.inner_right_scalar x y quaternionK)
  rw [S.inner_re] at hi hj hk
  simp only [quaternionI, quaternionJ, quaternionK, Quaternion.re_mul,
    zero_mul, mul_zero, mul_one, sub_zero, zero_sub] at hi hj hk
  change inner ℝ x (S.rightScalar quaternionI y) = -(S.quaternionInner x y).imI at hi
  change inner ℝ x (S.rightScalar quaternionJ y) = -(S.quaternionInner x y).imJ at hj
  change inner ℝ x (S.rightScalar quaternionK y) = -(S.quaternionInner x y).imK at hk
  apply Quaternion.ext
  · exact S.inner_re x y
  · change (S.quaternionInner x y).imI = -inner ℝ x (S.rightScalar quaternionI y)
    linarith
  · change (S.quaternionInner x y).imJ = -inner ℝ x (S.rightScalar quaternionJ y)
    linarith
  · change (S.quaternionInner x y).imK = -inner ℝ x (S.rightScalar quaternionK y)
    linarith

theorem quaternionInner_self (S : RightQuaternionicHilbertStructure H) (x : H) :
    S.quaternionInner x x = ((‖x‖ ^ 2 : ℝ) : Quaternion ℝ) := by
  have hs := S.inner_symm x x
  apply Quaternion.ext
  · change (S.quaternionInner x x).re = ‖x‖ ^ 2
    rw [S.inner_re, real_inner_self_eq_norm_sq]
  · have h := congrArg (fun q : Quaternion ℝ => q.imI) hs
    simp only [Quaternion.imI_star] at h
    change (S.quaternionInner x x).imI = 0
    linarith
  · have h := congrArg (fun q : Quaternion ℝ => q.imJ) hs
    simp only [Quaternion.imJ_star] at h
    change (S.quaternionInner x x).imJ = 0
    linarith
  · have h := congrArg (fun q : Quaternion ℝ => q.imK) hs
    simp only [Quaternion.imK_star] at h
    change (S.quaternionInner x x).imK = 0
    linarith

theorem norm_rightScalar (S : RightQuaternionicHilbertStructure H)
    (q : Quaternion ℝ) (x : H) : ‖S.rightScalar q x‖ = ‖x‖ * ‖q‖ := by
  have hh : S.quaternionInner (S.rightScalar q x) (S.rightScalar q x) =
      (star q * S.quaternionInner x x) * q := by
    rw [S.inner_right_scalar, S.inner_symm x (S.rightScalar q x),
      S.inner_right_scalar, star_mul, ← S.inner_symm x x]
  have hn := congrArg norm hh
  rw [S.quaternionInner_self, S.quaternionInner_self] at hn
  simp only [norm_mul, norm_star, Quaternion.norm_coe, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (sq_nonneg ‖S.rightScalar q x‖),
    abs_of_nonneg (sq_nonneg ‖x‖)] at hn
  have he : ‖S.rightScalar q x‖ ^ 2 = (‖x‖ * ‖q‖) ^ 2 := by
    nlinarith only [hn]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp he

end RightQuaternionicHilbertStructure
end AlbertSequential
