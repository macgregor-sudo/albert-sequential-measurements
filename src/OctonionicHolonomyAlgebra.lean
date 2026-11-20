/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionGeometry
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

public section
noncomputable section

namespace AlbertSequential

theorem real_imaginary_octonion_triple {x y z : Octonion}
    (hx : octonionReal x = 0) (hy : octonionReal y = 0) (hz : octonionReal z = 0) :
    octonionReal (octonionMul (octonionMul x y) z) = -octDot (octCross x y) z := by
  conv_lhs =>
    arg 1
    arg 1
    rw [oct_eq_scalar_add_octIm (octonionMul x y), ← octCross_eq_octIm hx hy]
  rw [octonionMul_add_left, octonionMul_scalar_left, octonionReal_add, octonionReal_smul, hz,
    mul_zero, zero_add, octonionReal_mul_imag_eq (octonionReal_octCross x y) hz]

theorem real_octonion_triple_expansion (a b c : Octonion) :
    octonionReal (octonionMul (octonionMul a b) c) =
      octonionReal a * octonionReal b * octonionReal c -
        octonionReal a * octDot (octIm b) (octIm c) -
        octonionReal b * octDot (octIm a) (octIm c) -
        octonionReal c * octDot (octIm a) (octIm b) +
        octonionReal (octonionMul (octonionMul (octIm a) (octIm b)) (octIm c)) := by
  conv_lhs => rw [oct_eq_scalar_add_octIm a, oct_eq_scalar_add_octIm b, oct_eq_scalar_add_octIm c]
  simp only [octonionMul_add_left, octonionMul_add_right, octonionMul_scalar_left,
    octonionMul_scalar_right, octonionMul_smul_left, octonionReal_add, octonionReal_smul,
    octonionReal_scalar, octonionReal_octIm,
    octonionReal_mul_imag_eq (octonionReal_octIm a) (octonionReal_octIm b),
    octonionReal_mul_imag_eq (octonionReal_octIm a) (octonionReal_octIm c),
    octonionReal_mul_imag_eq (octonionReal_octIm b) (octonionReal_octIm c)]
  ring

theorem octonion_hermitian_part (a : Octonion) :
    (1 / 2 : ℝ) • (a + octonionConj a) = octonionScalar (octonionReal a) := by
  rw [octAdd_conj, smul_smul]
  norm_num

theorem octIm_conjugate (a : Octonion) : octIm (octonionConj a) = -octIm a := by
  rw [octConj_eq_two_real_sub, octIm_sub, octIm_smul, octOne_eq_scalar, octIm_scalar,
    smul_zero, zero_sub]

theorem harvey_lawson_for_holonomies (a b c : Octonion) :
    let v : Fin 3 → Octonion := ![octIm a, octIm b, octIm c]
    (Matrix.of fun i j => octDot (v i) (v j)).det - (octDot (octCross (v 0) (v 1)) (v 2)) ^ 2 =
      (1 / 4 : ℝ) * octNormSq (octAssociator a b c) := by
  dsimp only
  have h := harvey_lawson a b c
  dsimp only at h
  have hcross : octDot (octCross (octIm a) (octIm b)) (octIm c) =
      -octDot (octCross (octIm a) (octIm c)) (octIm b) := by
    have hbc := octonionMul_imag_anticomm (octonionReal_octIm b) (octonionReal_octIm c)
    have h : octonionReal (octonionMul (octIm a)
        (octonionMul (octIm b) (octIm c) + octonionMul (octIm c) (octIm b))) = 0 := by
      rw [hbc, octonionMul_smul_right, octonionMul_one_right, octonionReal_smul,
        octonionReal_octIm, mul_zero]
    rw [octonionMul_add_right, octonionReal_add, ← octonionReal_mul_associative,
      ← octonionReal_mul_associative,
      real_imaginary_octonion_triple (octonionReal_octIm a) (octonionReal_octIm b) (octonionReal_octIm c),
      real_imaginary_octonion_triple (octonionReal_octIm a) (octonionReal_octIm c) (octonionReal_octIm b)] at h
    linarith
  change _ - (octDot (octCross (octIm a) (octIm b)) (octIm c)) ^ 2 = _
  rw [hcross, neg_sq]
  exact h

end AlbertSequential
