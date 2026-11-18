/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicRightLinearOperators
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Algebra.Module.Equiv.Opposite

/-! Two actual skew anticommuting complex structures and ordinary right
quaternionic Hilbert source data are equivalent presentations on the SAME
arbitrary complete real Hilbert space. No state or model is chosen here. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem quaternion_eq_of_real_parts_mul (a b : Quaternion ℝ)
    (h : ∀ q, (a*q).re = (b*q).re) : a = b := by
  apply Quaternion.ext
  · simpa only [mul_one] using h 1
  · apply neg_injective
    simpa [quaternionI, Quaternion.re_mul] using h quaternionI
  · apply neg_injective
    simpa [quaternionJ, Quaternion.re_mul] using h quaternionJ
  · apply neg_injective
    simpa [quaternionK, Quaternion.re_mul] using h quaternionK

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

namespace QuaternionicOperatorStructure

/-- The opposite algebra changes the ACTUAL operator composition into the
ordinary quaternion order; k=op(JI) is checked explicitly. -/
def oppositeQuaternionBasis (Q : QuaternionicOperatorStructure H) :
    QuaternionAlgebra.Basis (H →L[ℝ] H)ᵐᵒᵖ (-1 : ℝ) 0 (-1) where
  i := MulOpposite.op Q.rightI
  j := MulOpposite.op Q.rightJ
  k := MulOpposite.op Q.rightK
  i_mul_i := by
    apply MulOpposite.unop_injective
    simpa using Q.rightI_sq
  j_mul_j := by
    apply MulOpposite.unop_injective
    simpa using Q.rightJ_sq
  i_mul_j := rfl
  j_mul_i := by
    apply MulOpposite.unop_injective
    simpa using Q.rightI_mul_rightJ

def reconstructedRightScalar (Q : QuaternionicOperatorStructure H) :
    Quaternion ℝ →ₗ[ℝ] (H →L[ℝ] H) :=
  ((MulOpposite.opLinearEquiv ℝ (M := H →L[ℝ] H)).symm.toLinearMap).comp
    Q.oppositeQuaternionBasis.liftHom.toLinearMap

theorem reconstructedRightScalar_one (Q : QuaternionicOperatorStructure H) :
    Q.reconstructedRightScalar 1 = 1 := by
  change MulOpposite.unop (Q.oppositeQuaternionBasis.liftHom 1) = 1
  rw [map_one]
  rfl

theorem reconstructedRightScalar_mul (Q : QuaternionicOperatorStructure H) (q r : Quaternion ℝ) :
    Q.reconstructedRightScalar (q*r) = Q.reconstructedRightScalar r * Q.reconstructedRightScalar q := by
  change MulOpposite.unop (Q.oppositeQuaternionBasis.liftHom (q*r)) = _
  rw [map_mul]
  rfl

theorem reconstructedRightScalar_formula (Q : QuaternionicOperatorStructure H) (q : Quaternion ℝ) :
    Q.reconstructedRightScalar q = q.re • (1 : H →L[ℝ] H) +
      q.imI • Q.rightI + q.imJ • Q.rightJ + q.imK • Q.rightK := by
  change MulOpposite.unop (Q.oppositeQuaternionBasis.lift q) = _
  simp only [QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one,
    MulOpposite.unop_add, MulOpposite.unop_smul, MulOpposite.unop_one]
  rfl

theorem reconstructedRightScalar_I (Q : QuaternionicOperatorStructure H) :
    Q.reconstructedRightScalar quaternionI = Q.rightI := by
  rw [Q.reconstructedRightScalar_formula]
  simp [quaternionI]

theorem reconstructedRightScalar_J (Q : QuaternionicOperatorStructure H) :
    Q.reconstructedRightScalar quaternionJ = Q.rightJ := by
  rw [Q.reconstructedRightScalar_formula]
  simp [quaternionJ]

theorem reconstructedRightScalar_K (Q : QuaternionicOperatorStructure H) :
    Q.reconstructedRightScalar quaternionK = Q.rightK := by
  rw [Q.reconstructedRightScalar_formula]
  simp [quaternionK]

def reconstructedInner (Q : QuaternionicOperatorStructure H) (x y : H) : Quaternion ℝ :=
  ⟨inner ℝ x y, -inner ℝ x (Q.rightI y), -inner ℝ x (Q.rightJ y),
    -inner ℝ x (Q.rightK y)⟩

private theorem skew_operator_inner (T : H →L[ℝ] H) (hT : star T = -T) (x y : H) :
    inner ℝ y (T x) = -inner ℝ x (T y) := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ ((star T) y) x = _
  rw [hT]
  simp only [neg_apply, inner_neg_left, real_inner_comm]

theorem reconstructedInner_symm (Q : QuaternionicOperatorStructure H) (x y : H) :
    Q.reconstructedInner y x = star (Q.reconstructedInner x y) := by
  apply Quaternion.ext
  · rw [Quaternion.re_star]
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm _ _
  · change -inner ℝ y (Q.rightI x) = -(-inner ℝ x (Q.rightI y))
    rw [skew_operator_inner Q.rightI Q.star_rightI]
  · change -inner ℝ y (Q.rightJ x) = -(-inner ℝ x (Q.rightJ y))
    rw [skew_operator_inner Q.rightJ Q.star_rightJ]
  · change -inner ℝ y (Q.rightK x) = -(-inner ℝ x (Q.rightK y))
    rw [skew_operator_inner Q.rightK Q.star_rightK]

theorem reconstructedInner_add_right (Q : QuaternionicOperatorStructure H) (x y z : H) :
    Q.reconstructedInner x (y+z) = Q.reconstructedInner x y + Q.reconstructedInner x z := by
  ext <;> simp [reconstructedInner, map_add, inner_add_right, add_comm]

/-- The four-coordinate scalar formula is precisely the real-part pairing.
This one identity replaces a repeated table of quaternion products. -/
theorem reconstructedInner_real_mul (Q : QuaternionicOperatorStructure H)
    (x y : H) (q : Quaternion ℝ) :
    (Q.reconstructedInner x y * q).re = inner ℝ x (Q.reconstructedRightScalar q y) := by
  rw [Q.reconstructedRightScalar_formula]
  rw [Quaternion.re_mul]
  change inner ℝ x y * q.re - (-inner ℝ x (Q.rightI y)) * q.imI -
      (-inner ℝ x (Q.rightJ y)) * q.imJ - (-inner ℝ x (Q.rightK y)) * q.imK = _
  simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_right, inner_smul_right,
    RingHom.id_apply]
  ring

theorem reconstructedInner_right_scalar (Q : QuaternionicOperatorStructure H)
    (x y : H) (q : Quaternion ℝ) :
    Q.reconstructedInner x (Q.reconstructedRightScalar q y) = Q.reconstructedInner x y * q := by
  apply quaternion_eq_of_real_parts_mul
  intro r
  calc
    (Q.reconstructedInner x (Q.reconstructedRightScalar q y) * r).re =
        inner ℝ x (Q.reconstructedRightScalar r (Q.reconstructedRightScalar q y)) :=
      Q.reconstructedInner_real_mul _ _ _
    _ = inner ℝ x (Q.reconstructedRightScalar (q*r) y) := by
      rw [Q.reconstructedRightScalar_mul]
      rfl
    _ = (Q.reconstructedInner x y * (q*r)).re := (Q.reconstructedInner_real_mul x y (q*r)).symm
    _ = ((Q.reconstructedInner x y * q) * r).re := by rw [mul_assoc]

def toRightHilbertStructure (Q : QuaternionicOperatorStructure H) :
    RightQuaternionicHilbertStructure H where
  rightScalar := Q.reconstructedRightScalar
  right_one := Q.reconstructedRightScalar_one
  right_mul := Q.reconstructedRightScalar_mul
  quaternionInner := Q.reconstructedInner
  inner_add_right := Q.reconstructedInner_add_right
  inner_right_scalar := Q.reconstructedInner_right_scalar
  inner_symm := Q.reconstructedInner_symm
  inner_re _ _ := rfl

private theorem operatorStructure_ext (Q R : QuaternionicOperatorStructure H)
    (hI : Q.rightI = R.rightI) (hJ : Q.rightJ = R.rightJ) : Q = R := by
  cases Q
  cases R
  cases hI
  cases hJ
  rfl

theorem toOperatorStructure_toRightHilbertStructure (Q : QuaternionicOperatorStructure H) :
    Q.toRightHilbertStructure.toOperatorStructure = Q := by
  apply operatorStructure_ext
  · exact Q.reconstructedRightScalar_I
  · exact Q.reconstructedRightScalar_J

end QuaternionicOperatorStructure

namespace RightQuaternionicHilbertStructure

private theorem rightHilbertStructure_ext (S T : RightQuaternionicHilbertStructure H)
    (hR : S.rightScalar = T.rightScalar) (hh : S.quaternionInner = T.quaternionInner) : S = T := by
  cases S
  cases T
  cases hR
  cases hh
  rfl

theorem toRightHilbertStructure_toOperatorStructure (S : RightQuaternionicHilbertStructure H) :
    S.toOperatorStructure.toRightHilbertStructure = S := by
  apply rightHilbertStructure_ext
  · apply LinearMap.ext
    intro q
    change S.toOperatorStructure.reconstructedRightScalar q = S.rightScalar q
    rw [S.toOperatorStructure.reconstructedRightScalar_formula, S.rightScalar_decomposition,
      S.rightScalar_quaternionK]
    rfl
  · funext x y
    change S.toOperatorStructure.reconstructedInner x y = S.quaternionInner x y
    rw [S.quaternionInner_reconstruction]
    unfold QuaternionicOperatorStructure.reconstructedInner
    rw [S.rightScalar_quaternionK]
    rfl

end RightQuaternionicHilbertStructure

def rightQuaternionicHilbertPresentationEquiv (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] :
    RightQuaternionicHilbertStructure H ≃ QuaternionicOperatorStructure H where
  toFun := RightQuaternionicHilbertStructure.toOperatorStructure
  invFun := QuaternionicOperatorStructure.toRightHilbertStructure
  left_inv := RightQuaternionicHilbertStructure.toRightHilbertStructure_toOperatorStructure
  right_inv := QuaternionicOperatorStructure.toOperatorStructure_toRightHilbertStructure

end AlbertSequential
