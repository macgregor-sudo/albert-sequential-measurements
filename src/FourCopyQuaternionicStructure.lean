/- SPDX-License-Identifier: Apache-2.0
Ordinary right quaternion scalar operators on four real copies of H. -/
module
public import RealPairOperators
public import QuaternionicPresentationEquivalence

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev RealHilbertQuaternionification (H : Type*) :=
  RealHilbertComplexification (RealHilbertComplexification H)

def quaternionRightIIsometry : RealHilbertQuaternionification H →ₗᵢ[ℝ]
    RealHilbertQuaternionification H where
  toFun u := pair (realPairQuarterTurn (realPart u))
    (-realPairQuarterTurn (imagPart u))
  map_add' u v := by
    apply real_imag_ext <;> simp [map_add, add_comm]
  map_smul' r u := by
    apply real_imag_ext <;> simp [map_smul]
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖pair (realPairQuarterTurn (realPart u))
      (-realPairQuarterTurn (imagPart u))‖ ^ 2 = ‖u‖ ^ 2
    simp only [RealHilbertComplexification.norm_sq, realPart_pair,
      imagPart_pair, norm_neg, LinearIsometry.norm_map]

def quaternionRightIOperator : RealHilbertQuaternionification H →L[ℝ]
    RealHilbertQuaternionification H := quaternionRightIIsometry.toContinuousLinearMap

@[simp] theorem quaternionRightIOperator_apply (u : RealHilbertQuaternionification H) :
    quaternionRightIOperator u = pair (realPairQuarterTurn (realPart u))
      (-realPairQuarterTurn (imagPart u)) := rfl

theorem quaternionRightIOperator_sq :
    quaternionRightIOperator (H := H) * quaternionRightIOperator = -1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply real_imag_ext <;> apply real_imag_ext <;>
    simp [mul_apply_eq_comp]

theorem quaternionRightOperators_anticommute :
    quaternionRightIOperator (H := H) * realPairQuarterTurnOperator =
      -(realPairQuarterTurnOperator * quaternionRightIOperator) := by
  apply ContinuousLinearMap.ext
  intro u
  apply real_imag_ext <;> apply real_imag_ext <;>
    simp [mul_apply_eq_comp]

theorem quaternionRightIOperator_inner (u v : RealHilbertQuaternionification H) :
    inner ℝ (quaternionRightIOperator u) v =
      -inner ℝ u (quaternionRightIOperator v) := by
  simp only [quaternionRightIOperator_apply, realPair_inner, realPart_pair,
    imagPart_pair, inner_neg_left, inner_neg_right]
  simp only [realPairQuarterTurn_apply, realPart_pair, imagPart_pair,
    inner_neg_left, inner_neg_right]
  ring

variable [CompleteSpace H]

theorem quaternionRightIOperator_star :
    star (quaternionRightIOperator (H := H)) = -quaternionRightIOperator := by
  change quaternionRightIOperator.adjoint = -quaternionRightIOperator
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  change inner ℝ (-(quaternionRightIOperator u)) v =
    inner ℝ u (quaternionRightIOperator v)
  rw [inner_neg_left, quaternionRightIOperator_inner, neg_neg]

def fourCopyQuaternionicStructure :
    QuaternionicOperatorStructure (RealHilbertQuaternionification H) where
  rightI := quaternionRightIOperator
  rightJ := realPairQuarterTurnOperator
  rightI_sq := quaternionRightIOperator_sq
  rightJ_sq := realPairQuarterTurnOperator_sq
  anticommute := quaternionRightOperators_anticommute
  star_rightI := quaternionRightIOperator_star
  star_rightJ := realPairQuarterTurnOperator_star

@[simp] theorem fourCopy_rightI_firstAxis (x : H) :
    (fourCopyQuaternionicStructure (H := H)).rightI (pair (pair x 0) 0) =
      pair (pair 0 x) 0 := by
  apply real_imag_ext <;> apply real_imag_ext <;>
    simp [fourCopyQuaternionicStructure]

@[simp] theorem fourCopy_rightJ_firstAxis (x : H) :
    (fourCopyQuaternionicStructure (H := H)).rightJ (pair (pair x 0) 0) =
      pair 0 (pair x 0) := by
  apply real_imag_ext <;> apply real_imag_ext <;>
    simp [fourCopyQuaternionicStructure]

@[simp] theorem fourCopy_rightK_firstAxis (x : H) :
    (fourCopyQuaternionicStructure (H := H)).rightK (pair (pair x 0) 0) =
      pair 0 (pair 0 x) := by
  rw [QuaternionicOperatorStructure.rightK, mul_apply_eq_comp,
    fourCopy_rightI_firstAxis]
  apply real_imag_ext <;> apply real_imag_ext <;>
    simp [fourCopyQuaternionicStructure]

end AlbertSequential
