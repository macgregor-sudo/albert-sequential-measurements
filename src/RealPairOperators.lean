/- SPDX-License-Identifier: Apache-2.0
Actual real L2-pair operators used in scalar extension. -/
module
public import Robustness.ComplexifiedBoundedOperators

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

instance realPairInnerProductSpace : InnerProductSpace ℝ (RealHilbertComplexification H) :=
  InnerProductSpace.complexToReal

theorem realPair_inner (u v : RealHilbertComplexification H) :
    inner ℝ u v = inner ℝ (realPart u) (realPart v) +
      inner ℝ (imagPart u) (imagPart v) := by
  rw [real_inner_eq_re_inner ℂ]
  rfl

def realPairQuarterTurn : RealHilbertComplexification H →ₗᵢ[ℝ]
    RealHilbertComplexification H where
  toFun u := pair (-imagPart u) (realPart u)
  map_add' u v := by apply real_imag_ext <;> simp <;> abel
  map_smul' r u := by apply real_imag_ext <;> simp
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖pair (-imagPart u) (realPart u)‖ ^ 2 = ‖u‖ ^ 2
    simp only [RealHilbertComplexification.norm_sq, realPart_pair,
      imagPart_pair, norm_neg]
    ring

@[simp] theorem realPairQuarterTurn_apply (u : RealHilbertComplexification H) :
    realPairQuarterTurn u = pair (-imagPart u) (realPart u) := rfl

theorem realPairQuarterTurn_inner (u v : RealHilbertComplexification H) :
    inner ℝ (realPairQuarterTurn u) v = -inner ℝ u (realPairQuarterTurn v) := by
  simp only [realPair_inner, realPairQuarterTurn_apply, realPart_pair,
    imagPart_pair, inner_neg_left, inner_neg_right]
  ring

def realPairQuarterTurnOperator : RealHilbertComplexification H →L[ℝ]
    RealHilbertComplexification H := realPairQuarterTurn.toContinuousLinearMap

@[simp] theorem realPairQuarterTurnOperator_apply (u : RealHilbertComplexification H) :
    realPairQuarterTurnOperator u = pair (-imagPart u) (realPart u) := rfl

theorem realPairQuarterTurnOperator_sq :
    (realPairQuarterTurnOperator (H := H)) * realPairQuarterTurnOperator = -1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply real_imag_ext <;> simp [mul_apply_eq_comp]

variable [CompleteSpace H]

theorem realPairQuarterTurnOperator_star :
    star (realPairQuarterTurnOperator (H := H)) = -realPairQuarterTurnOperator := by
  change realPairQuarterTurnOperator.adjoint = -realPairQuarterTurnOperator
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  change inner ℝ (-(realPairQuarterTurn u)) v = inner ℝ u (realPairQuarterTurn v)
  rw [inner_neg_left, realPairQuarterTurn_inner, neg_neg]

def realDiagonalPairOperatorValue (T : H →L[ℝ] H) :
    RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H :=
  (complexifyBoundedOperator T).restrictScalars ℝ

@[simp] theorem realDiagonalPairOperatorValue_apply (T : H →L[ℝ] H)
    (u : RealHilbertComplexification H) :
    realDiagonalPairOperatorValue T u = pair (T (realPart u)) (T (imagPart u)) := rfl

theorem realDiagonalPairOperatorValue_star (T : H →L[ℝ] H) :
    realDiagonalPairOperatorValue (star T) = star (realDiagonalPairOperatorValue T) := by
  change realDiagonalPairOperatorValue T.adjoint = (realDiagonalPairOperatorValue T).adjoint
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [realPair_inner, realDiagonalPairOperatorValue_apply,
    realPart_pair, imagPart_pair, ContinuousLinearMap.adjoint_inner_left]

def realDiagonalPairOperator : (H →L[ℝ] H) →⋆ₐ[ℝ]
    (RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H) where
  toFun := realDiagonalPairOperatorValue
  map_zero' := by ext u <;> rfl
  map_one' := by ext u <;> rfl
  map_add' S T := by ext u <;> rfl
  map_mul' S T := by ext u <;> rfl
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro u
    apply real_imag_ext <;> simp [Algebra.algebraMap_eq_smul_one]
  map_star' := realDiagonalPairOperatorValue_star

@[simp] theorem realDiagonalPairOperator_apply (T : H →L[ℝ] H)
    (u : RealHilbertComplexification H) :
    realDiagonalPairOperator T u = pair (T (realPart u)) (T (imagPart u)) := rfl

theorem realDiagonalPairOperator_quarterTurn (T : H →L[ℝ] H) :
    realDiagonalPairOperator T * realPairQuarterTurnOperator (H := H) =
      realPairQuarterTurnOperator * realDiagonalPairOperator T := by
  apply ContinuousLinearMap.ext
  intro u
  apply real_imag_ext <;> simp [mul_apply_eq_comp]

end AlbertSequential
