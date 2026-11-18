/- SPDX-License-Identifier: Apache-2.0
Positive first-axis compression for arbitrary real pair operators. -/
module
public import RealPairOperators
public import Robustness.RealOperatorDescent
public import HilbertClassIConstructor

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def realPairOperatorCompression
    (T : RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H) :
    H →L[ℝ] H :=
  realPartContinuousLinearMap.comp (T.comp embedRealHilbertSpace.toContinuousLinearMap)

@[simp] theorem realPairOperatorCompression_apply
    (T : RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H) (x : H) :
    realPairOperatorCompression T x = realPart (T (pair x 0)) := rfl

theorem realPairOperatorCompression_inner
    (T : RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H) (x y : H) :
    inner ℝ (realPairOperatorCompression T x) y = inner ℝ (T (pair x 0)) (pair y 0) := by
  simp only [realPairOperatorCompression_apply, realPair_inner, realPart_pair,
    imagPart_pair, inner_zero_right, add_zero]

@[simp] theorem realPairOperatorCompression_one :
    realPairOperatorCompression (1 : RealHilbertComplexification H →L[ℝ]
      RealHilbertComplexification H) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable [CompleteSpace H]

theorem realPairOperatorCompression_isSelfAdjoint
    (T : RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (realPairOperatorCompression T) := by
  change (realPairOperatorCompression T).adjoint = realPairOperatorCompression T
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  calc
    _ = inner ℝ (T (pair x 0)) (pair y 0) := realPairOperatorCompression_inner T x y
    _ = inner ℝ (pair x 0) (T (pair y 0)) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, show T.adjoint = T from hT]
    _ = inner ℝ (T (pair y 0)) (pair x 0) := real_inner_comm _ _
    _ = inner ℝ (realPairOperatorCompression T y) x :=
      (realPairOperatorCompression_inner T y x).symm
    _ = _ := real_inner_comm _ _

theorem realPairOperatorCompression_isPositive
    (T : RealHilbertComplexification H →L[ℝ] RealHilbertComplexification H)
    (hT : T.IsPositive) : (realPairOperatorCompression T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨realPairOperatorCompression_isSelfAdjoint T hT.isSelfAdjoint, ?_⟩
  intro x
  change 0 ≤ inner ℝ (realPairOperatorCompression T x) x
  rw [realPairOperatorCompression_inner]
  exact hT.re_inner_nonneg_left (pair x 0)

@[simp] theorem realPairOperatorCompression_diagonal (T : H →L[ℝ] H) :
    realPairOperatorCompression (realDiagonalPairOperator T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end AlbertSequential
