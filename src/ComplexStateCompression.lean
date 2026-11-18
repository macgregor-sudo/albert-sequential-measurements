/- SPDX-License-Identifier: Apache-2.0
Compression of arbitrary complex self-adjoint
operators, without a conjugation-fixed premise or state extension axiom. -/
module
public import Robustness.RealOperatorDescent
public import HilbertClassIConstructor

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem restrictOperatorRealPart_inner (T : RealHilbertComplexification H →L[ℂ]
    RealHilbertComplexification H) (x y : H) :
    inner ℝ (restrictOperatorRealPart T x) y =
      (inner ℂ (T (pair x 0)) (pair y 0)).re := by
  simp only [complex_inner_re, realPart_pair, imagPart_pair, inner_zero_right, add_zero]
  rfl

theorem restrictOperatorRealPart_isSelfAdjoint
    (T : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (restrictOperatorRealPart T) := by
  change (restrictOperatorRealPart T).adjoint = restrictOperatorRealPart T
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [restrictOperatorRealPart_inner, real_inner_comm,
    restrictOperatorRealPart_inner]
  have h := congrArg Complex.re
    (ContinuousLinearMap.adjoint_inner_left T (pair x 0) (pair y 0))
  rw [show T.adjoint = T from hT] at h
  rw [h]
  exact inner_re_symm (𝕜 := ℂ) (T (pair x 0)) (pair y 0)

theorem restrictOperatorRealPart_isPositive
    (T : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hT : T.IsPositive) : (restrictOperatorRealPart T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨restrictOperatorRealPart_isSelfAdjoint T hT.isSelfAdjoint, ?_⟩
  intro x
  change 0 ≤ inner ℝ (restrictOperatorRealPart T x) x
  rw [restrictOperatorRealPart_inner]
  exact hT.re_inner_nonneg_left (pair x 0)

omit [CompleteSpace H] in
@[simp] theorem restrictOperatorRealPart_one :
    restrictOperatorRealPart (1 : RealHilbertComplexification H →L[ℂ]
      RealHilbertComplexification H) = 1 := by ext x; rfl

@[simp] theorem restrictOperatorRealPart_complexified (T : H →L[ℝ] H) :
    restrictOperatorRealPart (complexifyBoundedOperator T) = T := by ext x; rfl

def complexStateCompression :
    selfAdjoint (HilbertOperatorAlgebra ℂ (RealHilbertComplexification H)) →ₗ[ℝ]
      selfAdjoint (HilbertOperatorAlgebra ℝ H) where
  toFun T := ⟨(operatorValue ℝ H).symm
    (restrictOperatorRealPart (operatorValue ℂ (RealHilbertComplexification H) T.val)),
    inverse_operatorValue_isSelfAdjoint _ (restrictOperatorRealPart_isSelfAdjoint _ T.property)⟩
  map_add' T S := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change realPart ((operatorValue ℂ _ T.val + operatorValue ℂ _ S.val) (pair x 0)) = _
    rfl
  map_smul' r T := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change realPart ((r : ℂ) • operatorValue ℂ _ T.val (pair x 0)) =
      r • realPart (operatorValue ℂ _ T.val (pair x 0))
    exact realPart_real_smul r _

@[simp] theorem complexStateCompression_one :
    complexStateCompression (H := H) 1 = 1 := by
  apply Subtype.ext
  exact restrictOperatorRealPart_one

theorem complexStateCompression_positive
    (T : selfAdjoint (HilbertOperatorAlgebra ℂ (RealHilbertComplexification H)))
    (hT : (operatorValue ℂ (RealHilbertComplexification H) T.val).IsPositive) :
    (operatorValue ℝ H (complexStateCompression T).val).IsPositive :=
  restrictOperatorRealPart_isPositive _ hT

end AlbertSequential
