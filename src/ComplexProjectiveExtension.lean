/- SPDX-License-Identifier: Apache-2.0
An actual complex model for each real model, with its original state transported
by first-coordinate compression and all chronological word probabilities. -/
module
public import ComplexStateCompression

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem complexify_boundedOutcome (P : ι → H →L[ℝ] H) (a : Outcome ι) :
    complexifyBoundedOperator (boundedOutcome P a) =
      boundedOutcome (fun i => complexifyBoundedOperator (P i)) a := by
  rcases a with ⟨i,b⟩
  cases b <;> simp only [boundedOutcome, Bool.false_eq_true, ↓reduceIte,
    map_sub, map_one]
  rfl

theorem complexify_boundedWordEffect (P : ι → H →L[ℝ] H) (w : Word ι) :
    complexifyBoundedOperator (boundedWordEffect P w) =
      boundedWordEffect (fun i => complexifyBoundedOperator (P i)) w := by
  induction w with
  | nil => exact map_one complexifyBoundedOperator
  | cons a w ih =>
    change complexifyBoundedOperator
      (boundedOutcome P a * boundedWordEffect P w * boundedOutcome P a) =
      boundedOutcome (fun i => complexifyBoundedOperator (P i)) a *
        boundedWordEffect (fun i => complexifyBoundedOperator (P i)) w *
        boundedOutcome (fun i => complexifyBoundedOperator (P i)) a
    rw [map_mul, map_mul, complexify_boundedOutcome, ih]

namespace HilbertProjectiveData

def complexExtensionState (M : HilbertProjectiveData ι ℝ H) :
    selfAdjoint (HilbertOperatorAlgebra ℂ (RealHilbertComplexification H)) →ₗ[ℝ] ℝ :=
  M.state.comp complexStateCompression

theorem complexExtensionState_normalized (M : HilbertProjectiveData ι ℝ H) :
    M.complexExtensionState 1 = 1 := by
  change M.state (complexStateCompression 1) = 1
  rw [complexStateCompression_one]
  exact M.normalized

theorem complexExtensionState_positive (M : HilbertProjectiveData ι ℝ H)
    (T : selfAdjoint (HilbertOperatorAlgebra ℂ (RealHilbertComplexification H)))
    (hT : (operatorValue ℂ (RealHilbertComplexification H) T.val).IsPositive) :
    0 ≤ M.complexExtensionState T :=
  M.positive _ (complexStateCompression_positive T hT)

def complexExtensionModel (M : HilbertProjectiveData ι ℝ H) :
    HilbertProjectiveData ι ℂ (RealHilbertComplexification H) :=
  ofBoundedProjections (fun i => complexifyBoundedOperator (M.operatorProjection i))
    (fun i => (M.operatorProjection_isStarProjection i).map complexifyBoundedOperator)
    M.complexExtensionState M.complexExtensionState_normalized M.complexExtensionState_positive

theorem complexExtensionModel_probability (M : HilbertProjectiveData ι ℝ H)
    (w : Word ι) :
    M.complexExtensionModel.toAlgebraic.probability w = M.toAlgebraic.probability w := by
  rw [complexExtensionModel, ofBoundedProjections_probability, M.toAlgebraic_probability]
  change M.state (complexStateCompression _) = M.state (M.wordEffect w)
  apply congrArg M.state
  apply Subtype.ext
  apply (operatorValue ℝ H).injective
  change restrictOperatorRealPart
    (boundedWordEffect (fun i => complexifyBoundedOperator (M.operatorProjection i)) w) =
    operatorValue ℝ H (M.wordEffect w).val
  rw [← complexify_boundedWordEffect, restrictOperatorRealPart_complexified,
    M.wordEffect_operatorValue]

end HilbertProjectiveData
end AlbertSequential
