/- SPDX-License-Identifier: Apache-2.0
Every actual real projective model has an ordinary quaternionic model with the
same original state values on every chronological outcome word. -/
module
public import FourCopyOperatorEmbedding
public import HilbertClassIConstructor
public import QuaternionicProjectiveData

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
open RealHilbertComplexification
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def fourCopyStateCompression :
    selfAdjoint (fourCopyQuaternionicStructure (H := H)).operatorAlgebra →ₗ[ℝ]
      selfAdjoint (HilbertOperatorAlgebra ℝ H) where
  toFun T := ⟨(operatorValue ℝ H).symm
    (realPairOperatorCompression (realPairOperatorCompression
      ((fourCopyQuaternionicStructure (H := H)).operatorValue T.val))),
    inverse_operatorValue_isSelfAdjoint _
      (realPairOperatorCompression_isSelfAdjoint _
        (realPairOperatorCompression_isSelfAdjoint _
          (T.property.map (fourCopyQuaternionicStructure (H := H)).operatorValue)))⟩
  map_add' T S := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_smul' r T := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change realPart (realPart (r •
      (fourCopyQuaternionicStructure (H := H)).operatorValue T.val
        (pair (pair x 0) 0))) = _
    simp only [realPart_real_smul]
    rfl

@[simp] theorem fourCopyStateCompression_one :
    fourCopyStateCompression (H := H) 1 = 1 := by
  apply Subtype.ext
  apply (operatorValue ℝ H).injective
  change realPairOperatorCompression (realPairOperatorCompression 1) = 1
  rw [realPairOperatorCompression_one, realPairOperatorCompression_one]

theorem fourCopyStateCompression_positive
    (T : selfAdjoint (fourCopyQuaternionicStructure (H := H)).operatorAlgebra)
    (hT : ((fourCopyQuaternionicStructure (H := H)).operatorValue T.val).IsPositive) :
    (operatorValue ℝ H (fourCopyStateCompression T).val).IsPositive :=
  realPairOperatorCompression_isPositive _ (realPairOperatorCompression_isPositive _ hT)

theorem fourCopyDiagonalOperator_boundedOutcome (P : ι → H →L[ℝ] H) (a : Outcome ι) :
    fourCopyDiagonalOperator (boundedOutcome P a) =
      boundedOutcome (fun i => fourCopyDiagonalOperator (P i)) a := by
  rcases a with ⟨i,b⟩
  cases b <;> simp only [boundedOutcome, Bool.false_eq_true, ↓reduceIte,
    map_sub, map_one]
  rfl

theorem fourCopyDiagonalOperator_boundedWordEffect (P : ι → H →L[ℝ] H) (w : Word ι) :
    fourCopyDiagonalOperator (boundedWordEffect P w) =
      boundedWordEffect (fun i => fourCopyDiagonalOperator (P i)) w := by
  induction w with
  | nil => exact map_one fourCopyDiagonalOperator
  | cons a w ih =>
    change fourCopyDiagonalOperator
      (boundedOutcome P a * boundedWordEffect P w * boundedOutcome P a) =
      boundedOutcome (fun i => fourCopyDiagonalOperator (P i)) a *
        boundedWordEffect (fun i => fourCopyDiagonalOperator (P i)) w *
        boundedOutcome (fun i => fourCopyDiagonalOperator (P i)) a
    rw [map_mul, map_mul, fourCopyDiagonalOperator_boundedOutcome, ih]

namespace HilbertProjectiveData

def quaternionExtensionState (M : HilbertProjectiveData ι ℝ H) :
    selfAdjoint (fourCopyQuaternionicStructure (H := H)).operatorAlgebra →ₗ[ℝ] ℝ :=
  M.state.comp fourCopyStateCompression

theorem quaternionExtensionState_normalized (M : HilbertProjectiveData ι ℝ H) :
    M.quaternionExtensionState 1 = 1 := by
  change M.state (fourCopyStateCompression 1) = 1
  rw [fourCopyStateCompression_one]
  exact M.normalized

theorem quaternionExtensionState_positive (M : HilbertProjectiveData ι ℝ H)
    (T : selfAdjoint (fourCopyQuaternionicStructure (H := H)).operatorAlgebra)
    (hT : ((fourCopyQuaternionicStructure (H := H)).operatorValue T.val).IsPositive) :
    0 ≤ M.quaternionExtensionState T :=
  M.positive _ (fourCopyStateCompression_positive T hT)

def quaternionExtensionModel (M : HilbertProjectiveData ι ℝ H) :
    QuaternionicProjectiveData ι (fourCopyQuaternionicStructure (H := H)) where
  projection i := fourCopyOperatorEmbedding (M.operatorProjection i)
  isStarProjection i := (M.operatorProjection_isStarProjection i).map fourCopyOperatorEmbedding
  state := M.quaternionExtensionState
  normalized := M.quaternionExtensionState_normalized
  positive := M.quaternionExtensionState_positive

@[simp] theorem quaternionExtensionModel_operatorProjection
    (M : HilbertProjectiveData ι ℝ H) (i : ι) :
    M.quaternionExtensionModel.operatorProjection i =
      fourCopyDiagonalOperator (M.operatorProjection i) := rfl

theorem quaternionExtensionModel_probability (M : HilbertProjectiveData ι ℝ H)
    (w : Word ι) :
    M.quaternionExtensionModel.toAlgebraic.probability w = M.toAlgebraic.probability w := by
  rw [QuaternionicProjectiveData.toAlgebraic_probability, M.toAlgebraic_probability]
  change M.state (fourCopyStateCompression (M.quaternionExtensionModel.wordEffect w)) =
    M.state (M.wordEffect w)
  apply congrArg M.state
  apply Subtype.ext
  apply (operatorValue ℝ H).injective
  change realPairOperatorCompression (realPairOperatorCompression
    ((fourCopyQuaternionicStructure (H := H)).operatorValue
      (M.quaternionExtensionModel.wordEffect w).val)) =
    operatorValue ℝ H (M.wordEffect w).val
  rw [QuaternionicProjectiveData.wordEffect_operatorValue]
  change realPairOperatorCompression (realPairOperatorCompression
    (boundedWordEffect (fun i => fourCopyDiagonalOperator (M.operatorProjection i)) w)) = _
  rw [← fourCopyDiagonalOperator_boundedWordEffect]
  change realPairOperatorCompression (realPairOperatorCompression
    (realDiagonalPairOperator (realDiagonalPairOperator
      (boundedWordEffect M.operatorProjection w)))) = _
  rw [realPairOperatorCompression_diagonal, realPairOperatorCompression_diagonal,
    M.wordEffect_operatorValue]

end HilbertProjectiveData
end AlbertSequential
