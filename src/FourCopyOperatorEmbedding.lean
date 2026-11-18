/- SPDX-License-Identifier: Apache-2.0
Diagonal real operator embedding into the actual quaternionic commutant. -/
module
public import FourCopyQuaternionicStructure
public import RealPairCompression

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def fourCopyDiagonalOperator : (H →L[ℝ] H) →⋆ₐ[ℝ]
    (RealHilbertQuaternionification H →L[ℝ] RealHilbertQuaternionification H) :=
  realDiagonalPairOperator.comp realDiagonalPairOperator

@[simp] theorem fourCopyDiagonalOperator_apply (T : H →L[ℝ] H)
    (u : RealHilbertQuaternionification H) :
    fourCopyDiagonalOperator T u =
      pair (pair (T (realPart (realPart u))) (T (imagPart (realPart u))))
        (pair (T (realPart (imagPart u))) (T (imagPart (imagPart u)))) := rfl

theorem fourCopyDiagonalOperator_mem (T : H →L[ℝ] H) :
    fourCopyDiagonalOperator T ∈ (fourCopyQuaternionicStructure (H := H)).operatorAlgebra := by
  rw [QuaternionicOperatorStructure.mem_operatorAlgebra_iff]
  constructor
  all_goals
    apply ContinuousLinearMap.ext
    intro u
    apply real_imag_ext <;> apply real_imag_ext <;>
      simp [fourCopyQuaternionicStructure, mul_apply_eq_comp]

def fourCopyOperatorEmbedding : (H →L[ℝ] H) →⋆ₐ[ℝ]
    (fourCopyQuaternionicStructure (H := H)).operatorAlgebra where
  toFun T := ⟨fourCopyDiagonalOperator T, fourCopyDiagonalOperator_mem T⟩
  map_zero' := Subtype.ext (map_zero fourCopyDiagonalOperator)
  map_one' := Subtype.ext (map_one fourCopyDiagonalOperator)
  map_add' S T := Subtype.ext (map_add fourCopyDiagonalOperator S T)
  map_mul' S T := Subtype.ext (map_mul fourCopyDiagonalOperator S T)
  commutes' r := Subtype.ext (fourCopyDiagonalOperator.commutes r)
  map_star' T := Subtype.ext (map_star fourCopyDiagonalOperator T)

@[simp] theorem fourCopyOperatorEmbedding_value (T : H →L[ℝ] H) :
    (fourCopyQuaternionicStructure (H := H)).operatorValue (fourCopyOperatorEmbedding T) =
      fourCopyDiagonalOperator T := rfl

end AlbertSequential
