/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicRightLinearOperators

/-! End-to-end source right-Hilbert projections/state to the algebraic
comparator, retaining the original quaternionic state and all actual words. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

namespace RightQuaternionicHilbertStructure

def rightProjection (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i)) :
    ι → S.toOperatorStructure.operatorAlgebra :=
  fun i => ⟨P i, (S.mem_operatorAlgebra_iff_rightLinear (P i)).mpr (hlinear i)⟩

theorem rightProjection_isStarProjection (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i))
    (hP : ∀ i, IsStarProjection (P i)) (i : ι) :
    IsStarProjection (S.rightProjection P hlinear i) := by
  constructor
  · exact Subtype.ext (hP i).isIdempotentElem
  · exact Subtype.ext (hP i).isSelfAdjoint

def rightWordEffect (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i)) (w : Word ι) :
    selfAdjoint S.toOperatorStructure.operatorAlgebra :=
  ⟨wordOperator (S.rightProjection P hlinear) w,
    wordOperator_star (S.rightProjection P hlinear) w⟩

theorem rightWordEffect_actual (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i))
    (hP : ∀ i, IsStarProjection (P i)) (w : Word ι) :
    S.toOperatorStructure.operatorValue (S.rightWordEffect P hlinear w).val =
      boundedWordEffect P w := by
  exact QuaternionicProjectiveData.operatorValue_wordOperator
    (S.rightProjection P hlinear)
    (fun i => (S.rightProjection_isStarProjection P hlinear hP i).isSelfAdjoint) w

def classIModel (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i))
    (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ ψ T) :
    QuaternionicProjectiveData ι S.toOperatorStructure where
  projection := S.rightProjection P hlinear
  isStarProjection := S.rightProjection_isStarProjection P hlinear hP
  state := ψ
  normalized := hunit
  positive T hT := hpositive T ((S.positive_iff_real_operator T.val).mpr hT)

theorem classIModel_probability (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i))
    (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ ψ T) (w : Word ι) :
    (S.classIModel P hlinear hP ψ hunit hpositive).toAlgebraic.probability w =
      ψ (S.rightWordEffect P hlinear w) :=
  QuaternionicProjectiveData.toAlgebraic_probability _ w

theorem classIModel_matches_iff (S : RightQuaternionicHilbertStructure H)
    (P : ι → H →L[ℝ] H) (hlinear : ∀ i, S.IsRightLinear (P i))
    (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ ψ T)
    (p : ι → Albert) (ρ : Albert) :
    (S.classIModel P hlinear hP ψ hunit hpositive).toAlgebraic.Matches p ρ ↔
      ∀ w, ψ (S.rightWordEffect P hlinear w) = nativeWordProbability p ρ w := by
  simp only [AlgebraicProjectiveData.Matches, S.classIModel_probability]

end RightQuaternionicHilbertStructure
end AlbertSequential
