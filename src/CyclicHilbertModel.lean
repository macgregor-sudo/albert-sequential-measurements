/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicWordVectors
public import HilbertClassIConstructor

/-! An actual real Hilbert model with its ordinary unit-vector state.
All word values equal the original arbitrary positive functional's values. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential

section VectorState
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def realHilbertVectorState (Ω : H) : selfAdjoint (HilbertOperatorAlgebra ℝ H) →ₗ[ℝ] ℝ where
  toFun T := inner ℝ Ω (operatorValue ℝ H T.val Ω)
  map_add' T U := by
    change inner ℝ Ω (operatorValue ℝ H T.val Ω+operatorValue ℝ H U.val Ω)=_
    exact inner_add_right _ _ _
  map_smul' r T := by
    change inner ℝ Ω (r • (operatorValue ℝ H T.val Ω))=r*inner ℝ Ω (operatorValue ℝ H T.val Ω)
    simp only [inner_smul_right]

theorem realHilbertVectorState_normalized (Ω : H) (hΩ : ‖Ω‖=1) :
    realHilbertVectorState Ω 1=1 := by
  change inner ℝ Ω Ω=1
  rw [real_inner_self_eq_norm_sq,hΩ]
  norm_num

theorem realHilbertVectorState_positive (Ω : H)
    (T : selfAdjoint (HilbertOperatorAlgebra ℝ H)) (hT : (operatorValue ℝ H T.val).IsPositive) :
    0 ≤ realHilbertVectorState Ω T := hT.inner_nonneg_right Ω
end VectorState

section CyclicModel
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def cyclicHilbertModel (M : AlgebraicProjectiveData ι A) :
    HilbertProjectiveData ι ℝ (CyclicHilbert M) :=
  HilbertProjectiveData.ofBoundedProjections (cyclicHilbertProjection M)
    (cyclicHilbertProjection_isStarProjection M) (realHilbertVectorState (cyclicHilbertVector M))
    (realHilbertVectorState_normalized _ (cyclicHilbertVector_norm M))
    (realHilbertVectorState_positive _)

theorem cyclicHilbertModel_probability (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    (cyclicHilbertModel M).toAlgebraic.probability w=M.probability w := by
  rw [cyclicHilbertModel,HilbertProjectiveData.ofBoundedProjections_probability]
  change inner ℝ (cyclicHilbertVector M)
    (operatorValue ℝ (CyclicHilbert M)
      ((operatorValue ℝ (CyclicHilbert M)).symm (boundedWordEffect (cyclicHilbertProjection M) w))
      (cyclicHilbertVector M))=M.probability w
  rw [RingEquiv.apply_symm_apply,boundedWordEffect_eq_star_mul _
    (fun i => (cyclicHilbertProjection_isStarProjection M i).isSelfAdjoint)]
  change inner ℝ (cyclicHilbertVector M)
    ((ContinuousLinearMap.adjoint (boundedWordAmplitude (cyclicHilbertProjection M) w))
      (boundedWordAmplitude (cyclicHilbertProjection M) w (cyclicHilbertVector M)))=M.probability w
  rw [ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq,
    boundedWordAmplitude_eq_wordAmplitude]
  exact cyclicHilbert_word_probability M w

end CyclicModel
end AlbertSequential
