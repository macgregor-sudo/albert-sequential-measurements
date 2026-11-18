/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RightQuaternionicHilbert
public import QuaternionicProjectiveData

/-! Exact identification of actual bounded right-linear operators with the
commutant, preserving their quaternionic adjoint and positive cone. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem quaternion_decomposition (q : Quaternion ℝ) :
    q = q.re • (1 : Quaternion ℝ) + q.imI • quaternionI +
      q.imJ • quaternionJ + q.imK • quaternionK := by
  ext <;> simp [quaternionI, quaternionJ, quaternionK]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

namespace RightQuaternionicHilbertStructure

theorem includedOperator_norm (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) : ‖T.val‖ = ‖T‖ := rfl

theorem rightScalar_decomposition (S : RightQuaternionicHilbertStructure H)
    (q : Quaternion ℝ) :
    S.rightScalar q = q.re • (1 : H →L[ℝ] H) +
      q.imI • S.rightScalar quaternionI + q.imJ • S.rightScalar quaternionJ +
      q.imK • S.rightScalar quaternionK := by
  conv_lhs => rw [quaternion_decomposition q]
  simp only [map_add, map_smul, S.right_one]

/-- Actual right linearity, quantified over every quaternion and vector. -/
def IsRightLinear (S : RightQuaternionicHilbertStructure H) (T : H →L[ℝ] H) : Prop :=
  ∀ q x, T (S.rightScalar q x) = S.rightScalar q (T x)

theorem mem_operatorAlgebra_iff_rightLinear (S : RightQuaternionicHilbertStructure H)
    (T : H →L[ℝ] H) :
    T ∈ S.toOperatorStructure.operatorAlgebra ↔ S.IsRightLinear T := by
  rw [QuaternionicOperatorStructure.mem_operatorAlgebra_iff]
  constructor
  · rintro ⟨hI,hJ⟩ q x
    have hK : S.rightScalar quaternionK * T = T * S.rightScalar quaternionK := by
      rw [S.rightScalar_quaternionK]
      change (S.toOperatorStructure.rightJ * S.toOperatorStructure.rightI) * T =
        T * (S.toOperatorStructure.rightJ * S.toOperatorStructure.rightI)
      calc
        _ = S.toOperatorStructure.rightJ * (T * S.toOperatorStructure.rightI) := by
          rw [mul_assoc, hI]
        _ = (T * S.toOperatorStructure.rightJ) * S.toOperatorStructure.rightI := by
          rw [← mul_assoc, hJ]
        _ = _ := mul_assoc _ _ _
    have h : S.rightScalar q * T = T * S.rightScalar q := by
      rw [S.rightScalar_decomposition q]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      change _ = _
      rw [show S.rightScalar quaternionI * T = T * S.rightScalar quaternionI from hI,
        show S.rightScalar quaternionJ * T = T * S.rightScalar quaternionJ from hJ, hK]
    exact congrArg (fun F : H →L[ℝ] H => F x) h.symm
  · intro h
    constructor
    · ext x
      exact (h quaternionI x).symm
    · ext x
      exact (h quaternionJ x).symm

theorem adjoint_quaternionInner (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) (x y : H) :
    S.quaternionInner (T.val x) y =
      S.quaternionInner x ((star T).val y) := by
  have hstar := (S.mem_operatorAlgebra_iff_rightLinear (star T).val).mp (star T).property
  rw [S.quaternionInner_reconstruction, S.quaternionInner_reconstruction]
  apply Quaternion.ext
  · change inner ℝ (T.val x) y = inner ℝ x (ContinuousLinearMap.adjoint T.val y)
    exact (ContinuousLinearMap.adjoint_inner_right T.val x y).symm
  · change -inner ℝ (T.val x) (S.rightScalar quaternionI y) =
      -inner ℝ x (S.rightScalar quaternionI ((star T).val y))
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change -inner ℝ x ((star T).val (S.rightScalar quaternionI y)) = _
    rw [hstar quaternionI y]
  · change -inner ℝ (T.val x) (S.rightScalar quaternionJ y) =
      -inner ℝ x (S.rightScalar quaternionJ ((star T).val y))
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change -inner ℝ x ((star T).val (S.rightScalar quaternionJ y)) = _
    rw [hstar quaternionJ y]
  · change -inner ℝ (T.val x) (S.rightScalar quaternionK y) =
      -inner ℝ x (S.rightScalar quaternionK ((star T).val y))
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change -inner ℝ x ((star T).val (S.rightScalar quaternionK y)) = _
    rw [hstar quaternionK y]

/-- Quaternionic self-adjointness is exactly actual real-adjoint equality. -/
theorem selfAdjoint_iff_quaternionInner (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) :
    IsSelfAdjoint T ↔ ∀ x y, S.quaternionInner (T.val x) y = S.quaternionInner x (T.val y) := by
  constructor
  · intro h x y
    rw [S.adjoint_quaternionInner, h]
  · intro h
    apply Subtype.ext
    have he : T.val = ContinuousLinearMap.adjoint T.val := by
      apply (ContinuousLinearMap.eq_adjoint_iff T.val T.val).mpr
      intro x y
      have hr := congrArg (fun q : Quaternion ℝ => q.re) (h x y)
      simpa only [S.inner_re] using hr
    exact he.symm

theorem selfAdjoint_quaternionInner_real (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) (hT : IsSelfAdjoint T) (x : H) :
    S.quaternionInner x (T.val x) = (inner ℝ x (T.val x) : Quaternion ℝ) := by
  have hs : S.quaternionInner x (T.val x) = star (S.quaternionInner x (T.val x)) := by
    rw [← S.inner_symm x (T.val x)]
    exact ((S.selfAdjoint_iff_quaternionInner T).mp hT x x).symm
  apply Quaternion.ext
  · exact S.inner_re _ _
  · have hi := congrArg (fun q : Quaternion ℝ => q.imI) hs
    simp only [Quaternion.imI_star] at hi
    change (S.quaternionInner x (T.val x)).imI = 0
    linarith
  · have hj := congrArg (fun q : Quaternion ℝ => q.imJ) hs
    simp only [Quaternion.imJ_star] at hj
    change (S.quaternionInner x (T.val x)).imJ = 0
    linarith
  · have hk := congrArg (fun q : Quaternion ℝ => q.imK) hs
    simp only [Quaternion.imK_star] at hk
    change (S.quaternionInner x (T.val x)).imK = 0
    linarith

/-- Ordinary quaternionic positivity: each h(x,Tx) is a nonnegative real. -/
def IsQuaternionPositive (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, ∃ r : ℝ, 0 ≤ r ∧ S.quaternionInner x (T.val x) = (r : Quaternion ℝ)

theorem positive_iff_real_operator (S : RightQuaternionicHilbertStructure H)
    (T : S.toOperatorStructure.operatorAlgebra) :
    S.IsQuaternionPositive T ↔ T.val.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · rintro ⟨hT, hp⟩
    refine ⟨?_, ?_⟩
    · exact congrArg Subtype.val hT
    · intro x
      rcases hp x with ⟨r,hr,heq⟩
      have he := congrArg (fun q : Quaternion ℝ => q.re) heq
      rw [S.inner_re, Quaternion.re_coe] at he
      simpa only [← he, real_inner_comm] using hr
  · rintro ⟨hT,hp⟩
    have ht : IsSelfAdjoint T := Subtype.ext hT
    refine ⟨ht, fun x => ⟨inner ℝ x (T.val x), ?_, S.selfAdjoint_quaternionInner_real T ht x⟩⟩
    simpa only [real_inner_comm] using hp x

end RightQuaternionicHilbertStructure
end AlbertSequential
