/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceBasis
public import QuaternionicRightLinearOperators

/-! The actual quaternionic rank-one operators and their realified trace. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The quaternionic dyad on the underlying real Hilbert space. -/
def quaternionicDyad (S : RightQuaternionicHilbertStructure H) (u v : H) : H →L[ℝ] H :=
  InnerProductSpace.rankOne ℝ u v +
  InnerProductSpace.rankOne ℝ (S.rightScalar quaternionI u) (S.rightScalar quaternionI v) +
  InnerProductSpace.rankOne ℝ (S.rightScalar quaternionJ u) (S.rightScalar quaternionJ v) +
  InnerProductSpace.rankOne ℝ (S.rightScalar quaternionK u) (S.rightScalar quaternionK v)

private theorem star_quaternionK : star quaternionK = -quaternionK := by
  ext <;> simp [quaternionK]

private theorem inner_rightScalar_of_star_neg (S : RightQuaternionicHilbertStructure H)
    (q : Quaternion ℝ) (hq : star q = -q) (v x : H) :
    ⟪S.rightScalar q v, x⟫_ℝ = -⟪v, S.rightScalar q x⟫_ℝ := by
  rw [← (S.rightScalar q).adjoint_inner_right, S.adjoint_rightScalar, hq, map_neg, neg_apply,
    inner_neg_right]

/-- `|u⟩⟨v|` acts by the actual right inner-product scalar. -/
theorem quaternionicDyad_apply (S : RightQuaternionicHilbertStructure H) (u v x : H) :
    quaternionicDyad S u v x = S.rightScalar (S.quaternionInner v x) u := by
  rw [S.rightScalar_decomposition]
  simp only [quaternionicDyad, add_apply, InnerProductSpace.rankOne_apply,
    smul_apply, one_apply_eq_self,
    inner_rightScalar_of_star_neg S quaternionI star_quaternionI,
    inner_rightScalar_of_star_neg S quaternionJ star_quaternionJ,
    inner_rightScalar_of_star_neg S quaternionK star_quaternionK,
    S.quaternionInner_reconstruction]

theorem quaternionicDyad_mem_operatorAlgebra (S : RightQuaternionicHilbertStructure H) (u v : H) :
    quaternionicDyad S u v ∈ S.toOperatorStructure.operatorAlgebra := by
  apply (S.mem_operatorAlgebra_iff_rightLinear _).mpr
  intro q x
  rw [quaternionicDyad_apply, S.inner_right_scalar, S.right_mul, quaternionicDyad_apply]
  rfl

omit [CompleteSpace H] in
theorem quaternionicDyad_self_isPositive (S : RightQuaternionicHilbertStructure H) (u : H) :
    (quaternionicDyad S u u).IsPositive := by
  unfold quaternionicDyad
  repeat' apply ContinuousLinearMap.IsPositive.add
  all_goals exact InnerProductSpace.isPositive_rankOne_self _

private theorem norm_imaginary_units :
    ‖quaternionI‖ = 1 ∧ ‖quaternionJ‖ = 1 ∧ ‖quaternionK‖ = 1 := by
  simp only [norm_eq_sqrt_real_inner, Quaternion.inner_self]
  norm_num [quaternionI, quaternionJ, quaternionK, Quaternion.normSq]

/-- On the realification, a quaternionic vector dyad has four times its quaternionic trace. -/
theorem positiveTrace_quaternionicDyad_self {ι : Type*} (b : HilbertBasis ι ℝ H)
    (S : RightQuaternionicHilbertStructure H) (u : H) :
    positiveTrace b (quaternionicDyad S u u) = ENNReal.ofReal (4 * ‖u‖ ^ 2) := by
  rcases norm_imaginary_units with ⟨hi, hj, hk⟩
  have pu := InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) u
  have pi := InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) (S.rightScalar quaternionI u)
  have pj := InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) (S.rightScalar quaternionJ u)
  have pk := InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) (S.rightScalar quaternionK u)
  unfold quaternionicDyad
  rw [positiveTrace_add b ((pu.add pi).add pj) pk, positiveTrace_add b (pu.add pi) pj,
    positiveTrace_add b pu pi]
  simp only [positiveTrace_rankOne, S.norm_rightScalar, hi, hj, hk, mul_one]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)]
  ring_nf

theorem quaternionicDyad_normalized_trace {ι : Type*} (b : HilbertBasis ι ℝ H)
    (S : RightQuaternionicHilbertStructure H) (u : H) :
    (positiveTrace b (quaternionicDyad S u u)).toReal / 4 = ‖u‖ ^ 2 := by
  rw [positiveTrace_quaternionicDyad_self,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (sq_nonneg _))]
  ring

end AlbertSequential.HilbertTrace
