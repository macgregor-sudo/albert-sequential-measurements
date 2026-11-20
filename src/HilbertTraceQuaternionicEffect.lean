/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceQuaternionicAverage

/-! Measured effect recovery on the actual right-quaternionic trace-class carrier. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

private theorem realSandwich_vectorDyad (R : H →L[ℝ] H) (x : H) :
    realSandwich b R (realVectorDyad b x) = realVectorDyad b (R x) := by
  apply Subtype.ext
  ext y
  change R (InnerProductSpace.rankOne ℝ x x (ContinuousLinearMap.adjoint R y)) =
    InnerProductSpace.rankOne ℝ (R x) (R x) y
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, map_smul,
    R.adjoint_inner_right]

private theorem commutes_of_phase_invariant_quadratic_form {A R : H →L[ℝ] H}
    (hA : A.IsPositive) (hR : R * star R = 1)
    (h : ∀ x, ⟪A (R x), R x⟫_ℝ = ⟪A x, x⟫_ℝ) : R * A = A * R := by
  let C := star R * A * R
  have hC : C.IsPositive := hA.adjoint_conj R
  have hs := (hC.isSelfAdjoint.sub hA.isSelfAdjoint).isSymmetric
  have hzero : (C - A).toLinearMap = 0 := hs.inner_map_self_eq_zero.mp (by
    intro x
    change ⟪(C - A) x, x⟫_ℝ = 0
    rw [sub_apply, inner_sub_left]
    change ⟪ContinuousLinearMap.adjoint R (A (R x)), x⟫_ℝ - ⟪A x, x⟫_ℝ = 0
    rw [R.adjoint_inner_left, h x, sub_self])
  have hh : C - A = 0 := by
    ext x
    exact LinearMap.congr_fun hzero x
  have hCA : C = A := sub_eq_zero.mp hh
  calc
    R * A = R * C := congrArg (R * ·) hCA.symm
    _ = (R * star R) * A * R := by simp only [C, mul_assoc]
    _ = A * R := by rw [hR, one_mul]

/-- The trace-dominated positive branch functional on the actual quaternionic carrier has a
genuinely right-linear measured effect for the normalized quaternionic trace pairing. -/
theorem exists_quaternionic_effect_of_trace_dominated
    (f : quaternionicSignedFiniteTrace b S →ₗ[ℝ] ℝ)
    (hf : ∀ T : quaternionicSignedFiniteTrace b S, T.val.IsPositive →
      0 ≤ f T ∧ f T ≤ quaternionicSignedTrace b S T) :
    ∃ A : S.toOperatorStructure.operatorAlgebra, A.val.IsPositive ∧ (1 - A.val).IsPositive ∧
      ∀ T : quaternionicSignedFiniteTrace b S, f T = quaternionicTracePairing b S A T := by
  let F : signedFiniteTrace b →ₗ[ℝ] ℝ := (4 : ℝ) • (f.comp (quaternionicAverage b S))
  have hF (X : signedFiniteTrace b) (hX : X.val.IsPositive) :
      0 ≤ F X ∧ F X ≤ signedTrace b X := by
    have h := hf (quaternionicAverage b S X) (quaternionicAverage_positive b S X hX)
    change 0 ≤ (4 : ℝ) * f (quaternionicAverage b S X) ∧
      (4 : ℝ) * f (quaternionicAverage b S X) ≤ signedTrace b X
    refine ⟨mul_nonneg (by norm_num) h.1, ?_⟩
    calc
      _ ≤ 4 * quaternionicSignedTrace b S (quaternionicAverage b S X) :=
        mul_le_mul_of_nonneg_left h.2 (by norm_num)
      _ = _ := quaternionicAverage_trace b S X
  obtain ⟨A, hA, hAc, hpair⟩ := exists_real_effect_of_trace_dominated b F hF
  have hquad (R : H →L[ℝ] H)
      (hR : ∀ X, quaternionicAverage b S (realSandwich b R X) = quaternionicAverage b S X)
      (x : H) : ⟪A (R x), R x⟫_ℝ = ⟪A x, x⟫_ℝ := by
    calc
      _ = signedTracePairing b A (realVectorDyad b (R x)) := (realVectorDyad_pairing b A _).symm
      _ = F (realVectorDyad b (R x)) := (hpair _).symm
      _ = F (realVectorDyad b x) := by
        rw [← realSandwich_vectorDyad b R x]
        change (4 : ℝ) * f (quaternionicAverage b S (realSandwich b R (realVectorDyad b x))) =
          (4 : ℝ) * f (quaternionicAverage b S (realVectorDyad b x))
        rw [hR]
      _ = signedTracePairing b A (realVectorDyad b x) := hpair _
      _ = _ := realVectorDyad_pairing b A x
  let Q := S.toOperatorStructure
  have hi : Q.rightI * star Q.rightI = 1 := by rw [Q.star_rightI, mul_neg, Q.rightI_sq, neg_neg]
  have hj : Q.rightJ * star Q.rightJ = 1 := by rw [Q.star_rightJ, mul_neg, Q.rightJ_sq, neg_neg]
  have hAmem : A ∈ Q.operatorAlgebra := (Q.mem_operatorAlgebra_iff A).mpr
    ⟨commutes_of_phase_invariant_quadratic_form hA hi (hquad _ (quaternionicAverage_conj_I b S)),
      commutes_of_phase_invariant_quadratic_form hA hj (hquad _ (quaternionicAverage_conj_J b S))⟩
  refine ⟨⟨A, hAmem⟩, hA, hAc, fun T => ?_⟩
  have hh := hpair (quaternionicCarrierInclusion b S T)
  change 4 * f (quaternionicAverage b S (quaternionicCarrierInclusion b S T)) =
    signedTracePairing b A (quaternionicCarrierInclusion b S T) at hh
  rw [quaternionicAverage_inclusion] at hh
  change f T = (1 / 4 : ℝ) * signedTracePairing b A (quaternionicCarrierInclusion b S T)
  linarith

end AlbertSequential.HilbertTrace
