/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceSandwich

/-! Absolute convergence of the actual bounded-operator trace pairing. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (b : HilbertBasis ι 𝕜 H)

/-- A product of two Hilbert–Schmidt operators has absolutely summable real diagonal. -/
theorem summable_pairing_of_hilbertSchmidt (C B : H →L[𝕜] H)
    (hC : hilbertSchmidtMassSq b C ≠ ∞) (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    Summable (fun i => ‖RCLike.re ⟪(C ∘L ContinuousLinearMap.adjoint B) (b i), b i⟫_𝕜‖) := by
  rw [hilbertSchmidtMassSq_adjoint b b C] at hC
  rw [hilbertSchmidtMassSq_adjoint b b B] at hB
  have hCsq : Summable (fun i => ‖ContinuousLinearMap.adjoint C (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hC
  have hBsq : Summable (fun i => ‖ContinuousLinearMap.adjoint B (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hB
  apply ((hBsq.add hCsq).mul_right (1 / 2)).of_norm_bounded
  intro i
  rw [norm_norm, ContinuousLinearMap.comp_apply, ← C.adjoint_inner_right]
  calc
    ‖RCLike.re ⟪ContinuousLinearMap.adjoint B (b i),
        ContinuousLinearMap.adjoint C (b i)⟫_𝕜‖ ≤ ‖⟪ContinuousLinearMap.adjoint B (b i),
        ContinuousLinearMap.adjoint C (b i)⟫_𝕜‖ := RCLike.norm_re_le_norm _
    _ ≤ ‖ContinuousLinearMap.adjoint B (b i)‖ * ‖ContinuousLinearMap.adjoint C (b i)‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖ContinuousLinearMap.adjoint B (b i)‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint C (b i)‖ ^ 2) * (1 / 2) := by
      nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint B (b i)‖ -
        ‖ContinuousLinearMap.adjoint C (b i)‖)]

theorem summable_pairing_of_positive_factor (A B : H →L[𝕜] H)
    (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    Summable (fun i => ‖RCLike.re ⟪A ((B ∘L ContinuousLinearMap.adjoint B) (b i)), b i⟫_𝕜‖) := by
  have hAB : hilbertSchmidtMassSq b (A ∘L B) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB)
      (hilbertSchmidtMassSq_comp_le b A B)
  exact summable_pairing_of_hilbertSchmidt b (A ∘L B) B hAB hB

variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

private theorem summable_pairing_of_signedFiniteTrace
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T)
    (A : H →L[𝕜] H) (T : signedFiniteTrace b) :
    Summable (fun i => ‖RCLike.re ⟪A (T.val (b i)), b i⟫_𝕜‖) := by
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property
  have aux (X : H →L[𝕜] H) (hX : IsPositiveFiniteTrace b X) :
      Summable (fun i => ‖RCLike.re ⟪A (X (b i)), b i⟫_𝕜‖) := by
    obtain ⟨B, hB⟩ := factor hX.1
    have hfin := hX.2
    rw [← hB, positiveTrace_comp_adjoint] at hfin
    rw [← hB]
    exact summable_pairing_of_positive_factor b A B hfin
  apply ((aux X hX).add (aux Y hY)).of_norm_bounded
  intro i
  rw [norm_norm, hT, sub_apply, map_sub, inner_sub_left]
  change ‖(RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (_ - _)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

/-- The real diagonal expression for `Tr(A T)` in the given basis. -/
def signedTracePairing (A : H →L[𝕜] H) (T : signedFiniteTrace b) : ℝ :=
  ∑' i, RCLike.re ⟪A (T.val (b i)), b i⟫_𝕜

omit [CompleteSpace H] in
/-- The actual trace pairing recovers the quadratic form on a rank-one dyad. -/
theorem signedTracePairing_rankOne (A : H →L[𝕜] H) (x : H) :
    signedTracePairing b A ⟨InnerProductSpace.rankOne 𝕜 x x, rankOne_mem_signedFiniteTrace b x⟩ =
      RCLike.re ⟪A x, x⟫_𝕜 := by
  have hp := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasSum (b.hasSum_inner_mul_inner (A x) x)
  rw [RCLike.reCLM_apply] at hp
  apply HasSum.tsum_eq _
  refine hp.congr_fun fun i => ?_
  change RCLike.re ⟪A (InnerProductSpace.rankOne 𝕜 x x (b i)), b i⟫_𝕜 =
    RCLike.re (⟪A x, b i⟫_𝕜 * ⟪b i, x⟫_𝕜)
  rw [InnerProductSpace.rankOne_apply, map_smul, inner_smul_left, inner_conj_symm, mul_comm]

theorem complex_summable_tracePairing [InnerProductSpace ℂ H] (c : HilbertBasis ι ℂ H)
    (A : H →L[ℂ] H) (T : signedFiniteTrace c) :
    Summable (fun i => ‖RCLike.re ⟪A (T.val (c i)), c i⟫_ℂ‖) := by
  refine summable_pairing_of_signedFiniteTrace c (fun h => ?_) A T
  obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor h
  exact ⟨B, hB⟩

theorem real_summable_tracePairing [InnerProductSpace ℝ H] (c : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (T : signedFiniteTrace c) :
    Summable (fun i => ‖RCLike.re ⟪A (T.val (c i)), c i⟫_ℝ‖) := by
  refine summable_pairing_of_signedFiniteTrace c (fun h => ?_) A T
  obtain ⟨B, hB, hBB⟩ := exists_real_positive_square_root h
  refine ⟨B, ?_⟩
  change B * star B = _
  rw [hB.isSelfAdjoint.star_eq, hBB]

omit [CompleteSpace H] in
/-- With absolutely convergent diagonals the trace pairing is real-linear in the trace variable. -/
def signedTracePairingLinear (A : H →L[𝕜] H)
    (hA : ∀ T : signedFiniteTrace b, Summable (fun i => RCLike.re ⟪A (T.val (b i)), b i⟫_𝕜)) :
    signedFiniteTrace b →ₗ[ℝ] ℝ where
  toFun := signedTracePairing b A
  map_add' S T := by
    unfold signedTracePairing
    rw [← (hA S).tsum_add (hA T)]
    refine tsum_congr fun i => ?_
    change RCLike.re ⟪A ((S.val + T.val) (b i)), b i⟫_𝕜 = _
    rw [add_apply, map_add, inner_add_left]
    exact map_add (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) _ _
  map_smul' r T := by
    change (∑' i, RCLike.re ⟪A ((r • T.val) (b i)), b i⟫_𝕜) =
      r * ∑' i, RCLike.re ⟪A (T.val (b i)), b i⟫_𝕜
    rw [← (hA T).tsum_mul_left r]
    refine tsum_congr fun i => ?_
    rw [← algebraMap_smul 𝕜 r T.val, smul_apply, map_smul, inner_smul_left,
      RCLike.conj_ofReal, RCLike.re_ofReal_mul]

end AlbertSequential.HilbertTrace
