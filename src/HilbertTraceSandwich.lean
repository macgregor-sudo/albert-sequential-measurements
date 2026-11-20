/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceCarrier
public import HilbertTraceReal

/-! Bounds and compression for the actual positive and signed Hilbert trace. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (b : HilbertBasis ι 𝕜 H)

omit [CompleteSpace H] in
theorem hilbertSchmidtMassSq_comp_le (S B : H →L[𝕜] H) :
    hilbertSchmidtMassSq b (S ∘L B) ≤ ENNReal.ofReal (‖S‖ ^ 2) * hilbertSchmidtMassSq b B := by
  unfold hilbertSchmidtMassSq
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro i
  change ENNReal.ofReal (‖S (B (b i))‖ ^ 2) ≤
    ENNReal.ofReal (‖S‖ ^ 2) * ENNReal.ofReal (‖B (b i)‖ ^ 2)
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (B (b i))) 2

theorem positiveTrace_comp_adjoint (D : H →L[𝕜] H) :
    positiveTrace b (D ∘L ContinuousLinearMap.adjoint D) = hilbertSchmidtMassSq b D := by
  calc
    positiveTrace b (D ∘L ContinuousLinearMap.adjoint D) =
        hilbertSchmidtMassSq b (ContinuousLinearMap.adjoint D) := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using
        positiveTrace_adjoint_comp_self b (ContinuousLinearMap.adjoint D)
    _ = _ := (hilbertSchmidtMassSq_adjoint b b D).symm

/-- An operator-norm estimate for the extended trace of an actual positive sandwich. -/
theorem positiveTrace_sandwich_le_of_factor {T : H →L[𝕜] H} (S B : H →L[𝕜] H)
    (hT : B ∘L ContinuousLinearMap.adjoint B = T) :
    positiveTrace b (S ∘L T ∘L ContinuousLinearMap.adjoint S) ≤
      ENNReal.ofReal (‖S‖ ^ 2) * positiveTrace b T := by
  have hS : S ∘L T ∘L ContinuousLinearMap.adjoint S =
      (S ∘L B) ∘L ContinuousLinearMap.adjoint (S ∘L B) := by
    rw [← hT, ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hS, positiveTrace_comp_adjoint, ← hT, positiveTrace_comp_adjoint]
  exact hilbertSchmidtMassSq_comp_le b S B

theorem positiveTrace_eq_zero_iff_of_factor {T : H →L[𝕜] H} {B : H →L[𝕜] H}
    (hT : B ∘L ContinuousLinearMap.adjoint B = T) : positiveTrace b T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hmass : hilbertSchmidtMassSq b B = 0 := by
      rw [← positiveTrace_comp_adjoint, hT, h]
    have hb : ∀ i, B (b i) = 0 := by
      unfold hilbertSchmidtMassSq at hmass
      intro i
      have hzero := (tsum_eq_zero_iff.mp hmass) i
      rw [ENNReal.ofReal_eq_zero] at hzero
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (B (b i))])
    have hB : B = 0 := by
      ext x
      have hs := B.hasSum (b.hasSum_repr x)
      simp only [map_smul, hb, smul_zero] at hs
      exact hs.unique hasSum_zero
    simp [← hT, hB]
  · rintro rfl
    simp [positiveTrace]

private theorem complex_factor [InnerProductSpace ℂ H] {T : H →L[ℂ] H} (hT : T.IsPositive) :
    ∃ B : H →L[ℂ] H, B ∘L ContinuousLinearMap.adjoint B = T := by
  obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor hT
  exact ⟨B, hB⟩

private theorem real_factor [InnerProductSpace ℝ H] {T : H →L[ℝ] H} (hT : T.IsPositive) :
    ∃ B : H →L[ℝ] H, B ∘L ContinuousLinearMap.adjoint B = T := by
  obtain ⟨B, hB, hBB⟩ := exists_real_positive_square_root hT
  refine ⟨B, ?_⟩
  change B * star B = T
  rw [hB.isSelfAdjoint.star_eq, hBB]

private theorem signedFiniteTrace_sandwich_of_factor
    [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T)
    (S : H →L[𝕜] H) (T : signedFiniteTrace b) :
    S ∘L T.val ∘L ContinuousLinearMap.adjoint S ∈ signedFiniteTrace b := by
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property
  have aux (U : H →L[𝕜] H) (hU : IsPositiveFiniteTrace b U) :
      IsPositiveFiniteTrace b (S ∘L U ∘L ContinuousLinearMap.adjoint S) := by
    obtain ⟨B, hB⟩ := factor hU.1
    refine ⟨hU.1.conj_adjoint S, ne_top_of_le_ne_top ?_ (positiveTrace_sandwich_le_of_factor b S B hB)⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU.2
  refine ⟨S ∘L X ∘L ContinuousLinearMap.adjoint S, S ∘L Y ∘L ContinuousLinearMap.adjoint S,
    aux X hX, aux Y hY, ?_⟩
  change S * T.val * star S = S * X * star S - S * Y * star S
  rw [hT, mul_sub, sub_mul]

section Complex

variable [InnerProductSpace ℂ H]

theorem complex_positiveTrace_eq_zero_iff (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : T.IsPositive) : positiveTrace b T = 0 ↔ T = 0 := by
  obtain ⟨B, hB⟩ := complex_factor hT
  exact positiveTrace_eq_zero_iff_of_factor b hB

theorem complex_signedFiniteTrace_sandwich (b : HilbertBasis ι ℂ H)
    (S : H →L[ℂ] H) (T : signedFiniteTrace b) :
    S ∘L T.val ∘L ContinuousLinearMap.adjoint S ∈ signedFiniteTrace b :=
  signedFiniteTrace_sandwich_of_factor b (fun h => complex_factor h) S T

end Complex

section Real

variable [InnerProductSpace ℝ H]

theorem real_positiveTrace_eq_zero_iff (b : HilbertBasis ι ℝ H) {T : H →L[ℝ] H}
    (hT : T.IsPositive) : positiveTrace b T = 0 ↔ T = 0 := by
  obtain ⟨B, hB⟩ := real_factor hT
  exact positiveTrace_eq_zero_iff_of_factor b hB

theorem real_signedFiniteTrace_sandwich (b : HilbertBasis ι ℝ H)
    (S : H →L[ℝ] H) (T : signedFiniteTrace b) :
    S ∘L T.val ∘L ContinuousLinearMap.adjoint S ∈ signedFiniteTrace b :=
  signedFiniteTrace_sandwich_of_factor b (fun h => real_factor h) S T

end Real

end AlbertSequential.HilbertTrace
