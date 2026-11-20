/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTracePairing

/-! Polarization of the basis-independent Hilbert–Schmidt mass and trace pairing. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (b : HilbertBasis ι 𝕜 H)

omit [CompleteSpace H] in
private theorem tsum_normSq_eq_mass_toReal (A : H →L[𝕜] H) :
    (∑' i, ‖A (b i)‖ ^ 2) = (hilbertSchmidtMassSq b A).toReal := by
  rw [hilbertSchmidtMassSq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun _ => (ENNReal.toReal_ofReal (sq_nonneg _)).symm

omit [CompleteSpace H] in
private theorem summable_normSq_add_sub (C B : H →L[𝕜] H)
    (hC : hilbertSchmidtMassSq b C ≠ ∞) (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    Summable (fun i => ‖(C + B) (b i)‖ ^ 2) ∧ Summable (fun i => ‖(C - B) (b i)‖ ^ 2) := by
  have hc : Summable (fun i => ‖C (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hC
  have hb : Summable (fun i => ‖B (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hB
  have hg := (hc.add hb).mul_left (2 : ℝ)
  have hbound (x y : H) : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  constructor
  · apply hg.of_norm_bounded
    intro i
    rw [add_apply, Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (hbound _ _)
  · apply hg.of_norm_bounded
    intro i
    rw [sub_apply, Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans (hbound _ _)

omit [CompleteSpace H] in
private theorem tsum_re_inner_eq_mass_difference (C B : H →L[𝕜] H)
    (hC : hilbertSchmidtMassSq b C ≠ ∞) (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    (∑' i, RCLike.re ⟪C (b i), B (b i)⟫_𝕜) =
      ((hilbertSchmidtMassSq b (C + B)).toReal - (hilbertSchmidtMassSq b (C - B)).toReal) / 4 := by
  obtain ⟨ha, hs⟩ := summable_normSq_add_sub b C B hC hB
  rw [← tsum_normSq_eq_mass_toReal, ← tsum_normSq_eq_mass_toReal, ← ha.tsum_sub hs,
    div_eq_mul_inv, ← (ha.sub hs).tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [add_apply, sub_apply, norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜)]
  ring

/-- The actual real diagonal of the product of two Hilbert–Schmidt maps equals their native
Hilbert–Schmidt inner pairing, and the two diagonals may use different Hilbert bases. -/
theorem tsum_re_diagonal_comp_adjoint_eq (c : HilbertBasis κ 𝕜 H) (C B : H →L[𝕜] H)
    (hC : hilbertSchmidtMassSq b C ≠ ∞) (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    (∑' i, RCLike.re ⟪(C ∘L ContinuousLinearMap.adjoint B) (b i), b i⟫_𝕜) =
      ∑' j, RCLike.re ⟪C (c j), B (c j)⟫_𝕜 := by
  let D := ContinuousLinearMap.adjoint C
  let E := ContinuousLinearMap.adjoint B
  have hD : hilbertSchmidtMassSq b D ≠ ∞ := hilbertSchmidtMassSq_adjoint b b C ▸ hC
  have hE : hilbertSchmidtMassSq b E ≠ ∞ := hilbertSchmidtMassSq_adjoint b b B ▸ hB
  have hc : hilbertSchmidtMassSq c C ≠ ∞ := hilbertSchmidtMassSq_basis_independent b c C ▸ hC
  have hb : hilbertSchmidtMassSq c B ≠ ∞ := hilbertSchmidtMassSq_basis_independent b c B ▸ hB
  calc
    _ = ∑' i, RCLike.re ⟪D (b i), E (b i)⟫_𝕜 := by
      refine tsum_congr fun i => ?_
      rw [ContinuousLinearMap.comp_apply, ← C.adjoint_inner_right]
      change RCLike.re ⟪E (b i), D (b i)⟫_𝕜 = RCLike.re ⟪D (b i), E (b i)⟫_𝕜
      rw [← inner_conj_symm (D (b i)) (E (b i))]
      exact (RCLike.conj_re (inner 𝕜 (E (b i)) (D (b i)))).symm
    _ = _ := by
      rw [tsum_re_inner_eq_mass_difference b D E hD hE, tsum_re_inner_eq_mass_difference c C B hc hb]
      have hadd : ContinuousLinearMap.adjoint (C + B) = D + E := map_add ContinuousLinearMap.adjoint _ _
      have hsub : ContinuousLinearMap.adjoint (C - B) = D - E := map_sub ContinuousLinearMap.adjoint _ _
      rw [← hadd, ← hsub, ← hilbertSchmidtMassSq_adjoint c b (C + B),
        ← hilbertSchmidtMassSq_adjoint c b (C - B)]

variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- Exact evaluation of the weighted native trace on the summable positive dyads of a factor. -/
theorem signedTracePairing_eq_factor_sum (c : HilbertBasis κ 𝕜 H) (A B : H →L[𝕜] H)
    (T : signedFiniteTrace b) (hT : B ∘L ContinuousLinearMap.adjoint B = T.val)
    (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    signedTracePairing b A T = ∑' j, RCLike.re ⟪A (B (c j)), B (c j)⟫_𝕜 := by
  have hAB : hilbertSchmidtMassSq b (A ∘L B) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB)
      (hilbertSchmidtMassSq_comp_le b A B)
  unfold signedTracePairing
  rw [← hT]
  exact tsum_re_diagonal_comp_adjoint_eq b c (A ∘L B) B hAB hB

/-- On positive factors the trace pairing is the squared Hilbert–Schmidt mass of the
composed factors. This gives positivity and identifies the zero pairing with `A T = 0`. -/
theorem signedTracePairing_nonneg_zero_iff_of_factors
    (A F B : H →L[𝕜] H) (T : signedFiniteTrace b)
    (hA : ContinuousLinearMap.adjoint F ∘L F = A)
    (hT : B ∘L ContinuousLinearMap.adjoint B = T.val)
    (hB : hilbertSchmidtMassSq b B ≠ ∞) :
    0 ≤ signedTracePairing b A T ∧ (signedTracePairing b A T = 0 ↔ A * T.val = 0) := by
  let D := F ∘L B
  have hD : hilbertSchmidtMassSq b D ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB)
      (hilbertSchmidtMassSq_comp_le b F B)
  have hpair : signedTracePairing b A T = (hilbertSchmidtMassSq b D).toReal := by
    rw [signedTracePairing_eq_factor_sum b b A B T hT hB, ← tsum_normSq_eq_mass_toReal]
    refine tsum_congr fun i => ?_
    rw [← hA, ContinuousLinearMap.comp_apply, F.adjoint_inner_left, inner_self_eq_norm_sq]
    rfl
  refine ⟨hpair ▸ ENNReal.toReal_nonneg, ?_⟩
  constructor
  · intro ha
    rw [hpair, ENNReal.toReal_eq_zero_iff] at ha
    have hDmass : hilbertSchmidtMassSq b D = 0 := ha.resolve_right hD
    have hDprod : D ∘L ContinuousLinearMap.adjoint D = 0 := by
      apply (positiveTrace_eq_zero_iff_of_factor b rfl).mp
      rw [positiveTrace_comp_adjoint, hDmass]
    have hDadj : ContinuousLinearMap.adjoint D = 0 :=
      ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp (by
        simpa only [ContinuousLinearMap.adjoint_adjoint] using hDprod)
    have hDz : D = 0 := by
      rw [← ContinuousLinearMap.adjoint_adjoint D, hDadj, map_zero]
    change F * B = 0 at hDz
    change star F * F = A at hA
    change B * star B = T.val at hT
    rw [← hA, ← hT]
    calc
      _ = star F * (F * B) * star B := by simp only [mul_assoc]
      _ = 0 := by rw [hDz, mul_zero, zero_mul]
  · intro hs
    unfold signedTracePairing
    have hz (i : ι) : A (T.val (b i)) = 0 := congrArg (fun D : H →L[𝕜] H => D (b i)) hs
    simp only [hz, inner_zero_left, map_zero, tsum_zero]

private theorem positiveFactor_finite
    (T : signedFiniteTrace b) (hp : T.val.IsPositive) (B : H →L[𝕜] H)
    (hB : B ∘L ContinuousLinearMap.adjoint B = T.val) : hilbertSchmidtMassSq b B ≠ ∞ := by
  have hfin := (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b T.property hp).2
  rwa [← hB, positiveTrace_comp_adjoint] at hfin

section Complex

variable [InnerProductSpace ℂ H]

/-- The weighted native trace is nonnegative on positive complex operators and vanishes exactly
when the input is supported in the effect's kernel. -/
theorem complex_signedTracePairing_nonneg_zero_iff (c : HilbertBasis ι ℂ H)
    (A : H →L[ℂ] H) (T : signedFiniteTrace c) (hA : A.IsPositive) (hT : T.val.IsPositive) :
    0 ≤ signedTracePairing c A T ∧ (signedTracePairing c A T = 0 ↔ A * T.val = 0) := by
  obtain ⟨F, _, hF, _⟩ := exists_selfAdjoint_factor hA
  obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor hT
  exact signedTracePairing_nonneg_zero_iff_of_factors c A F B T hF hB
    (positiveFactor_finite c T hT B hB)

end Complex

section Real

variable [InnerProductSpace ℝ H]

/-- The weighted native trace is nonnegative on positive real operators and vanishes exactly
when the input is supported in the effect's kernel. -/
theorem real_signedTracePairing_nonneg_zero_iff (c : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (T : signedFiniteTrace c) (hA : A.IsPositive) (hT : T.val.IsPositive) :
    0 ≤ signedTracePairing c A T ∧ (signedTracePairing c A T = 0 ↔ A * T.val = 0) := by
  obtain ⟨F, hFp, hF⟩ := exists_real_positive_square_root hA
  obtain ⟨B, hBp, hB⟩ := exists_real_positive_square_root hT
  have hf : ContinuousLinearMap.adjoint F ∘L F = A := by
    change star F * F = A
    rw [hFp.isSelfAdjoint.star_eq, hF]
  have hb : B ∘L ContinuousLinearMap.adjoint B = T.val := by
    change B * star B = T.val
    rw [hBp.isSelfAdjoint.star_eq, hB]
  exact signedTracePairing_nonneg_zero_iff_of_factors c A F B T hf hb
    (positiveFactor_finite c T hT B hb)

end Real

end AlbertSequential.HilbertTrace
