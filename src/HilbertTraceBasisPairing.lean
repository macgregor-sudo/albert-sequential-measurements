/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTracePairingExpansion

/-! The signed carrier and weighted diagonal pairing do not depend on the Hilbert basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
variable (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H)

omit [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
private theorem positiveFiniteTrace_rebase
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T)
    {X : H →L[𝕜] H} (hX : IsPositiveFiniteTrace b X) : IsPositiveFiniteTrace c X := by
  obtain ⟨B, hB⟩ := factor hX.1
  have h : positiveTrace b X = positiveTrace c X := by
    rw [← hB, positiveTrace_comp_adjoint, positiveTrace_comp_adjoint]
    exact hilbertSchmidtMassSq_basis_independent b c B
  exact ⟨hX.1, h ▸ hX.2⟩

theorem signedFiniteTrace_basis_eq_of_factor
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T) :
    signedFiniteTrace b = signedFiniteTrace c := by
  ext T
  constructor
  · rintro ⟨X, Y, hX, hY, hT⟩
    exact ⟨X, Y, positiveFiniteTrace_rebase b c factor hX, positiveFiniteTrace_rebase b c factor hY, hT⟩
  · rintro ⟨X, Y, hX, hY, hT⟩
    exact ⟨X, Y, positiveFiniteTrace_rebase c b factor hX, positiveFiniteTrace_rebase c b factor hY, hT⟩

theorem signedTracePairing_basis_eq_of_factor
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T)
    (A : H →L[𝕜] H)
    (hs : ∀ X : signedFiniteTrace b, Summable (fun i => RCLike.re ⟪A (X.val (b i)), b i⟫_𝕜))
    (ht : ∀ X : signedFiniteTrace c, Summable (fun i => RCLike.re ⟪A (X.val (c i)), c i⟫_𝕜))
    (U : signedFiniteTrace b) (V : signedFiniteTrace c) (hUV : U.val = V.val) :
    signedTracePairing b A U = signedTracePairing c A V := by
  let f := signedTracePairingLinear b A hs
  let g := signedTracePairingLinear c A ht
  have hpos {T : H →L[𝕜] H} (hT : IsPositiveFiniteTrace b T) :
      f ⟨T, hT.mem_signedFiniteTrace b⟩ =
        g ⟨T, (positiveFiniteTrace_rebase b c factor hT).mem_signedFiniteTrace c⟩ := by
    obtain ⟨B, hB⟩ := factor hT.1
    have hfin := hT.2
    rw [← hB, positiveTrace_comp_adjoint] at hfin
    have hc : hilbertSchmidtMassSq c B ≠ ∞ :=
      hilbertSchmidtMassSq_basis_independent b c B ▸ hfin
    change signedTracePairing b A _ = signedTracePairing c A _
    rw [signedTracePairing_eq_factor_sum b b A B _ hB hfin,
      signedTracePairing_eq_factor_sum c b A B _ hB hc]
  obtain ⟨X, Y, hX, hY, hU⟩ := U.property
  let Xb : signedFiniteTrace b := ⟨X, hX.mem_signedFiniteTrace b⟩
  let Yb : signedFiniteTrace b := ⟨Y, hY.mem_signedFiniteTrace b⟩
  let Xc : signedFiniteTrace c := ⟨X, (positiveFiniteTrace_rebase b c factor hX).mem_signedFiniteTrace c⟩
  let Yc : signedFiniteTrace c := ⟨Y, (positiveFiniteTrace_rebase b c factor hY).mem_signedFiniteTrace c⟩
  have hUb : U = Xb - Yb := Subtype.ext hU
  have hVc : V = Xc - Yc := Subtype.ext (hUV.symm.trans hU)
  change f U = g V
  rw [hUb, hVc, map_sub, map_sub]
  exact congrArg₂ (· - ·) (hpos hX) (hpos hY)

private theorem real_positive_factor_for_rebase [InnerProductSpace ℝ H] {T : H →L[ℝ] H}
    (h : T.IsPositive) : ∃ B : H →L[ℝ] H, B ∘L ContinuousLinearMap.adjoint B = T := by
  obtain ⟨B, hp, hsq⟩ := exists_real_positive_square_root h
  refine ⟨B, ?_⟩
  change B * star B = T
  rw [hp.isSelfAdjoint.star_eq, hsq]

theorem real_signedFiniteTrace_basis_eq [InnerProductSpace ℝ H] (d : HilbertBasis ι ℝ H)
    (e : HilbertBasis κ ℝ H) : signedFiniteTrace d = signedFiniteTrace e :=
  signedFiniteTrace_basis_eq_of_factor d e real_positive_factor_for_rebase

theorem complex_signedFiniteTrace_basis_eq [InnerProductSpace ℂ H] (d : HilbertBasis ι ℂ H)
    (e : HilbertBasis κ ℂ H) : signedFiniteTrace d = signedFiniteTrace e :=
  signedFiniteTrace_basis_eq_of_factor d e (fun h => by
    obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor h
    exact ⟨B, hB⟩)

theorem real_signedTracePairing_basis_eq [InnerProductSpace ℝ H] (d : HilbertBasis ι ℝ H)
    (e : HilbertBasis κ ℝ H) (A : H →L[ℝ] H)
    (U : signedFiniteTrace d) (V : signedFiniteTrace e) (hUV : U.val = V.val) :
    signedTracePairing d A U = signedTracePairing e A V :=
  signedTracePairing_basis_eq_of_factor d e real_positive_factor_for_rebase A
    (fun T => (real_summable_tracePairing d A T).of_norm)
    (fun T => (real_summable_tracePairing e A T).of_norm) U V hUV

theorem complex_signedTracePairing_basis_eq [InnerProductSpace ℂ H] (d : HilbertBasis ι ℂ H)
    (e : HilbertBasis κ ℂ H) (A : H →L[ℂ] H)
    (U : signedFiniteTrace d) (V : signedFiniteTrace e) (hUV : U.val = V.val) :
    signedTracePairing d A U = signedTracePairing e A V :=
  signedTracePairing_basis_eq_of_factor d e (fun h => by
    obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor h
    exact ⟨B, hB⟩) A (fun T => (complex_summable_tracePairing d A T).of_norm)
    (fun T => (complex_summable_tracePairing e A T).of_norm) U V hUV

end AlbertSequential.HilbertTrace
