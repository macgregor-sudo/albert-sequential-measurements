/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTracePairingExpansion

/-! Extending trace-dominated positive functionals from vector dyads. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Filter
open scoped BigOperators InnerProductSpace ENNReal Topology

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
variable (b : HilbertBasis ι 𝕜 H)

omit [CompleteSpace H] in
private def dyad (x : H) : signedFiniteTrace b :=
  ⟨InnerProductSpace.rankOne 𝕜 x x, rankOne_mem_signedFiniteTrace b x⟩

private theorem dyad_tail_isPositive (T : signedFiniteTrace b) (B : H →L[𝕜] H)
    (hB : B ∘L ContinuousLinearMap.adjoint B = T.val) (s : Finset ι) :
    (T - ∑ i ∈ s, dyad b (B (b i))).val.IsPositive := by
  let S : signedFiniteTrace b := ∑ i ∈ s, dyad b (B (b i))
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨signedFiniteTrace_isSelfAdjoint b (T - S), ?_⟩
  intro z
  have hTv : RCLike.re ⟪T.val z, z⟫_𝕜 = ‖ContinuousLinearMap.adjoint B z‖ ^ 2 := by
    rw [← hB, ContinuousLinearMap.comp_apply, ← B.adjoint_inner_right, inner_self_eq_norm_sq]
  have hSv : RCLike.re ⟪S.val z, z⟫_𝕜 = ∑ i ∈ s, ‖⟪b i, ContinuousLinearMap.adjoint B z⟫_𝕜‖ ^ 2 := by
    have hSval : S.val = ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (B (b i)) (B (b i)) :=
      map_sum (signedFiniteTrace b).subtype _ s
    rw [hSval, sum_apply, sum_inner]
    change (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (∑ i ∈ s, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.reCLM_apply, InnerProductSpace.rankOne_apply, inner_smul_left,
      ← B.adjoint_inner_right, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  change 0 ≤ RCLike.re ⟪(T.val - S.val) z, z⟫_𝕜
  rw [sub_apply, inner_sub_left]
  change 0 ≤ (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (_ - _)
  rw [map_sub]
  change 0 ≤ RCLike.re ⟪T.val z, z⟫_𝕜 - RCLike.re ⟪S.val z, z⟫_𝕜
  rw [hTv, hSv]
  exact sub_nonneg.mpr (sum_le_hasSum s (fun _ _ => sq_nonneg _)
    (hasSum_normSq_inner b (ContinuousLinearMap.adjoint B z)))

private theorem signedTrace_dyad (x : H) : signedTrace b (dyad b x) = ‖x‖ ^ 2 := by
  change signedTracePairing b 1 (dyad b x) = _
  rw [show dyad b x = ⟨InnerProductSpace.rankOne 𝕜 x x, rankOne_mem_signedFiniteTrace b x⟩ from rfl,
    signedTracePairing_rankOne, one_apply_eq_self, inner_self_eq_norm_sq]

private theorem equality_on_positive_of_dyads
    (f g : signedFiniteTrace b →ₗ[ℝ] ℝ)
    (hf : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ f T ∧ f T ≤ signedTrace b T)
    (hg : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ g T ∧ g T ≤ signedTrace b T)
    (hvec : ∀ x : H, f (dyad b x) = g (dyad b x))
    (T : signedFiniteTrace b) (B : H →L[𝕜] H)
    (hB : B ∘L ContinuousLinearMap.adjoint B = T.val) (hfin : hilbertSchmidtMassSq b B ≠ ∞) :
    f T = g T := by
  let tail (s : Finset ι) : signedFiniteTrace b := T - ∑ i ∈ s, dyad b (B (b i))
  have hsize : HasSum (fun i => ‖B (b i)‖ ^ 2) (signedTrace b T) := by
    have hs : Summable (fun i => ‖B (b i)‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hfin
    convert hs.hasSum using 1
    change signedTracePairing b 1 T = _
    rw [signedTracePairing_eq_factor_sum b b 1 B T hB hfin]
    exact tsum_congr fun i => by rw [one_apply_eq_self, inner_self_eq_norm_sq]
  have hsmall : Tendsto (fun s : Finset ι => signedTrace b (tail s)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : Finset ι => signedTrace b T) atTop (𝓝 (signedTrace b T)) :=
      tendsto_const_nhds
    have h := hconst.sub hsize
    rw [sub_self] at h
    simpa only [tail, map_sub, map_sum, signedTrace_dyad] using h
  have hbound (s : Finset ι) : |f T - g T| ≤ signedTrace b (tail s) := by
    have hs := dyad_tail_isPositive b T B hB s
    have hf' := hf (tail s) hs
    have hg' := hg (tail s) hs
    have heq : f (tail s) - g (tail s) = f T - g T := by
      simp only [tail, map_sub, map_sum, hvec]
      ring
    rw [← heq, abs_le]
    exact ⟨by linarith [hf'.1, hg'.2], by linarith [hf'.2, hg'.1]⟩
  have hz := le_of_tendsto_of_tendsto' tendsto_const_nhds hsmall hbound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

/-- The positive finite-trace vector dyads determine every trace-dominated positive functional
on the whole signed carrier. The positive factorization input is available for R and C. -/
theorem positiveFunctional_ext_of_rankOne
    (factor : ∀ {T : H →L[𝕜] H}, T.IsPositive →
      ∃ B : H →L[𝕜] H, B ∘L ContinuousLinearMap.adjoint B = T)
    (f g : signedFiniteTrace b →ₗ[ℝ] ℝ)
    (hf : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ f T ∧ f T ≤ signedTrace b T)
    (hg : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ g T ∧ g T ≤ signedTrace b T)
    (hvec : ∀ x : H, f ⟨InnerProductSpace.rankOne 𝕜 x x, rankOne_mem_signedFiniteTrace b x⟩ =
      g ⟨InnerProductSpace.rankOne 𝕜 x x, rankOne_mem_signedFiniteTrace b x⟩) : f = g := by
  have hpos (T : signedFiniteTrace b) (hp : T.val.IsPositive) : f T = g T := by
    obtain ⟨B, hB⟩ := factor hp
    have hfin := (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b T.property hp).2
    rw [← hB, positiveTrace_comp_adjoint] at hfin
    exact equality_on_positive_of_dyads b f g hf hg hvec T B hB hfin
  ext T
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property
  let U : signedFiniteTrace b := ⟨X, hX.mem_signedFiniteTrace b⟩
  let V : signedFiniteTrace b := ⟨Y, hY.mem_signedFiniteTrace b⟩
  have hTV : T = U - V := Subtype.ext hT
  rw [hTV, map_sub, map_sub, hpos U hX.1, hpos V hY.1]

end AlbertSequential.HilbertTrace
