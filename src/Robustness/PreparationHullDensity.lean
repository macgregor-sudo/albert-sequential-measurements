/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.HilbertPreparationHull

/-! The physical trace-norm hull consists of positive, normalized operators. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.HilbertTrace

open PreparationHull SharpDisturbance Filter
open scoped InnerProductSpace ENNReal Topology

section Bounds

variable {𝕜 H B : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

private theorem norm_le_trace_of_positive_factor (b : HilbertBasis B 𝕜 H)
    (X : signedFiniteTrace b) (hX : X.val.IsPositive) (A : H →L[𝕜] H)
    (hA : A ∘L ContinuousLinearMap.adjoint A = X.val) : ‖X.val‖ ≤ signedTrace b X := by
  have hf := (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b X.property hX).2
  rw [← hA, positiveTrace_comp_adjoint] at hf
  have hsum := hasSum_rankOne_of_hilbertSchmidt b A hf
  have hs : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hf
  have hmass : (∑' i, ‖A (b i)‖ ^ 2) = signedTrace b X := by
    rw [signedTrace_eq_positiveTrace_toReal b X hX, ← hA, positiveTrace_comp_adjoint,
      hilbertSchmidtMassSq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun _ => (ENNReal.toReal_ofReal (sq_nonneg _)).symm
  rw [← hA, ← hmass]
  exact hsum.norm_le_of_bounded hs.hasSum fun i => by rw [InnerProductSpace.norm_rankOne, pow_two]

private theorem norm_le_traceNorm_of_decomposition (b : HilbertBasis B 𝕜 H)
    (factor : ∀ {X : H →L[𝕜] H}, X.IsPositive →
      ∃ A : H →L[𝕜] H, A ∘L ContinuousLinearMap.adjoint A = X)
    (X U V : signedFiniteTrace b) (hU : U.val.IsPositive) (hV : V.val.IsPositive)
    (hX : X = U - V) : ‖X.val‖ ≤ signedTrace b U + signedTrace b V := by
  obtain ⟨A, hA⟩ := factor hU
  obtain ⟨B, hB⟩ := factor hV
  rw [hX]
  change ‖U.val - V.val‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_le_trace_of_positive_factor b U hU A hA) (norm_le_trace_of_positive_factor b V hV B hB))

end Bounds

theorem real_operator_norm_le_traceNorm {H B : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : HilbertBasis B ℝ H) (X : signedFiniteTrace b) :
    ‖X.val‖ ≤ realTraceNorm b X := by
  let D := Classical.choose (realModulus_exists b X)
  obtain ⟨hD, hs⟩ := Classical.choose_spec (realModulus_exists b X)
  obtain ⟨u, v, hu, hv, he, hm⟩ := real_signedTrace_jordan_decomposition b X D hD hs
  change ‖X.val‖ ≤ (positiveTrace b D).toReal
  rw [← hm]
  refine norm_le_traceNorm_of_decomposition b (fun h => ?_) X u v hu hv he
  obtain ⟨A, hA, hsq⟩ := exists_real_positive_square_root h
  refine ⟨A, ?_⟩
  change A * star A = _
  rw [hA.isSelfAdjoint.star_eq, hsq]

theorem complex_operator_norm_le_traceNorm {H B : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis B ℂ H) (X : signedFiniteTrace b) :
    ‖X.val‖ ≤ complexTraceNorm b X := by
  obtain ⟨u, v, hu, hv, he, hm⟩ := complex_signedTrace_jordan_decomposition b X
  rw [← hm]
  refine norm_le_traceNorm_of_decomposition b (fun h => ?_) X u v hu hv he
  obtain ⟨A, _, _, hA⟩ := exists_selfAdjoint_factor h
  exact ⟨A, hA⟩

theorem quaternionic_realified_operator_norm_le_traceNorm {H B : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : HilbertBasis B ℝ H)
    (S : RightQuaternionicHilbertStructure H) (X : quaternionicSignedFiniteTrace b S) :
    ‖X.val‖ ≤ 4 * quaternionicTraceNorm b S X := by
  have h := real_operator_norm_le_traceNorm b (quaternionicCarrierInclusion b S X)
  change ‖X.val‖ ≤ realTraceNorm b (quaternionicCarrierInclusion b S X) at h
  change ‖X.val‖ ≤ 4 * (realTraceNorm b (quaternionicCarrierInclusion b S X) / 4)
  linarith

section Limits

variable {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

omit [CompleteSpace H] in
private theorem positive_real_smul {A : H →L[𝕜] H} (hA : A.IsPositive) (r : ℝ) (hr : 0 ≤ r) :
    (r • A).IsPositive := by
  rw [← algebraMap_smul 𝕜]
  exact hA.smul_of_nonneg (RCLike.ofReal_nonneg.mpr hr)

/-- Operator-norm domination passes positive preparations through the physical trace-norm limit. -/
theorem positive_of_mem_traceNormPreparationHull (V : Submodule ℝ (H →L[𝕜] H))
    (tr : V →ₗ[ℝ] ℝ) (F : Outcome I → V →ₗ[ℝ] V) (initial : V) (traceNorm : V → ℝ)
    (hinitial : initial.val.IsPositive) (hp : ∀ q X, X.val.IsPositive → (F q X).val.IsPositive)
    (c : ℝ) (hc : 0 < c) (hbound : ∀ X : V, ‖X.val‖ ≤ c * traceNorm X)
    {z : V} (hzself : IsSelfAdjoint z.val) (hz : z ∈ traceNormPreparationHull traceNorm tr F initial) :
    z.val.IsPositive := by
  let C := {X : V | X.val.IsPositive}
  have hC : Convex ℝ C := by
    intro x hx y hy a b ha hb _
    exact (positive_real_smul hx a ha).add (positive_real_smul hy b hb)
  have hpre : preparedStates tr F initial ⊆ C := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hy
    have hpv : (wordMap F v initial).val.IsPositive := by
      rw [wordMap_eq_chronologicalState]
      exact chronologicalState_mem C (fun a => F a) hp hinitial v
    exact positive_real_smul hpv _ (inv_nonneg.mpr hv.le)
  have hh := convexHull_min hpre hC
  have happrox (n : ℕ) : ∃ y ∈ convexHull ℝ (preparedStates tr F initial),
      traceNorm (y - z) < 1 / ((n : ℝ) + 1) := hz _ (by positivity)
  choose y hy hd using happrox
  have hlim : Tendsto (fun n => (y n).val) atTop (𝓝 z.val) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have he : Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
      have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [mul_zero] using hconst.mul hseq
    apply squeeze_zero (fun _ => dist_nonneg) _ he
    intro n
    rw [dist_eq_norm]
    exact (hbound (y n - z)).trans (mul_le_mul_of_nonneg_left (hd n).le hc.le)
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨hzself, fun x => ?_⟩
  have hf : Continuous (fun T : H →L[𝕜] H => RCLike.re ⟪T x, x⟫_𝕜) :=
    (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).continuous.comp
      ((ContinuousLinearMap.apply 𝕜 H x).continuous.inner continuous_const)
  exact ge_of_tendsto' (hf.continuousAt.tendsto.comp hlim) fun n => (hh (hy n)).re_inner_nonneg_left x

end Limits

section Real

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem real_preparationHull_density (b : HilbertBasis B ℝ H) (M : I → RealInstrument b)
    (p : I → Albert) (initial z : signedFiniteTrace b) (hi : IsRealDensity b initial)
    (hmatch : ∀ w, signedTrace b (wordMap (realBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ realPreparationHull b M initial) : IsRealDensity b z := by
  have hpos : z.val.IsPositive := positive_of_mem_traceNormPreparationHull (signedFiniteTrace b)
    (signedTrace b) (realBranch b M) initial (realTraceNorm b) hi.1 (by
      rintro ⟨i,a⟩ X hX
      cases a
      · exact (M i).zero_positive X hX
      · exact (M i).one_positive X hX)
    1 (by norm_num) (fun X => by simpa only [one_mul] using real_operator_norm_le_traceNorm b X)
    (signedFiniteTrace_isSelfAdjoint b z) hz
  obtain ⟨ρ, hρ, ht⟩ := real_native_table_of_preparationHull b M p initial z hmatch hz
  have hn := ht []
  change signedTrace b z = albertTrace ρ at hn
  exact ⟨hpos, hn.trans (native_reachableStateSpace_density p hρ).2⟩

end Real

section Complex

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complex_preparationHull_density (b : HilbertBasis B ℂ H) (M : I → ComplexInstrument b)
    (p : I → Albert) (initial z : signedFiniteTrace b) (hi : IsComplexDensity b initial)
    (hmatch : ∀ w, signedTrace b (wordMap (complexBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ complexPreparationHull b M initial) : IsComplexDensity b z := by
  have hpos : z.val.IsPositive := positive_of_mem_traceNormPreparationHull (signedFiniteTrace b)
    (signedTrace b) (complexBranch b M) initial (complexTraceNorm b) hi.1 (by
      rintro ⟨i,a⟩ X hX
      cases a
      · exact (M i).zero_positive X hX
      · exact (M i).one_positive X hX)
    1 (by norm_num) (fun X => by simpa only [one_mul] using complex_operator_norm_le_traceNorm b X)
    (signedFiniteTrace_isSelfAdjoint b z) hz
  obtain ⟨ρ, hρ, ht⟩ := complex_native_table_of_preparationHull b M p initial z hmatch hz
  have hn := ht []
  change signedTrace b z = albertTrace ρ at hn
  exact ⟨hpos, hn.trans (native_reachableStateSpace_density p hρ).2⟩

end Complex

section Quaternionic

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem quaternionic_preparationHull_density (b : HilbertBasis B ℝ H)
    (S : RightQuaternionicHilbertStructure H) (M : I → QuaternionicInstrument b S)
    (p : I → Albert) (initial z : quaternionicSignedFiniteTrace b S)
    (hi : IsQuaternionicDensity b S initial)
    (hmatch : ∀ w, quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ quaternionicPreparationHull b S M initial) : IsQuaternionicDensity b S z := by
  have hpos : z.val.IsPositive := positive_of_mem_traceNormPreparationHull
    (quaternionicSignedFiniteTrace b S) (quaternionicSignedTrace b S) (quaternionicBranch b S M)
    initial (quaternionicTraceNorm b S) hi.1 (by
      rintro ⟨i,a⟩ X hX
      cases a
      · exact (M i).zero_positive X hX
      · exact (M i).one_positive X hX)
    4 (by norm_num) (quaternionic_realified_operator_norm_le_traceNorm b S)
    (signedFiniteTrace_isSelfAdjoint b (quaternionicCarrierInclusion b S z)) hz
  obtain ⟨ρ, hρ, ht⟩ := quaternionic_native_table_of_preparationHull b S M p initial z hmatch hz
  have hn := ht []
  change quaternionicSignedTrace b S z = albertTrace ρ at hn
  exact ⟨hpos, hn.trans (native_reachableStateSpace_density p hρ).2⟩

end Quaternionic

end AlbertSequential.HilbertTrace
