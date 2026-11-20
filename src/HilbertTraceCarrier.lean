/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceBasis

/-! The real-linear span of positive finite-trace operators and its signed trace. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (b : HilbertBasis ι 𝕜 H)

/-- A positive operator whose basis diagonal has a finite sum. -/
def IsPositiveFiniteTrace (T : H →L[𝕜] H) : Prop :=
  T.IsPositive ∧ positiveTrace b T ≠ ∞

omit [CompleteSpace H] in
private theorem positiveFiniteTrace_zero : IsPositiveFiniteTrace b (0 : H →L[𝕜] H) := by
  refine ⟨ContinuousLinearMap.isPositive_zero, ?_⟩
  simp [positiveTrace]

omit [CompleteSpace H] in
private theorem positiveFiniteTrace_add {X Y : H →L[𝕜] H}
    (hX : IsPositiveFiniteTrace b X) (hY : IsPositiveFiniteTrace b Y) :
    IsPositiveFiniteTrace b (X + Y) := by
  refine ⟨hX.1.add hY.1, ?_⟩
  rw [positiveTrace_add b hX.1 hY.1]
  exact ENNReal.add_ne_top.mpr ⟨hX.2, hY.2⟩

omit [CompleteSpace H] in
private theorem positiveFiniteTrace_smul' (r : ℝ) (hr : 0 ≤ r) {X : H →L[𝕜] H}
    (hX : IsPositiveFiniteTrace b X) : IsPositiveFiniteTrace b ((r : 𝕜) • X) := by
  refine ⟨hX.1.smul_of_nonneg (RCLike.ofReal_nonneg.mpr hr), ?_⟩
  have h : positiveTrace b ((r : 𝕜) • X) = ENNReal.ofReal r * positiveTrace b X := by
    unfold positiveTrace
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, ENNReal.ofReal_mul hr]
  rw [h]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX.2

variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

omit [CompleteSpace H] in
private theorem positiveFiniteTrace_smul (r : ℝ) (hr : 0 ≤ r) {X : H →L[𝕜] H}
    (hX : IsPositiveFiniteTrace b X) : IsPositiveFiniteTrace b (r • X) := by
  rw [← algebraMap_smul 𝕜 r X]
  exact positiveFiniteTrace_smul' b r hr hX

/-- The subspace of actual operators expressible as differences of positive finite-trace ones. -/
def signedFiniteTrace : Submodule ℝ (H →L[𝕜] H) where
  carrier := {T | ∃ X Y, IsPositiveFiniteTrace b X ∧ IsPositiveFiniteTrace b Y ∧ T = X - Y}
  zero_mem' := by
    exact ⟨0, 0, positiveFiniteTrace_zero b, positiveFiniteTrace_zero b, (sub_self 0).symm⟩
  add_mem' := by
    rintro _ _ ⟨X, Y, hX, hY, rfl⟩ ⟨U, V, hU, hV, rfl⟩
    refine ⟨X + U, Y + V, positiveFiniteTrace_add b hX hU, positiveFiniteTrace_add b hY hV, ?_⟩
    abel
  smul_mem' := by
    rintro r _ ⟨X, Y, hX, hY, rfl⟩
    rcases le_total 0 r with hr | hr
    · exact ⟨r • X, r • Y, positiveFiniteTrace_smul b r hr hX,
        positiveFiniteTrace_smul b r hr hY, smul_sub r X Y⟩
    · refine ⟨(-r) • Y, (-r) • X, positiveFiniteTrace_smul b (-r) (neg_nonneg.mpr hr) hY,
        positiveFiniteTrace_smul b (-r) (neg_nonneg.mpr hr) hX, ?_⟩
      rw [smul_sub, neg_smul, neg_smul, sub_neg_eq_add, sub_eq_add_neg, add_comm]

omit [CompleteSpace H] in
theorem IsPositiveFiniteTrace.mem_signedFiniteTrace {T : H →L[𝕜] H}
    (hT : IsPositiveFiniteTrace b T) : T ∈ signedFiniteTrace b := by
  exact ⟨T, 0, hT, positiveFiniteTrace_zero b, (sub_zero T).symm⟩

omit [CompleteSpace H] in
theorem IsPositiveFiniteTrace.of_mem_signedFiniteTrace {T : H →L[𝕜] H}
    (hm : T ∈ signedFiniteTrace b) (hT : T.IsPositive) : IsPositiveFiniteTrace b T := by
  obtain ⟨X, Y, hX, hY, hEq⟩ := hm
  refine ⟨hT, ?_⟩
  have hXY : T + Y = X := by rw [hEq, sub_add_cancel]
  have hFin := hX.2
  rw [← hXY, positiveTrace_add b hT hY.1] at hFin
  exact (ENNReal.add_ne_top.mp hFin).1

omit [CompleteSpace H] in
theorem rankOne_mem_signedFiniteTrace (x : H) : InnerProductSpace.rankOne 𝕜 x x ∈ signedFiniteTrace b := by
  apply IsPositiveFiniteTrace.mem_signedFiniteTrace b
  refine ⟨InnerProductSpace.isPositive_rankOne_self x, ?_⟩
  exact positiveTrace_rankOne b x ▸ ENNReal.ofReal_ne_top

theorem signedFiniteTrace_isSelfAdjoint (T : signedFiniteTrace b) :
    IsSelfAdjoint (T : H →L[𝕜] H) := by
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property
  rw [hT]
  exact hX.1.isSelfAdjoint.sub hY.1.isSelfAdjoint

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
private theorem summable_diagonal_of_positiveFiniteTrace {X : H →L[𝕜] H}
    (hX : IsPositiveFiniteTrace b X) : Summable (fun i => RCLike.re ⟪X (b i), b i⟫_𝕜) := by
  have h := ENNReal.summable_toReal hX.2
  simpa only [ENNReal.toReal_ofReal (hX.1.re_inner_nonneg_left _)] using h

theorem summable_signedFiniteTrace_diagonal (T : signedFiniteTrace b) :
    Summable (fun i => RCLike.re ⟪T.val (b i), b i⟫_𝕜) := by
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property
  rw [hT]
  have h := (summable_diagonal_of_positiveFiniteTrace b hX).sub
    (summable_diagonal_of_positiveFiniteTrace b hY)
  convert h using 1
  funext i
  rw [sub_apply, inner_sub_left]
  exact map_sub (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) _ _

/-- The signed real trace, computed by the absolutely summable actual basis diagonal. -/
def signedTrace : signedFiniteTrace b →ₗ[ℝ] ℝ where
  toFun T := ∑' i, RCLike.re ⟪T.val (b i), b i⟫_𝕜
  map_add' S T := by
    rw [← (summable_signedFiniteTrace_diagonal b S).tsum_add
      (summable_signedFiniteTrace_diagonal b T)]
    refine tsum_congr fun i => ?_
    change RCLike.re ⟪(S.val + T.val) (b i), b i⟫_𝕜 = _
    rw [add_apply, inner_add_left]
    exact map_add (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) _ _
  map_smul' r T := by
    change (∑' i, RCLike.re ⟪(r • T.val) (b i), b i⟫_𝕜) =
      r * ∑' i, RCLike.re ⟪T.val (b i), b i⟫_𝕜
    rw [← (summable_signedFiniteTrace_diagonal b T).tsum_mul_left r]
    refine tsum_congr fun i => ?_
    rw [← algebraMap_smul 𝕜 r T.val, smul_apply, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul]

theorem signedTrace_eq_positiveTrace_toReal (T : signedFiniteTrace b) (hT : T.val.IsPositive) :
    signedTrace b T = (positiveTrace b T.val).toReal := by
  rw [positiveTrace, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  change (∑' i, RCLike.re ⟪T.val (b i), b i⟫_𝕜) = _
  exact tsum_congr (fun i => (ENNReal.toReal_ofReal (hT.re_inner_nonneg_left (b i))).symm)

end AlbertSequential.HilbertTrace
