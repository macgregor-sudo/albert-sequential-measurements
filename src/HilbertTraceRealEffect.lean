/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceDensity
public import HilbertTraceRiesz

/-! Real Riesz recovery of the measured effect on the genuine trace-class carrier. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H)

def realVectorDyad (x : H) : signedFiniteTrace b :=
  ⟨InnerProductSpace.rankOne ℝ x x, rankOne_mem_signedFiniteTrace b x⟩

private def symmetricDyad (x y : H) : signedFiniteTrace b :=
  ⟨(1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ x y + InnerProductSpace.rankOne ℝ y x), by
    have h : InnerProductSpace.rankOne ℝ x y + InnerProductSpace.rankOne ℝ y x =
        (realVectorDyad b (x + y)).val - (realVectorDyad b x).val - (realVectorDyad b y).val := by
      change _ = InnerProductSpace.rankOne ℝ (x + y) (x + y) -
        InnerProductSpace.rankOne ℝ x x - InnerProductSpace.rankOne ℝ y y
      simp only [map_add, add_apply]
      abel
    rw [h]
    exact (signedFiniteTrace b).smul_mem _ ((signedFiniteTrace b).sub_mem
      ((signedFiniteTrace b).sub_mem (realVectorDyad b (x + y)).property (realVectorDyad b x).property)
      (realVectorDyad b y).property)⟩

omit [CompleteSpace H] in
private theorem symmetricDyad_comm (x y : H) : symmetricDyad b x y = symmetricDyad b y x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ x y + InnerProductSpace.rankOne ℝ y x) = _
  rw [add_comm]
  rfl

omit [CompleteSpace H] in
private theorem symmetricDyad_self (x : H) : symmetricDyad b x x = realVectorDyad b x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ x x + InnerProductSpace.rankOne ℝ x x) = _
  rw [← two_smul ℝ, smul_smul]
  norm_num [realVectorDyad]

omit [CompleteSpace H] in
private theorem symmetricDyad_add_left (x y z : H) :
    symmetricDyad b (x + y) z = symmetricDyad b x z + symmetricDyad b y z := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ (x + y) z + InnerProductSpace.rankOne ℝ z (x + y)) =
    (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ x z + InnerProductSpace.rankOne ℝ z x) +
      (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ y z + InnerProductSpace.rankOne ℝ z y)
  simp only [map_add, add_apply, smul_add]
  abel

omit [CompleteSpace H] in
private theorem symmetricDyad_smul_left (r : ℝ) (x y : H) :
    symmetricDyad b (r • x) y = r • symmetricDyad b x y := by
  have hl : InnerProductSpace.rankOne ℝ (r • x) y = r • InnerProductSpace.rankOne ℝ x y := by
    ext z
    simp only [InnerProductSpace.rankOne_apply, smul_apply, smul_smul, mul_comm]
  have hr : InnerProductSpace.rankOne ℝ y (r • x) = r • InnerProductSpace.rankOne ℝ y x := by
    ext z
    simp only [InnerProductSpace.rankOne_apply, real_inner_smul_left, smul_apply, smul_smul]
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ (r • x) y + InnerProductSpace.rankOne ℝ y (r • x)) =
    r • ((1 / 2 : ℝ) • (InnerProductSpace.rankOne ℝ x y + InnerProductSpace.rankOne ℝ y x))
  rw [hl, hr, ← smul_add, smul_comm]

private def branchBilinear (f : signedFiniteTrace b →ₗ[ℝ] ℝ) : H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => f (symmetricDyad b x y))
    (fun x y z => by rw [symmetricDyad_add_left, map_add])
    (fun r x y => by rw [symmetricDyad_smul_left, map_smul])
    (fun x y z => by rw [symmetricDyad_comm b x (y + z), symmetricDyad_add_left, map_add,
      symmetricDyad_comm b y x, symmetricDyad_comm b z x])
    (fun r x y => by rw [symmetricDyad_comm b x (r • y), symmetricDyad_smul_left, map_smul,
      symmetricDyad_comm b y x])

theorem realTracePairing_complement_eq (A : H →L[ℝ] H) (T : signedFiniteTrace b) :
    signedTracePairing b (1 - A) T = signedTrace b T - signedTracePairing b A T := by
  unfold signedTracePairing
  change (∑' i, RCLike.re ⟪(1 - A) (T.val (b i)), b i⟫_ℝ) =
    (∑' i, RCLike.re ⟪T.val (b i), b i⟫_ℝ) - ∑' i, RCLike.re ⟪A (T.val (b i)), b i⟫_ℝ
  rw [← (summable_signedFiniteTrace_diagonal b T).tsum_sub (real_summable_tracePairing b A T).of_norm]
  refine tsum_congr fun i => ?_
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, RCLike.re_to_real]

/-- Native effect recovery for a positive real trace-dominated branch functional on the entire
self-adjoint trace-class carrier. The measured effect is a positive contraction. -/
theorem exists_real_effect_of_trace_dominated (f : signedFiniteTrace b →ₗ[ℝ] ℝ)
    (hf : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ f T ∧ f T ≤ signedTrace b T) :
    ∃ A : H →L[ℝ] H, A.IsPositive ∧ (1 - A).IsPositive ∧
      ∀ T : signedFiniteTrace b, f T = signedTracePairing b A T := by
  let B := branchBilinear b f
  have hB (x y : H) : B x y = B y x := by
    change f (symmetricDyad b x y) = f (symmetricDyad b y x)
    rw [symmetricDyad_comm]
  have hD (x : H) : B x x = f (realVectorDyad b x) := by
    change f (symmetricDyad b x x) = _
    rw [symmetricDyad_self]
  have hmin (x : H) : 0 ≤ B x x := by
    rw [hD]
    exact (hf (realVectorDyad b x) (InnerProductSpace.isPositive_rankOne_self x)).1
  have hmax (x : H) : B x x ≤ ‖x‖ ^ 2 := by
    have h := (hf (realVectorDyad b x) (InnerProductSpace.isPositive_rankOne_self x)).2
    have ht : signedTrace b (realVectorDyad b x) = ‖x‖ ^ 2 := by
      change signedTracePairing b 1 ⟨InnerProductSpace.rankOne ℝ x x, rankOne_mem_signedFiniteTrace b x⟩ = _
      rw [signedTracePairing_rankOne, one_apply_eq_self, inner_self_eq_norm_sq]
    rwa [hD, ← ht]
  obtain ⟨A, hA, hAc, hq⟩ := exists_positiveContraction_of_diagonal_bilinear B hB hmin hmax
  let g := signedTracePairingLinear b A (fun T => (real_summable_tracePairing b A T).of_norm)
  have hg (T : signedFiniteTrace b) (hT : T.val.IsPositive) :
      0 ≤ g T ∧ g T ≤ signedTrace b T := by
    change 0 ≤ signedTracePairing b A T ∧ signedTracePairing b A T ≤ signedTrace b T
    refine ⟨(real_signedTracePairing_nonneg_zero_iff b A T hA hT).1, ?_⟩
    have h := (real_signedTracePairing_nonneg_zero_iff b (1 - A) T hAc hT).1
    rw [realTracePairing_complement_eq] at h
    exact sub_nonneg.mp h
  have hvec (x : H) : f (realVectorDyad b x) = g (realVectorDyad b x) := by
    change f (realVectorDyad b x) = signedTracePairing b A
      ⟨InnerProductSpace.rankOne ℝ x x, rankOne_mem_signedFiniteTrace b x⟩
    rw [signedTracePairing_rankOne, RCLike.re_to_real, hq, hD]
  have hfg : f = g := positiveFunctional_ext_of_rankOne b (fun h => by
    obtain ⟨S, hS, hSq⟩ := exists_real_positive_square_root h
    refine ⟨S, ?_⟩
    change S * star S = _
    rw [hS.isSelfAdjoint.star_eq, hSq]) f g hf hg hvec
  exact ⟨A, hA, hAc, fun T => LinearMap.congr_fun hfg T⟩

end AlbertSequential.HilbertTrace
