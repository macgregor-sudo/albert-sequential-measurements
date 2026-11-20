/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-! The two certainty eigenspaces and their orthogonal complement. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The projections onto the two certainty kernels and their complement. -/
theorem exists_endpointProjections (A : H →L[𝕜] H) (hA : IsSelfAdjoint A) :
    ∃ P Q R : H →L[𝕜] H,
      IsStarProjection P ∧ IsStarProjection Q ∧ IsStarProjection R ∧
      P.range = (1 - A).ker ∧ Q.range = A.ker ∧ P * Q = 0 ∧
      A * P = P ∧ A * Q = 0 ∧ P + Q + R = 1 ∧ (R = 0 → A = P) := by
  let U := (1 - A).ker
  let V := A.ker
  have hU : IsComplete (U : Set H) := (1 - A).isComplete_ker
  have hV : IsComplete (V : Set H) := A.isComplete_ker
  let : CompleteSpace U := hU.completeSpace_coe
  let : CompleteSpace V := hV.completeSpace_coe
  let P := U.starProjection
  let Q := V.starProjection
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hQ : IsStarProjection Q := isStarProjection_starProjection
  have hPu : P.range = U := Submodule.range_starProjection U
  have hQv : Q.range = V := Submodule.range_starProjection V
  have horth : U ⟂ V := by
    intro x hx y hy
    have hx' : x - A x = 0 := hx
    have hy' : A y = 0 := hy
    have hAx : A x = x := (sub_eq_zero.mp hx').symm
    have hh := ContinuousLinearMap.adjoint_inner_right A x y
    rw [show ContinuousLinearMap.adjoint A = A from hA, hy', inner_zero_right, hAx] at hh
    exact inner_eq_zero_symm.mp hh.symm
  have hPQ : P * Q = 0 := horth.starProjection_comp_starProjection
  have hAP : A * P = P := by
    ext x
    have hxP : P x ∈ P.range := ⟨x, rfl⟩
    have hx : P x ∈ U := hPu ▸ hxP
    have hx' : P x - A (P x) = 0 := hx
    exact (sub_eq_zero.mp hx').symm
  have hAQ : A * Q = 0 := by
    ext x
    have hxQ : Q x ∈ Q.range := ⟨x, rfl⟩
    have hx : Q x ∈ V := hQv ▸ hxQ
    exact hx
  refine ⟨P, Q, 1 - (P + Q), hP, hQ, (hP.add hQ hPQ).one_sub, hPu, hQv,
    hPQ, hAP, hAQ, ?_, ?_⟩
  · abel
  · intro h
    have hsum : P + Q = 1 := (sub_eq_zero.mp h).symm
    calc
      A = A * (P + Q) := by rw [hsum, mul_one]
      _ = P := by rw [mul_add, hAP, hAQ, add_zero]

/-- Positivity along an entire real affine line forces the operator slope to vanish. -/
theorem eq_zero_of_positive_affine_line (X Y : H →L[𝕜] H)
    (h : ∀ t : ℝ, (X + (t : 𝕜) • Y).IsPositive) : Y = 0 := by
  have hX : X.IsPositive := by simpa using h 0
  have hXY : (X + Y).IsPositive := by simpa using h 1
  have hY : IsSelfAdjoint Y := by
    simpa only [add_sub_cancel_left] using hXY.isSelfAdjoint.sub hX.isSelfAdjoint
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hY
  have hform (x : H) (t : ℝ) :
      0 ≤ RCLike.re ⟪X x, x⟫_𝕜 + t * RCLike.re ⟪Y x, x⟫_𝕜 := by
    have hp := (h t).re_inner_nonneg_left x
    rw [add_apply, smul_apply, inner_add_left, inner_smul_left, RCLike.conj_ofReal] at hp
    change 0 ≤ (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (_ + _) at hp
    rw [map_add] at hp
    simpa only [RCLike.reCLM_apply, RCLike.re_ofReal_mul] using hp
  have hZero : Y.toLinearMap = 0 := hs.inner_map_self_eq_zero.mp fun x => by
    rw [← hs.coe_re_inner_apply_self, RCLike.ofReal_eq_zero]
    by_contra hn
    change RCLike.re ⟪Y x, x⟫_𝕜 ≠ 0 at hn
    have hh := hform x (-(RCLike.re ⟪X x, x⟫_𝕜 + 1) / RCLike.re ⟪Y x, x⟫_𝕜)
    rw [div_mul_cancel₀ _ hn] at hh
    linarith
  ext x
  exact LinearMap.congr_fun hZero x

end AlbertSequential.HilbertTrace
