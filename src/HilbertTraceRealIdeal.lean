/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceRealInstrument
public import Mathlib.Tactic.NoncommRing

/-! Ideality and sharpness on the native real trace-class Hilbert carrier. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H)

private theorem proj_mul_eq_of_range {P X : H →L[ℝ] H} (hP : IsStarProjection P)
    (h : ∀ x, X x ∈ P.range) : P * X = X := by
  ext x
  obtain ⟨z, hz⟩ := h x
  change P (X x) = X x
  rw [← hz]
  exact congrArg (fun T : H →L[ℝ] H => T z) hP.isIdempotentElem.eq

private theorem proj_mul_eq_of_mul_eq_zero {A P X : H →L[ℝ] H} (hP : IsStarProjection P)
    (hr : P.range = A.ker) (h : A * X = 0) : P * X = X := by
  apply proj_mul_eq_of_range hP
  intro z
  rw [hr]
  exact congrArg (fun T : H →L[ℝ] H => T z) h

private theorem proj_mul_swap {P X : H →L[ℝ] H} (hP : IsStarProjection P)
    (hX : IsSelfAdjoint X) (h : P * X = X) : X * P = X := by
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hX.star_eq] using congrArg star h

omit [CompleteSpace H] in
private theorem norm_inv_smul_unit {x : H} (h : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr h

private theorem projection_has_unit_fixed_point {R : H →L[ℝ] H}
    (hR : IsStarProjection R) (h : R ≠ 0) : ∃ u : H, ‖u‖ = 1 ∧ R u = u := by
  have hn : ∃ x : H, R x ≠ 0 := by
    by_contra! hz
    exact h (ContinuousLinearMap.ext hz)
  obtain ⟨x, hx⟩ := hn
  let u := ‖R x‖⁻¹ • R x
  refine ⟨u, norm_inv_smul_unit hx, ?_⟩
  change R (‖R x‖⁻¹ • R x) = ‖R x‖⁻¹ • R x
  rw [map_smul]
  exact congrArg (fun y : H => ‖R x‖⁻¹ • y)
    (congrArg (fun T : H →L[ℝ] H => T x) hR.isIdempotentElem.eq)

theorem RealInstrument.measuredEffect_isProjection_of_sharp (M : RealInstrument b)
    (hm : M.IsIdealTest b) {A : H →L[ℝ] H} (hA : IsRealEffect A)
    (hpair : ∀ X, M.massOne b X = signedTracePairing b A X) : IsStarProjection A := by
  obtain ⟨P, Q, R, hP, hQ, hR, hPr, hQr, hPQ, _, _, hsum, hcomplete⟩ :=
    exists_endpointProjections A hA.1.isSelfAdjoint
  have hQP : Q * P = 0 := by
    simpa only [star_mul, star_zero, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq] using
      congrArg star hPQ
  have hRdef : R = 1 - (P + Q) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum
  have hRP : R * P = 0 := by
    rw [hRdef, sub_mul, one_mul, add_mul, hP.isIdempotentElem.eq, hQP, add_zero, sub_self]
  have hRQ : R * Q = 0 := by
    rw [hRdef, sub_mul, one_mul, add_mul, hQ.isIdempotentElem.eq, hPQ, zero_add, sub_self]
  have hZ : R = 0 := by
    by_contra hn
    obtain ⟨u, hu, hRu⟩ := projection_has_unit_fixed_point hR hn
    apply hm.2.2
    refine ⟨realVectorDyad b u, R, real_density_of_unit_vector b u hu,
      real_projection_isEffect hR, ?_, ?_⟩
    · rw [realVectorDyad_pairing, hRu, real_inner_self_eq_norm_sq, hu, one_pow]
    · intro X hX hface
      apply real_tracePairing_eq_zero_of_mul_eq_zero b
      rcases hface with h0 | h1
      · rw [hpair] at h0
        have hz := (real_signedTracePairing_nonneg_zero_iff b A X hA.1 hX.1).2.mp h0
        have hQX := proj_mul_eq_of_mul_eq_zero hQ hQr hz
        rw [← hQX, ← mul_assoc, hRQ, zero_mul]
      · rw [hpair] at h1
        have hz := (real_density_pairing_eq_one_iff b A hA X hX).mp h1
        have hPX := proj_mul_eq_of_mul_eq_zero hP hPr hz
        rw [← hPX, ← mul_assoc, hRP, zero_mul]
  exact hcomplete hZ ▸ hP

private theorem projection_fixed_corner
    (L : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b) {P : H →L[ℝ] H}
    (hP : IsStarProjection P)
    (hfix : ∀ X, IsRealDensity b X → signedTracePairing b P X = 1 → L X = X)
    (Y : signedFiniteTrace b) (hY : Y.val.IsPositive) (hPY : P * Y.val = Y.val) : L Y = Y := by
  by_cases hz : Y.val = 0
  · have h : Y = 0 := Subtype.ext hz
    simp [h]
  have hp := (real_signedTrace_pos_iff b hY).mpr hz
  let D : signedFiniteTrace b := (signedTrace b Y)⁻¹ • Y
  have hDp : D.val.IsPositive := hY.smul_of_nonneg (inv_nonneg.mpr hp.le)
  have hDt : signedTrace b D = 1 := by
    change signedTrace b ((signedTrace b Y)⁻¹ • Y) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']
  have hPD : (1 - P) * D.val = 0 := by
    change (1 - P) * ((signedTrace b Y)⁻¹ • Y.val) = 0
    rw [mul_smul_comm, sub_mul, one_mul, hPY, sub_self, smul_zero]
  have hD : L D = D := hfix D ⟨hDp, hDt⟩
    ((real_density_pairing_eq_one_iff b P (real_projection_isEffect hP) D ⟨hDp, hDt⟩).mpr hPD)
  have h := congrArg (fun X : signedFiniteTrace b => signedTrace b Y • X) hD
  simpa only [D, map_smul, smul_smul, mul_inv_cancel₀ hp.ne', one_smul] using h

private theorem opposite_corner_killed
    (L : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b) (P : H →L[ℝ] H)
    (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, signedTrace b (L X) = signedTracePairing b P X)
    (Y : signedFiniteTrace b) (hY : Y.val.IsPositive) (hPY : P * Y.val = 0) : L Y = 0 := by
  have ht : signedTrace b (L Y) = 0 := (hmass Y).trans
    (real_tracePairing_eq_zero_of_mul_eq_zero b P Y hPY)
  apply Subtype.ext
  change (L Y).val = 0
  by_contra! hn
  have hp := (real_signedTrace_pos_iff b (hL Y hY)).mpr hn
  linarith

/-- A positive branch measuring a projection factors through its input compression. -/
theorem branch_factors_through_realSandwich
    (L : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b) {P : H →L[ℝ] H}
    (hP : IsStarProjection P)
    (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, signedTrace b (L X) = signedTracePairing b P X)
    : ∀ X, L X = L (realSandwich b P X) := by
  let Q := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have hPQ : P * Q = 0 := by
    change P * (1 - P) = 0
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  have hp (X : signedFiniteTrace b) (hX : X.val.IsPositive) : L X = L (realSandwich b P X) := by
    let Y := realSandwich b P X
    let Z := realSandwich b Q X
    let W := X - Y - Z
    have hYval : Y.val = P * X.val * P := by
      change P * X.val * star P = _
      rw [hP.isSelfAdjoint.star_eq]
    have hZval : Z.val = Q * X.val * Q := by
      change Q * X.val * star Q = _
      rw [hQ.isSelfAdjoint.star_eq]
    have hZp := realSandwich_positive b Q X hX
    have hPZ : P * Z.val = 0 := by
      rw [hZval, ← mul_assoc P, ← mul_assoc P, hPQ, zero_mul, zero_mul]
    have hZ := opposite_corner_killed b L P hL hmass Z hZp hPZ
    have hWval : W.val = P * X.val * Q + Q * X.val * P := by
      change X.val - Y.val - Z.val = _
      rw [hYval, hZval]
      dsimp [Q]
      noncomm_ring
    have hPolynomial (t : ℝ) : realSandwich b (P + t • Q) X = Y + t • W + (t * t) • Z := by
      apply Subtype.ext
      change (P + t • Q) * X.val * star (P + t • Q) = Y.val + t • W.val + (t * t) • Z.val
      rw [star_add, star_smul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
        hYval, hZval, hWval]
      simp only [star_trivial, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
      abel
    have hAffine (t : ℝ) : ((L Y).val + (t : ℝ) • (L W).val).IsPositive := by
      have hr := hL (realSandwich b (P + t • Q) X) (realSandwich_positive b (P + t • Q) X hX)
      rw [hPolynomial, map_add, map_add, map_smul, map_smul, hZ, smul_zero, add_zero] at hr
      exact hr
    have hw : L W = 0 := Subtype.ext (eq_zero_of_positive_affine_line _ _ hAffine)
    change L (X - Y - Z) = 0 at hw
    rwa [map_sub, map_sub, hZ, sub_zero, sub_eq_zero] at hw
  intro X
  obtain ⟨U₀, V₀, hU, hV, hX⟩ := X.property
  let U : signedFiniteTrace b := ⟨U₀, hU.mem_signedFiniteTrace b⟩
  let V : signedFiniteTrace b := ⟨V₀, hV.mem_signedFiniteTrace b⟩
  have hd : X = U - V := Subtype.ext hX
  rw [hd, map_sub, map_sub, map_sub, hp U hU.1, hp V hV.1]

private theorem branch_eq_compression
    (L : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b) {P : H →L[ℝ] H}
    (hP : IsStarProjection P)
    (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, signedTrace b (L X) = signedTracePairing b P X)
    (hfix : ∀ X, IsRealDensity b X → signedTracePairing b P X = 1 → L X = X) :
    L = realSandwich b P := by
  apply LinearMap.ext
  intro X
  rw [branch_factors_through_realSandwich b L hP hL hmass X]
  let K := L - LinearMap.id
  have kills (U : signedFiniteTrace b) (hU : U.val.IsPositive) :
      K (realSandwich b P U) = 0 := by
    apply sub_eq_zero.mpr
    apply projection_fixed_corner b L hP hfix _ (realSandwich_positive b P U hU)
    change P * (P * U.val * star P) = P * U.val * star P
    rw [← mul_assoc, ← mul_assoc, hP.isIdempotentElem.eq]
  obtain ⟨U₀,V₀,hU,hV,hX⟩ := X.property
  let U : signedFiniteTrace b := ⟨U₀,hU.mem_signedFiniteTrace b⟩
  let V : signedFiniteTrace b := ⟨V₀,hV.mem_signedFiniteTrace b⟩
  have hd : X = U - V := Subtype.ext hX
  have h : K (realSandwich b P X) = 0 := by
    rw [hd,map_sub,map_sub,kills U hU.1,kills V hV.1,sub_self]
  exact sub_eq_zero.mp h

private theorem sandwiched_if_fixed {P : H →L[ℝ] H} (hP : IsStarProjection P)
    (X : signedFiniteTrace b) (h : P * X.val = X.val) : realSandwich b P X = X := by
  apply Subtype.ext
  change P * X.val * star P = X.val
  rw [hP.isSelfAdjoint.star_eq, h, proj_mul_swap hP (signedFiniteTrace_isSelfAdjoint b X) h]

private theorem effect_zero_on_range {F R : H →L[ℝ] H} (hF : F.IsPositive) (hR : IsStarProjection R)
    (hv : ∀ u, ‖u‖ = 1 → R u = u → signedTracePairing b F (realVectorDyad b u) = 0) : F * R = 0 := by
  ext x
  change F (R x) = 0
  by_cases h : R x = 0
  · rw [h, map_zero]
  let u := ‖R x‖⁻¹ • R x
  have hu : ‖u‖ = 1 := norm_inv_smul_unit h
  have hRu : R u = u := by
    change R (‖R x‖⁻¹ • R x) = ‖R x‖⁻¹ • R x
    rw [map_smul]
    exact congrArg (fun y : H => ‖R x‖⁻¹ • y)
      (congrArg (fun T : H →L[ℝ] H => T x) hR.isIdempotentElem.eq)
  have hh := (real_signedTracePairing_nonneg_zero_iff b F (realVectorDyad b u) hF
    (realVectorDyad_positive b u)).2.mp (hv u hu hRu)
  have hFu : F u = 0 := by
    have h := congrArg (fun T : H →L[ℝ] H => T u) hh
    change F (InnerProductSpace.rankOne ℝ u u u) = 0 at h
    rwa [InnerProductSpace.rankOne_apply, real_inner_self_eq_norm_sq, hu, one_pow, one_smul] at h
  have hRnormalize : ‖R x‖ • u = R x := by
    change ‖R x‖ • (‖R x‖⁻¹ • R x) = R x
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
  rw [← hRnormalize, map_smul, hFu, smul_zero]

namespace RealInstrument

variable (M : RealInstrument b)

theorem measuredEffect_of_branchOne_compression {P : H →L[ℝ] H} (hP : IsStarProjection P)
    (h : M.branchOne = realSandwich b P) :
    ∀ X : signedFiniteTrace b, M.massOne b X = signedTracePairing b P X := by
  intro X
  change signedTrace b (M.branchOne X) = _
  rw [h, signedTrace_realSandwich, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]

private theorem ideal_of_compression {P : H →L[ℝ] H} (hP : IsStarProjection P)
    (h₁ : M.branchOne = realSandwich b P) (h₀ : M.branchZero = realSandwich b (1 - P)) :
    M.IsIdealTest b := by
  have hpair := M.measuredEffect_of_branchOne_compression b hP h₁
  have heffect := real_projection_isEffect hP
  refine ⟨?_, ?_, ?_⟩
  · intro X hX hx
    rw [hpair] at hx
    have hh := (real_density_pairing_eq_one_iff b P heffect X hX).mp hx
    rw [sub_mul, one_mul, sub_eq_zero] at hh
    rw [h₁]
    exact sandwiched_if_fixed b hP X hh.symm
  · intro X hX hx
    rw [hpair] at hx
    have hh := (real_signedTracePairing_nonneg_zero_iff b P X heffect.1 hX.1).2.mp hx
    rw [h₀]
    apply sandwiched_if_fixed b hP.one_sub X
    rw [sub_mul, one_mul, hh, sub_zero]
  · rintro ⟨S, F, _, hF, hFS, hv⟩
    have hFP : F * P = 0 := effect_zero_on_range b hF.1 hP (by
      intro u hu hPu
      have hcert : M.massOne b (realVectorDyad b u) = 1 := by
        rw [hpair, realVectorDyad_pairing, hPu, real_inner_self_eq_norm_sq, hu, one_pow]
      exact hv _ (real_density_of_unit_vector b u hu) (Or.inr hcert))
    have hFQ : F * (1 - P) = 0 := effect_zero_on_range b hF.1 hP.one_sub (by
      intro u hu hQu
      rw [sub_apply, one_apply_eq_self, sub_eq_self] at hQu
      have hcert : M.massOne b (realVectorDyad b u) = 0 := by
        rw [hpair, realVectorDyad_pairing, hQu, inner_zero_left]
      exact hv _ (real_density_of_unit_vector b u hu) (Or.inl hcert))
    have hF0 : F = 0 := by
      have hsum : P + (1 - P) = 1 := by abel
      calc
        F = F * (P + (1 - P)) := by rw [hsum, mul_one]
        _ = 0 := by rw [mul_add, hFP, hFQ, add_zero]
    have hzero := real_tracePairing_eq_zero_of_mul_eq_zero b F S (by rw [hF0, zero_mul])
    rw [hzero] at hFS
    exact zero_ne_one hFS

/-- The real Hilbert case of the ideal-test classification, with its measured effect.
The statement is valid for any Hilbert basis, including an empty one, and both zero and
identity projections are allowed. -/
theorem idealTest_iff_projection : M.IsIdealTest b ↔ ∃ P : H →L[ℝ] H, IsStarProjection P ∧
    M.branchOne = realSandwich b P ∧ M.branchZero = realSandwich b (1 - P) ∧
    ∀ X, M.massOne b X = signedTracePairing b P X := by
  constructor
  · intro hm
    obtain ⟨P, heffect, hpair⟩ := M.exists_measuredEffect b
    have hP := M.measuredEffect_isProjection_of_sharp b hm heffect hpair
    refine ⟨P, hP, branch_eq_compression b M.branchOne hP M.one_positive hpair ?_,
      branch_eq_compression b M.branchZero hP.one_sub M.zero_positive ?_ ?_, hpair⟩
    · intro X hx hX
      apply hm.1 X hx
      rw [hpair, hX]
    · intro X
      rw [M.signedTrace_branchZero b X, hpair, realTracePairing_complement_eq]
    · intro X hx hX
      apply hm.2.1 X hx
      rw [realTracePairing_complement_eq, hx.2] at hX
      rw [hpair]
      linarith
  · rintro ⟨P, hP, h₁, h₀, _⟩
    exact M.ideal_of_compression b hP h₁ h₀

end RealInstrument

end AlbertSequential.HilbertTrace
