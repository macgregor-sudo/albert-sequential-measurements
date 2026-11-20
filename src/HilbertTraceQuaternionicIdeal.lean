/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceQuaternionicInstrument
public import Mathlib.Tactic.NoncommRing

/-! Sharpness and ideality for genuine right-quaternionic trace-class maps. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "qTrace" => quaternionicSignedTrace b S
local notation "qPair" => quaternionicTracePairing b S

private theorem quat_proj_mul_eq_of_kernel {A P X : H →L[ℝ] H}
    (hP : IsStarProjection P) (hPr : P.range = A.ker) (hAX : A * X = 0) : P * X = X := by
  ext x
  have hx : X x ∈ A.ker := congrArg (fun T : H →L[ℝ] H => T x) hAX
  rw [← hPr] at hx
  obtain ⟨y, hy⟩ := hx
  change P (X x) = X x
  rw [← hy]
  exact congrArg (fun T : H →L[ℝ] H => T y) hP.isIdempotentElem.eq

private theorem commutes_kernelProjection_of_skew {A P R : H →L[ℝ] H}
    (hP : IsStarProjection P) (hPr : P.range = A.ker)
    (hRA : R * A = A * R) (hR : star R = -R) : R * P = P * R := by
  have hAP : A * P = 0 := by
    ext x
    have hx : P x ∈ P.range := ⟨x, rfl⟩
    rw [hPr] at hx
    exact hx
  have hz : A * (R * P) = 0 := by
    rw [← mul_assoc, ← hRA, mul_assoc, hAP, mul_zero]
  have h := quat_proj_mul_eq_of_kernel hP hPr hz
  have hs := congrArg star h
  simp only [star_mul, hP.isSelfAdjoint.star_eq, hR, mul_neg, neg_mul, neg_inj] at hs
  exact h.symm.trans (by simpa only [mul_assoc] using hs)

private theorem kernelProjection_mem_operatorAlgebra (A : Op) {P : H →L[ℝ] H}
    (hP : IsStarProjection P) (hPr : P.range = A.val.ker) : P ∈ Op := by
  let Q := S.toOperatorStructure
  obtain ⟨hi, hj⟩ := (Q.mem_operatorAlgebra_iff A.val).mp A.property
  exact (Q.mem_operatorAlgebra_iff P).mpr
    ⟨commutes_kernelProjection_of_skew hP hPr hi Q.star_rightI,
      commutes_kernelProjection_of_skew hP hPr hj Q.star_rightJ⟩

private theorem isStarProjection_of_operatorValue (P : Op) (hP : IsStarProjection P.val) :
    IsStarProjection P := ⟨Subtype.ext hP.isIdempotentElem.eq, Subtype.ext hP.isSelfAdjoint.star_eq⟩

omit [CompleteSpace H] in
private theorem quat_norm_inv_smul_unit {x : H} (h : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr h

private theorem QuaternionicInstrument.measuredEffect_isProjection_of_sharp (M : QuaternionicInstrument b S)
    (hm : M.IsIdealTest b S) {A : Op} (hA : IsQuaternionicEffect S A)
    (hpair : ∀ X, M.massOne b S X = qPair A X) : IsStarProjection A := by
  obtain ⟨P, Q, R, hP, hQ, hR, hPr, hQr, hPQ, _, _, hsum, hcomplete⟩ :=
    exists_endpointProjections A.val hA.1.isSelfAdjoint
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
  have hPm := kernelProjection_mem_operatorAlgebra S (1 - A) hP hPr
  have hQm := kernelProjection_mem_operatorAlgebra S A hQ hQr
  have hRm : R ∈ Op := by
    rw [hRdef]
    exact sub_mem (one_mem _) (add_mem hPm hQm)
  let r : Op := ⟨R, hRm⟩
  have hr := isStarProjection_of_operatorValue S r hR
  have hZ : R = 0 := by
    by_contra hn
    have hv : ∃ x : H, R x ≠ 0 := by
      by_contra! hz
      exact hn (ContinuousLinearMap.ext hz)
    obtain ⟨x, hx⟩ := hv
    let u := ‖R x‖⁻¹ • R x
    have hu : ‖u‖ = 1 := quat_norm_inv_smul_unit hx
    have hRu : R u = u := by
      change R (‖R x‖⁻¹ • R x) = ‖R x‖⁻¹ • R x
      rw [map_smul]
      exact congrArg (fun y : H => ‖R x‖⁻¹ • y)
        (congrArg (fun T : H →L[ℝ] H => T x) hR.isIdempotentElem.eq)
    apply hm.2.2
    refine ⟨quaternionicVectorDyad b S u, r, quaternionic_density_of_unit_vector b S u hu,
      quaternionic_projection_isEffect S hr, ?_, ?_⟩
    · rw [quaternionicVectorDyad_pairing]
      change ⟪R u, u⟫_ℝ = 1
      rw [hRu, real_inner_self_eq_norm_sq, hu, one_pow]
    · intro X hX hface
      apply quaternionic_tracePairing_eq_zero_of_mul_eq_zero b S
      change R * X.val = 0
      rcases hface with h0 | h1
      · rw [hpair] at h0
        have hz := (quaternionic_pairing_nonneg_zero_iff b S A X hA.1 hX.1).2.mp h0
        have hQX := quat_proj_mul_eq_of_kernel hQ hQr hz
        rw [← hQX, ← mul_assoc, hRQ, zero_mul]
      · rw [hpair] at h1
        have hz := (quaternionic_density_pairing_eq_one_iff b S A hA X hX).mp h1
        have hPX := quat_proj_mul_eq_of_kernel hP hPr hz
        rw [← hPX, ← mul_assoc, hRP, zero_mul]
  exact isStarProjection_of_operatorValue S A (hcomplete hZ ▸ hP)

private theorem quat_projection_fixed_corner
    (L : Carrier →ₗ[ℝ] Carrier) {P : Op} (hP : IsStarProjection P)
    (hfix : ∀ X, IsQuaternionicDensity b S X → qPair P X = 1 → L X = X)
    (Y : Carrier) (hY : Y.val.IsPositive) (hPY : P.val * Y.val = Y.val) : L Y = Y := by
  by_cases hz : Y.val = 0
  · have h : Y = 0 := Subtype.ext hz
    simp [h]
  have hp := (quaternionic_signedTrace_pos_iff b S hY).mpr hz
  let D : Carrier := (qTrace Y)⁻¹ • Y
  have hDp : D.val.IsPositive := hY.smul_of_nonneg (inv_nonneg.mpr hp.le)
  have hDt : qTrace D = 1 := by
    change qTrace ((qTrace Y)⁻¹ • Y) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']
  have hPD : (1 - P.val) * D.val = 0 := by
    change (1 - P.val) * ((qTrace Y)⁻¹ • Y.val) = 0
    rw [mul_smul_comm, sub_mul, one_mul, hPY, sub_self, smul_zero]
  have hD : L D = D := hfix D ⟨hDp, hDt⟩
    ((quaternionic_density_pairing_eq_one_iff b S P (quaternionic_projection_isEffect S hP)
      D ⟨hDp, hDt⟩).mpr hPD)
  have h := congrArg (fun X : Carrier => qTrace Y • X) hD
  simpa only [D, map_smul, smul_smul, mul_inv_cancel₀ hp.ne', one_smul] using h

private theorem quat_opposite_corner_killed
    (L : Carrier →ₗ[ℝ] Carrier) (P : Op) (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, qTrace (L X) = qPair P X)
    (Y : Carrier) (hY : Y.val.IsPositive) (hPY : P.val * Y.val = 0) : L Y = 0 := by
  have ht : qTrace (L Y) = 0 := (hmass Y).trans
    (quaternionic_tracePairing_eq_zero_of_mul_eq_zero b S P Y hPY)
  apply Subtype.ext
  change (L Y).val = 0
  by_contra! hn
  have hp := (quaternionic_signedTrace_pos_iff b S (hL Y hY)).mpr hn
  linarith

/-- A positive quaternionic branch measuring a projection factors through its input compression. -/
theorem branch_factors_through_quaternionicSandwich
    (L : Carrier →ₗ[ℝ] Carrier) {P : Op} (hP : IsStarProjection P)
    (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, qTrace (L X) = qPair P X) :
    ∀ X, L X = L (quaternionicSandwich b S P X) := by
  let Q : Op := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have hpv : IsStarProjection P.val := hP.map S.toOperatorStructure.operatorValue
  have hqv : IsStarProjection Q.val := hQ.map S.toOperatorStructure.operatorValue
  have hPQ : P.val * Q.val = 0 := by
    change P.val * (1 - P.val) = 0
    rw [mul_sub, mul_one, hpv.isIdempotentElem.eq, sub_self]
  have hp (X : Carrier) (hX : X.val.IsPositive) : L X = L (quaternionicSandwich b S P X) := by
    let Y := quaternionicSandwich b S P X
    let Z := quaternionicSandwich b S Q X
    let W := X - Y - Z
    have hYval : Y.val = P.val * X.val * P.val := by
      change P.val * X.val * star P.val = _
      rw [hpv.isSelfAdjoint.star_eq]
    have hZval : Z.val = Q.val * X.val * Q.val := by
      change Q.val * X.val * star Q.val = _
      rw [hqv.isSelfAdjoint.star_eq]
    have hZp := quaternionicSandwich_positive b S Q X hX
    have hPZ : P.val * Z.val = 0 := by
      rw [hZval, ← mul_assoc P.val, ← mul_assoc P.val, hPQ, zero_mul, zero_mul]
    have hZ := quat_opposite_corner_killed b S L P hL hmass Z hZp hPZ
    have hWval : W.val = P.val * X.val * Q.val + Q.val * X.val * P.val := by
      change X.val - Y.val - Z.val = _
      rw [hYval, hZval]
      change X.val - P.val * X.val * P.val - (1 - P.val) * X.val * (1 - P.val) =
        P.val * X.val * (1 - P.val) + (1 - P.val) * X.val * P.val
      noncomm_ring
    have hPoly (t : ℝ) : quaternionicSandwich b S (P + t • Q) X = Y + t • W + (t * t) • Z := by
      apply Subtype.ext
      change (P.val + t • Q.val) * X.val * star (P.val + t • Q.val) =
        Y.val + t • W.val + (t * t) • Z.val
      rw [star_add, star_smul, hpv.isSelfAdjoint.star_eq, hqv.isSelfAdjoint.star_eq,
        hYval, hZval, hWval]
      simp only [star_trivial, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
      abel
    have hAffine (t : ℝ) : ((L Y).val + (t : ℝ) • (L W).val).IsPositive := by
      have hr := hL _ (quaternionicSandwich_positive b S (P + t • Q) X hX)
      rw [hPoly, map_add, map_add, map_smul, map_smul, hZ, smul_zero, add_zero] at hr
      exact hr
    have hw : L W = 0 := Subtype.ext (eq_zero_of_positive_affine_line _ _ hAffine)
    change L (X - Y - Z) = 0 at hw
    rwa [map_sub, map_sub, hZ, sub_zero, sub_eq_zero] at hw
  intro X
  obtain ⟨U, V, hU, hV, hX⟩ := quaternionic_signedFiniteTrace_decomposition b S X
  rw [hX, map_sub, map_sub, map_sub, hp U hU, hp V hV]

private theorem quat_branch_eq_compression
    (L : Carrier →ₗ[ℝ] Carrier) {P : Op} (hP : IsStarProjection P)
    (hL : ∀ X, X.val.IsPositive → (L X).val.IsPositive)
    (hmass : ∀ X, qTrace (L X) = qPair P X)
    (hfix : ∀ X, IsQuaternionicDensity b S X → qPair P X = 1 → L X = X) :
    L = quaternionicSandwich b S P := by
  apply LinearMap.ext
  intro X
  rw [branch_factors_through_quaternionicSandwich b S L hP hL hmass X]
  let K := L - LinearMap.id
  have kills (U : Carrier) (hU : U.val.IsPositive) :
      K (quaternionicSandwich b S P U) = 0 := by
    apply sub_eq_zero.mpr
    apply quat_projection_fixed_corner b S L hP hfix _ (quaternionicSandwich_positive b S P U hU)
    change P.val * (P.val * U.val * star P.val) = P.val * U.val * star P.val
    have hpv : IsStarProjection P.val := hP.map S.toOperatorStructure.operatorValue
    rw [← mul_assoc, ← mul_assoc, hpv.isIdempotentElem.eq]
  obtain ⟨U, V, hU, hV, hX⟩ := quaternionic_signedFiniteTrace_decomposition b S X
  have h : K (quaternionicSandwich b S P X) = 0 := by
    rw [hX, map_sub, map_sub, kills U hU, kills V hV, sub_self]
  exact sub_eq_zero.mp h

private theorem quaternionicSandwich_if_fixed {P : Op} (hP : IsStarProjection P)
    (X : Carrier) (h : P.val * X.val = X.val) : quaternionicSandwich b S P X = X := by
  have hs : star P.val = P.val := (hP.map S.toOperatorStructure.operatorValue).isSelfAdjoint.star_eq
  have hx : IsSelfAdjoint X.val := signedFiniteTrace_isSelfAdjoint b (quaternionicCarrierInclusion b S X)
  have hr : X.val * P.val = X.val := by
    simpa only [star_mul, hs, hx.star_eq] using congrArg star h
  apply Subtype.ext
  change P.val * X.val * star P.val = X.val
  rw [hs, h, hr]

private theorem quat_effect_zero_on_range {F R : Op} (hF : F.val.IsPositive) (hR : IsStarProjection R)
    (hv : ∀ u, ‖u‖ = 1 → R.val u = u → qPair F (quaternionicVectorDyad b S u) = 0) :
    F.val * R.val = 0 := by
  ext x
  change F.val (R.val x) = 0
  by_cases h : R.val x = 0
  · rw [h, map_zero]
  let u := ‖R.val x‖⁻¹ • R.val x
  have hu : ‖u‖ = 1 := quat_norm_inv_smul_unit h
  have hRu : R.val u = u := by
    change R.val (‖R.val x‖⁻¹ • R.val x) = ‖R.val x‖⁻¹ • R.val x
    rw [map_smul]
    exact congrArg (fun y : H => ‖R.val x‖⁻¹ • y)
      (congrArg (fun T : H →L[ℝ] H => T x) (hR.map S.toOperatorStructure.operatorValue).isIdempotentElem.eq)
  have hh := (quaternionic_pairing_nonneg_zero_iff b S F (quaternionicVectorDyad b S u) hF
    (quaternionicVectorDyad_positive b S u)).2.mp (hv u hu hRu)
  have hFu : F.val u = 0 := by
    have he := congrArg (fun T : H →L[ℝ] H => T u) hh
    change F.val (quaternionicDyad S u u u) = 0 at he
    rw [quaternionicDyad_apply, S.quaternionInner_self, hu, one_pow, Quaternion.coe_one, S.right_one,
      one_apply_eq_self] at he
    exact he
  have hRnormalize : ‖R.val x‖ • u = R.val x := by
    change ‖R.val x‖ • (‖R.val x‖⁻¹ • R.val x) = R.val x
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
  rw [← hRnormalize, map_smul, hFu, smul_zero]

namespace QuaternionicInstrument

variable (M : QuaternionicInstrument b S)

theorem measuredEffect_of_branchOne_compression {P : Op} (hP : IsStarProjection P)
    (h : M.branchOne = quaternionicSandwich b S P) :
    ∀ X : Carrier, M.massOne b S X = qPair P X := by
  intro X
  change qTrace (M.branchOne X) = _
  rw [h, signedTrace_quaternionicSandwich, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]

private theorem quat_ideal_of_compression {P : Op} (hP : IsStarProjection P)
    (h₁ : M.branchOne = quaternionicSandwich b S P)
    (h₀ : M.branchZero = quaternionicSandwich b S (1 - P)) : M.IsIdealTest b S := by
  have hpair := M.measuredEffect_of_branchOne_compression b S hP h₁
  have heffect := quaternionic_projection_isEffect S hP
  refine ⟨?_, ?_, ?_⟩
  · intro X hX hx
    rw [hpair] at hx
    have hh := (quaternionic_density_pairing_eq_one_iff b S P heffect X hX).mp hx
    rw [sub_mul, one_mul, sub_eq_zero] at hh
    rw [h₁]
    exact quaternionicSandwich_if_fixed b S hP X hh.symm
  · intro X hX hx
    rw [hpair] at hx
    have hh := (quaternionic_pairing_nonneg_zero_iff b S P X heffect.1 hX.1).2.mp hx
    rw [h₀]
    apply quaternionicSandwich_if_fixed b S hP.one_sub X
    change (1 - P.val) * X.val = X.val
    rw [sub_mul, one_mul, hh, sub_zero]
  · rintro ⟨T, F, _, hF, hFT, hv⟩
    have hFP : F.val * P.val = 0 := quat_effect_zero_on_range b S hF.1 hP (by
      intro u hu hPu
      have hcert : M.massOne b S (quaternionicVectorDyad b S u) = 1 := by
        rw [hpair, quaternionicVectorDyad_pairing, hPu, real_inner_self_eq_norm_sq, hu, one_pow]
      exact hv _ (quaternionic_density_of_unit_vector b S u hu) (Or.inr hcert))
    have hFQ : F.val * (1 - P.val) = 0 := quat_effect_zero_on_range b S hF.1 hP.one_sub (by
      intro u hu hQu
      change (1 - P.val) u = u at hQu
      rw [sub_apply, one_apply_eq_self, sub_eq_self] at hQu
      have hcert : M.massOne b S (quaternionicVectorDyad b S u) = 0 := by
        rw [hpair, quaternionicVectorDyad_pairing, hQu, inner_zero_left]
      exact hv _ (quaternionic_density_of_unit_vector b S u hu) (Or.inl hcert))
    have hF0 : F.val = 0 := by
      have hsum : P.val + (1 - P.val) = 1 := by abel
      calc
        F.val = F.val * (P.val + (1 - P.val)) := by rw [hsum, mul_one]
        _ = 0 := by rw [mul_add, hFP, hFQ, add_zero]
    have hzero := quaternionic_tracePairing_eq_zero_of_mul_eq_zero b S F T (by rw [hF0, zero_mul])
    rw [hzero] at hFT
    exact zero_ne_one hFT

/-- The right-quaternionic Hilbert case of the ideal-test classification, including its measured
projection and both trivial outcomes. -/
theorem idealTest_iff_projection : M.IsIdealTest b S ↔ ∃ P : Op, IsStarProjection P ∧
    M.branchOne = quaternionicSandwich b S P ∧ M.branchZero = quaternionicSandwich b S (1 - P) ∧
    ∀ X, M.massOne b S X = qPair P X := by
  constructor
  · intro hm
    obtain ⟨P, heffect, hpair⟩ := M.exists_measuredEffect b S
    have hP := M.measuredEffect_isProjection_of_sharp b S hm heffect hpair
    refine ⟨P, hP, quat_branch_eq_compression b S M.branchOne hP M.one_positive hpair ?_,
      quat_branch_eq_compression b S M.branchZero hP.one_sub M.zero_positive ?_ ?_, hpair⟩
    · intro X hx hX
      apply hm.1 X hx
      rw [hpair, hX]
    · intro X
      rw [M.signedTrace_branchZero b S X, hpair, quaternionicTracePairing_complement_eq]
    · intro X hx hX
      apply hm.2.1 X hx
      rw [quaternionicTracePairing_complement_eq, hx.2] at hX
      rw [hpair]
      linarith
  · rintro ⟨P, hP, h₁, h₀, _⟩
    exact M.quat_ideal_of_compression b S hP h₁ h₀

end QuaternionicInstrument

end AlbertSequential.HilbertTrace
