/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.RealOperatorSpectralRounding
public import Robustness.QuaternionicOperatorSpectralRounding

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ContinuousFunctionalCalculus

namespace AlbertSequential

section Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Half-threshold rounding with the sharp effect deviation in both orders. -/
theorem exists_complex_calibration_projection (A : H →L[ℂ] H)
    (hA : A.IsPositive) (hAc : (1 - A).IsPositive)
    {ε : ℝ} (hdefect : ‖A * A - A‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧ P = cfc halfThresholdCutoff A ∧
      (spectralRoundingError ε • (1 : H →L[ℂ] H) - (A - P)).IsPositive ∧
      (spectralRoundingError ε • (1 : H →L[ℂ] H) - (P - A)).IsPositive := by
  let τ := spectralRoundingError ε
  let r := continuousRoundingRamp τ
  have hr : Continuous r := continuous_continuousRoundingRamp τ
  have h0 : 0 ≤ ε := (norm_nonneg _).trans hdefect
  have hτ := spectralRoundingError_lt_half hε
  have hs := positive_complex_effect_spectrum_subset A hA hAc
  have hband (x : ℝ) (hx : x ∈ spectrum ℝ A) : x ≤ τ ∨ 1 - τ ≤ x :=
    scalar_spectral_rounding_gap h0 hε (hs hx).1 (hs hx).2
      (spectral_point_defect_le A hA.isSelfAdjoint hs hdefect hx)
  have hcut (x : ℝ) (hx : x ∈ spectrum ℝ A) : r x = halfThresholdCutoff x :=
    continuousRoundingRamp_eq_cutoff hτ (hband x hx)
  have hdiff (x : ℝ) (hx : x ∈ spectrum ℝ A) : -τ ≤ x - r x ∧ x - r x ≤ τ := by
    rw [hcut x hx]
    rcases hband x hx with hlo | hhi
    · simp only [halfThresholdCutoff, ite_eq_left (hlo.trans_lt hτ), sub_zero]
      exact ⟨by linarith [(hs hx).1, spectralRoundingError_nonneg h0], hlo⟩
    · have hnot : ¬ x < 1 / 2 := by linarith
      simp only [halfThresholdCutoff, ite_eq_right hnot]
      exact ⟨by linarith, by linarith [(hs hx).2, spectralRoundingError_nonneg h0]⟩
  let P := cfc r A
  have hP : IsStarProjection P := by
    refine ⟨?_, cfc_predicate r A⟩
    change cfc r A * cfc r A = cfc r A
    rw [← cfc_mul r r A hr.continuousOn hr.continuousOn]
    apply cfc_congr
    intro x hx
    change r x * r x = r x
    rw [hcut x hx]
    exact halfThresholdCutoff_idempotent x
  refine ⟨P, hP, cfc_congr hcut, ?_, ?_⟩
  · have h : 0 ≤ cfc (fun x : ℝ => τ - (x - r x)) A :=
      cfc_nonneg (fun x hx => sub_nonneg.mpr (hdiff x hx).2)
    rw [cfc_sub (fun _ : ℝ => τ) (fun x : ℝ => x - r x) A continuousOn_const
        (continuous_id.sub hr).continuousOn,
      cfc_sub (fun x : ℝ => x) r A continuous_id.continuousOn hr.continuousOn,
      cfc_id' ℝ A hA.isSelfAdjoint, cfc_const τ A hA.isSelfAdjoint] at h
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    simpa only [Algebra.smul_def, mul_one] using h
  · have h : 0 ≤ cfc (fun x : ℝ => τ - (r x - x)) A :=
      cfc_nonneg (fun x hx => sub_nonneg.mpr (by linarith [(hdiff x hx).1]))
    rw [cfc_sub (fun _ : ℝ => τ) (fun x : ℝ => r x - x) A continuousOn_const
        (hr.sub continuous_id).continuousOn,
      cfc_sub r (fun x : ℝ => x) A hr.continuousOn continuous_id.continuousOn,
      cfc_id' ℝ A hA.isSelfAdjoint, cfc_const τ A hA.isSelfAdjoint] at h
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    simpa only [Algebra.smul_def, mul_one] using h

end Complex

section Real
open RealHilbertComplexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_real_calibration_projection (A : H →L[ℝ] H)
    (hA : A.IsPositive) (hAc : (1 - A).IsPositive)
    {ε : ℝ} (hdefect : ‖A * A - A‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ P : H →L[ℝ] H, IsStarProjection P ∧
      complexifyBoundedOperator P = cfc halfThresholdCutoff (complexifyBoundedOperator A) ∧
      (∀ S : H →L[ℝ] H, Commute A S → Commute P S) ∧
      (spectralRoundingError ε • (1 : H →L[ℝ] H) - (A - P)).IsPositive ∧
      (spectralRoundingError ε • (1 : H →L[ℝ] H) - (P - A)).IsPositive := by
  let C := complexifyBoundedOperator A
  have hC := (complexifyBoundedOperator_isPositive_iff A).mpr hA
  have hCc : (1 - C).IsPositive := by
    simpa only [C, map_sub, map_one] using (complexifyBoundedOperator_isPositive_iff (1 - A)).mpr hAc
  have hdef : ‖C * C - C‖ ≤ ε := by
    change ‖complexifyBoundedOperator A * complexifyBoundedOperator A - complexifyBoundedOperator A‖ ≤ ε
    rw [← map_mul, ← map_sub, complexifyBoundedOperator_norm]
    exact hdefect
  obtain ⟨Q, hQ, hQcut, hplus, hminus⟩ := exists_complex_calibration_projection C hC hCc hdef hε
  let r := continuousRoundingRamp (spectralRoundingError ε)
  have hr : Continuous r := continuous_continuousRoundingRamp _
  have heps : 0 ≤ ε := (norm_nonneg _).trans hdefect
  have hs := positive_complex_effect_spectrum_subset C hC hCc
  have hcut : cfc r C = cfc halfThresholdCutoff C := by
    apply cfc_congr
    intro x hx
    exact continuousRoundingRamp_eq_cutoff (spectralRoundingError_lt_half hε)
      (scalar_spectral_rounding_gap heps hε (hs hx).1 (hs hx).2
        (spectral_point_defect_le C hC.isSelfAdjoint hs hdef hx))
  let P := realOperatorCalculusValue A hA.isSelfAdjoint r hr.continuousOn
  have hP : complexifyBoundedOperator P = Q := by
    change complexifyBoundedOperator (realOperatorCalculusValue A hA.isSelfAdjoint r hr.continuousOn) = Q
    rw [complexify_realOperatorCalculusValue A hA.isSelfAdjoint r hr.continuousOn]
    exact hcut.trans hQcut.symm
  refine ⟨P, ⟨?_, realOperatorCalculusValue_selfAdjoint A hA.isSelfAdjoint r hr.continuousOn⟩,
    hP.trans hQcut, fun S hS => realOperatorCalculusValue_commute A S hA.isSelfAdjoint r hr.continuousOn hS,
    ?_, ?_⟩
  · change P * P = P
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_mul, hP]
    exact hQ.isIdempotentElem
  · apply (complexifyBoundedOperator_isPositive_iff _).mp
    rw [map_sub, map_sub, map_smul, map_one, hP]
    exact hplus
  · apply (complexifyBoundedOperator_isPositive_iff _).mp
    rw [map_sub, map_sub, map_smul, map_one, hP]
    exact hminus

theorem RightQuaternionicHilbertStructure.exists_quaternionic_calibration_projection
    (S : RightQuaternionicHilbertStructure H) (A : S.toOperatorStructure.operatorAlgebra)
    (hA : A.val.IsPositive) (hAc : (1 - A.val).IsPositive)
    {ε : ℝ} (hdefect : ‖A.val * A.val - A.val‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ P : S.toOperatorStructure.operatorAlgebra, IsStarProjection P ∧
      complexifyBoundedOperator P.val = cfc halfThresholdCutoff (complexifyBoundedOperator A.val) ∧
      (spectralRoundingError ε • (1 : H →L[ℝ] H) - (A.val - P.val)).IsPositive ∧
      (spectralRoundingError ε • (1 : H →L[ℝ] H) - (P.val - A.val)).IsPositive := by
  obtain ⟨P, hP, hcut, hcomm, hplus, hminus⟩ := exists_real_calibration_projection A.val hA hAc hdefect hε
  have hAcomm := (S.toOperatorStructure.mem_operatorAlgebra_iff A.val).mp A.property
  let Q : S.toOperatorStructure.operatorAlgebra :=
    ⟨P, (S.toOperatorStructure.mem_operatorAlgebra_iff P).mpr
      ⟨(hcomm _ hAcomm.1.symm).symm, (hcomm _ hAcomm.2.symm).symm⟩⟩
  have hQ : IsStarProjection Q := ⟨Subtype.ext hP.isIdempotentElem,
    Subtype.ext hP.isSelfAdjoint⟩
  exact ⟨Q, hQ, hcut, hplus, hminus⟩

end Real
end AlbertSequential
