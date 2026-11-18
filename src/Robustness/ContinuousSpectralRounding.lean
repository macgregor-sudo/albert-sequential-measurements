module

public import Robustness.SpectralRoundingScalars
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! Conditional real-isometric-CFC spectral rounding. Native bounded-operator
instances, order/spectrum identification and trace-class bindings are separate.
The globally continuous ramp avoids applying algebraic CFC rules to a globally
discontinuous cutoff without proving continuity on the actual spectrum.
-/
@[expose] public section
noncomputable section
open scoped ContinuousFunctionalCalculus
namespace AlbertSequential

def continuousRoundingRamp (tau x : ℝ) : ℝ :=
  min 1 (max 0 ((x - tau) / (1 - 2 * tau)))

theorem continuous_continuousRoundingRamp (tau : ℝ) :
    Continuous (continuousRoundingRamp tau) := by
  exact continuous_const.min (continuous_const.max
    ((continuous_id.sub continuous_const).div_const _))

theorem continuousRoundingRamp_eq_cutoff {tau x : ℝ} (htau : tau < 1 / 2)
    (hband : x ≤ tau ∨ 1 - tau ≤ x) :
    continuousRoundingRamp tau x = halfThresholdCutoff x := by
  have hden : 0 < 1 - 2 * tau := by linarith
  rcases hband with hlo | hhi
  · have hfrac : (x - tau) / (1 - 2 * tau) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlo) hden.le
    have hcut : x < 1 / 2 := hlo.trans_lt htau
    have hcutEq : halfThresholdCutoff x = 0 := ite_eq_left hcut
    rw [hcutEq]
    unfold continuousRoundingRamp
    rw [max_eq_left hfrac, min_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  · have hfrac : 1 ≤ (x - tau) / (1 - 2 * tau) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    have hcut : ¬x < 1 / 2 := by linarith
    have hmax : 1 ≤ max 0 ((x - tau) / (1 - 2 * tau)) :=
      hfrac.trans (le_max_right _ _)
    have hcutEq : halfThresholdCutoff x = 1 := ite_eq_right hcut
    rw [hcutEq]
    exact min_eq_left hmax

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

theorem norm_one_le_one_of_isometric_real_cfc : ‖(1 : A)‖ ≤ 1 := by
  rw [← cfc_const_one ℝ (0 : A) (IsSelfAdjoint.zero A)]
  apply norm_cfc_le (by norm_num)
  intro x hx
  simp

theorem spectral_point_defect_le (a : A) (ha : IsSelfAdjoint a)
    (hspectrum : spectrum ℝ a ⊆ Set.Icc 0 1) {epsilon : ℝ}
    (hdefect : ‖a * a - a‖ ≤ epsilon) {x : ℝ} (hx : x ∈ spectrum ℝ a) :
    x * (1 - x) ≤ epsilon := by
  have hpoly : cfc (fun t : ℝ => t * t - t) a = a * a - a := by
    rw [cfc_sub (fun t : ℝ => t * t) (fun t : ℝ => t) a (by fun_prop) (by fun_prop),
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) a
        continuous_id.continuousOn continuous_id.continuousOn, cfc_id' ℝ a ha]
  have hn := norm_apply_le_norm_cfc (fun t : ℝ => t * t - t) a hx
    (by fun_prop) ha
  rw [hpoly, Real.norm_eq_abs] at hn
  have hnegative : x * x - x ≤ 0 := by
    have hbounds := hspectrum hx
    nlinarith [mul_nonneg hbounds.1 (sub_nonneg.mpr hbounds.2)]
  rw [abs_of_nonpos hnegative] at hn
  nlinarith [hn.trans hdefect]

theorem exists_rounded_projection_of_isometric_real_cfc
    (a : A) (ha : IsSelfAdjoint a)
    (hspectrum : spectrum ℝ a ⊆ Set.Icc 0 1)
    {epsilon : ℝ} (hdefect : ‖a * a - a‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ P : A, IsSelfAdjoint P ∧ P * P = P ∧
      P = cfc halfThresholdCutoff a ∧
      ‖cfc Real.sqrt a - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖cfc (fun t : ℝ => Real.sqrt (1 - t)) a - (1 - P)‖ ≤
        Real.sqrt (spectralRoundingError epsilon) ∧
      ‖cfc Real.sqrt a‖ ≤ 1 ∧
      ‖cfc (fun t : ℝ => Real.sqrt (1 - t)) a‖ ≤ 1 ∧
      ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 := by
  have heps : 0 ≤ epsilon := (norm_nonneg _).trans hdefect
  let tau := spectralRoundingError epsilon
  let r := continuousRoundingRamp tau
  have hr : Continuous r := continuous_continuousRoundingRamp tau
  have htau : tau < 1 / 2 := spectralRoundingError_lt_half hepsilon
  have hround : ∀ x ∈ spectrum ℝ a, r x = halfThresholdCutoff x := by
    intro x hx
    have hb := hspectrum hx
    exact continuousRoundingRamp_eq_cutoff htau
      (scalar_spectral_rounding_gap heps hepsilon hb.1 hb.2
        (spectral_point_defect_le a ha hspectrum hdefect hx))
  have hcut : cfc r a = cfc halfThresholdCutoff a := cfc_congr hround
  have hone : cfc (fun _ : ℝ => 1) a = 1 := cfc_const_one ℝ a ha
  refine ⟨cfc r a, cfc_predicate r a, ?_, hcut, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_mul r r a hr.continuousOn hr.continuousOn]
    apply cfc_congr
    intro x hx
    change r x * r x = r x
    rw [hround x hx]
    exact halfThresholdCutoff_idempotent x
  · rw [← cfc_sub Real.sqrt r a Real.continuous_sqrt.continuousOn hr.continuousOn]
    apply norm_cfc_le (Real.sqrt_nonneg _)
    intro x hx
    rw [Real.norm_eq_abs, hround x hx]
    have hb := hspectrum hx
    exact (scalar_square_root_rounding_bounds heps hepsilon hb.1 hb.2
      (spectral_point_defect_le a ha hspectrum hdefect hx)).1
  · rw [← hone, ← cfc_sub (fun _ : ℝ => 1) r a continuousOn_const hr.continuousOn,
      ← cfc_sub (fun t : ℝ => Real.sqrt (1 - t)) (fun t : ℝ => 1 - r t) a
        (by fun_prop) (by fun_prop)]
    apply norm_cfc_le (Real.sqrt_nonneg _)
    intro x hx
    rw [Real.norm_eq_abs, hround x hx]
    have hb := hspectrum hx
    exact (scalar_square_root_rounding_bounds heps hepsilon hb.1 hb.2
      (spectral_point_defect_le a ha hspectrum hdefect hx)).2
  · apply norm_cfc_le (by norm_num)
    intro x hx
    rw [Real.norm_eq_abs]
    exact (scalar_root_contractions (hspectrum hx).1 (hspectrum hx).2).1
  · apply norm_cfc_le (by norm_num)
    intro x hx
    rw [Real.norm_eq_abs]
    exact (scalar_root_contractions (hspectrum hx).1 (hspectrum hx).2).2
  · apply norm_cfc_le (by norm_num)
    intro x hx
    rw [Real.norm_eq_abs, hround x hx]
    exact (scalar_cutoff_contractions x).1
  · rw [← hone, ← cfc_sub (fun _ : ℝ => 1) r a continuousOn_const hr.continuousOn]
    apply norm_cfc_le (by norm_num)
    intro x hx
    rw [Real.norm_eq_abs, hround x hx]
    exact (scalar_cutoff_contractions x).2

end AlbertSequential
