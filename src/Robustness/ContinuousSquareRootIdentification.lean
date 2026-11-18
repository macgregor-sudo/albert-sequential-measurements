module

public import Robustness.ContinuousSpectralRounding

/-! Identifying supplied nonnegative-spectrum roots with the REAL continuous
functional calculus. The CFC instance is an explicit conditional input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ContinuousFunctionalCalculus
namespace AlbertSequential
variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

theorem cfc_real_sqrt_mul_self (s : A) (hs : IsSelfAdjoint s)
    (hspectrum : ∀ x ∈ spectrum ℝ s, 0 ≤ x) :
    cfc Real.sqrt (s * s) = s := by
  have hmul : cfc (fun x : ℝ => x * x) s = s * s := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) s
      continuous_id.continuousOn continuous_id.continuousOn, cfc_id' ℝ s hs]
  rw [← hmul, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) s hs
    Real.continuous_sqrt.continuousOn (by fun_prop)]
  calc
    _ = cfc (fun x : ℝ => x) s := by
      apply cfc_congr
      intro x hx
      change Real.sqrt (x * x) = x
      simpa only [← pow_two] using Real.sqrt_sq (hspectrum x hx)
    _ = s := cfc_id' ℝ s hs

theorem supplied_nonnegative_spectrum_root_eq_cfc
    (s a : A) (hs : IsSelfAdjoint s)
    (hspectrum : ∀ x ∈ spectrum ℝ s, 0 ≤ x) (hsquare : s * s = a) :
    s = cfc Real.sqrt a := by
  rw [← hsquare]
  exact (cfc_real_sqrt_mul_self s hs hspectrum).symm

theorem cfc_real_sqrt_complement (a : A) (ha : IsSelfAdjoint a) :
    cfc Real.sqrt (1 - a) = cfc (fun x : ℝ => Real.sqrt (1 - x)) a := by
  have hc : cfc (fun x : ℝ => 1 - x) a = 1 - a := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) a
      continuousOn_const continuous_id.continuousOn,
      cfc_const_one ℝ a ha, cfc_id' ℝ a ha]
  rw [← hc, ← cfc_comp Real.sqrt (fun x : ℝ => 1 - x) a ha
    Real.continuous_sqrt.continuousOn (by fun_prop)]
  rfl

theorem exists_rounded_projection_for_supplied_roots
    (a sYes sNo : A) (ha : IsSelfAdjoint a)
    (hspectrum : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hsYes : IsSelfAdjoint sYes) (hsNo : IsSelfAdjoint sNo)
    (hsYes_spectrum : ∀ x ∈ spectrum ℝ sYes, 0 ≤ x)
    (hsNo_spectrum : ∀ x ∈ spectrum ℝ sNo, 0 ≤ x)
    (hsYes_sq : sYes * sYes = a) (hsNo_sq : sNo * sNo = 1 - a)
    {epsilon : ℝ} (hdefect : ‖a * a - a‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ P : A, IsSelfAdjoint P ∧ P * P = P ∧
      P = cfc halfThresholdCutoff a ∧
      ‖sYes - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sNo - (1 - P)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sYes‖ ≤ 1 ∧ ‖sNo‖ ≤ 1 ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 := by
  have hYes := supplied_nonnegative_spectrum_root_eq_cfc
    sYes a hsYes hsYes_spectrum hsYes_sq
  have hNo := supplied_nonnegative_spectrum_root_eq_cfc
    sNo (1 - a) hsNo hsNo_spectrum hsNo_sq
  rw [cfc_real_sqrt_complement a ha] at hNo
  simpa only [hYes, hNo] using
    exists_rounded_projection_of_isometric_real_cfc a ha hspectrum hdefect hepsilon

end AlbertSequential
