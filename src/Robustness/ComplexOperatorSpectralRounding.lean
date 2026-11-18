/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.ContinuousSquareRootIdentification
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Actual complex Hilbert operator rounding through the canonical complex
continuous functional calculus.
No finite dimension, nonzero space, state or trace-class assumption is used. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Pointwise
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_complex_operator_spectrum_nonnegative
    (T : H →L[ℂ] H) (hT : T.IsPositive) :
    ∀ x ∈ spectrum ℝ T, 0 ≤ x :=
  SpectrumRestricts.nnreal_iff.mp hT.spectrumRestricts

theorem positive_complex_effect_spectrum_subset
    (E : H →L[ℂ] H) (hE : E.IsPositive) (hEc : (1 - E).IsPositive) :
    spectrum ℝ E ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨positive_complex_operator_spectrum_nonnegative E hE x hx, ?_⟩
  have hmem : 1 - x ∈ ({1} : Set ℝ) - spectrum ℝ E :=
    Set.sub_mem_sub (by simp) hx
  rw [spectrum.singleton_sub_eq E (1 : ℝ)] at hmem
  have hcx : 1 - x ∈ spectrum ℝ (1 - E) := by simpa only [map_one] using hmem
  have hnonnegative := positive_complex_operator_spectrum_nonnegative (1 - E) hEc
    (1 - x) hcx
  linarith

theorem complex_operator_cfc_sqrt_positive_and_square
    (E : H →L[ℂ] H) (hE : E.IsPositive) :
    (cfc Real.sqrt E).IsPositive ∧ cfc Real.sqrt E * cfc Real.sqrt E = E := by
  have hsa : IsSelfAdjoint E := hE.isSelfAdjoint
  have hsp := positive_complex_operator_spectrum_nonnegative E hE
  constructor
  · exact ContinuousLinearMap.nonneg_iff_isPositive.mp
      ((cfc_nonneg_iff Real.sqrt E Real.continuous_sqrt.continuousOn hsa).mpr
        (fun x _ => Real.sqrt_nonneg x))
  · calc
      _ = cfc (fun x : ℝ => Real.sqrt x * Real.sqrt x) E :=
        (cfc_mul Real.sqrt Real.sqrt E Real.continuous_sqrt.continuousOn
          Real.continuous_sqrt.continuousOn).symm
      _ = cfc (fun x : ℝ => x) E :=
        cfc_congr (fun x hx => Real.mul_self_sqrt (hsp x hx))
      _ = E := cfc_id' ℝ E hsa

theorem positive_complex_square_root_unique
    (E S : H →L[ℂ] H) (hS : S.IsPositive) (hSq : S * S = E) :
    S = cfc Real.sqrt E :=
  supplied_nonnegative_spectrum_root_eq_cfc S E hS.isSelfAdjoint
    (positive_complex_operator_spectrum_nonnegative S hS) hSq

/-- All four contractions are conclusions, not additional root hypotheses. -/
theorem exists_complex_rounded_projection
    (E sYes sNo : H →L[ℂ] H)
    (hE : E.IsPositive) (hEc : (1 - E).IsPositive)
    (hYes : sYes.IsPositive) (hNo : sNo.IsPositive)
    (hYesSq : sYes * sYes = E) (hNoSq : sNo * sNo = 1 - E)
    {epsilon : ℝ} (hdefect : ‖E * E - E‖ ≤ epsilon) (hepsilon : epsilon < 1 / 4) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧ P = cfc halfThresholdCutoff E ∧
      ‖sYes - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sNo - (1 - P)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sYes‖ ≤ 1 ∧ ‖sNo‖ ≤ 1 ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 := by
  obtain ⟨P, hsa, hid, hcut, h1, h0, hn1, hn0, hnP, hnQ⟩ :=
    exists_rounded_projection_for_supplied_roots E sYes sNo hE.isSelfAdjoint
      (positive_complex_effect_spectrum_subset E hE hEc) hYes.isSelfAdjoint hNo.isSelfAdjoint
      (positive_complex_operator_spectrum_nonnegative sYes hYes)
      (positive_complex_operator_spectrum_nonnegative sNo hNo) hYesSq hNoSq hdefect hepsilon
  exact ⟨P, ⟨hid, hsa⟩, hcut, h1, h0, hn1, hn0, hnP, hnQ⟩

theorem exists_complex_rounded_projection_for_canonical_roots
    (E : H →L[ℂ] H) (hE : E.IsPositive) (hEc : (1 - E).IsPositive)
    {epsilon : ℝ} (hdefect : ‖E * E - E‖ ≤ epsilon) (hepsilon : epsilon < 1 / 4) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧ P = cfc halfThresholdCutoff E ∧
      ‖cfc Real.sqrt E - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖cfc Real.sqrt (1 - E) - (1 - P)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖cfc Real.sqrt E‖ ≤ 1 ∧ ‖cfc Real.sqrt (1 - E)‖ ≤ 1 ∧
      ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 := by
  have hYes := complex_operator_cfc_sqrt_positive_and_square E hE
  have hNo := complex_operator_cfc_sqrt_positive_and_square (1 - E) hEc
  exact exists_complex_rounded_projection E _ _ hE hEc hYes.1 hNo.1
    hYes.2 hNo.2 hdefect hepsilon

end AlbertSequential
