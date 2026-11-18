/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.ComplexOperatorSpectralRounding
public import Robustness.RealOperatorCalculusDescent
public import Robustness.ComplexificationPositivity

/-! Actual same-space real square roots and spectral rounding through
isometric complexification and fixed-range descent. The original real state
is never extended. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem realOperatorCalculusValue_commute
    (T S : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) (hTS : Commute T S) :
    Commute (realOperatorCalculusValue T hT f hf) S := by
  have hC : Commute (complexifyBoundedOperator T) (complexifyBoundedOperator S) := by
    change complexifyBoundedOperator T * complexifyBoundedOperator S =
      complexifyBoundedOperator S * complexifyBoundedOperator T
    rw [← map_mul, ← map_mul, hTS.eq]
  have hcfc := hC.cfc_real f
  change realOperatorCalculusValue T hT f hf * S = S * realOperatorCalculusValue T hT f hf
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  simpa only [map_mul, complexify_realOperatorCalculusValue] using hcfc.eq

def realPositiveSquareRoot (E : H →L[ℝ] H) (hE : E.IsPositive) : H →L[ℝ] H :=
  realOperatorCalculusValue E hE.isSelfAdjoint Real.sqrt Real.continuous_sqrt.continuousOn

theorem complexify_realPositiveSquareRoot (E : H →L[ℝ] H) (hE : E.IsPositive) :
    complexifyBoundedOperator (realPositiveSquareRoot E hE) =
      cfc Real.sqrt (complexifyBoundedOperator E) :=
  complexify_realOperatorCalculusValue E hE.isSelfAdjoint Real.sqrt
    Real.continuous_sqrt.continuousOn

theorem realPositiveSquareRoot_positive_and_square (E : H →L[ℝ] H) (hE : E.IsPositive) :
    (realPositiveSquareRoot E hE).IsPositive ∧
      realPositiveSquareRoot E hE * realPositiveSquareRoot E hE = E := by
  have hc := complex_operator_cfc_sqrt_positive_and_square (complexifyBoundedOperator E)
    ((complexifyBoundedOperator_isPositive_iff E).mpr hE)
  constructor
  · apply (complexifyBoundedOperator_isPositive_iff _).mp
    rw [complexify_realPositiveSquareRoot]
    exact hc.1
  · apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_mul, complexify_realPositiveSquareRoot]
    exact hc.2

theorem realPositiveSquareRoot_unique
    (E S : H →L[ℝ] H) (hE : E.IsPositive) (hS : S.IsPositive) (hSq : S * S = E) :
    S = realPositiveSquareRoot E hE := by
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  rw [complexify_realPositiveSquareRoot]
  apply positive_complex_square_root_unique
    (complexifyBoundedOperator E) (complexifyBoundedOperator S)
    ((complexifyBoundedOperator_isPositive_iff S).mpr hS)
  rw [← map_mul, hSq]

theorem realPositiveSquareRoot_commute
    (E S : H →L[ℝ] H) (hE : E.IsPositive) (hES : Commute E S) :
    Commute (realPositiveSquareRoot E hE) S :=
  realOperatorCalculusValue_commute E S hE.isSelfAdjoint Real.sqrt
    Real.continuous_sqrt.continuousOn hES

theorem exists_real_rounded_projection
    (E sYes sNo : H →L[ℝ] H)
    (hE : E.IsPositive) (hEc : (1 - E).IsPositive)
    (hYes : sYes.IsPositive) (hNo : sNo.IsPositive)
    (hYesSq : sYes * sYes = E) (hNoSq : sNo * sNo = 1 - E)
    {epsilon : ℝ} (hdefect : ‖E * E - E‖ ≤ epsilon) (hepsilon : epsilon < 1 / 4) :
    ∃ P : H →L[ℝ] H, IsStarProjection P ∧
      (∀ S : H →L[ℝ] H, Commute E S → Commute P S) ∧
      ‖sYes - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sNo - (1 - P)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sYes‖ ≤ 1 ∧ ‖sNo‖ ≤ 1 ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 := by
  have hCE := (complexifyBoundedOperator_isPositive_iff E).mpr hE
  have hCEc : (1 - complexifyBoundedOperator E).IsPositive := by
    simpa only [map_sub, map_one] using (complexifyBoundedOperator_isPositive_iff (1 - E)).mpr hEc
  have hCY := (complexifyBoundedOperator_isPositive_iff sYes).mpr hYes
  have hCN := (complexifyBoundedOperator_isPositive_iff sNo).mpr hNo
  have hCYesSq : complexifyBoundedOperator sYes * complexifyBoundedOperator sYes =
      complexifyBoundedOperator E := by rw [← map_mul, hYesSq]
  have hCNoSq : complexifyBoundedOperator sNo * complexifyBoundedOperator sNo =
      1 - complexifyBoundedOperator E := by rw [← map_mul, hNoSq, map_sub, map_one]
  have hCD : ‖complexifyBoundedOperator E * complexifyBoundedOperator E -
      complexifyBoundedOperator E‖ ≤ epsilon := by
    rw [← map_mul, ← map_sub, complexifyBoundedOperator_norm]
    exact hdefect
  obtain ⟨PC, hPC, hcut, hY, hN, hnY, hnN, hnPC, hnQC⟩ :=
    exists_complex_rounded_projection (complexifyBoundedOperator E)
      (complexifyBoundedOperator sYes) (complexifyBoundedOperator sNo)
      hCE hCEc hCY hCN hCYesSq hCNoSq hCD hepsilon
  let tau := spectralRoundingError epsilon
  let r := continuousRoundingRamp tau
  have hr : Continuous r := continuous_continuousRoundingRamp tau
  have hsp := positive_complex_effect_spectrum_subset (complexifyBoundedOperator E) hCE hCEc
  have heps : 0 ≤ epsilon := (norm_nonneg _).trans hdefect
  have hround : ∀ x ∈ spectrum ℝ (complexifyBoundedOperator E), r x = halfThresholdCutoff x := by
    intro x hx
    exact continuousRoundingRamp_eq_cutoff (spectralRoundingError_lt_half hepsilon)
      (scalar_spectral_rounding_gap heps hepsilon (hsp hx).1 (hsp hx).2
        (spectral_point_defect_le _ hCE.isSelfAdjoint hsp hCD hx))
  have hrCut : cfc r (complexifyBoundedOperator E) =
      cfc halfThresholdCutoff (complexifyBoundedOperator E) := cfc_congr hround
  let P := realOperatorCalculusValue E hE.isSelfAdjoint r hr.continuousOn
  have hCP : complexifyBoundedOperator P = PC := by
    change complexifyBoundedOperator (realOperatorCalculusValue E hE.isSelfAdjoint r hr.continuousOn) = PC
    rw [complexify_realOperatorCalculusValue E hE.isSelfAdjoint r hr.continuousOn, hrCut]
    exact hcut.symm
  have hCQ : complexifyBoundedOperator (1 - P) = 1 - PC := by rw [map_sub, map_one, hCP]
  have hPSq : P * P = P := by
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_mul, hCP]
    exact hPC.isIdempotentElem
  refine ⟨P, ⟨hPSq, realOperatorCalculusValue_selfAdjoint E hE.isSelfAdjoint r hr.continuousOn⟩,
    (fun S hES => realOperatorCalculusValue_commute E S hE.isSelfAdjoint r hr.continuousOn hES),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = ‖complexifyBoundedOperator (sYes - P)‖ :=
        (complexifyBoundedOperator_norm (sYes - P)).symm
      _ = ‖complexifyBoundedOperator sYes - PC‖ := by rw [map_sub, hCP]
      _ ≤ Real.sqrt tau := hY
  · calc
      _ = ‖complexifyBoundedOperator (H := H) (sNo - (1 - P))‖ :=
        (complexifyBoundedOperator_norm (sNo - (1 - P))).symm
      _ = ‖complexifyBoundedOperator sNo - (1 - PC)‖ := by rw [map_sub, hCQ]
      _ ≤ Real.sqrt tau := hN
  · simpa only [complexifyBoundedOperator_norm] using hnY
  · simpa only [complexifyBoundedOperator_norm] using hnN
  · calc
      _ = ‖complexifyBoundedOperator P‖ := (complexifyBoundedOperator_norm P).symm
      _ = ‖PC‖ := congrArg norm hCP
      _ ≤ 1 := hnPC
  · calc
      _ = ‖complexifyBoundedOperator (H := H) (1 - P)‖ := (complexifyBoundedOperator_norm (1 - P)).symm
      _ = ‖1 - PC‖ := congrArg norm hCQ
      _ ≤ 1 := hnQC

theorem exists_real_rounded_projection_for_canonical_roots
    (E : H →L[ℝ] H) (hE : E.IsPositive) (hEc : (1 - E).IsPositive)
    {epsilon : ℝ} (hdefect : ‖E * E - E‖ ≤ epsilon) (hepsilon : epsilon < 1 / 4) :
    ∃ P : H →L[ℝ] H, IsStarProjection P ∧
      (∀ S : H →L[ℝ] H, Commute E S → Commute P S) ∧
      ‖realPositiveSquareRoot E hE - P‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖realPositiveSquareRoot (1 - E) hEc - (1 - P)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖realPositiveSquareRoot E hE‖ ≤ 1 ∧ ‖realPositiveSquareRoot (1 - E) hEc‖ ≤ 1 ∧
      ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 :=
  exists_real_rounded_projection E (realPositiveSquareRoot E hE)
    (realPositiveSquareRoot (1 - E) hEc) hE hEc
    (realPositiveSquareRoot_positive_and_square E hE).1
    (realPositiveSquareRoot_positive_and_square (1 - E) hEc).1
    (realPositiveSquareRoot_positive_and_square E hE).2
    (realPositiveSquareRoot_positive_and_square (1 - E) hEc).2 hdefect hepsilon

end AlbertSequential
