/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.RobustNativeMS
public import Robustness.SpectralRoundingScalars
public import Robustness.WitnessTransport

/-! Exact numerical readout and defect thresholds in companion §2.5. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.BlockB

/-- Exact native witness margin divided by the merged coefficient norm. -/
def maximizerRobustRatio : ℝ :=
  (4588961 / 169869312 : ℝ) / robustFunctionalM.coefficientNorm

/-- Exact native witness margin divided by the merged coefficient norm. -/
def fixedSRobustRatio : ℝ :=
  (412734271 / 18345885696 : ℝ) / robustFunctionalS.coefficientNorm

private theorem positive_norm_of_negative_evaluation (C : FiniteRealWordFunctional 4)
    (target : Word (Fin 4) → ℝ) {γ : ℝ} (hγ : 0 < γ) (h : C.evaluate target ≤ -γ) :
    0 < C.coefficientNorm := by
  have hz : C.evaluate (fun _ => 0) = 0 := by
    rw [FiniteRealWordFunctional.evaluate_eq_coefficients]
    simp [Finsupp.sum]
  have hz0 : 0 ≤ C.evaluate (fun _ => 0) := by rw [hz]
  exact (C.positive_witness_margin_forces_some_word target (fun _ => 0) hγ hz0 h).1

theorem maximizerRobustRatio_gt_printed_floor : (51 / 10 ^ 13 : ℝ) < maximizerRobustRatio := by
  have hp : 0 < robustFunctionalM.coefficientNorm :=
    positive_norm_of_negative_evaluation _ _ (by norm_num) robustFunctionalM_eval_e3.le
  apply (lt_div_iff₀ hp).mpr
  calc
    _ ≤ (51 / 10 ^ 13 : ℝ) * (5268 * 10 ^ 6) :=
      mul_le_mul_of_nonneg_left robustFunctionalM_coefficientNorm_le_paper (by norm_num)
    _ < _ := by norm_num

theorem fixedSRobustRatio_gt_printed_floor : (77 / 10 ^ 14 : ℝ) < fixedSRobustRatio := by
  have hp : 0 < robustFunctionalS.coefficientNorm :=
    positive_norm_of_negative_evaluation _ _ (by norm_num) robustFunctionalS_eval_e3.le
  apply (lt_div_iff₀ hp).mpr
  calc
    _ ≤ (77 / 10 ^ 14 : ℝ) * (2892 * 10 ^ 7) :=
      mul_le_mul_of_nonneg_left robustFunctionalS_coefficientNorm_le_paper (by norm_num)
    _ < _ := by norm_num

private theorem root_budget_of_spectral_defect {ε c : ℝ} (hε : 0 ≤ ε) (hl : ε < 1 / 4)
    (hc : 0 ≤ c) (hch : c ^ 2 ≤ 1 / 2) (hsmall : ε < c ^ 2 * (1 - c ^ 2)) :
    Real.sqrt (spectralRoundingError ε) < c := by
  let τ := spectralRoundingError ε
  have hτ : τ < 1 / 2 := spectralRoundingError_lt_half hl
  have hτeq : τ * (1 - τ) = ε := spectralRoundingError_equation hl
  have hlt : τ < c ^ 2 := by
    by_contra! h
    have hsum := add_le_add hτ.le hch
    have hnonneg : 0 ≤ 1 - τ - c ^ 2 := by
      rw [sub_sub]
      exact sub_nonneg.mpr (hsum.trans (by norm_num))
    have hp := mul_nonneg (sub_nonneg.mpr h) hnonneg
    rw [← hτeq] at hsmall
    nlinarith
  have h := Real.sqrt_lt_sqrt (spectralRoundingError_nonneg hε) hlt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hc] using h

theorem maximizer_printed_exact_defect_budget {ε : ℝ} (hε : 0 ≤ ε)
    (hcut : ε ≤ 12 / 10 ^ 26) :
    14 * Real.sqrt (spectralRoundingError ε) < maximizerRobustRatio := by
  have h := root_budget_of_spectral_defect hε (hcut.trans_lt (by norm_num))
    (c := (51 / 10 ^ 13 : ℝ) / 14) (by norm_num) (by norm_num) (hcut.trans_lt (by norm_num))
  linarith [maximizerRobustRatio_gt_printed_floor]

theorem fixedS_printed_exact_defect_budget {ε : ℝ} (hε : 0 ≤ ε)
    (hcut : ε ≤ 3 / 10 ^ 27) :
    14 * Real.sqrt (spectralRoundingError ε) < fixedSRobustRatio := by
  have h := root_budget_of_spectral_defect hε (hcut.trans_lt (by norm_num))
    (c := (77 / 10 ^ 14 : ℝ) / 14) (by norm_num) (by norm_num) (hcut.trans_lt (by norm_num))
  linarith [fixedSRobustRatio_gt_printed_floor]

theorem maximizer_printed_projective_readout_budget {δ : ℝ} (hδ : δ ≤ 25 / 10 ^ 13) :
    2 * δ < maximizerRobustRatio := by
  linarith [maximizerRobustRatio_gt_printed_floor]

theorem fixedS_printed_projective_readout_budget {δ : ℝ} (hδ : δ ≤ 38 / 10 ^ 14) :
    2 * δ < fixedSRobustRatio := by
  linarith [fixedSRobustRatio_gt_printed_floor]

theorem maximizer_printed_calibration_budget {β : ℝ} (hβ : β ≤ 72 / 10 ^ 14) :
    7 * β < maximizerRobustRatio := by
  linarith [maximizerRobustRatio_gt_printed_floor]

theorem fixedS_printed_calibration_budget {β : ℝ} (hβ : β ≤ 11 / 10 ^ 14) :
    7 * β < fixedSRobustRatio := by
  linarith [fixedSRobustRatio_gt_printed_floor]

/-- Two probabilities separated by the remaining certificate margin cannot
both agree with one readout to the stated common tolerance. -/
theorem no_common_readout_of_budget {m drift δ target observed model : ℝ}
    (hgap : m - drift ≤ |target - model|)
    (ht : |target - observed| ≤ δ) (hm : |model - observed| ≤ δ)
    (hbudget : 2 * δ + drift < m) : False := by
  have h := abs_sub_le target observed model
  rw [abs_sub_comm observed model] at h
  linarith

end AlbertSequential.BlockB
