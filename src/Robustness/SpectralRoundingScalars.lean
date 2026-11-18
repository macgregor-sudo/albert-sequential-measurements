module

public import Interfaces.MeasuresAndRobustness
public import Mathlib.Tactic.Linarith

/-! Exact scalar spectral-gap and root estimates for the canonical rounding
error. These are not an operator spectral/CFC theorem or an R/C/H binding.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

def halfThresholdCutoff (x : ℝ) : ℝ := if x < 1 / 2 then 0 else 1

theorem spectralRoundingError_nonneg {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    0 ≤ spectralRoundingError epsilon := by
  have hs : Real.sqrt (1 - 4 * epsilon) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 - 4 * epsilon ≤ 1 by linarith)
  unfold spectralRoundingError
  linarith

theorem spectralRoundingError_lt_half {epsilon : ℝ} (hepsilon : epsilon < 1 / 4) :
    spectralRoundingError epsilon < 1 / 2 := by
  have hs : 0 < Real.sqrt (1 - 4 * epsilon) := Real.sqrt_pos.mpr (by linarith)
  unfold spectralRoundingError
  linarith

theorem spectralRoundingError_equation {epsilon : ℝ} (hepsilon : epsilon < 1 / 4) :
    spectralRoundingError epsilon * (1 - spectralRoundingError epsilon) = epsilon := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - 4 * epsilon by linarith)
  unfold spectralRoundingError
  nlinarith

theorem scalar_spectral_rounding_gap {epsilon x : ℝ}
    (_hepsilon : 0 ≤ epsilon) (heps : epsilon < 1 / 4) (_hx : 0 ≤ x) (_hxone : x ≤ 1)
    (herror : x * (1 - x) ≤ epsilon) :
    x ≤ spectralRoundingError epsilon ∨ 1 - spectralRoundingError epsilon ≤ x := by
  by_cases hlo : x ≤ spectralRoundingError epsilon
  · exact Or.inl hlo
  · right
    by_contra hhi
    have hleft : 0 < x - spectralRoundingError epsilon := sub_pos.mpr (lt_of_not_ge hlo)
    have hright : 0 < 1 - spectralRoundingError epsilon - x := sub_pos.mpr (lt_of_not_ge hhi)
    have hproduct := mul_pos hleft hright
    have htau := spectralRoundingError_equation heps
    nlinarith

theorem sqrt_add_sqrt_complement_ge_one {x : ℝ} (hx : 0 ≤ x) (hxone : x ≤ 1) :
    1 ≤ Real.sqrt x + Real.sqrt (1 - x) := by
  have hs := Real.sq_sqrt hx
  have ht := Real.sq_sqrt (sub_nonneg.mpr hxone)
  apply le_of_sq_le_sq _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (1 - x))]

theorem scalar_root_contractions {x : ℝ} (hx : 0 ≤ x) (hxone : x ≤ 1) :
    |Real.sqrt x| ≤ 1 ∧ |Real.sqrt (1 - x)| ≤ 1 := by
  constructor
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hxone
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 - x ≤ 1 by linarith)

theorem halfThresholdCutoff_idempotent (x : ℝ) :
    halfThresholdCutoff x * halfThresholdCutoff x = halfThresholdCutoff x := by
  unfold halfThresholdCutoff
  split_ifs <;> norm_num

theorem scalar_cutoff_contractions (x : ℝ) :
    |halfThresholdCutoff x| ≤ 1 ∧ |1 - halfThresholdCutoff x| ≤ 1 := by
  unfold halfThresholdCutoff
  split_ifs <;> norm_num

theorem scalar_square_root_rounding_bounds {epsilon x : ℝ}
    (hepsilon : 0 ≤ epsilon) (heps : epsilon < 1 / 4) (hx : 0 ≤ x) (hxone : x ≤ 1)
    (herror : x * (1 - x) ≤ epsilon) :
    |Real.sqrt x - halfThresholdCutoff x| ≤ Real.sqrt (spectralRoundingError epsilon) ∧
    |Real.sqrt (1 - x) - (1 - halfThresholdCutoff x)| ≤ Real.sqrt (spectralRoundingError epsilon) := by
  have htau := spectralRoundingError_lt_half heps
  have hsum := sqrt_add_sqrt_complement_ge_one hx hxone
  have hsx : Real.sqrt x ≤ 1 := by
    simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using (scalar_root_contractions hx hxone).1
  have hsy : Real.sqrt (1 - x) ≤ 1 := by
    simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using (scalar_root_contractions hx hxone).2
  obtain hlo | hhi := scalar_spectral_rounding_gap hepsilon heps hx hxone herror
  · have hcut : halfThresholdCutoff x = 0 := by
      unfold halfThresholdCutoff
      exact ite_eq_left (hlo.trans_lt htau)
    rw [hcut]
    constructor
    · simpa only [sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hlo
    · have hr : 1 - Real.sqrt (1 - x) ≤ Real.sqrt x := by linarith
      have hmon := Real.sqrt_le_sqrt hlo
      rw [sub_zero, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsy)]
      exact hr.trans hmon
  · have hcut : halfThresholdCutoff x = 1 := by
      unfold halfThresholdCutoff
      exact ite_eq_right (by linarith)
    rw [hcut]
    constructor
    · have hr : 1 - Real.sqrt x ≤ Real.sqrt (1 - x) := by linarith
      have hmon := Real.sqrt_le_sqrt (show 1 - x ≤ spectralRoundingError epsilon by linarith)
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsx)]
      exact hr.trans hmon
    · simpa only [sub_self, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] using
        Real.sqrt_le_sqrt (show 1 - x ≤ spectralRoundingError epsilon by linarith)

end AlbertSequential
