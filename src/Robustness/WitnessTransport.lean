module

public import RealWordFunctionals
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! Uses the merged-word coefficient norm. The model
and target witness signs are explicit assumptions; this is not a new no-go.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace FiniteRealWordFunctional

theorem positive_witness_margin_forces_some_word {n : ℕ}
    (c : FiniteRealWordFunctional n) (target projective : Word (Fin n) → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hprojective : 0 ≤ c.evaluate projective)
    (htarget : c.evaluate target ≤ -gamma) :
    0 < c.coefficientNorm ∧ ∃ w ∈ c.coefficients.support,
      gamma / c.coefficientNorm ≤ |projective w - target w| := by
  classical
  have hs : c.coefficients.support.Nonempty := by
    by_contra h
    have hb := c.separation_forces_error projective target 0 gamma (by norm_num)
      (fun w hw => False.elim (h ⟨w, hw⟩)) hprojective htarget
    simp only [mul_zero] at hb
    exact (not_le_of_gt hgamma) hb
  obtain ⟨w, hw, hmax⟩ := c.coefficients.support.exists_max_image
    (fun v => |projective v - target v|) hs
  have hb := c.separation_forces_error projective target
    |projective w - target w| gamma (abs_nonneg _) hmax hprojective htarget
  have hn : 0 ≤ c.coefficientNorm := c.coefficientNorm_nonneg
  have hpos : 0 < c.coefficientNorm := by
    by_contra h
    have hz : c.coefficientNorm = 0 := le_antisymm (le_of_not_gt h) hn
    rw [hz, zero_mul] at hb
    exact (not_le_of_gt hgamma) hb
  exact ⟨hpos, w, hw, (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hb)⟩

theorem positive_witness_margin_perturbed_word {n : ℕ}
    (c : FiniteRealWordFunctional n) (target perturbed projective : Word (Fin n) → ℝ)
    {gamma delta : ℝ} (hgamma : 0 < gamma)
    (hprojective : 0 ≤ c.evaluate projective)
    (htarget : c.evaluate target ≤ -gamma)
    (hperturbed : ∀ w ∈ c.coefficients.support, |perturbed w - target w| ≤ delta) :
    ∃ w ∈ c.coefficients.support,
      gamma / c.coefficientNorm - delta ≤ |projective w - perturbed w| := by
  obtain ⟨_, w, hw, hgap⟩ :=
    c.positive_witness_margin_forces_some_word target projective hgamma hprojective htarget
  refine ⟨w, hw, ?_⟩
  have ht := abs_sub_le (projective w) (perturbed w) (target w)
  have hp := hperturbed w hw
  linarith

theorem probability_error_to_projective_bound {n : ℕ}
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target measured projective : Word (Fin n) → ℝ)
    {eta beta : ℝ} (_heta : 0 ≤ eta) (hbeta : 0 ≤ beta)
    (hobserved : ∀ w ∈ c.coefficients.support, |measured w - target w| ≤ eta)
    (hupdate : ∀ w ∈ c.coefficients.support,
      |projective w - measured w| ≤ (w.length : ℝ) * beta)
    (w : Word (Fin n)) (hw : w ∈ c.coefficients.support) :
    |projective w - target w| ≤ eta + L * beta := by
  have hlength : (w.length : ℝ) ≤ L := by
    exact_mod_cast c.coefficient_support_hasHorizon L hL w hw
  calc
    |projective w - target w| ≤
        |projective w - measured w| + |measured w - target w| :=
      abs_sub_le _ _ _
    _ ≤ (w.length : ℝ) * beta + eta := add_le_add (hupdate w hw) (hobserved w hw)
    _ ≤ eta + L * beta := by nlinarith

theorem witness_margin_forces_instrument_error {n : ℕ}
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target measured projective : Word (Fin n) → ℝ)
    {eta beta gamma : ℝ} (heta : 0 ≤ eta) (hbeta : 0 ≤ beta)
    (hobserved : ∀ w ∈ c.coefficients.support, |measured w - target w| ≤ eta)
    (hupdate : ∀ w ∈ c.coefficients.support,
      |projective w - measured w| ≤ (w.length : ℝ) * beta)
    (hprojective : 0 ≤ c.evaluate projective)
    (htarget : c.evaluate target ≤ -gamma) :
    gamma ≤ c.coefficientNorm * (eta + L * beta) := by
  apply c.separation_forces_error projective target (eta + L * beta) gamma
    (add_nonneg heta (mul_nonneg (Nat.cast_nonneg _) hbeta))
    (fun w hw => c.probability_error_to_projective_bound L hL target measured projective
      heta hbeta hobserved hupdate w hw) hprojective htarget

theorem positive_witness_margin_normalized_error {n : ℕ}
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target measured projective : Word (Fin n) → ℝ)
    {eta beta gamma : ℝ} (heta : 0 ≤ eta) (hbeta : 0 ≤ beta) (hgamma : 0 < gamma)
    (hobserved : ∀ w ∈ c.coefficients.support, |measured w - target w| ≤ eta)
    (hupdate : ∀ w ∈ c.coefficients.support,
      |projective w - measured w| ≤ (w.length : ℝ) * beta)
    (hprojective : 0 ≤ c.evaluate projective)
    (htarget : c.evaluate target ≤ -gamma) :
    0 < c.coefficientNorm ∧ gamma / c.coefficientNorm ≤ eta + L * beta := by
  have hbound := c.witness_margin_forces_instrument_error L hL target measured projective
    heta hbeta hobserved hupdate hprojective htarget
  have hn : 0 ≤ c.coefficientNorm := c.coefficientNorm_nonneg
  have hpos : 0 < c.coefficientNorm := by
    by_contra h
    have hz : c.coefficientNorm = 0 := le_antisymm (le_of_not_gt h) hn
    rw [hz, zero_mul] at hbound
    exact (not_le_of_gt hgamma) hbound
  exact ⟨hpos, (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hbound)⟩

end FiniteRealWordFunctional
end AlbertSequential
