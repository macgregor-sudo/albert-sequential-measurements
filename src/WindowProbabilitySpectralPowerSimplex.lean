/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralPowerRadial

/-! The exact trace-normalized joint eigenvalue density in the generic ordered chamber. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped ENNReal

/-- The actual `(m + 3)`-column Gram spectrum, normalized by its trace, has exactly
this normalized density on the ordered positive simplex. -/
theorem lintegral_traceNormalizedPowerSpectrum_eq_weight (m : ℕ) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ M, g (spectrumSimplexProjection (sortedGramSpectrum M)) ∂rawPowerHermitianGramLaw m) =
      (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p)⁻¹ *
        ∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p * g p := by
  have hp : Measurable spectrumSimplexProjection := by
    unfold spectrumSimplexProjection
    fun_prop
  have htest : Measurable (fun x => g (spectrumSimplexProjection x)) := hg.comp hp
  rw [lintegral_rawPowerSpectrum_eq_weight m _ htest]
  have h₀ := spectralPowerWeight_orderedSimplex_integral m (fun _ => 1) measurable_const
  have h₁ := spectralPowerWeight_orderedSimplex_integral m g hg
  let Γ := ENNReal.ofReal (Nat.factorial (3 * m + 8) : ℝ)
  let b := ∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p
  have hB : (∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x) = Γ * b := by
    simpa only [Γ, b, mul_one] using h₀
  change (∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x)⁻¹ *
    (∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x * g (spectrumSimplexProjection x)) = _
  rw [hB]
  rw [h₁]
  have hΓ0 : Γ ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < (Nat.factorial (3 * m + 8) : ℝ))).ne'
  have hΓT : Γ ≠ ∞ := ENNReal.ofReal_ne_top
  change (Γ * b)⁻¹ * (Γ * _) = _
  rw [ENNReal.mul_inv (Or.inl hΓ0) (Or.inl hΓT), mul_comm Γ⁻¹ b⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel_left hΓ0 hΓT]

end AlbertSequential.WindowProbability
