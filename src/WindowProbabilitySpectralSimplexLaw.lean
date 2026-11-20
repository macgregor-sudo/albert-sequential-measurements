/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralRawMarginal
public import WindowProbabilitySpectralOrderedRadial

/-! The exact trace-normalized joint eigenvalue density in the ordered chamber. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped ENNReal

/-- The printed fixed-trace weight in the two free ordered simplex coordinates. -/
def fourColumnOrderedSimplexWeight (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fourColumnEigenvalueWeight ![p.1, p.2, 1 - p.1 - p.2])

/-- The true four-column Gram spectrum, normalized by its trace, has exactly
this normalized density on the ordered positive simplex. -/
theorem lintegral_traceNormalizedFourColumnSpectrum_eq_weight (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ M, g (spectrumSimplexProjection (sortedGramSpectrum M)) ∂rawFourColumnHermitianGramLaw) =
      (∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p)⁻¹ *
        ∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p * g p := by
  have hp : Measurable spectrumSimplexProjection := by
    unfold spectrumSimplexProjection
    fun_prop
  have htest : Measurable (fun x => g (spectrumSimplexProjection x)) := hg.comp hp
  rw [lintegral_rawFourColumnSpectrum_eq_weight _ htest]
  have h₀ := fourColumnEigenvalueWeight_orderedSimplex_integral (fun _ => 1) measurable_const
  have h₁ := fourColumnEigenvalueWeight_orderedSimplex_integral g hg
  let Γ := ENNReal.ofReal (Nat.factorial 11 : ℝ)
  let b := ∫⁻ p in orderedEigenvalueSimplex, fourColumnOrderedSimplexWeight p
  have hB : (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x) = Γ * b := by
    simpa only [Γ, b, spectralFourColumnWeight, fourColumnOrderedSimplexWeight, mul_one] using h₀
  change (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x)⁻¹ *
    (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * g (spectrumSimplexProjection x)) = _
  rw [hB]
  change (Γ * b)⁻¹ * (∫⁻ x in spectralPositiveChamber,
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x) * g (spectrumSimplexProjection x)) = _
  rw [h₁]
  have hΓ0 : Γ ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < (Nat.factorial 11 : ℝ))).ne'
  have hΓT : Γ ≠ ∞ := ENNReal.ofReal_ne_top
  change (Γ * b)⁻¹ * (Γ * _) = _
  rw [ENNReal.mul_inv (Or.inl hΓ0) (Or.inl hΓT), mul_comm Γ⁻¹ b⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel_left hΓ0 hΓT]
  rfl

end AlbertSequential.WindowProbability
