/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralPowerMarginal
public import WindowProbabilitySpectralOrderedRadial

/-! Exact radial integration of the generic homogeneous eigenvalue weight. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter Set MeasureTheory
open scoped ENNReal

/-- Homogeneity of the printed eigenvalue polynomial of the `(m + 3)`-column law. -/
theorem powerEigenvaluePolynomial_dilate (m : ℕ) (r : ℝ) (x : Fin 3 → ℝ) :
    powerEigenvaluePolynomial m (fun i => r * x i) = r ^ (3 * m + 6) * powerEigenvaluePolynomial m x := by
  have hprod : (r * x 0) * (r * x 1) * (r * x 2) = r^3 * (x 0 * x 1 * x 2) := by ring
  have hgap : (r * x 0 - r * x 1)^2 * (r * x 0 - r * x 2)^2 * (r * x 1 - r * x 2)^2 =
      r^6 * ((x 0 - x 1)^2 * (x 0 - x 2)^2 * (x 1 - x 2)^2) := by ring
  unfold powerEigenvaluePolynomial
  simp only
  rw [hprod, hgap, mul_pow (r^3), ← pow_mul, pow_add]
  ring

private theorem lintegral_gamma_monomial (n : ℕ) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^n * Real.exp (-r))) = ENNReal.ofReal (Nat.factorial n : ℝ) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hi := Real.GammaIntegral_convergent hn
  have hG := Real.Gamma_eq_integral hn
  rw [add_sub_cancel_right] at hi hG
  simp only [Real.rpow_natCast] at hi hG
  have hInt : IntegrableOn (fun r : ℝ => r^n * Real.exp (-r)) (Ioi 0) := by
    simpa only [mul_comm] using hi
  have hnon : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] (fun r => r^n * Real.exp (-r)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr
    exact mul_nonneg (pow_nonneg hr.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnon]
  congr 1
  calc
    _ = Real.Gamma ((n : ℝ) + 1) := by simpa only [mul_comm] using hG.symm
    _ = _ := Real.Gamma_nat_eq_factorial n

/-- The generic fixed-trace polynomial weight in the two free coordinates. -/
def powerSimplexWeight (m : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (powerEigenvaluePolynomial m ![p.1, p.2, 1 - p.1 - p.2])

/-- The generic joint weight has the exact Gamma trace factor on the whole simplex. -/
theorem spectralPowerWeight_simplex_integral (m : ℕ) (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in positiveEigenvalueOrthant, spectralPowerWeight m x * φ (spectrumSimplexProjection x)) =
      ENNReal.ofReal (Nat.factorial (3 * m + 8) : ℝ) * ∫⁻ p in positiveEigenvalueSimplex,
        powerSimplexWeight m p * φ p := by
  let f (r : ℝ) := ENNReal.ofReal (r ^ (3 * m + 8) * Real.exp (-r))
  let g (p : ℝ × ℝ) := powerSimplexWeight m p * φ p
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g powerSimplexWeight powerEigenvaluePolynomial; simp; fun_prop
  rw [lintegral_positiveEigenvalueOrthant_traceSimplex]
  have he : (∫⁻ u in traceSimplexRegion,
      ENNReal.ofReal ((u 0)^2) * (spectralPowerWeight m (eigenvaluesFromTraceAndSimplex (u 0) (u 1) (u 2)) *
        φ (spectrumSimplexProjection (eigenvaluesFromTraceAndSimplex (u 0) (u 1) (u 2))))) =
      ∫⁻ u in traceSimplexRegion, f (u 0) * g (u 1, u 2) := by
    apply setLIntegral_congr_fun measurableSet_traceSimplexRegion
    intro u hu
    let r := u 0
    let p : Fin 3 → ℝ := ![u 1, u 2, 1 - u 1 - u 2]
    let x := eigenvaluesFromTraceAndSimplex r (u 1) (u 2)
    have hr : 0 < r := hu.1
    have htrace : (∑ i, x i) = r := by
      simp [x, eigenvaluesFromTraceAndSimplex, Fin.sum_univ_three]
      ring
    have hproj : spectrumSimplexProjection x = (u 1, u 2) := by
      unfold spectrumSimplexProjection
      rw [htrace]
      apply Prod.ext
      · change r * u 1 / r = u 1
        field_simp [hr.ne']
      · change r * u 2 / r = u 2
        field_simp [hr.ne']
    have hd : x = fun i => r * p i := by funext i; fin_cases i <;> rfl
    have hw : r^2 * (Real.exp (-r) * powerEigenvaluePolynomial m x) =
        (r^(3*m+8) * Real.exp (-r)) * powerEigenvaluePolynomial m p := by
      rw [hd, powerEigenvaluePolynomial_dilate, show 3*m+8 = (3*m+6)+2 by omega, pow_add]
      ring
    change ENNReal.ofReal (r^2) * (spectralPowerWeight m x * φ (spectrumSimplexProjection x)) =
      f r * g (u 1, u 2)
    rw [spectralPowerWeight, hproj, htrace, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), hw,
      ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hr.le _) (Real.exp_pos _).le), mul_assoc]
    rfl
  rw [he, lintegral_traceSimplexRegion_product f g hf hg]
  exact congrArg (fun c : ℝ≥0∞ => c * (∫⁻ p in positiveEigenvalueSimplex, g p)) (lintegral_gamma_monomial _)

/-- The generic radial normalization on the actual descending positive chamber. -/
theorem spectralPowerWeight_orderedSimplex_integral (m : ℕ) (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x * φ (spectrumSimplexProjection x)) =
      ENNReal.ofReal (Nat.factorial (3 * m + 8) : ℝ) * ∫⁻ p in orderedEigenvalueSimplex,
        powerSimplexWeight m p * φ p := by
  exact restrict_traceSimplex_integral_to_order _ _ _ (spectralPowerWeight_simplex_integral m) φ hφ

end AlbertSequential.WindowProbability
