/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramCandidate

/-! The generic complex Gram density candidate at shape parameter `m + 3`. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The unnormalized matrix density in native Hermitian coordinates. -/
def complexGramPowerWeight (m : ℕ) (M : Hermitian3) : ℝ :=
  complexPositiveDefiniteCone.indicator
    (fun H => Real.exp (-H.val.trace.re) * H.val.det.re ^ m) M

theorem measurable_complexGramPowerWeight (m : ℕ) : Measurable (complexGramPowerWeight m) :=
  (by fun_prop : Continuous (fun M : Hermitian3 =>
    Real.exp (-M.val.trace.re) * M.val.det.re ^ m)).measurable.indicator
    measurableSet_complexPositiveDefiniteCone

/-- On the positive cone the determinant's real part equals the positive eigenvalue product. -/
theorem positiveDetRe_of_complexPosDef (M : ComplexMatrix3) (hM : M.PosDef) : 0 < M.det.re := by
  have h : M.det = (↑(∏ i, hM.isHermitian.eigenvalues i) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact hM.isHermitian.det_eq_prod_eigenvalues
  rw [h, Complex.ofReal_re]
  exact Finset.prod_pos fun i _ => hM.eigenvalues_pos i

theorem complexGramPowerWeight_nonneg (m : ℕ) (M : Hermitian3) : 0 ≤ complexGramPowerWeight m M := by
  by_cases hM : M ∈ complexPositiveDefiniteCone
  · rw [complexGramPowerWeight, indicator_of_mem hM]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (positiveDetRe_of_complexPosDef M.val hM).le _)
  · rw [complexGramPowerWeight, indicator_of_notMem hM]

private theorem gram_power_weight_decay (m : ℕ) (t a : ℝ) (ha : 0 ≤ a) (ht : a ≤ t) :
    (Real.exp (-t) * t ^ (3 * m)) * (1 + a) ^ 10 ≤ (Nat.factorial (3 * m + 10) : ℝ) * Real.exp 1 := by
  have htn := ha.trans ht
  have hf : 0 < (Nat.factorial (3 * m + 10) : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1 + t) (by positivity) (3 * m + 10))
  calc
    _ ≤ (Real.exp (-t) * (1 + t) ^ (3 * m)) * (1 + t) ^ 10 := by gcongr; linarith
    _ = Real.exp (-t) * (1 + t) ^ (3 * m + 10) := by rw [pow_add, mul_assoc]
    _ ≤ Real.exp (-t) * (Real.exp (1 + t) * (Nat.factorial (3 * m + 10) : ℝ)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, show -t + (1 + t) = 1 by ring, mul_comm]

/-- Finite mass of every nonnegative determinant power used in the printed law. -/
theorem integrable_complexGramPowerWeight (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    Integrable (complexGramPowerWeight m) μ := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  have hi : Integrable (fun H : Hermitian3 => (1 + ‖H‖) ^ (-(10 : ℝ))) μ :=
    integrable_one_add_norm (μ := μ) (by norm_num [hermitian3_finrank])
  let C : ℝ := (Nat.factorial (3 * m + 10) : ℝ) * Real.exp 1
  apply (hi.const_mul C).mono'
  · exact (measurable_complexGramPowerWeight m).aestronglyMeasurable
  apply ae_of_all
  intro H
  by_cases hH : H ∈ complexPositiveDefiniteCone
  · obtain ⟨ht, hd⟩ := complexPositiveDefinite_trace_bounds H hH
    have hn := (positiveDetRe_of_complexPosDef H.val hH).le
    rw [complexGramPowerWeight, indicator_of_mem hH, Real.norm_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg hn _)), Real.rpow_neg (by positivity),
      show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have hm : H.val.det.re ^ m ≤ H.val.trace.re ^ (3 * m) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ hn hd _
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
      (by positivity)).trans (gram_power_weight_decay m H.val.trace.re ‖H‖ (norm_nonneg _) ht)
  · rw [complexGramPowerWeight, indicator_of_notMem hH, norm_zero]
    positivity

/-- The generic unnormalized weight has positive Haar mass. -/
theorem lintegral_complexGramPowerWeight_pos (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    0 < ∫⁻ M, ENNReal.ofReal (complexGramPowerWeight m M) ∂μ := by
  rw [lintegral_pos_iff_support (measurable_complexGramPowerWeight m).ennreal_ofReal]
  have hs : Metric.ball (1 : Hermitian3) 1 ⊆
      Function.support (fun M => ENNReal.ofReal (complexGramPowerWeight m M)) := by
    intro M hM
    have hP := ball_one_subset_complexPositiveDefiniteCone hM
    change ENNReal.ofReal (complexGramPowerWeight m M) ≠ 0
    rw [complexGramPowerWeight, indicator_of_mem hP]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _)
      (pow_pos (positiveDetRe_of_complexPosDef M.val hP) _))).ne'
  exact (Metric.isOpen_ball.measure_pos μ ⟨1, Metric.mem_ball_self zero_lt_one⟩).trans_le (measure_mono hs)

/-- A determinant ratio reweights the four-column density to any required shape. -/
theorem complexGramPowerWeight_reweight_four (m : ℕ) (M : Hermitian3) :
    complexGramPowerWeight m M = complexFourColumnGramWeight M * (M.val.det.re ^ m / M.val.det.re) := by
  by_cases hM : M ∈ complexPositiveDefiniteCone
  · have hd := (positiveDetRe_of_complexPosDef M.val hM).ne'
    rw [complexGramPowerWeight, indicator_of_mem hM, complexFourColumnGramWeight, indicator_of_mem hM]
    rw [mul_assoc, mul_comm M.val.det.re, div_mul_cancel₀ _ hd]
  · rw [complexGramPowerWeight, indicator_of_notMem hM, complexFourColumnGramWeight,
      indicator_of_notMem hM, zero_mul]

theorem complexGramPowerWeight_one : complexGramPowerWeight 1 = complexFourColumnGramWeight := by
  funext M
  simp [complexGramPowerWeight, complexFourColumnGramWeight, pow_one]

end AlbertSequential.WindowProbability
