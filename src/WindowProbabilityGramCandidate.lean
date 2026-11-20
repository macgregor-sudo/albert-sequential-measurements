/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityHermitianHaar
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! The candidate complex four-column Gram density on native Hermitian matrices. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ENNReal ComplexOrder

/-- Positive definite Hermitian matrices. -/
def complexPositiveDefiniteCone : Set Hermitian3 := {M | M.val.PosDef}

/-- The unnormalized Lebesgue weight of the four-column complex Gram candidate. -/
def complexFourColumnGramWeight (M : Hermitian3) : ℝ :=
  complexPositiveDefiniteCone.indicator (fun H => Real.exp (-H.val.trace.re) * H.val.det.re) M

theorem measurableSet_complexPositiveDefiniteCone : MeasurableSet complexPositiveDefiniteCone := by
  have h : complexPositiveDefiniteCone = Subtype.val ⁻¹'
      ({A : ComplexMatrix3 | 0 ≤ A} ∩ {A | IsUnit A}) := by
    ext M
    change M.val.PosDef ↔ 0 ≤ M.val ∧ IsUnit M.val
    rw [Matrix.nonneg_iff_posSemidef]
    exact ⟨fun h => ⟨h.posSemidef, h.isUnit⟩, fun h => h.1.posDef_iff_isUnit.mpr h.2⟩
  exact h ▸ measurable_subtype_coe ((isClosed_le continuous_const continuous_id).measurableSet.inter
    Units.isOpen.measurableSet)

theorem measurable_complexFourColumnGramWeight : Measurable complexFourColumnGramWeight :=
  (by fun_prop : Continuous (fun M : Hermitian3 =>
    Real.exp (-M.val.trace.re) * M.val.det.re)).measurable.indicator
    measurableSet_complexPositiveDefiniteCone

private theorem trace_re_posDef_eq_sum (M : Hermitian3) (hM : M.val.PosDef) :
    M.val.trace.re = ∑ i, hM.isHermitian.eigenvalues i := by
  rw [hM.isHermitian.trace_eq_sum_eigenvalues]
  simp [Complex.re_sum]

private theorem det_re_posDef_eq_prod (M : Hermitian3) (hM : M.val.PosDef) :
    M.val.det.re = ∏ i, hM.isHermitian.eigenvalues i := by
  have h : M.val.det = (↑(∏ i, hM.isHermitian.eigenvalues i) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact hM.isHermitian.det_eq_prod_eigenvalues
  rw [h, Complex.ofReal_re]

private theorem norm_posDef_le_trace (M : Hermitian3) (hM : M.val.PosDef) : ‖M‖ ≤ M.val.trace.re := by
  have ht : 0 ≤ M.val.trace.re := by
    rw [trace_re_posDef_eq_sum M hM]
    exact Finset.sum_nonneg fun i _ => (hM.eigenvalues_pos i).le
  change ‖M.val‖ ≤ M.val.trace.re
  conv_lhs => rw [hM.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg ht).mpr fun i => ?_
  rw [trace_re_posDef_eq_sum M hM]
  change ‖(hM.isHermitian.eigenvalues i : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_of_nonneg (hM.eigenvalues_pos i).le]
  exact Finset.single_le_sum (fun j _ => (hM.eigenvalues_pos j).le) (Finset.mem_univ i)

private theorem det_re_posDef_le_trace_cube (M : Hermitian3) (hM : M.val.PosDef) :
    M.val.det.re ≤ M.val.trace.re ^ 3 := by
  rw [det_re_posDef_eq_prod M hM, trace_re_posDef_eq_sum M hM]
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => (hM.eigenvalues_pos i).le)
    (fun i _ => Finset.single_le_sum (fun j _ => (hM.eigenvalues_pos j).le) (Finset.mem_univ i))
  simpa using h

/-- On the positive definite cone, the operator norm and determinant are bounded by the trace. -/
theorem complexPositiveDefinite_trace_bounds (M : Hermitian3) (hM : M.val.PosDef) :
    ‖M‖ ≤ M.val.trace.re ∧ M.val.det.re ≤ M.val.trace.re ^ 3 :=
  ⟨norm_posDef_le_trace M hM, det_re_posDef_le_trace_cube M hM⟩

private theorem gram_weight_decay (t a : ℝ) (ha : 0 ≤ a) (ht : a ≤ t) :
    (Real.exp (-t) * t ^ 3) * (1 + a) ^ 10 ≤ (Nat.factorial 13 : ℝ) * Real.exp 1 := by
  have htn := ha.trans ht
  have hf : 0 < (Nat.factorial 13 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1 + t) (by positivity) 13)
  calc
    _ ≤ (Real.exp (-t) * (1 + t) ^ 3) * (1 + t) ^ 10 := by gcongr; linarith
    _ = Real.exp (-t) * (1 + t) ^ 13 := by ring
    _ ≤ Real.exp (-t) * (Real.exp (1 + t) * (Nat.factorial 13 : ℝ)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, show -t + (1 + t) = 1 by ring, mul_comm]

/-- The raw Hermitian density candidate has finite mass for an additive Haar measure. -/
theorem integrable_complexFourColumnGramWeight (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    Integrable complexFourColumnGramWeight μ := by
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  have hi : Integrable (fun H : Hermitian3 => (1 + ‖H‖) ^ (-(10 : ℝ))) μ :=
    integrable_one_add_norm (μ := μ) (by norm_num [hermitian3_finrank])
  let C : ℝ := (Nat.factorial 13 : ℝ) * Real.exp 1
  apply (hi.const_mul C).mono'
  · exact measurable_complexFourColumnGramWeight.aestronglyMeasurable
  apply ae_of_all
  intro H
  by_cases hH : H ∈ complexPositiveDefiniteCone
  · have hpos : H.val.PosDef := hH
    have hd : 0 ≤ H.val.det.re := by
      rw [det_re_posDef_eq_prod H hpos]
      exact Finset.prod_nonneg fun i _ => (hpos.eigenvalues_pos i).le
    rw [complexFourColumnGramWeight, indicator_of_mem hH, Real.norm_of_nonneg
      (mul_nonneg (Real.exp_pos _).le hd), Real.rpow_neg (by positivity),
      show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (det_re_posDef_le_trace_cube H hpos) (Real.exp_pos _).le) (by positivity)).trans ?_
    exact gram_weight_decay H.val.trace.re ‖H‖ (norm_nonneg _) (norm_posDef_le_trace H hpos)
  · rw [complexFourColumnGramWeight, indicator_of_notMem hH, norm_zero]
    positivity

/-- The open operator-norm unit ball about the identity lies in the positive definite cone. -/
theorem ball_one_subset_complexPositiveDefiniteCone :
    Metric.ball (1 : Hermitian3) 1 ⊆ complexPositiveDefiniteCone := by
  intro M hM
  have hn : ‖M.val - 1‖ < 1 := by
    have hn : ‖M - (1 : Hermitian3)‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hM
    change ‖((M - 1 : Hermitian3) : ComplexMatrix3)‖ < 1 at hn
    simpa only [AddSubgroup.coe_sub, selfAdjoint.val_one] using hn
  have hHerm : M.val.IsHermitian := M.property
  apply hHerm.posDef_iff_eigenvalues_pos.mpr
  intro i
  let D := Matrix.diagonal (fun j => (hHerm.eigenvalues j : ℂ))
  let U := hHerm.eigenvectorUnitary
  have he : M.val = (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U) D := hHerm.spectral_theorem
  have hd : ‖D - 1‖ < 1 := by
    rw [he, ← map_one (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U), ← map_sub,
      Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul] at hn
    exact hn
  unfold D at hd
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal] at hd
  have hi := (norm_le_pi_norm (fun j => ((hHerm.eigenvalues j : ℂ) - 1)) i).trans_lt hd
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hi
  linarith [abs_lt.mp hi]

/-- The raw Hermitian density candidate has strictly positive mass. -/
theorem lintegral_complexFourColumnGramWeight_pos (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    0 < ∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂μ := by
  rw [lintegral_pos_iff_support measurable_complexFourColumnGramWeight.ennreal_ofReal]
  have hs : Metric.ball (1 : Hermitian3) 1 ⊆
      Function.support (fun M => ENNReal.ofReal (complexFourColumnGramWeight M)) := by
    intro M hM
    have hP := ball_one_subset_complexPositiveDefiniteCone hM
    have hd : 0 < M.val.det.re := by
      rw [det_re_posDef_eq_prod M hP]
      exact Finset.prod_pos fun i _ => hP.eigenvalues_pos i
    change ENNReal.ofReal (complexFourColumnGramWeight M) ≠ 0
    rw [complexFourColumnGramWeight, indicator_of_mem hP]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) hd)).ne'
  exact (Metric.isOpen_ball.measure_pos μ ⟨1, Metric.mem_ball_self zero_lt_one⟩).trans_le (measure_mono hs)

end AlbertSequential.WindowProbability
