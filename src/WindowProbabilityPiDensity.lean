/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! Product densities for the chart's real Gaussian coordinate vectors
and the complex Gaussian test columns. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

/-- The finite product of identical nonnegative integrable real densities
has the product density against the corresponding product measure. -/
theorem measure_pi_withDensity_ofReal {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (f : X → ℝ)
    (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x) :
    Measure.pi (fun _ : I => μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      (Measure.pi (fun _ : I => μ)).withDensity (fun z => ENNReal.ofReal (∏ i, f (z i))) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf₀)]
    exact ENNReal.ofReal_lt_top⟩
  change Measure.pi (fun _ : I => ν) = _
  refine Measure.pi_eq (μ := fun _ : I => ν) (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi (i : I) : Integrable f (μ.restrict (s i)) := hf.restrict
  have hpi : Integrable (fun z : I → X => ∏ i, f (z i))
      (Measure.pi fun i : I => μ.restrict (s i)) := Integrable.fintype_prod (f := fun _ => f) hi
  rw [← ofReal_integral_eq_lintegral_ofReal hpi
    (Filter.Eventually.of_forall fun _ => Finset.prod_nonneg fun _ _ => hf₀ _),
    integral_fintype_prod_eq_prod (fun _ => f),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg hf₀)]
  apply Finset.prod_congr rfl
  intro i _
  change ENNReal.ofReal (∫ x in s i, f x ∂μ) = (μ.withDensity fun x => ENNReal.ofReal (f x)) (s i)
  rw [withDensity_apply _ (hs i), ofReal_integral_eq_lintegral_ofReal (hi i)
    (Filter.Eventually.of_forall hf₀)]

/-- The density of a finite real Gaussian vector with independent
mean-zero variance-one-half coordinates. -/
theorem realGaussianVector_eq_withDensity (n : ℕ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 (1 / 2)) =
      volume.withDensity (fun u : Fin n → ℝ =>
        ENNReal.ofReal ((√π)⁻¹ ^ n * exp (-∑ i, (u i)^2))) := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  simp_rw [gaussianReal_of_var_ne_zero 0 hv, gaussianPDF_def]
  rw [measure_pi_withDensity_ofReal volume _ (integrable_gaussianPDFReal _ _)
    (gaussianPDFReal_nonneg _ _)]
  change volume.withDensity _ = volume.withDensity _
  apply congrArg (fun f : (Fin n → ℝ) → ℝ≥0∞ => volume.withDensity f)
  funext u
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    show 2 * π * (1 / 2 : ℝ) = π by ring, show 2 * (1 / 2 : ℝ) = 1 by norm_num,
    div_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← exp_sum, Finset.sum_neg_distrib]

end AlbertSequential.WindowProbability
