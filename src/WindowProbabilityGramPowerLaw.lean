/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramPowerTilt
public import WindowProbabilityGramLaw

/-! The exact Hermitian Lebesgue density of the generic rectangular Gaussian Gram law. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory ProbabilityTheory Set
open scoped Matrix ENNReal ComplexOrder

local instance : NormedAddCommGroup ComplexMatrix3 :=
  inferInstanceAs (NormedAddCommGroup (Fin 3 → Fin 3 → ℂ))
local instance : NormedSpace ℝ ComplexMatrix3 :=
  inferInstanceAs (NormedSpace ℝ (Fin 3 → Fin 3 → ℂ))
local instance : CompleteSpace ComplexMatrix3 :=
  inferInstanceAs (CompleteSpace (Fin 3 → Fin 3 → ℂ))
local instance : SecondCountableTopology ComplexMatrix3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℂ))
local instance : BorelSpace ComplexMatrix3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℂ))

/-- Normalization of the Hermitian Lebesgue density `exp(-tr X) det(X)^m` on the positive cone. -/
def complexGramPowerDensityMeasure (m : ℕ) (μ : Measure Hermitian3) : Measure Hermitian3 :=
  let w (M : Hermitian3) := ENNReal.ofReal (complexGramPowerWeight m M)
  (∫⁻ M, w M ∂μ)⁻¹ • μ.withDensity w

private theorem complexGramPowerMass_ne_top (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    (∫⁻ M, ENNReal.ofReal (complexGramPowerWeight m M) ∂μ) ≠ ∞ :=
  (integrable_complexGramPowerWeight m μ).lintegral_lt_top.ne

instance (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (complexGramPowerDensityMeasure m μ) where
  measure_univ := by
    unfold complexGramPowerDensityMeasure
    rw [smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ENNReal.inv_mul_cancel (lintegral_complexGramPowerWeight_pos m μ).ne'
      (complexGramPowerMass_ne_top m μ)

private theorem gramPowerWeight_mul_exp_apply (m : ℕ) (H : Hermitian3) (t : ℝ) (M : Hermitian3) :
    complexGramPowerWeight m M * Real.exp (t * (H.val * M.val).trace.re) =
      complexGramPowerTilt m (1 - t • H.val) M := by
  by_cases hM : M ∈ complexPositiveDefiniteCone
  · rw [complexGramPowerWeight, indicator_of_mem hM, complexGramPowerTilt,
      indicator_of_mem hM, sub_mul, one_mul, Matrix.smul_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, mul_right_comm, ← Real.exp_add]
    rw [show -M.val.trace.re + t * (H.val * M.val).trace.re =
      -(M.val.trace.re - t * (H.val * M.val).trace.re) by ring]
  · rw [complexGramPowerWeight, indicator_of_notMem hM, complexGramPowerTilt,
      indicator_of_notMem hM, zero_mul]

/-- Exponential moments of the exact Hermitian density, for every positive test. -/
theorem integral_complexGramPowerDensity (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (H : Hermitian3) (t : ℝ) (hP : ((1 : ComplexMatrix3) - t • H.val).PosDef)
    (hd : 0 < ((1 : ComplexMatrix3) - t • H.val).det.re) :
    (∫ M, Real.exp (t * (H.val * M.val).trace.re) ∂complexGramPowerDensityMeasure m μ) =
      ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ (m + 3))⁻¹ := by
  let f (M : Hermitian3) := Real.exp (t * (H.val * M.val).trace.re)
  let w (M : Hermitian3) := ENNReal.ofReal (complexGramPowerWeight m M)
  have hf : Measurable f := by unfold f; fun_prop
  have hw : Measurable w := (measurable_complexGramPowerWeight m).ennreal_ofReal
  let mass := ∫⁻ M, w M ∂μ
  have hn : mass ≠ 0 := (lintegral_complexGramPowerWeight_pos m μ).ne'
  have hT : mass ≠ ∞ := complexGramPowerMass_ne_top m μ
  change (∫ M, f M ∂(mass⁻¹ • μ.withDensity w)) = _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun M => (Real.exp_pos _).le)
    hf.aestronglyMeasurable, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul μ hw hf.ennreal_ofReal]
  have hrew : (∫⁻ M, (w * fun x => ENNReal.ofReal (f x)) M ∂μ) =
      ∫⁻ M, ENNReal.ofReal (complexGramPowerTilt m (1 - t • H.val) M) ∂μ := by
    apply lintegral_congr
    intro M
    change ENNReal.ofReal (complexGramPowerWeight m M) * ENNReal.ofReal (f M) = _
    rw [← ENNReal.ofReal_mul (complexGramPowerWeight_nonneg m M), gramPowerWeight_mul_exp_apply]
  rw [hrew, lintegral_complexGramPowerTilt_posDef m μ _ hP]
  change (mass⁻¹ * (((ENNReal.ofReal (((1 : ComplexMatrix3) - t • H.val).det.re)) ^ (m + 3))⁻¹ * mass)).toReal = _
  rw [mul_comm (((ENNReal.ofReal (((1 : ComplexMatrix3) - t • H.val).det.re)) ^ (m + 3))⁻¹),
    ENNReal.inv_mul_cancel_left hn hT, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le]

/-- The actual `(m + 3)`-column Gaussian Gram law has the normalized Hermitian determinant-power density. -/
theorem gaussianGram_add_three_eq_powerDensity (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    (standardComplexGaussianMatrix (m + 3)).map
        (fun Z : Matrix (Fin 3) (Fin (m + 3)) ℂ => Z * Z.conjTranspose) =
      (complexGramPowerDensityMeasure m μ).map (Subtype.val : Hermitian3 → ComplexMatrix3) := by
  let gram := fun Z : Matrix (Fin 3) (Fin (m + 3)) ℂ => Z * Z.conjTranspose
  let ν := (standardComplexGaussianMatrix (m + 3)).map gram
  let ρ := (complexGramPowerDensityMeasure m μ).map (Subtype.val : Hermitian3 → ComplexMatrix3)
  have hg : Measurable gram := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have hval : Measurable (Subtype.val : Hermitian3 → ComplexMatrix3) := measurable_subtype_coe
  have : IsProbabilityMeasure ν := by unfold ν; infer_instance
  have : IsProbabilityMeasure ρ := by unfold ρ; infer_instance
  change ν = ρ
  apply measure_eq_of_local_exponential_transforms
  intro L
  obtain ⟨H, hL⟩ := exists_hermitian_test L
  obtain ⟨ε, hε, htest⟩ := exists_gaussian_test_radius_with_pos_det H
  have hExp (t : ℝ) : Measurable (fun M : ComplexMatrix3 => Real.exp (t * L M)) := by
    exact Real.continuous_exp.measurable.comp (L.continuous.measurable.const_mul t)
  have hν (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ M, Real.exp (t * L M) ∂ν) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ (m + 3))⁻¹ := by
    rw [integral_map hg.aemeasurable (hExp t).aestronglyMeasurable]
    refine Eq.trans ?_ (integral_gaussianMatrix_exp_hermitian_trace (m + 3) H.val H.property t (htest t ht).1)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun Z => congrArg (fun x : ℝ => Real.exp (t * x))
      (hL (gram Z) (Matrix.isHermitian_mul_conjTranspose_self Z))
  have hρ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ M, Real.exp (t * L M) ∂ρ) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ (m + 3))⁻¹ := by
    rw [integral_map hval.aemeasurable (hExp t).aestronglyMeasurable]
    refine Eq.trans ?_ (integral_complexGramPowerDensity m μ H t
      (positive_test_of_eigenvalues H t (htest t ht).1) (htest t ht).2)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun M : Hermitian3 =>
      congrArg (fun x : ℝ => Real.exp (t * x)) (hL M.val M.property)
  have hNZ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ (m + 3))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero (m + 3) (htest t ht).2.ne')
  exact ⟨ε, hε,
    fun t ht => Integrable.of_integral_ne_zero (by rw [hν t ht]; exact hNZ t ht),
    fun t ht => Integrable.of_integral_ne_zero (by rw [hρ t ht]; exact hNZ t ht),
    fun t ht => (hν t ht).trans (hρ t ht).symm⟩

end AlbertSequential.WindowProbability
