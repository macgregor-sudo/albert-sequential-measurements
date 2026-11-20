/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramTilt
public import WindowProbabilityAlbertWindowLaw

/-! The Hermitian Lebesgue density of the actual unnormalized four-column Gram law. -/

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

/-- Normalization of the Hermitian Lebesgue density `exp(-tr X) det X` on the positive cone. -/
def complexFourColumnGramDensityMeasure (μ : Measure Hermitian3) : Measure Hermitian3 :=
  let w (M : Hermitian3) := ENNReal.ofReal (complexFourColumnGramWeight M)
  (∫⁻ M, w M ∂μ)⁻¹ • μ.withDensity w

private theorem complexFourColumnGramWeight_nonneg (M : Hermitian3) :
    0 ≤ complexFourColumnGramWeight M := by
  by_cases hM : M ∈ complexPositiveDefiniteCone
  · have hP : M.val.PosDef := hM
    have hd : 0 ≤ M.val.det.re := (Complex.le_def.mp hP.posSemidef.det_nonneg).1
    rw [complexFourColumnGramWeight, indicator_of_mem hM]
    exact mul_nonneg (Real.exp_pos _).le hd
  · rw [complexFourColumnGramWeight, indicator_of_notMem hM]

private theorem complexFourColumnGramMass_ne_top (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    (∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂μ) ≠ ∞ :=
  (integrable_complexFourColumnGramWeight μ).lintegral_lt_top.ne

instance (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (complexFourColumnGramDensityMeasure μ) where
  measure_univ := by
    unfold complexFourColumnGramDensityMeasure
    rw [smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ENNReal.inv_mul_cancel (lintegral_complexFourColumnGramWeight_pos μ).ne'
      (complexFourColumnGramMass_ne_top μ)

private theorem gramWeight_mul_exp_apply (H : Hermitian3) (t : ℝ) (M : Hermitian3) :
    complexFourColumnGramWeight M * Real.exp (t * (H.val * M.val).trace.re) =
      complexFourColumnGramTilt (1 - t • H.val) M := by
  by_cases hM : M ∈ complexPositiveDefiniteCone
  · rw [complexFourColumnGramWeight, indicator_of_mem hM, complexFourColumnGramTilt,
      indicator_of_mem hM, sub_mul, one_mul, Matrix.smul_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, mul_right_comm, ← Real.exp_add]
    rw [show -M.val.trace.re + t * (H.val * M.val).trace.re =
      -(M.val.trace.re - t * (H.val * M.val).trace.re) by ring]
  · rw [complexFourColumnGramWeight, indicator_of_notMem hM, complexFourColumnGramTilt,
      indicator_of_notMem hM, zero_mul]

/-- The Gaussian spectral scale condition gives a positive definite exponential test matrix. -/
theorem positive_test_of_eigenvalues (H : Hermitian3) (t : ℝ)
    (ht : ∀ i, t * (show H.val.IsHermitian from H.property).eigenvalues i < 1) :
    ((1 : ComplexMatrix3) - t • H.val).PosDef := by
  let hH : H.val.IsHermitian := H.property
  let U := hH.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ ComplexMatrix3 U
  let D : ComplexMatrix3 := Matrix.diagonal fun i => (hH.eigenvalues i : ℂ)
  have hE : H.val = C D := hH.spectral_theorem
  have hsmul (M : ComplexMatrix3) : t • M = (t : ℂ) • M := by
    ext i j
    simp [Complex.real_smul]
  have he : (1 : ComplexMatrix3) - t • H.val = C (1 - t • D) := by
    rw [map_sub, map_one, hsmul D, map_smul, ← hE, hsmul H.val]
  rw [he, Unitary.conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
  have hdiag : (1 : ComplexMatrix3) - t • D =
      Matrix.diagonal (fun i => ((1 - t * hH.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Complex.real_smul]
    · simp [D, hij]
  rw [hdiag, Matrix.posDef_diagonal_iff]
  exact fun i => Complex.zero_lt_real.mpr (sub_pos.mpr (ht i))

/-- Exponential moments of the exact Hermitian density, for every positive test. -/
theorem integral_complexFourColumnGramDensity (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (H : Hermitian3) (t : ℝ) (hP : ((1 : ComplexMatrix3) - t • H.val).PosDef)
    (hd : 0 < ((1 : ComplexMatrix3) - t • H.val).det.re) :
    (∫ M, Real.exp (t * (H.val * M.val).trace.re) ∂complexFourColumnGramDensityMeasure μ) =
      ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ 4)⁻¹ := by
  let f (M : Hermitian3) := Real.exp (t * (H.val * M.val).trace.re)
  let w (M : Hermitian3) := ENNReal.ofReal (complexFourColumnGramWeight M)
  have hf : Measurable f := by unfold f; fun_prop
  have hw : Measurable w := measurable_complexFourColumnGramWeight.ennreal_ofReal
  let mass := ∫⁻ M, w M ∂μ
  have hn : mass ≠ 0 := (lintegral_complexFourColumnGramWeight_pos μ).ne'
  have hT : mass ≠ ∞ := complexFourColumnGramMass_ne_top μ
  change (∫ M, f M ∂(mass⁻¹ • μ.withDensity w)) = _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun M => (Real.exp_pos _).le)
    hf.aestronglyMeasurable, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul μ hw hf.ennreal_ofReal]
  have hrew : (∫⁻ M, (w * fun x => ENNReal.ofReal (f x)) M ∂μ) =
      ∫⁻ M, ENNReal.ofReal (complexFourColumnGramTilt (1 - t • H.val) M) ∂μ := by
    apply lintegral_congr
    intro M
    change ENNReal.ofReal (complexFourColumnGramWeight M) * ENNReal.ofReal (f M) = _
    rw [← ENNReal.ofReal_mul (complexFourColumnGramWeight_nonneg M), gramWeight_mul_exp_apply]
  rw [hrew, lintegral_complexFourColumnGramTilt_posDef μ _ hP]
  change (mass⁻¹ * (((ENNReal.ofReal (((1 : ComplexMatrix3) - t • H.val).det.re)) ^ 4)⁻¹ * mass)).toReal = _
  rw [mul_comm (((ENNReal.ofReal (((1 : ComplexMatrix3) - t • H.val).det.re)) ^ 4)⁻¹),
    ENNReal.inv_mul_cancel_left hn hT, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le]

/-- The unnormalized four-column complex Gaussian Gram law has the actual Hermitian Lebesgue density. -/
theorem fourColumnGaussianGram_eq_density (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    (standardComplexGaussianMatrix 4).map
        (fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose) =
      (complexFourColumnGramDensityMeasure μ).map (Subtype.val : Hermitian3 → ComplexMatrix3) := by
  let gram := fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose
  let ν := (standardComplexGaussianMatrix 4).map gram
  let ρ := (complexFourColumnGramDensityMeasure μ).map (Subtype.val : Hermitian3 → ComplexMatrix3)
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
      (∫ M, Real.exp (t * L M) ∂ν) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ 4)⁻¹ := by
    rw [integral_map hg.aemeasurable (hExp t).aestronglyMeasurable]
    refine Eq.trans ?_ (integral_gaussianMatrix_exp_hermitian_trace 4 H.val H.property t (htest t ht).1)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun Z => congrArg (fun x : ℝ => Real.exp (t * x))
      (hL (gram Z) (Matrix.isHermitian_mul_conjTranspose_self Z))
  have hρ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ M, Real.exp (t * L M) ∂ρ) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ 4)⁻¹ := by
    rw [integral_map hval.aemeasurable (hExp t).aestronglyMeasurable]
    refine Eq.trans ?_ (integral_complexFourColumnGramDensity μ H t
      (positive_test_of_eigenvalues H t (htest t ht).1) (htest t ht).2)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun M : Hermitian3 =>
      congrArg (fun x : ℝ => Real.exp (t * x)) (hL M.val M.property)
  have hNZ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ 4)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero 4 (htest t ht).2.ne')
  exact ⟨ε, hε,
    fun t ht => Integrable.of_integral_ne_zero (by rw [hν t ht]; exact hNZ t ht),
    fun t ht => Integrable.of_integral_ne_zero (by rw [hρ t ht]; exact hNZ t ht),
    fun t ht => (hν t ht).trans (hρ t ht).symm⟩

end AlbertSequential.WindowProbability
