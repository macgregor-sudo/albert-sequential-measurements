/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramPowerLaw
public import WindowProbabilitySpectralRawMarginal

/-! Reweight the verified four-column Weyl integral by a determinant power. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The literal native Hermitian Gram matrix of an `(m + 3)`-column draw. -/
def rawPowerHermitianGram (m : ℕ) (Z : Matrix (Fin 3) (Fin (m + 3)) ℂ) : Hermitian3 :=
  ⟨Z * Z.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self Z⟩

def rawPowerHermitianGramLaw (m : ℕ) : Measure Hermitian3 :=
  (standardComplexGaussianMatrix (m + 3)).map (rawPowerHermitianGram m)

theorem measurable_rawPowerHermitianGram (m : ℕ) : Measurable (rawPowerHermitianGram m) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  fun_prop

theorem rawPowerHermitianGramLaw_eq_density (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    rawPowerHermitianGramLaw m = complexGramPowerDensityMeasure m μ := by
  have hc : IsClosed (selfAdjoint ComplexMatrix3 : Set ComplexMatrix3) := by
    change IsClosed {M : ComplexMatrix3 | star M = M}
    exact isClosed_eq continuous_star continuous_id
  apply (MeasurableEmbedding.subtype_coe hc.measurableSet).map_injective
  have hg : Measurable (Subtype.val : Hermitian3 → ComplexMatrix3) := measurable_subtype_coe
  exact (Measure.map_map hg (measurable_rawPowerHermitianGram m)).trans
    (gaussianGram_add_three_eq_powerDensity m μ)

/-- The real determinant is the product of the three actual descending eigenvalues. -/
theorem det_re_eq_prod_sortedGramSpectrum (M : Hermitian3) : M.val.det.re = ∏ i, sortedGramSpectrum M i := by
  let h : M.val.IsHermitian := M.property
  have hdet : M.val.det = (↑(∏ i, h.eigenvalues i) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact h.det_eq_prod_eigenvalues
  rw [hdet, Complex.ofReal_re]
  let e : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := (Fintype.equivOfCardEq (Fintype.card_fin 3)).symm
  let e' : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := finCongr (Fintype.card_fin 3).symm
  have he := Fintype.prod_equiv (e.trans e'.symm) h.eigenvalues (sortedGramSpectrum M)
  apply he
  intro i
  change h.eigenvalues₀ (e i) = h.eigenvalues₀ (e' (e'.symm (e i)))
  rw [Equiv.apply_symm_apply]

/-- The nonnegative Radon–Nikodym weight from the four-column Gram density. -/
def gramPowerDetRatio (m : ℕ) (M : Hermitian3) : ℝ≥0∞ :=
  ENNReal.ofReal (M.val.det.re ^ m / M.val.det.re)

private theorem measurable_gramPowerDetRatio (m : ℕ) : Measurable (gramPowerDetRatio m) := by
  unfold gramPowerDetRatio
  have h : Continuous (fun M : Hermitian3 => M.val.det.re) := by fun_prop
  exact ((h.measurable.pow_const m).div h.measurable).ennreal_ofReal

/-- The law for any admissible column count is an exact reweighting of the four-column measure. -/
theorem rawPowerHermitianGramLaw_reweight_four (m : ℕ) :
    ∃ C : ℝ≥0∞, rawPowerHermitianGramLaw m = C • rawFourColumnHermitianGramLaw.withDensity (gramPowerDetRatio m) := by
  let μ := spectralHermitianVolume
  let w₁ (M : Hermitian3) := ENNReal.ofReal (complexFourColumnGramWeight M)
  let wₘ (M : Hermitian3) := ENNReal.ofReal (complexGramPowerWeight m M)
  let a := ∫⁻ M, w₁ M ∂μ
  let b := ∫⁻ M, wₘ M ∂μ
  let r := gramPowerDetRatio m
  have ha₀ : a ≠ 0 := (lintegral_complexFourColumnGramWeight_pos μ).ne'
  have haTop : a ≠ ∞ := (integrable_complexFourColumnGramWeight μ).lintegral_lt_top.ne
  have hw : wₘ = w₁ * r := by
    funext M
    change ENNReal.ofReal (complexGramPowerWeight m M) = ENNReal.ofReal (complexFourColumnGramWeight M) * r M
    have hn : 0 ≤ complexFourColumnGramWeight M := complexGramPowerWeight_one ▸ complexGramPowerWeight_nonneg 1 M
    rw [complexGramPowerWeight_reweight_four, ENNReal.ofReal_mul hn]
    rfl
  have hμ : a • complexFourColumnGramDensityMeasure μ = μ.withDensity w₁ := by
    change a • (a⁻¹ • μ.withDensity w₁) = _
    rw [smul_smul, ENNReal.mul_inv_cancel ha₀ haTop, one_smul]
  refine ⟨b⁻¹ * a, ?_⟩
  rw [rawPowerHermitianGramLaw_eq_density m μ, rawFourColumnHermitianGramLaw_eq_density μ]
  change b⁻¹ • μ.withDensity wₘ = (b⁻¹ * a) • (complexFourColumnGramDensityMeasure μ).withDensity r
  rw [hw, withDensity_mul μ measurable_complexFourColumnGramWeight.ennreal_ofReal (measurable_gramPowerDetRatio m),
    ← hμ, withDensity_smul_measure, smul_smul]

theorem rawPowerHermitianGramLaw_absolutelyContinuous_four (m : ℕ) :
    rawPowerHermitianGramLaw m ≪ rawFourColumnHermitianGramLaw := by
  obtain ⟨C, h⟩ := rawPowerHermitianGramLaw_reweight_four m
  rw [h]
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

/-- The general unnormalized positive eigenvalue weight in the printed law. -/
def powerEigenvaluePolynomial (m : ℕ) (x : Fin 3 → ℝ) : ℝ :=
  (x 0 * x 1 * x 2) ^ m * ((x 0 - x 1)^2 * (x 0 - x 2)^2 * (x 1 - x 2)^2)

def spectralPowerWeight (m : ℕ) (x : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ i, x i)) * powerEigenvaluePolynomial m x)

private def eigenvaluePowerRatio (m : ℕ) (x : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ i, x i) ^ m / ∏ i, x i)

private theorem measurable_eigenvaluePowerRatio (m : ℕ) : Measurable (eigenvaluePowerRatio m) := by
  unfold eigenvaluePowerRatio
  have h : Continuous (fun x : Fin 3 → ℝ => ∏ i, x i) := by fun_prop
  exact ((h.measurable.pow_const m).div h.measurable).ennreal_ofReal

private theorem spectralFourColumnWeight_mul_ratio (m : ℕ) (x : Fin 3 → ℝ) (hx : x ∈ spectralPositiveChamber) :
    spectralFourColumnWeight x * eigenvaluePowerRatio m x = spectralPowerWeight m x := by
  let t := x 0 * x 1 * x 2
  let v := (x 0 - x 1)^2 * (x 0 - x 2)^2 * (x 1 - x 2)^2
  have ht : 0 < t := mul_pos (mul_pos (hx.2 0) (hx.2 1)) (hx.2 2)
  have hv : 0 ≤ v := by unfold v; positivity
  unfold spectralFourColumnWeight spectralPowerWeight powerEigenvaluePolynomial eigenvaluePowerRatio fourColumnEigenvalueWeight
  rw [Fin.prod_univ_three]
  change ENNReal.ofReal (Real.exp (-(∑ i, x i)) * (t * v)) * ENNReal.ofReal (t^m / t) =
    ENNReal.ofReal (Real.exp (-(∑ i, x i)) * (t^m * v))
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (mul_nonneg ht.le hv))]
  congr 1
  calc
    _ = Real.exp (-(∑ i, x i)) * ((t^m / t * t) * v) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ ht.ne']

/-- The raw `(m + 3)`-column Gram law has the exact weighted ordered spectrum. -/
theorem lintegral_rawPowerSpectrum_eq_weight (m : ℕ) (g : (Fin 3 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ M, g (sortedGramSpectrum M) ∂rawPowerHermitianGramLaw m) =
      (∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x)⁻¹ *
        ∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x * g x := by
  obtain ⟨C, hC⟩ := rawPowerHermitianGramLaw_reweight_four m
  let a := ∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x
  let b := ∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x
  have hprod (f : (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ M, f (sortedGramSpectrum M) ∂rawPowerHermitianGramLaw m) =
        (C * a⁻¹) * ∫⁻ x in spectralPositiveChamber, spectralPowerWeight m x * f x := by
    rw [hC, lintegral_smul_measure, smul_eq_mul, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_gramPowerDetRatio m) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have he : (∫⁻ M, (gramPowerDetRatio m * fun N => f (sortedGramSpectrum N)) M ∂rawFourColumnHermitianGramLaw) =
        ∫⁻ M, eigenvaluePowerRatio m (sortedGramSpectrum M) * f (sortedGramSpectrum M)
          ∂rawFourColumnHermitianGramLaw := by
      apply lintegral_congr
      intro M
      change ENNReal.ofReal (M.val.det.re ^ m / M.val.det.re) * f (sortedGramSpectrum M) = _
      rw [det_re_eq_prod_sortedGramSpectrum]
      rfl
    have htest : Measurable (fun x => eigenvaluePowerRatio m x * f x) := (measurable_eigenvaluePowerRatio m).mul hf
    rw [he, lintegral_rawFourColumnSpectrum_eq_weight _ htest]
    change C * (a⁻¹ * _) = _
    rw [← mul_assoc]
    congr 1
    apply setLIntegral_congr_fun isOpen_spectralPositiveChamber.measurableSet
    intro x hx
    change spectralFourColumnWeight x * (eigenvaluePowerRatio m x * f x) = _
    rw [← mul_assoc, spectralFourColumnWeight_mul_ratio m x hx]
  have hprob : IsProbabilityMeasure (rawPowerHermitianGramLaw m) := by
    rw [rawPowerHermitianGramLaw_eq_density m spectralHermitianVolume]
    infer_instance
  have hOne : 1 = (C * a⁻¹) * b := by simpa [b] using hprod (fun _ => 1) measurable_const
  have hb₀ : b ≠ 0 := by intro h; rw [h, mul_zero] at hOne; exact one_ne_zero hOne
  have hbTop : b ≠ ∞ := by
    intro h
    by_cases hc : C * a⁻¹ = 0
    · rw [hc, zero_mul] at hOne
      exact one_ne_zero hOne
    · rw [h, ENNReal.mul_top hc] at hOne
      exact ENNReal.one_ne_top hOne
  have hc : C * a⁻¹ = b⁻¹ := by
    calc
      _ = (C * a⁻¹) * b * b⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hb₀ hbTop, mul_one]
      _ = _ := by rw [← hOne, one_mul]
  rw [hprod g hg, hc]

end AlbertSequential.WindowProbability
