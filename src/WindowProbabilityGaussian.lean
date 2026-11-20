/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.MeasuresAndRobustness
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The exact complex Gaussian ensemble and normalization appearing in the
companion, independently of any assertion about the projected Albert measure. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexOrder

/-- One standard complex Gaussian entry. Its real and imaginary parts are
independent real Gaussians of mean zero and variance one half. -/
def standardComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
    Complex.measurableEquivRealProd.symm

instance : IsProbabilityMeasure standardComplexGaussian := by
  unfold standardComplexGaussian
  infer_instance

private theorem gaussianPDF_pair (z : ℂ) :
    gaussianPDF 0 (1 / 2) z.re * gaussianPDF 0 (1 / 2) z.im =
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z)) := by
  simp only [gaussianPDF_def, gaussianPDFReal_def, sub_zero, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat, show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one]
  rw [← ENNReal.ofReal_mul (by positivity), Complex.normSq_apply]
  congr 1
  have hs : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = Real.pi⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
  calc
    _ = ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹) *
        (Real.exp (-(z.re ^ 2)) * Real.exp (-(z.im ^ 2))) := by ring
    _ = _ := by rw [hs, ← Real.exp_add]; congr 2; ring

/-- The density convention is `π⁻¹ exp(−|z|²)` with respect to planar
Lebesgue measure, using Mathlib's isometric real coordinate convention. -/
theorem standardComplexGaussian_eq_withDensity :
    standardComplexGaussian = volume.withDensity
      (fun z => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z))) := by
  let e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have hd := measurable_gaussianPDF 0 (1 / 2 : ℝ≥0)
  ext s hs
  unfold standardComplexGaussian
  rw [Measure.map_apply e.symm.measurable hs, gaussianReal_of_var_ne_zero 0 hv,
    prod_withDensity hd hd, withDensity_apply _ (e.symm.measurable hs), withDensity_apply _ hs]
  rw [← Measure.volume_eq_prod, ← Complex.volume_preserving_equiv_real_prod.map_eq]
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => gaussianPDF 0 (1 / 2) p.1 * gaussianPDF 0 (1 / 2) p.2
  have hg : Measurable g := (hd.comp measurable_fst).mul (hd.comp measurable_snd)
  change (∫⁻ p in e.symm ⁻¹' s, g p ∂((volume : Measure ℂ).map e)) = _
  rw [setLIntegral_map (e.symm.measurable hs) hg e.measurable]
  have hpre : e ⁻¹' (e.symm ⁻¹' s) = s := by ext z; simp
  rw [hpre]
  exact setLIntegral_congr_fun hs (fun z _ => gaussianPDF_pair z)

instance : NullSingletonClass standardComplexGaussian := by
  rw [standardComplexGaussian_eq_withDensity]
  infer_instance

/-- Complex conjugation preserves this exact Gaussian measure, including
the real orientation reversal. -/
theorem map_conj_standardComplexGaussian :
    standardComplexGaussian.map Complex.conjLIE = standardComplexGaussian := by
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hpres := Complex.conjLIE.measurePreserving
  rw [standardComplexGaussian_eq_withDensity]
  change (volume.withDensity f).map Complex.conjLIE = volume.withDensity f
  ext s hs
  rw [Measure.map_apply hpres.measurable hs, withDensity_apply f (hpres.measurable hs),
    withDensity_apply f hs]
  calc
    _ = ∫⁻ y in Complex.conjLIE ⁻¹' s, f y ∂((volume : Measure ℂ).map Complex.conjLIE) := by
      rw [hpres.map_eq]
    _ = _ := by
      rw [setLIntegral_map (hpres.measurable hs) hf hpres.measurable]
      have hpre : Complex.conjLIE ⁻¹' (Complex.conjLIE ⁻¹' s) = s := by ext z; simp
      rw [hpre]
      exact setLIntegral_congr_fun hs (fun z _ => by simp [f, Complex.normSq_conj])

/-- A single complex Gaussian factor in the unnormalized Gram transform. -/
theorem integral_standardComplexGaussian_exp_normSq (a : ℝ) (ha : -1 < a) :
    (∫ z, Real.exp (-a * Complex.normSq z) ∂standardComplexGaussian) = (1 + a)⁻¹ := by
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hfin : ∀ᵐ z ∂(volume : Measure ℂ), f z < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have h : (0 : ℝ) < 1 + a := by linarith
  rw [standardComplexGaussian_eq_withDensity]
  change (∫ z, Real.exp (-a * Complex.normSq z) ∂(volume.withDensity f)) = (1 + a)⁻¹
  rw [integral_withDensity_eq_integral_toReal_smul hf hfin]
  have hfun (z : ℂ) :
      (f z).toReal • Real.exp (-a * Complex.normSq z) =
        Real.pi⁻¹ * Real.exp (-(1 + a) * ‖z‖ ^ (2 : ℝ)) := by
    dsimp [f]
    rw [ENNReal.toReal_ofReal (by positivity), mul_assoc, ← Real.exp_add,
      Real.rpow_two, Complex.sq_norm]
    congr 2
    ring
  simp_rw [hfun, integral_const_mul]
  have hg := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 0) (by norm_num) (by norm_num) h
  have hg' : (∫ z : ℂ, Real.exp (-(1 + a) * ‖z‖ ^ (2 : ℝ))) = Real.pi * (1 + a)⁻¹ := by
    simpa only [Real.rpow_zero, one_mul, zero_add, show (2 : ℝ) / 2 = 1 by norm_num,
      show (-(2 : ℝ)) / 2 = -1 by norm_num, show 2 * Real.pi / 2 = Real.pi by ring,
      Real.Gamma_one, mul_one, Real.rpow_neg_one] using hg
  rw [hg', ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

theorem integrable_standardComplexGaussian_exp_normSq (a : ℝ) (ha : -1 < a) :
    Integrable (fun z => Real.exp (-a * Complex.normSq z)) standardComplexGaussian := by
  by_contra h
  have he := integral_standardComplexGaussian_exp_normSq a ha
  rw [integral_undef h] at he
  exact (inv_ne_zero (show 1 + a ≠ 0 by linarith)) he.symm

/-- All entries of the `3 × k` matrix are independent copies of the specified
complex Gaussian, realized by the two finite product measures. -/
def standardComplexGaussianMatrix (k : ℕ) : Measure (Matrix (Fin 3) (Fin k) ℂ) :=
  Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin k => standardComplexGaussian

instance (k : ℕ) : IsProbabilityMeasure (standardComplexGaussianMatrix k) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin 3 => Measure.pi fun _ : Fin k => standardComplexGaussian) :
      Measure (Fin 3 → Fin k → ℂ))
  infer_instance

/-- Simultaneous entrywise conjugation preserves the exact matrix ensemble. -/
theorem measurePreserving_conj_standardComplexGaussianMatrix (k : ℕ) :
    MeasurePreserving (fun Z : Matrix (Fin 3) (Fin k) ℂ => fun i j => Complex.conjLIE (Z i j))
      (standardComplexGaussianMatrix k) (standardComplexGaussianMatrix k) := by
  have h : MeasurePreserving Complex.conjLIE standardComplexGaussian standardComplexGaussian :=
    ⟨Complex.conjLIE.continuous.measurable, map_conj_standardComplexGaussian⟩
  exact measurePreserving_pi _ _ (fun _ => measurePreserving_pi _ _ (fun _ => h))

/-- Exact Laplace transform for diagonal test matrices against the unnormalized
complex Gaussian Gram law. The real coefficients are free above `-1`. -/
theorem integral_gaussianMatrix_exp_weighted_normSq (k : ℕ) (a : Fin 3 → ℝ)
    (ha : ∀ i, -1 < a i) :
    (∫ Z, Real.exp (-∑ i, a i * ∑ j, Complex.normSq (Z i j))
      ∂standardComplexGaussianMatrix k) = ∏ i, ((1 + a i)⁻¹)^k := by
  change (∫ Z : Fin 3 → Fin k → ℂ,
      Real.exp (-∑ i, a i * ∑ j, Complex.normSq (Z i j))
        ∂(Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin k => standardComplexGaussian)))) = _
  have hrow (i : Fin 3) (z : Fin k → ℂ) :
      Real.exp (-(a i * ∑ j, Complex.normSq (z j))) =
        ∏ j, Real.exp (-(a i) * Complex.normSq (z j)) := by
    rw [← neg_mul, Finset.mul_sum, Real.exp_sum]
  have hfun (Z : Fin 3 → Fin k → ℂ) :
      Real.exp (-∑ i, a i * ∑ j, Complex.normSq (Z i j)) =
        ∏ i, Real.exp (-(a i * ∑ j, Complex.normSq (Z i j))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod
    (fun i (z : Fin k → ℂ) => Real.exp (-(a i * ∑ j, Complex.normSq (z j))))]
  apply Finset.prod_congr rfl
  intro i _
  simp_rw [hrow]
  rw [integral_fintype_prod_eq_pow (fun z => Real.exp (-(a i) * Complex.normSq z)),
    integral_standardComplexGaussian_exp_normSq _ (ha i), Fintype.card_fin]

/-- The complex induced state distribution `ν_{3,k}` in the companion. -/
def inducedComplexStateLaw (k : ℕ) : Measure (ComplexMatrix 3) :=
  normalizedGramPushforward k (standardComplexGaussianMatrix k)

theorem measurable_normalizedComplexGram (k : ℕ) : Measurable (normalizedComplexGram k) := by
  let gram := fun Z : Matrix (Fin 3) (Fin k) ℂ => Z * Z.conjTranspose
  have hgram : Measurable gram := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun Z : Matrix (Fin 3) (Fin k) ℂ => (Z * Z.conjTranspose) i j)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have htrace : Measurable (fun A : ComplexMatrix 3 => A.trace) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  exact (htrace.comp hgram).inv.smul hgram

instance (k : ℕ) : IsProbabilityMeasure (inducedComplexStateLaw k) := by
  unfold inducedComplexStateLaw normalizedGramPushforward
  infer_instance

theorem ae_gaussianMatrix_ne_zero (k : ℕ) (hk : 0 < k) :
    ∀ᵐ Z ∂(standardComplexGaussianMatrix k), Z ≠ 0 := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hset : {Z : Matrix (Fin 3) (Fin k) ℂ | ¬Z ≠ 0} = {0} := by ext; simp
  rw [ae_iff, hset]
  change (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin k => standardComplexGaussian)
    ({0} : Set (Fin 3 → Fin k → ℂ)) = 0
  simp

theorem ae_gaussianGram_trace_ne_zero (k : ℕ) (hk : 0 < k) :
    ∀ᵐ Z ∂(standardComplexGaussianMatrix k), Matrix.trace (Z * Z.conjTranspose) ≠ 0 := by
  filter_upwards [ae_gaussianMatrix_ne_zero k hk] with Z hZ
  exact fun ht => hZ (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp ht)

/-- Rank is preserved by passing to the Gram matrix and normalizing it. -/
theorem rank_normalizedComplexGram (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) :
    (normalizedComplexGram k Z).rank = Z.rank := by
  by_cases hz : Z = 0
  · simp [hz, normalizedComplexGram]
  · have ht : Matrix.trace (Z * Z.conjTranspose) ≠ 0 :=
      fun he => hz (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp he)
    unfold normalizedComplexGram
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero ht)), Matrix.rank_self_mul_conjTranspose]

end AlbertSequential.WindowProbability
