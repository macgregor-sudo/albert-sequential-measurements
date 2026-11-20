/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityChartMeasure
public import WindowProbabilityChartTransform
public import WindowProbabilityPiDensity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Coordinate density and change of variables for the native Gamma and
Gaussian chart sample. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory ProbabilityTheory Set Real
open scoped AlbertSequential.WindowProbability ENNReal

/-- Product Lebesgue measure on the open positive ray and the two real
coordinate vectors. -/
def albertChartCoordinateMeasure : Measure AlbertChartSamplingSpace :=
  (volume.restrict (Ioi (0 : ℝ))).prod volume

private theorem gammaMeasure_four_one_eq_restrict :
    gammaMeasure 4 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal ((Gamma 4)⁻¹ * t^3 * exp (-t))) := by
  unfold gammaMeasure
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  refine Filter.Eventually.of_forall fun t => ?_
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [gammaPDF_of_neg h, not_lt.mpr h.le]
  · simp [gammaPDF_eq, show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat]
  · rw [gammaPDF_of_nonneg h.le, indicator_of_mem h]
    simp [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat]

theorem albertChartCoordinateMeasure_ae_positive :
    ∀ᵐ p ∂albertChartCoordinateMeasure, 0 < p.1 := by
  unfold albertChartCoordinateMeasure
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
  simp only [Filter.eventually_const]
  exact ae_restrict_mem measurableSet_Ioi

theorem trace_sampleAlbertChartRay (p : AlbertChartSamplingSpace) (hp : 0 < p.1) :
    albertTrace (sampleAlbertChartRay p) =
      p.1 + (∑ i, (p.2.1 i)^2) + ∑ i, (p.2.2 i)^2 := by
  rw [sampleAlbertChartRay, albertTrace_smul, chartDyad_trace,
    octNormSq_smul, octNormSq_smul, octNormSq_octonionChartCoordinates, octNormSq_octonionChartCoordinates]
  rw [show ((√p.1)⁻¹)^2 = p.1⁻¹ by rw [inv_pow, sq_sqrt hp.le]]
  field_simp [hp.ne']

/-- The sampling law has the exact trace tilt in Gaussian coordinates.
The unscaled chart is recovered by the positive-ray dilation. -/
theorem albertChartSamplingMeasure_eq_withDensity :
    albertChartSamplingMeasure = albertChartCoordinateMeasure.withDensity
      (fun p => ENNReal.ofReal ((π^8 * Gamma 4)⁻¹ * p.1^3 *
        exp (-albertTrace (sampleAlbertChartRay p)))) := by
  let γ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((Gamma 4)⁻¹ * t^3 * exp (-t))
  let g : (Fin 8 → ℝ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal ((√π)⁻¹ ^ 8 * exp (-∑ i, (u i)^2))
  have hγ : Measurable γ := by dsimp [γ]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hgg : Measurable (fun z : (Fin 8 → ℝ) × (Fin 8 → ℝ) => g z.1 * g z.2) :=
    (hg.comp measurable_fst).mul (hg.comp measurable_snd)
  unfold albertChartSamplingMeasure
  rw [realGaussianVector_eq_withDensity, gammaMeasure_four_one_eq_restrict]
  change ((volume.restrict (Ioi (0 : ℝ))).withDensity γ).prod
    ((volume.withDensity g).prod (volume.withDensity g)) = _
  rw [prod_withDensity hg hg, prod_withDensity hγ hgg]
  change albertChartCoordinateMeasure.withDensity (fun p => γ p.1 * (g p.2.1 * g p.2.2)) = _
  apply withDensity_congr_ae
  filter_upwards [albertChartCoordinateMeasure_ae_positive] with p hp
  dsimp only [γ, g]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [trace_sampleAlbertChartRay p hp, neg_add, neg_add, exp_add, exp_add]
  apply congrArg ENNReal.ofReal
  have hπ : (√π)⁻¹ ^ 8 * (√π)⁻¹ ^ 8 = (π ^ 8)⁻¹ := by
    rw [← pow_add, show (8 + 8 : ℕ) = 2 * 8 by decide, pow_mul, inv_pow, sq_sqrt pi_pos.le, inv_pow]
  rw [mul_inv]
  linear_combination (Gamma 4)⁻¹ * p.1^3 * exp (-p.1) *
    exp (-∑ i, (p.2.1 i)^2) * exp (-∑ i, (p.2.2 i)^2) * hπ

/-- Scalar Haar dilation converts the Gaussian-scaled coordinates to the
unscaled affine chart with radial weight of degree eleven. -/
theorem integral_sampleAlbertChartRay_trace_kernel (a b c : ℝ) (x y z : Octonion)
    (hb : 0 < b) (hr : 0 < c - octNormSq z / b) (hs : 0 < schurScalar a b c x y z) :
    (∫ t in Ioi (0 : ℝ), t^3 *
      (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ,
        exp (-tracePairing (schurMatrix a b c x y z) (sampleAlbertChartRay (t, u, w))))) =
      π^8 * Gamma 4 / (albertCubicNorm (schurMatrix a b c x y z))^4 := by
  let F (t : ℝ) (u w : Fin 8 → ℝ) :=
    exp (-tracePairing (schurMatrix a b c x y z) (t • chartDyad
      (octonionChartCoordinates u) (octonionChartCoordinates w)))
  have hdilate {t : ℝ} (ht : 0 < t) (f : (Fin 8 → ℝ) → ℝ) :
      (∫ v, f ((√t)⁻¹ • v)) = t^4 * ∫ v, f v := by
    have hroot : (√t)^8 = t^4 := by
      calc
        _ = ((√t)^2)^4 := pow_mul _ 2 4
        _ = _ := by rw [sq_sqrt ht.le]
    rw [Measure.integral_comp_inv_smul, Module.finrank_fin_fun, hroot,
      abs_of_nonneg (pow_nonneg ht.le _), smul_eq_mul]
  calc
    _ = ∫ t in Ioi (0 : ℝ), t ^ (11 : ℝ) *
        (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ, F t u w) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have he (u w : Fin 8 → ℝ) :
          exp (-tracePairing (schurMatrix a b c x y z) (sampleAlbertChartRay (t, u, w))) =
            F t ((√t)⁻¹ • u) ((√t)⁻¹ • w) := by
        simp [sampleAlbertChartRay, F, map_smul]
      have hu (w : Fin 8 → ℝ) :
          (∫ u, F t ((√t)⁻¹ • u) ((√t)⁻¹ • w)) =
            t^4 * ∫ u, F t u ((√t)⁻¹ • w) := hdilate ht (fun u => F t u ((√t)⁻¹ • w))
      simp_rw [he, hu, integral_const_mul]
      rw [hdilate ht (fun w => ∫ u, F t u w), Real.rpow_ofNat]
      ring
    _ = _ := integral_albertChart_trace_kernel a b c x y z hb hr hs

private theorem integrable_nonnegative_product
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite ν] (f : A × B → ℝ) (hf : Measurable f)
    (hf₀ : ∀ᵐ x ∂μ.prod ν, 0 ≤ f x)
    (h₁ : ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν)
    (h₂ : Integrable (fun x => ∫ y, f (x, y) ∂ν) μ) :
    Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  refine ⟨h₁, h₂.congr ?_⟩
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const hf)] at hf₀
  filter_upwards [hf₀] with x hx
  exact integral_congr_ae (hx.mono fun _ hy => (abs_of_nonneg hy).symm)

private theorem albertChart_gaussian_sections_pos (a b c : ℝ) (x y z : Octonion)
    (hb : 0 < b) (hr : 0 < c - octNormSq z / b) (t : ℝ) (ht : 0 < t) :
    let K := fun (u w : Fin 8 → ℝ) =>
      exp (-tracePairing (schurMatrix a b c x y z) (sampleAlbertChartRay (t, u, w)))
    (∀ w, 0 < ∫ u, K u w) ∧ (0 < ∫ w, ∫ u, K u w) := by
  let e := octonionChartCoordinates
  let q := (√t)⁻¹
  let r := c - octNormSq z / b
  let s := schurScalar a b c x y z
  let uCenter := fun w : Fin 8 → ℝ => e.symm (b⁻¹ • (x + octonionMul z (e w)))
  let wCenter := e.symm (r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x))
  let U := fun u w : Fin 8 → ℝ => exp (-(t * b) * ∑ i, (u i + uCenter w i)^2)
  let V := fun w : Fin 8 → ℝ => exp (-(t * r) * ∑ i, (w i + wCenter i)^2)
  let C := exp (-(t * s))
  have hscl (f : (Fin 8 → ℝ) → ℝ) : (∫ w, f (q • w)) = t^4 * ∫ w, f w := by
    have hroot : (√t)^8 = t^4 := by
      calc
        _ = ((√t)^2)^4 := pow_mul _ 2 4
        _ = _ := by rw [sq_sqrt ht.le]
    dsimp [q]
    rw [Measure.integral_comp_inv_smul, Module.finrank_fin_fun, hroot,
      abs_of_nonneg (pow_nonneg ht.le _), smul_eq_mul]
  have he (u w : Fin 8 → ℝ) :
      exp (-tracePairing (schurMatrix a b c x y z) (sampleAlbertChartRay (t, u, w))) =
        U (q • u) (q • w) * V (q • w) * C := by
    have hu : e (q • u) + b⁻¹ • (x + octonionMul z (e (q • w))) =
        e (q • u + uCenter (q • w)) := by rw [map_add]; simp [uCenter]
    have hw : e (q • w) + r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x) =
        e (q • w + wCenter) := by rw [map_add]; simp [wCenter]
    change exp (-tracePairing (schurMatrix a b c x y z)
      (t • chartDyad (q • e u) (q • e w))) = _
    rw [← map_smul, ← map_smul, tracePairing_smul_right,
      chartDyad_completeSquares a b c x y z (e (q • u)) (e (q • w)) hb.ne' hr.ne']
    change exp (-(t * (b * octNormSq (e (q • u) + b⁻¹ • (x + octonionMul z (e (q • w)))) +
      r * octNormSq (e (q • w) + r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x)) + s))) = _
    rw [hu, hw]
    dsimp only [U, V, C, e]
    rw [octNormSq_octonionChartCoordinates, octNormSq_octonionChartCoordinates,
      ← exp_add, ← exp_add]
    congr 1
    simp only [Pi.add_apply]
    ring
  have hg (w : Fin 8 → ℝ) : (∫ u, U u w) = (π / (t * b))^4 :=
    integral_exp_shifted_normSq 4 (t * b) (mul_pos ht hb) (uCenter w)
  have hv : (∫ w, V w) = (π / (t * r))^4 :=
    integral_exp_shifted_normSq 4 (t * r) (mul_pos ht hr) wCenter
  have hinner (w : Fin 8 → ℝ) :
      (∫ u, exp (-tracePairing (schurMatrix a b c x y z) (sampleAlbertChartRay (t, u, w)))) =
        (t^4 * (π / (t * b))^4) * V (q • w) * C := by
    simp_rw [he, integral_mul_const]
    rw [hscl (fun u => U u (q • w)), hg]
  constructor
  · intro w
    rw [hinner]
    dsimp only [V, C]
    positivity
  · simp_rw [hinner, integral_mul_const, integral_const_mul, hscl V, hv]
    dsimp only [C, r]
    positivity

/-- The unnormalized octonionic sample has a Borel probability law. -/
def albertChartRayMeasure : Measure Albert :=
  albertChartSamplingMeasure.map sampleAlbertChartRay

instance : IsProbabilityMeasure albertChartRayMeasure := by
  unfold albertChartRayMeasure
  infer_instance

/-- The determinant transform of the actual native octonionic rank-one
chart probability. This includes the trace tilt and all convergence
requirements of the probability integral. -/
theorem integral_albertChartRayMeasure_exp_trace (a b c : ℝ) (x y z : Octonion)
    (hb : 0 < b) (hr : 0 < c - octNormSq z / b) (hs : 0 < schurScalar a b c x y z) :
    (∫ X, exp (-(tracePairing (schurMatrix a b c x y z - albertUnit) X))
      ∂albertChartRayMeasure) =
      ((albertCubicNorm (schurMatrix a b c x y z))^4)⁻¹ := by
  let Y := schurMatrix a b c x y z
  let f (p : AlbertChartSamplingSpace) := p.1^3 * exp (-tracePairing Y (sampleAlbertChartRay p))
  let d (p : AlbertChartSamplingSpace) :=
    ENNReal.ofReal ((π^8 * Gamma 4)⁻¹ * p.1^3 * exp (-albertTrace (sampleAlbertChartRay p)))
  have hΓ : 0 < Gamma 4 := Gamma_pos_of_pos (by norm_num)
  have hp (Y : Albert) : Measurable (fun X : Albert => tracePairing Y X) :=
    ((NativeAnalysis.continuous_tracePairing.comp (continuous_const.prodMk continuous_id)).congr
      (fun _ => rfl)).measurable
  have hm : Measurable f := by
    exact (measurable_fst.pow_const 3).mul
      (continuous_exp.measurable.comp ((hp Y).comp measurable_sampleAlbertChartRay).neg)
  have hd : Measurable d := by
    have ht := ((NativeAnalysis.continuous_albertTrace).measurable.comp
      measurable_sampleAlbertChartRay).neg
    exact ((measurable_const.mul (measurable_fst.pow_const 3)).mul
      (continuous_exp.measurable.comp ht)).ennreal_ofReal
  have hden : 0 < albertCubicNorm Y := by
    rw [← schurScalar_cubicNorm a b c x y z hb.ne' hr.ne']
    exact mul_pos (mul_pos hb hr) hs
  have hsections (t : ℝ) (ht : 0 < t) :=
    albertChart_gaussian_sections_pos a b c x y z hb hr t ht
  have hf₀ : ∀ᵐ p ∂albertChartCoordinateMeasure, 0 ≤ f p :=
    albertChartCoordinateMeasure_ae_positive.mono fun _ ht => by dsimp [f]; positivity
  have h2 (t : ℝ) (ht : 0 < t) :
      Integrable (fun v : (Fin 8 → ℝ) × (Fin 8 → ℝ) => f (t, v)) (volume.prod volume) := by
    let F := fun v : (Fin 8 → ℝ) × (Fin 8 → ℝ) => f (t, v.swap)
    have hmm : Measurable F := hm.comp (measurable_prodMk_left.comp measurable_swap)
    have hnonneg (v : (Fin 8 → ℝ) × (Fin 8 → ℝ)) : 0 ≤ F v := by dsimp [F, f]; positivity
    have hf₁ : ∀ᵐ w ∂volume, Integrable (fun u => F (w, u)) := by
      refine Filter.Eventually.of_forall fun w => Integrable.of_integral_ne_zero ?_
      change (∫ u, t^3 * exp (-tracePairing Y (sampleAlbertChartRay (t, u, w)))) ≠ 0
      rw [integral_const_mul]
      exact (mul_pos (pow_pos ht _) ((hsections t ht).1 w)).ne'
    have hf₂ : Integrable (fun w => ∫ u, F (w, u)) := by
      apply Integrable.of_integral_ne_zero
      change (∫ w, ∫ u, t^3 * exp (-tracePairing Y (sampleAlbertChartRay (t, u, w)))) ≠ 0
      simp_rw [integral_const_mul]
      exact (mul_pos (pow_pos ht _) (hsections t ht).2).ne'
    have h := integrable_nonnegative_product volume volume F hmm
      (Filter.Eventually.of_forall hnonneg) hf₁ hf₂
    rw [← (Measure.measurePreserving_swap (μ := volume) (ν := volume)).integrable_comp_emb
      MeasurableEquiv.prodComm.measurableEmbedding]
    exact h
  have hiter :
      (∫ t in Ioi (0 : ℝ), ∫ v : (Fin 8 → ℝ) × (Fin 8 → ℝ), f (t, v)) =
        π^8 * Gamma 4 / (albertCubicNorm Y)^4 := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), t^3 *
          (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ,
            exp (-tracePairing Y (sampleAlbertChartRay (t, u, w)))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (∫ v : (Fin 8 → ℝ) × (Fin 8 → ℝ), f (t, v) ∂(volume.prod volume)) =
          t^3 * (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ,
            exp (-tracePairing Y (sampleAlbertChartRay (t, u, w))))
        rw [integral_prod_symm _ (h2 t ht)]
        simp_rw [f, integral_const_mul]
      _ = _ := integral_sampleAlbertChartRay_trace_kernel a b c x y z hb hr hs
  have hi : Integrable f albertChartCoordinateMeasure := by
    apply integrable_nonnegative_product _ _ f hm hf₀
    · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      exact h2
    · apply Integrable.of_integral_ne_zero
      change (∫ t in Ioi (0 : ℝ), ∫ v : (Fin 8 → ℝ) × (Fin 8 → ℝ), f (t, v)) ≠ 0
      rw [hiter]
      positivity
  have hmExp : Measurable (fun X : Albert => exp (-tracePairing (Y - albertUnit) X)) :=
    continuous_exp.measurable.comp (hp (Y - albertUnit)).neg
  change (∫ X, exp (-tracePairing (Y - albertUnit) X) ∂albertChartRayMeasure) = _
  rw [albertChartRayMeasure, integral_map measurable_sampleAlbertChartRay.aemeasurable
    hmExp.aestronglyMeasurable, albertChartSamplingMeasure_eq_withDensity]
  change (∫ p, exp (-tracePairing (Y - albertUnit) (sampleAlbertChartRay p))
    ∂albertChartCoordinateMeasure.withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ p, ((π^8 * Gamma 4)⁻¹) * f p ∂albertChartCoordinateMeasure := by
      apply integral_congr_ae
      filter_upwards [albertChartCoordinateMeasure_ae_positive] with p htp
      dsimp only [d, f]
      rw [ENNReal.toReal_ofReal (by positivity), tracePairing_sub_left,
        tracePairing_comm albertUnit, NativeAnalysis.tracePairing_unit_right, smul_eq_mul,
        mul_assoc, mul_assoc, ← exp_add]
      congr 3
      ring
    _ = _ := by
      rw [integral_const_mul, albertChartCoordinateMeasure, integral_prod _ hi]
      change (π^8 * Gamma 4)⁻¹ *
        (∫ t in Ioi (0 : ℝ), ∫ v : (Fin 8 → ℝ) × (Fin 8 → ℝ), f (t, v)) = _
      rw [hiter, div_eq_mul_inv, inv_mul_cancel_left₀ (show π^8 * Gamma 4 ≠ 0 by positivity)]

end AlbertSequential.WindowProbability
