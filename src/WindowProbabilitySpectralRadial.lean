/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralDerivative
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! The actual real change of variables from positive eigenvalues to trace and simplex coordinates. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix ENNReal

/-- Interior of the positive orthant for unnormalized eigenvalues. -/
def positiveEigenvalueOrthant : Set (Fin 3 → ℝ) := {x | ∀ i, 0 < x i}

/-- Positive trace and strictly positive simplex coordinates. -/
def traceSimplexRegion : Set (Fin 3 → ℝ) :=
  {u | 0 < u 0 ∧ 0 < u 1 ∧ 0 < u 2 ∧ u 1 + u 2 < 1}

private def traceSimplexExpansion (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  eigenvaluesFromTraceAndSimplex (u 0) (u 1) (u 2)

private theorem trace_traceSimplexExpansion (u : Fin 3 → ℝ) :
    (∑ i, traceSimplexExpansion u i) = u 0 := by
  simp [traceSimplexExpansion, eigenvaluesFromTraceAndSimplex, Fin.sum_univ_three]
  ring

private theorem traceSimplexExpansion_injOn : InjOn traceSimplexExpansion traceSimplexRegion := by
  intro u hu v hv h
  have h0 : u 0 = v 0 := by rw [← trace_traceSimplexExpansion u, ← trace_traceSimplexExpansion v, h]
  have h1 : u 1 = v 1 := by
    have h1 := congrFun h 0
    change u 0 * u 1 = v 0 * v 1 at h1
    rw [← h0] at h1
    exact mul_left_cancel₀ (ne_of_gt hu.1) h1
  have h2 : u 2 = v 2 := by
    have h2 := congrFun h 1
    change u 0 * u 2 = v 0 * v 2 at h2
    rw [← h0] at h2
    exact mul_left_cancel₀ (ne_of_gt hu.1) h2
  funext i
  fin_cases i <;> assumption

private theorem traceSimplexExpansion_image :
    traceSimplexExpansion '' traceSimplexRegion = positiveEigenvalueOrthant := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change ∀ i, 0 < traceSimplexExpansion u i
    intro i
    fin_cases i
    · exact mul_pos hu.1 hu.2.1
    · exact mul_pos hu.1 hu.2.2.1
    · change 0 < u 0 * (1 - u 1 - u 2)
      exact mul_pos hu.1 (by linarith [hu.2.2.2])
  · intro hx
    let r := ∑ i, x i
    have hr : 0 < r := by simpa [r, Fin.sum_univ_three] using add_pos (add_pos (hx 0) (hx 1)) (hx 2)
    let u : Fin 3 → ℝ := ![r, x 0 / r, x 1 / r]
    have hu : u ∈ traceSimplexRegion := by
      change 0 < r ∧ 0 < x 0 / r ∧ 0 < x 1 / r ∧ x 0 / r + x 1 / r < 1
      refine ⟨hr, div_pos (hx 0) hr, div_pos (hx 1) hr, ?_⟩
      rw [← add_div, div_lt_one hr]
      simp only [r, Fin.sum_univ_three]
      linarith [hx 2]
    refine ⟨u, hu, ?_⟩
    funext i
    fin_cases i
    · change r * (x 0 / r) = x 0
      field_simp
    · change r * (x 1 / r) = x 1
      field_simp
    · change r * (1 - x 0 / r - x 1 / r) = x 2
      field_simp
      dsimp [r]
      rw [Fin.sum_univ_three]
      ring

theorem measurableSet_traceSimplexRegion : MeasurableSet traceSimplexRegion := by
  unfold traceSimplexRegion
  exact (isOpen_lt continuous_const (continuous_apply 0)).measurableSet.inter
    ((isOpen_lt continuous_const (continuous_apply 1)).measurableSet.inter
      ((isOpen_lt continuous_const (continuous_apply 2)).measurableSet.inter
        (isOpen_lt ((continuous_apply 1).add (continuous_apply 2)) continuous_const).measurableSet))

/-- Literal Lebesgue change of variables from the positive orthant to trace and simplex coordinates. -/
theorem lintegral_positiveEigenvalueOrthant_traceSimplex (f : (Fin 3 → ℝ) → ℝ≥0∞) :
    (∫⁻ x in positiveEigenvalueOrthant, f x) = ∫⁻ u in traceSimplexRegion,
      ENNReal.ofReal ((u 0)^2) * f (eigenvaluesFromTraceAndSimplex (u 0) (u 1) (u 2)) := by
  let L (u : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    (traceSimplexJacobian (u 0) (u 1) (u 2)).mulVecLin.toContinuousLinearMap
  have hF : Differentiable ℝ traceSimplexExpansion := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [traceSimplexExpansion, eigenvaluesFromTraceAndSimplex] <;> fun_prop
  have hD (u : Fin 3 → ℝ) : HasFDerivAt traceSimplexExpansion (L u) u := by
    have h := (hF u).hasFDerivAt
    have he : fderiv ℝ traceSimplexExpansion u = L u :=
      ContinuousLinearMap.ext (fderiv_eigenvaluesFromTraceAndSimplex u)
    rw [he] at h
    exact h
  have hdet (u : Fin 3 → ℝ) : (L u).det = (u 0) ^ 2 := by
    dsimp [L, ContinuousLinearMap.det]
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin', traceSimplexJacobian_det]
  rw [← traceSimplexExpansion_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_traceSimplexRegion
      (fun u _ => (hD u).hasFDerivWithinAt) traceSimplexExpansion_injOn]
  apply setLIntegral_congr_fun measurableSet_traceSimplexRegion
  intro u _
  dsimp only
  rw [hdet, abs_of_nonneg (sq_nonneg _)]
  rfl

/-- Apply the real change of variables to the exact four-column eigenvalue
weight and separate its radial and simplex integrands. -/
theorem fourColumnEigenvalueWeight_radial_change_variables (φ : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ x in positiveEigenvalueOrthant,
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x) *
        φ (x 0 / (∑ i, x i), x 1 / (∑ i, x i))) =
      ∫⁻ u in traceSimplexRegion,
        ENNReal.ofReal ((u 0) ^ 11 * Real.exp (-(u 0))) *
          (ENNReal.ofReal (fourColumnEigenvalueWeight ![u 1, u 2, 1 - u 1 - u 2]) * φ (u 1, u 2)) := by
  rw [lintegral_positiveEigenvalueOrthant_traceSimplex]
  apply setLIntegral_congr_fun measurableSet_traceSimplexRegion
  intro u hu
  have h0 : traceSimplexExpansion u 0 / u 0 = u 1 := by
    change u 0 * u 1 / u 0 = u 1
    field_simp [ne_of_gt hu.1]
  have h1 : traceSimplexExpansion u 1 / u 0 = u 2 := by
    change u 0 * u 2 / u 0 = u 2
    field_simp [ne_of_gt hu.1]
  dsimp only
  change ENNReal.ofReal ((u 0)^2) *
      (ENNReal.ofReal (Real.exp (-(∑ i, traceSimplexExpansion u i)) *
        fourColumnEigenvalueWeight (traceSimplexExpansion u)) *
        φ (traceSimplexExpansion u 0 / (∑ i, traceSimplexExpansion u i),
          traceSimplexExpansion u 1 / (∑ i, traceSimplexExpansion u i))) = _
  rw [trace_traceSimplexExpansion, h0, h1, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  have hx : (u 0)^2 * (Real.exp (-(u 0)) * fourColumnEigenvalueWeight (traceSimplexExpansion u)) =
      ((u 0)^11 * Real.exp (-(u 0))) * fourColumnEigenvalueWeight ![u 1, u 2, 1 - u 1 - u 2] := by
    rw [show (u 0)^2 * (Real.exp (-(u 0)) * fourColumnEigenvalueWeight (traceSimplexExpansion u)) =
      Real.exp (-(u 0)) * (fourColumnEigenvalueWeight (traceSimplexExpansion u) * (u 0)^2) by ring]
    rw [← traceSimplexJacobian_det (u 0) (u 1) (u 2)]
    change _ * (fourColumnEigenvalueWeight (eigenvaluesFromTraceAndSimplex (u 0) (u 1) (u 2)) * _) = _
    rw [fourColumnEigenvalueWeight_trace_simplex]
    ring
  rw [hx, ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hu.1.le _) (Real.exp_pos _).le), mul_assoc]

/-- The interior of the simplex in the two free coordinates. -/
def positiveEigenvalueSimplex : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

theorem measurableSet_positiveEigenvalueSimplex : MeasurableSet positiveEigenvalueSimplex := by
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
    ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const).measurableSet)

private theorem lintegral_fourColumn_radialGammaIntegral :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^11 * Real.exp (-r))) = ENNReal.ofReal (Nat.factorial 11 : ℝ) := by
  have hi := Real.GammaIntegral_convergent (show (0 : ℝ) < 12 by norm_num)
  rw [show (12 : ℝ) - 1 = (11 : ℕ) by norm_num] at hi
  simp only [Real.rpow_natCast] at hi
  have hInt : IntegrableOn (fun r : ℝ => r^11 * Real.exp (-r)) (Ioi 0) := by
    simpa only [mul_comm] using hi
  have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] (fun r => r^11 * Real.exp (-r)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr
    exact mul_nonneg (pow_nonneg hr.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hn, fourColumn_radialGammaIntegral]

/-- Factor a measurable radial weight and simplex weight over the exact trace-simplex region. -/
theorem lintegral_traceSimplexRegion_product (f : ℝ → ℝ≥0∞) (g : ℝ × ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ u in traceSimplexRegion, f (u 0) * g (u 1, u 2)) =
      (∫⁻ r in Ioi (0 : ℝ), f r) * ∫⁻ p in positiveEigenvalueSimplex, g p := by
  let e₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e₁ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  let e := e₀.trans ((MeasurableEquiv.refl ℝ).prodCongr e₁)
  have he₀ : MeasurePreserving e₀ volume volume := volume_preserving_piFinSuccAbove _ _
  have he₁ : MeasurePreserving e₁ volume volume := volume_preserving_piFinTwo _
  have he : MeasurePreserving e volume (volume.prod volume) := by
    have h := (MeasurePreserving.id (volume : Measure ℝ)).prod he₁
    have he' : MeasurePreserving e volume volume := h.comp he₀
    simpa [Measure.volume_eq_prod] using he'
  have hr : (e ⁻¹' (Ioi 0 ×ˢ positiveEigenvalueSimplex)) = traceSimplexRegion := rfl
  have hk : Measurable (fun p : ℝ × (ℝ × ℝ) => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have ht : (∫⁻ u in traceSimplexRegion, f (u 0) * g (u 1, u 2)) =
      ∫⁻ p in Ioi 0 ×ˢ positiveEigenvalueSimplex, f p.1 * g p.2 ∂(volume.prod volume) := by
    rw [← he.map_eq, setLIntegral_map (measurableSet_Ioi.prod measurableSet_positiveEigenvalueSimplex)
      hk he.measurable, hr]
    rfl
  change (∫⁻ u in traceSimplexRegion, f (u 0) * g (u 1, u 2)) =
    (∫⁻ r in Ioi (0 : ℝ), f r) * ∫⁻ p in positiveEigenvalueSimplex, g p
  rw [ht, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

/-- Normalizing positive eigenvalues by their trace sends their exact
four-column weight to the printed simplex weight, with the radial gamma factor. -/
theorem fourColumnEigenvalueWeight_simplex_integral (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in positiveEigenvalueOrthant,
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x) *
        φ (x 0 / (∑ i, x i), x 1 / (∑ i, x i))) =
      ENNReal.ofReal (Nat.factorial 11 : ℝ) * ∫⁻ p in positiveEigenvalueSimplex,
        ENNReal.ofReal (fourColumnEigenvalueWeight ![p.1, p.2, 1 - p.1 - p.2]) * φ p := by
  rw [fourColumnEigenvalueWeight_radial_change_variables]
  let f := fun r : ℝ => ENNReal.ofReal (r^11 * Real.exp (-r))
  let g := fun p : ℝ × ℝ =>
    ENNReal.ofReal (fourColumnEigenvalueWeight ![p.1, p.2, 1 - p.1 - p.2]) * φ p
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g fourColumnEigenvalueWeight; simp; fun_prop
  change (∫⁻ u in traceSimplexRegion, f (u 0) * g (u 1, u 2)) = _
  rw [lintegral_traceSimplexRegion_product f g hf hg]
  exact congrArg (fun c : ℝ≥0∞ => c * (∫⁻ p in positiveEigenvalueSimplex, g p)) lintegral_fourColumn_radialGammaIntegral

end AlbertSequential.WindowProbability
