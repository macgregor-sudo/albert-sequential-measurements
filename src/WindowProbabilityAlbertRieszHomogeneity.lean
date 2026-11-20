/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityAlbertRiesz

/-! Uniqueness by a genuine finite tilt, and positive scalar homogeneity of the native Riesz measure. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory NativeAnalysis ProbabilityTheory Real Set
open scoped AlbertSequential.WindowProbability ENNReal Topology

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : CompleteSpace Octonion :=
  inferInstanceAs (CompleteSpace (Quaternion ℝ × Quaternion ℝ))
local instance : SecondCountableTopology Octonion :=
  inferInstanceAs (SecondCountableTopology (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : CompleteSpace Albert :=
  inferInstanceAs (CompleteSpace ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : SecondCountableTopology Albert :=
  inferInstanceAs (SecondCountableTopology ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem albertUnit_mem_openCone : albertUnit ∈ albertOpenPositiveCone := by
  apply (albertStrictPositive_mem_openCone _).mp
  apply (albertStrictPositive_iff_atoms _).mpr
  intro p hp
  rw [tracePairing_comm, tracePairing_unit_right, hp.2]
  exact zero_lt_one

theorem smul_mem_albertOpenPositiveCone {Y : Albert} (hY : Y ∈ albertOpenPositiveCone) {r : ℝ} (hr : 0 < r) :
    r • Y ∈ albertOpenPositiveCone := by
  apply (albertStrictPositive_mem_openCone _).mp
  apply (albertStrictPositive_iff_atoms _).mpr
  intro p hp
  rw [tracePairing_smul_left]
  exact mul_pos hr ((albertStrictPositive_iff_atoms _).mp ((albertStrictPositive_mem_openCone _).mpr hY) p hp)

/-- The closed cone of the native rank-three model is literally the square cone. -/
theorem closure_albertOpenPositiveCone :
    closure albertOpenPositiveCone = {X : Albert | IsPositive X} := by
  have hClosed : IsClosed {X : Albert | IsPositive X} := by
    have he : {X : Albert | IsPositive X} =
        ⋂ y : Albert, {X : Albert | 0 ≤ tracePairing X (jordanMul y y)} := by
      ext X
      simpa only [mem_ofPred_eq, mem_iInter] using isPositive_iff_dual_squares X
    rw [he]
    apply isClosed_iInter
    intro y
    have h : Continuous (fun X : Albert => tracePairing X (jordanMul y y)) :=
      (continuous_albertPairing_fixed (jordanMul y y)).congr (fun X => tracePairing_comm _ X)
    exact (isClosed_Ici : IsClosed (Ici (0 : ℝ))).preimage h
  apply Subset.antisymm (closure_minimal interior_subset hClosed)
  intro X hX
  change IsPositive X at hX
  let f (t : ℝ) := X + t • albertUnit
  have hf : Continuous f := (continuous_const : Continuous (fun _ : ℝ => X)).add
    (continuous_id.smul continuous_const)
  have ht : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 X) := by
    have h : Tendsto f (𝓝 (0 : ℝ)) (𝓝 (f 0)) := hf.continuousAt
    simpa only [f, zero_smul, add_zero] using
      h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  apply (albertStrictPositive_mem_openCone _).mp
  exact ⟨t, ht, by simpa only [f, add_sub_cancel_right] using hX⟩

theorem ae_albertRankOneRiesz_mem_closedCone :
    ∀ᵐ X ∂albertRankOneRiesz, X ∈ closure albertOpenPositiveCone := by
  rw [closure_albertOpenPositiveCone]
  exact ae_albertRankOneRiesz_positive

private def traceTilt (μ : Measure Albert) : Measure Albert :=
  μ.withDensity (fun X => ENNReal.ofReal (exp (-albertTrace X)))

private theorem traceTilt_injective : Function.Injective traceTilt := by
  have hn : Measurable (fun X => ENNReal.ofReal (exp (-albertTrace X))) := by
    simpa only [neg_one_mul] using measurable_albertTraceExp (-1)
  have hp : Measurable (fun X => ENNReal.ofReal (exp (albertTrace X))) := by
    simpa only [one_mul] using measurable_albertTraceExp 1
  have hw : (fun X => ENNReal.ofReal (exp (-albertTrace X))) *
      (fun X => ENNReal.ofReal (exp (albertTrace X))) = 1 := by
    funext X
    change ENNReal.ofReal (exp (-albertTrace X)) * ENNReal.ofReal (exp (albertTrace X)) = 1
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, neg_add_cancel, exp_zero, ENNReal.ofReal_one]
  intro μ ν h
  have hs (ξ : Measure Albert) :
      ((traceTilt ξ).withDensity (fun X => ENNReal.ofReal (exp (albertTrace X)))) = ξ := by
    unfold traceTilt
    rw [← withDensity_mul _ hn hp, hw, withDensity_one]
  rw [← hs μ, ← hs ν, h]

private theorem traceTilt_finite (μ : Measure Albert)
    (h : Integrable (fun X => exp (-(tracePairing albertUnit X))) μ) :
    IsFiniteMeasure (traceTilt μ) := by
  have ht : Integrable (fun X => exp (-albertTrace X)) μ := by
    simpa only [tracePairing_comm albertUnit, tracePairing_unit_right] using h
  refine ⟨?_⟩
  rw [traceTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall fun _ => (exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

private theorem integral_traceTilt_exp (μ : Measure Albert) (D : Albert) (t : ℝ) :
    (∫ X, exp (t * tracePairing D X) ∂traceTilt μ) =
      (∫ X, exp (-(tracePairing (albertUnit - t • D) X)) ∂μ) := by
  have hn : Measurable (fun X => ENNReal.ofReal (exp (-albertTrace X))) := by
    simpa only [neg_one_mul] using measurable_albertTraceExp (-1)
  unfold traceTilt
  rw [integral_withDensity_eq_integral_toReal_smul hn (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with X
  rw [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul, ← exp_add, tracePairing_sub_left,
    tracePairing_comm albertUnit, tracePairing_unit_right, tracePairing_smul_left]
  congr 1
  ring

/-- Equality of the genuine convergent Albert Laplace transforms on the open cone determines the measure. -/
theorem eq_albertRankOneRiesz_of_laplace (μ : Measure Albert)
    (hμ : ∀ Y ∈ albertOpenPositiveCone,
      Integrable (fun X => exp (-(tracePairing Y X))) μ ∧
        (∫ X, exp (-(tracePairing Y X)) ∂μ) = ((albertCubicNorm Y)^4)⁻¹) :
    μ = albertRankOneRiesz := by
  have : IsFiniteMeasure (traceTilt μ) := traceTilt_finite μ (hμ _ albertUnit_mem_openCone).1
  have : IsFiniteMeasure (traceTilt albertRankOneRiesz) :=
    traceTilt_finite _ (albertRankOneRiesz_laplace albertUnit_mem_openCone).1
  apply traceTilt_injective
  apply measure_eq_of_local_exponential_transforms
  intro L
  let D := traceRepresentative L.toLinearMap
  let f (t : ℝ) := albertUnit - t • D
  have hf : Continuous f := (continuous_const : Continuous (fun _ : ℝ => albertUnit)).sub
    (continuous_id.smul continuous_const)
  have hf₀ : f 0 = albertUnit := by simp [f]
  have hpre : 0 ∈ f ⁻¹' albertOpenPositiveCone := by
    change f 0 ∈ albertOpenPositiveCone
    rw [hf₀]
    exact albertUnit_mem_openCone
  have ho : IsOpen (f ⁻¹' albertOpenPositiveCone) := isOpen_interior.preimage hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hpre)
  have hpos (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : f t ∈ albertOpenPositiveCone := by
    apply hball
    change -ε < t ∧ t < ε at ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using ht
  have hD (X : Albert) : tracePairing D X = L X := traceRepresentative_pairing _ _
  have h₁ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ X, exp (t * L X) ∂traceTilt μ) = ((albertCubicNorm (f t))^4)⁻¹ := by
    simp_rw [← hD]
    rw [integral_traceTilt_exp]
    exact (hμ _ (hpos t ht)).2
  have h₂ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ X, exp (t * L X) ∂traceTilt albertRankOneRiesz) = ((albertCubicNorm (f t))^4)⁻¹ := by
    simp_rw [← hD]
    rw [integral_traceTilt_exp]
    exact (albertRankOneRiesz_laplace (hpos t ht)).2
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · intro t ht
    apply Integrable.of_integral_ne_zero
    rw [h₁ t ht]
    exact inv_ne_zero (pow_ne_zero 4 (albertCubicNorm_pos_of_mem_openCone (hpos t ht)).ne')
  · intro t ht
    apply Integrable.of_integral_ne_zero
    rw [h₂ t ht]
    exact inv_ne_zero (pow_ne_zero 4 (albertCubicNorm_pos_of_mem_openCone (hpos t ht)).ne')
  · intro t ht
    change (∫ X, exp (t * L X) ∂traceTilt μ) = ∫ X, exp (t * L X) ∂traceTilt albertRankOneRiesz
    rw [h₁ t ht, h₂ t ht]

/-- Positive scalar dilation has the exact homogeneous mass exponent twelve. -/
theorem albertRankOneRiesz_smul_map {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ 12) • (albertRankOneRiesz.map (fun X => r • X)) = albertRankOneRiesz := by
  apply eq_albertRankOneRiesz_of_laplace
  intro Y hY
  let s (X : Albert) := r • X
  have hc : Continuous s := (continuous_const : Continuous (fun _ : Albert => r)).smul
    (continuous_id : Continuous (id : Albert → Albert))
  have hs : Measurable s := hc.measurable
  have hT := albertRankOneRiesz_laplace (smul_mem_albertOpenPositiveCone hY hr)
  have he : (∫ X, exp (-(tracePairing Y X))
      ∂(ENNReal.ofReal (r ^ 12) • albertRankOneRiesz.map s)) = ((albertCubicNorm Y)^4)⁻¹ := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      integral_map hs.aemeasurable (measurable_albertLaplaceKernel Y).aestronglyMeasurable, smul_eq_mul]
    have hcomp (X : Albert) : exp (-(tracePairing Y (s X))) = exp (-(tracePairing (r • Y) X)) := by
      change exp (-(tracePairing Y (r • X))) = _
      rw [tracePairing_smul_right, tracePairing_smul_left]
    simp_rw [hcomp]
    rw [hT.2, albertCubicNorm_smul, mul_pow, ← pow_mul]
    have hN := (albertCubicNorm_pos_of_mem_openCone hY).ne'
    field_simp [hr.ne', hN]
  refine ⟨Integrable.of_integral_ne_zero ?_, he⟩
  rw [he]
  exact inv_ne_zero (pow_ne_zero 4 (albertCubicNorm_pos_of_mem_openCone hY).ne')

end AlbertSequential.WindowProbability
