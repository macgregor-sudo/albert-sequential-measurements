/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityAlbertRieszCone
public import WindowProbabilityAlbertInvariance
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The un-tilted rank-one Riesz measure of the actual Albert algebra. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory NativeAnalysis Real Set
open scoped AlbertSequential.WindowProbability ENNReal Topology

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

/-- Remove the exact exponential trace tilt from the native rank-one chart probability. -/
def albertRankOneRiesz : Measure Albert :=
  albertChartRayMeasure.withDensity (fun X => ENNReal.ofReal (exp (albertTrace X)))

theorem continuous_albertPairing_fixed (Y : Albert) :
    Continuous (fun X => tracePairing Y X) := by
  have h : Continuous (fun X : Albert => (Y, X)) := continuous_const.prodMk continuous_id
  exact (continuous_tracePairing.comp h).congr (fun _ => rfl)

theorem measurable_albertTraceExp (a : ℝ) :
    Measurable (fun X => ENNReal.ofReal (exp (a * albertTrace X))) :=
  (continuous_exp.measurable.comp (measurable_const.mul continuous_albertTrace.measurable)).ennreal_ofReal

theorem measurable_albertLaplaceKernel (Y : Albert) :
    Measurable (fun X => exp (-(tracePairing Y X))) :=
  continuous_exp.measurable.comp (continuous_albertPairing_fixed Y).measurable.neg

instance : SigmaFinite albertRankOneRiesz := by
  unfold albertRankOneRiesz
  infer_instance

instance : IsFiniteMeasureOnCompacts albertRankOneRiesz where
  lt_top_of_isCompact := by
    intro K hK
    obtain ⟨b, hb⟩ := hK.bddAbove_image (continuous_exp.comp continuous_albertTrace).continuousOn
    have hbound (X : Albert) (hX : X ∈ K) : exp (albertTrace X) ≤ b :=
      hb (mem_image_of_mem _ hX)
    rw [albertRankOneRiesz, withDensity_apply _ hK.isClosed.measurableSet]
    refine (setLIntegral_mono (measurable_const : Measurable (fun _ : Albert => ENNReal.ofReal b))
      (fun X hX => ENNReal.ofReal_le_ofReal (hbound X hX))).trans_lt ?_
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The inverse density recovers the exact probability without an unspecified constant. -/
theorem albertRankOneRiesz_traceTilt :
    albertRankOneRiesz.withDensity (fun X => ENNReal.ofReal (exp (-albertTrace X))) = albertChartRayMeasure := by
  have hp : Measurable (fun X => ENNReal.ofReal (exp (albertTrace X))) :=
    (continuous_exp.measurable.comp continuous_albertTrace.measurable).ennreal_ofReal
  have hn : Measurable (fun X => ENNReal.ofReal (exp (-albertTrace X))) :=
    (continuous_exp.measurable.comp continuous_albertTrace.measurable.neg).ennreal_ofReal
  have hw : (fun X => ENNReal.ofReal (exp (albertTrace X))) *
      (fun X => ENNReal.ofReal (exp (-albertTrace X))) = 1 := by
    funext X
    change ENNReal.ofReal (exp (albertTrace X)) * ENNReal.ofReal (exp (-albertTrace X)) = 1
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, add_neg_cancel, exp_zero, ENNReal.ofReal_one]
  unfold albertRankOneRiesz
  rw [← withDensity_mul _ hp hn, hw, withDensity_one]

theorem ae_albertChartRayMeasure_positive_trace :
    ∀ᵐ X ∂albertChartRayMeasure, 0 < albertTrace X := by
  rw [albertChartRayMeasure, ae_map_iff measurable_sampleAlbertChartRay.aemeasurable
    (measurableSet_lt measurable_const continuous_albertTrace.measurable)]
  filter_upwards [ae_albertChartSamplingMeasure_positive_ray] with p hp
  rw [trace_sampleAlbertChartRay p hp]
  positivity

theorem ae_albertChartRayMeasure_normalized_isAtom :
    ∀ᵐ X ∂albertChartRayMeasure, IsAtom (normalizeAlbert X) := by
  have he : albertChartAtomMeasure = albertChartRayMeasure.map normalizeAlbert := by
    rw [albertChartAtomMeasure, albertChartRayMeasure, Measure.map_map measurable_normalizeAlbert
      measurable_sampleAlbertChartRay]
  have h := ae_albertChartAtomMeasure_isAtom
  rw [he] at h
  exact ae_of_ae_map measurable_normalizeAlbert.aemeasurable h

/-- The un-tilted measure is carried by genuine positive rays through the native primitive atoms. -/
theorem ae_albertRankOneRiesz_rankOne :
    ∀ᵐ X ∂albertRankOneRiesz, ∃ t : ℝ, 0 < t ∧ ∃ p : Albert, IsAtom p ∧ X = t • p := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_albertChartRayMeasure_positive_trace, ae_albertChartRayMeasure_normalized_isAtom]
    with X hX ha
  refine ⟨albertTrace X, hX, normalizeAlbert X, ha, ?_⟩
  rw [normalizeAlbert, smul_smul, mul_inv_cancel₀ hX.ne', one_smul]

theorem ae_albertRankOneRiesz_positive :
    ∀ᵐ X ∂albertRankOneRiesz, IsPositive X := by
  filter_upwards [ae_albertRankOneRiesz_rankOne] with X hX
  obtain ⟨r, hr, p, hp, rfl⟩ := hX
  refine ⟨Real.sqrt r • p, ?_⟩
  rw [jordanMul_smul_left, jordanMul_smul_right, smul_smul, ← pow_two,
    Real.sq_sqrt hr.le, hp.1]

/-- The genuine positive-cone determinant is positive on the full test domain. -/
theorem albertCubicNorm_pos_of_mem_openCone {Y : Albert} (hY : Y ∈ albertOpenPositiveCone) :
    0 < albertCubicNorm Y := by
  obtain ⟨g,d,hd,hg⟩ := albertStrictPositive_diagonalization ((albertStrictPositive_mem_openCone Y).mpr hY)
  rw [← g.map_cubicNorm, hg]
  change 0 < albertCubicNorm (d, fun _ => 0)
  rw [albertCubicNorm_diag]
  exact mul_pos (mul_pos (hd 0) (hd 1)) (hd 2)

private theorem albertChartRayMeasure_exp_trace_of_mem_openCone {Y : Albert} (hY : Y ∈ albertOpenPositiveCone) :
    (∫ X, exp (-(tracePairing (Y - albertUnit) X)) ∂albertChartRayMeasure) =
      ((albertCubicNorm Y)^4)⁻¹ := by
  obtain ⟨g,d,hd,hg⟩ := albertStrictPositive_diagonalization ((albertStrictPositive_mem_openCone Y).mpr hY)
  have hmatrix : schurMatrix (d 0) (d 1) (d 2) 0 0 0 = diagonalElement d := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [schurMatrix, diagonalElement, octonionConj_zero]
  have hz : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hr : 0 < d 2 - octNormSq 0 / d 1 := by simpa [hz] using hd 2
  have hs : 0 < schurScalar (d 0) (d 1) (d 2) 0 0 0 := by
    simpa [schurScalar, hz, octonionConj_zero, octonionMul_zero_left] using hd 0
  have hD := integral_albertChartRayMeasure_exp_trace (d 0) (d 1) (d 2) 0 0 0 (hd 1) hr hs
  rw [hmatrix] at hD
  let f (X : Albert) := exp (-(tracePairing (diagonalElement d - albertUnit) X))
  have hf : Measurable f := measurable_albertLaplaceKernel _
  have hm : Measurable g.linearEquiv := g.linearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hcomp (X : Albert) : f (g.linearEquiv X) = exp (-(tracePairing (Y - albertUnit) X)) := by
    have hge : g.linearEquiv (Y - albertUnit) = diagonalElement d - albertUnit := by
      rw [map_sub, hg, g.preserves_unit]
    unfold f
    rw [← hge, nativeAutomorphism_pairing]
  calc
    _ = ∫ X, f (g.linearEquiv X) ∂albertChartRayMeasure := by simp_rw [hcomp]
    _ = ∫ X, f X ∂(albertChartRayMeasure.map g.linearEquiv) :=
      (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [map_nativeAutomorphism_albertChartRayMeasure]
      change (∫ X, exp (-(tracePairing (diagonalElement d - albertUnit) X)) ∂albertChartRayMeasure) = _
      rw [hD, ← hg, g.map_cubicNorm]

/-- Literal Appendix B transform on the full interior of the native positive cone. -/
theorem albertRankOneRiesz_laplace {Y : Albert} (hY : Y ∈ albertOpenPositiveCone) :
    Integrable (fun X => exp (-(tracePairing Y X))) albertRankOneRiesz ∧
    (∫ X, exp (-(tracePairing Y X)) ∂albertRankOneRiesz) = ((albertCubicNorm Y)^4)⁻¹ := by
  have hp : Measurable (fun X => ENNReal.ofReal (exp (albertTrace X))) :=
    (continuous_exp.measurable.comp continuous_albertTrace.measurable).ennreal_ofReal
  have he : (∫ X, exp (-(tracePairing Y X)) ∂albertRankOneRiesz) = ((albertCubicNorm Y)^4)⁻¹ := by
    unfold albertRankOneRiesz
    rw [integral_withDensity_eq_integral_toReal_smul hp (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have heq (X : Albert) :
        (ENNReal.ofReal (exp (albertTrace X))).toReal • exp (-(tracePairing Y X)) =
          exp (-(tracePairing (Y - albertUnit) X)) := by
      rw [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul, ← exp_add, tracePairing_sub_left,
        tracePairing_comm albertUnit, tracePairing_unit_right]
      congr 1
      ring
    simp_rw [heq]
    exact albertChartRayMeasure_exp_trace_of_mem_openCone hY
  have hn : ((albertCubicNorm Y)^4)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 4 (albertCubicNorm_pos_of_mem_openCone hY).ne')
  refine ⟨Integrable.of_integral_ne_zero ?_, he⟩
  rw [he]
  exact hn

/-- The un-tilted measure is invariant under each genuine native unital automorphism. -/
theorem map_nativeAutomorphism_albertRankOneRiesz (g : NativeAlbertAutomorphism) :
    albertRankOneRiesz.map g.linearEquiv = albertRankOneRiesz := by
  have hm : Measurable g.linearEquiv := g.linearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hw : Measurable (fun X => ENNReal.ofReal (exp (albertTrace X))) :=
    (continuous_exp.measurable.comp continuous_albertTrace.measurable).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun X => f (g.linearEquiv X)) := hf.comp hm
  rw [lintegral_map hf hm, albertRankOneRiesz,
    lintegral_withDensity_eq_lintegral_mul _ hw hF, lintegral_withDensity_eq_lintegral_mul _ hw hf]
  let k (X : Albert) := (ENNReal.ofReal (exp (albertTrace X))) * f X
  have hk : Measurable k := hw.mul hf
  calc
    _ = ∫⁻ X, k (g.linearEquiv X) ∂albertChartRayMeasure := by
      apply lintegral_congr
      intro X
      change ENNReal.ofReal (exp (albertTrace X)) * f (g.linearEquiv X) =
        ENNReal.ofReal (exp (albertTrace (g.linearEquiv X))) * f (g.linearEquiv X)
      rw [g.preserves_trace]
    _ = ∫⁻ X, k X ∂(albertChartRayMeasure.map g.linearEquiv) := (lintegral_map hk hm).symm
    _ = _ := by
      rw [map_nativeAutomorphism_albertChartRayMeasure]
      rfl

end AlbertSequential.WindowProbability
