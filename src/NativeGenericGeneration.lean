/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionQuadrangleTopology
public import ComplexWindowDeterminantAndMax
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

@[expose] public section
noncomputable section

namespace AlbertSequential.NativeAnalysis

open WindowProbability ProjectiveMetricInvariant Filter Set
open scoped Topology

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : FiniteDimensional ℝ Octonion := octonionChartCoordinates.finiteDimensional
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

private def JordanBilinear : Albert →L[ℝ] Albert →L[ℝ] Albert :=
  (LinearMap.mk₂' ℝ ℝ jordanMul jordanMul_add_left jordanMul_smul_left
    jordanMul_add_right jordanMul_smul_right).toContinuousBilinearMap

private def AlbertTraceLinear : Albert →L[ℝ] ℝ :=
  ({ toFun := albertTrace, map_add' := albertTrace_add, map_smul' := albertTrace_smul } :
    Albert →ₗ[ℝ] ℝ).toContinuousLinearMap

private def OctonionBilinear : Octonion →L[ℝ] Octonion →L[ℝ] Octonion :=
  (LinearMap.mk₂' ℝ ℝ octonionMul octonionMul_add_left octonionMul_smul_left
    octonionMul_add_right octonionMul_smul_right).toContinuousBilinearMap

private def OctonionDot : Octonion →L[ℝ] Octonion →L[ℝ] ℝ :=
  (LinearMap.mk₂' ℝ ℝ octDot octDot_add_left octDot_smul_left
    octDot_add_right octDot_smul_right).toContinuousBilinearMap

private def OctonionConjugate : Octonion →L[ℝ] Octonion :=
  ({ toFun := octonionConj, map_add' := octonionConj_add, map_smul' := octonionConj_smul } :
    Octonion →ₗ[ℝ] Octonion).toContinuousLinearMap

private theorem analyticAt_nativeInvariant (p : Fin 4 → Albert) :
    AnalyticAt ℝ fourPointInvariant p := by
  have h (i : Fin 4) : AnalyticAt ℝ (fun x : Fin 4 → Albert => x i) p :=
    (ContinuousLinearMap.proj i : (Fin 4 → Albert) →L[ℝ] Albert).analyticAt p
  have hj (i j : Fin 4) :
      AnalyticAt ℝ (fun x : Fin 4 → Albert => jordanMul (x i) (x j)) p := by
    change AnalyticAt ℝ (fun x : Fin 4 → Albert => JordanBilinear (x i) (x j)) p
    exact (JordanBilinear.analyticAt_bilinear (p i, p j)).comp₂ (h i) (h j)
  have hpair {f g : (Fin 4 → Albert) → Albert} (hf : AnalyticAt ℝ f p)
      (hg : AnalyticAt ℝ g p) :
      AnalyticAt ℝ (fun x => tracePairing (f x) (g x)) p := by
    change AnalyticAt ℝ (⇑AlbertTraceLinear ∘ fun x => JordanBilinear (f x) (g x)) p
    exact (AlbertTraceLinear.analyticAt _).comp ((JordanBilinear.analyticAt_bilinear _).comp₂ hf hg)
  have ho (i j : Fin 4) : AnalyticAt ℝ (fun q => fpOverlap q i j) p := hpair (h i) (h j)
  have hr (i j k : Fin 4) : AnalyticAt ℝ (fun q => fpTriangle q i j k) p := hpair (hj i j) (h k)
  have ht1 : AnalyticAt ℝ fpDoublePair1 p := hpair (hj 0 1) (hj 2 3)
  have ht2 : AnalyticAt ℝ fpDoublePair2 p := hpair (hj 0 2) (hj 1 3)
  have ht3 : AnalyticAt ℝ fpDoublePair3 p := hpair (hj 0 3) (hj 1 2)
  have hw1 : AnalyticAt ℝ fpOmega1 p := (ht2.add ht3).sub ht1
  have hw2 : AnalyticAt ℝ fpOmega2 p := (ht1.add ht3).sub ht2
  have hw3 : AnalyticAt ℝ fpOmega3 p := (ht1.add ht2).sub ht3
  unfold fourPointInvariant fourPointOmegaPoly
  fun_prop

private theorem analyticAt_chartDyad (x : Octonion × Octonion) :
    AnalyticAt ℝ (fun a : Octonion × Octonion => chartDyad a.1 a.2) x := by
  let v (a : Octonion × Octonion) : Fin 3 → Octonion := ![octOne, a.1, a.2]
  have hv (i : Fin 3) : AnalyticAt ℝ (fun a => v a i) x := by
    fin_cases i
    · change AnalyticAt ℝ (fun _ : Octonion × Octonion => octOne) x
      exact analyticAt_const
    · exact (ContinuousLinearMap.fst ℝ Octonion Octonion).analyticAt _
    · exact (ContinuousLinearMap.snd ℝ Octonion Octonion).analyticAt _
  have hd (i : Fin 3) : AnalyticAt ℝ (fun a => octNormSq (v a i)) x := by
    simp only [← octDot_self]
    exact (OctonionDot.analyticAt_bilinear _).comp₂ (hv i) (hv i)
  have hc (j : Fin 3) : AnalyticAt ℝ (fun a => octonionConj (v a j)) x := by
    change AnalyticAt ℝ (⇑OctonionConjugate ∘ fun a => v a j) x
    exact (OctonionConjugate.analyticAt _).comp (hv j)
  have he (i j : Fin 3) :
      AnalyticAt ℝ (fun a => octonionMul (v a i) (octonionConj (v a j))) x :=
    (OctonionBilinear.analyticAt_bilinear _).comp₂ (hv i) (hc j)
  apply AnalyticAt.prod (AnalyticAt.pi hd)
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact he 0 1
  · exact he 0 2
  · exact he 1 2

private def normalizedChartPoint (x : Octonion × Octonion) : AlbertAtomSpace :=
  ⟨(albertTrace (chartDyad x.1 x.2))⁻¹ • chartDyad x.1 x.2,
    chartDyad_normalize_isAtom x.1 x.2⟩

private theorem analyticAt_normalizedChart (x : Octonion × Octonion) :
    AnalyticAt ℝ (fun a => (normalizedChartPoint a).val) x := by
  have h := analyticAt_chartDyad x
  have htr : AnalyticAt ℝ (fun a : Octonion × Octonion => albertTrace (chartDyad a.1 a.2)) x := by
    change AnalyticAt ℝ (⇑AlbertTraceLinear ∘ fun a : Octonion × Octonion => chartDyad a.1 a.2) x
    exact (AlbertTraceLinear.analyticAt _).comp h
  exact (htr.inv (chartDyad_trace_pos x.1 x.2).ne').smul h

private theorem continuous_normalizedChart : Continuous normalizedChartPoint :=
  Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun x =>
    (analyticAt_normalizedChart x).continuousAt) _

private theorem octDyad_scale_from_chart (r : ℝ) (x : Octonion × Octonion) :
    octDyad ![octonionScalar r, r • x.1, r • x.2] = r^2 • chartDyad x.1 x.2 := by
  have hsnd (A : Albert) : (r ^ 2 • A).2 = r ^ 2 • A.2 := rfl
  have he : (![octonionScalar r, r • x.1, r • x.2] : Fin 3 → Octonion) =
      fun i => r • (![octOne, x.1, x.2] : Fin 3 → Octonion) i := by
    funext i
    fin_cases i
    · exact octonionScalar_eq_smul r
    · rfl
    · rfl
  rw [he]
  apply Prod.ext <;> funext i
  · exact octNormSq_smul _ _
  · rw [hsnd]
    fin_cases i <;>
      simp [chartDyad, octDyad, Pi.smul_apply, octonionConj_smul, octonionMul_smul_left,
        octonionMul_smul_right, smul_smul, pow_two]

private theorem atom_mem_normalizedChart {p : AlbertAtomSpace} (hp : 0 < p.val.1 0) :
    p ∈ Set.range normalizedChartPoint := by
  let r := Real.sqrt (p.val.1 0)
  have hr := Real.sqrt_pos.mpr hp
  let v := atomDyadVec p.val
  let x : Octonion × Octonion := (r⁻¹ • v 1, r⁻¹ • v 2)
  have hx : (![octonionScalar r, r • x.1, r • x.2] : Fin 3 → Octonion) = v := by
    funext i
    fin_cases i
    · rfl
    · change r • (r⁻¹ • v 1) = v 1
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · change r • (r⁻¹ • v 2) = v 2
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hd : p.val = r^2 • chartDyad x.1 x.2 := by
    rw [← octDyad_scale_from_chart, hx]
    exact eq_octDyad_of_isAtom_diag0_pos p.val p.property hp
  have ht := congrArg albertTrace hd
  rw [p.property.2, albertTrace_smul] at ht
  have hs : (albertTrace (chartDyad x.1 x.2))⁻¹ = r^2 := by
    apply inv_eq_of_mul_eq_one_left
    exact ht.symm
  refine ⟨x, Subtype.ext ?_⟩
  change (albertTrace (chartDyad x.1 x.2))⁻¹ • chartDyad x.1 x.2 = p.val
  rw [hs, ← hd]

private theorem dense_normalizedChart : DenseRange normalizedChartPoint := by
  refine (dense_off_polar_line ⟨diagAtom 0, diagAtom_isAtom 0⟩).mono ?_
  intro p hp
  change 0 < tracePairing (diagAtom 0) p.val at hp
  rw [tracePairing_diagAtom] at hp
  exact atom_mem_normalizedChart hp

private def menuChart (x : Fin 4 → Octonion × Octonion) : Fin 4 → AlbertAtomSpace :=
  fun i => normalizedChartPoint (x i)

private theorem dense_menuChart : DenseRange menuChart :=
  DenseRange.piMap (fun (_ : Fin 4) => dense_normalizedChart)

private theorem continuous_menuChart : Continuous menuChart :=
  continuous_pi fun i => continuous_normalizedChart.comp (continuous_apply i)

private def atomInvariant (p : Fin 4 → AlbertAtomSpace) : ℝ :=
  fourPointInvariant (fun i => (p i).val)

private theorem continuous_atomInvariant : Continuous atomInvariant := by
  have h : Continuous fourPointInvariant :=
    continuous_iff_continuousAt.mpr fun x => (analyticAt_nativeInvariant x).continuousAt
  exact h.comp (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))

private theorem analyticAt_menuChartInvariant (x : Fin 4 → Octonion × Octonion) :
    AnalyticAt ℝ (atomInvariant ∘ menuChart) x := by
  have h (i : Fin 4) : AnalyticAt ℝ (fun a : Fin 4 → Octonion × Octonion =>
      (normalizedChartPoint (a i)).val) x :=
    (analyticAt_normalizedChart _).comp
      ((ContinuousLinearMap.proj i : (Fin 4 → Octonion × Octonion) →L[ℝ]
        (Octonion × Octonion)).analyticAt x)
  exact (analyticAt_nativeInvariant _).comp (AnalyticAt.pi h)

private theorem atomInvariant_pos_iff (p : Fin 4 → AlbertAtomSpace) :
    0 < atomInvariant p ↔ GeneratesAlbert (fun i => (p i).val) :=
  fourPointInvariant_pos_iff _ (fun i => (p i).property)

/-- The full native Albert-generating ordered four-atom locus is open and dense. -/
theorem generating_fourAtoms_open_dense :
    IsOpen {p : Fin 4 → AlbertAtomSpace | GeneratesAlbert (fun i => (p i).val)} ∧
      Dense {p : Fin 4 → AlbertAtomSpace | GeneratesAlbert (fun i => (p i).val)} := by
  have hset : {p : Fin 4 → AlbertAtomSpace | GeneratesAlbert (fun i => (p i).val)} =
      {p : Fin 4 → AlbertAtomSpace | 0 < atomInvariant p} :=
    Set.ext fun x => (atomInvariant_pos_iff x).symm
  rw [hset]
  have hopen : IsOpen {p : Fin 4 → AlbertAtomSpace | 0 < atomInvariant p} :=
    isOpen_lt continuous_const continuous_atomInvariant
  refine ⟨hopen, ?_⟩
  let p (i : Fin 4) : AlbertAtomSpace := ⟨maximizerConfig i, maximizerConfig_isAtom i⟩
  have hp : p ∈ {p : Fin 4 → AlbertAtomSpace | 0 < atomInvariant p} := by
    change 0 < fourPointInvariant maximizerConfig
    rw [fourPointInvariant_maximizerConfig]
    norm_num
  obtain ⟨q, hq, ⟨d, hd⟩⟩ :=
    dense_iff_inter_open.mp dense_menuChart _ hopen ⟨p, hp⟩
  have hpos : 0 < atomInvariant (menuChart d) := hd ▸ hq
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra hbad
  obtain ⟨u, hu, ⟨c, hc⟩⟩ := dense_iff_inter_open.mp dense_menuChart U hU hne
  have hcU : c ∈ menuChart ⁻¹' U := by
    change menuChart c ∈ U
    rwa [hc]
  have hzero : (atomInvariant ∘ menuChart) =ᶠ[𝓝 c] 0 := by
    filter_upwards [(hU.preimage continuous_menuChart).mem_nhds hcU] with x hx
    change atomInvariant (menuChart x) = 0
    have hn : 0 ≤ atomInvariant (menuChart x) :=
      fourPointInvariant_nonneg _ (fun i => (menuChart x i).property)
    apply le_antisymm _ hn
    exact le_of_not_gt (fun hgt => hbad ⟨menuChart x, hx, hgt⟩)
  have hana : AnalyticOnNhd ℝ (atomInvariant ∘ menuChart) univ := fun x _ =>
    analyticAt_menuChartInvariant x
  have hd0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ c) hzero (mem_univ d)
  exact hpos.ne' hd0

end AlbertSequential.NativeAnalysis
