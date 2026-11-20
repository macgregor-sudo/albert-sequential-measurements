/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityAlbertGroup
public import WindowProbabilityChartBinding
public import WindowProbabilityLaplace
public import NativeTraceRiesz

/-! Invariance of the octonionic chart probability under native unital
Jordan automorphisms. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped AlbertSequential.WindowProbability Topology

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := NativeAnalysis.recoveredCoordinateEquiv.symm.finiteDimensional
local instance : CompleteSpace Octonion :=
  inferInstanceAs (CompleteSpace (Quaternion ℝ × Quaternion ℝ))
local instance : CompleteSpace Albert :=
  inferInstanceAs (CompleteSpace ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : SecondCountableTopology Octonion :=
  inferInstanceAs (SecondCountableTopology (Quaternion ℝ × Quaternion ℝ))
local instance : SecondCountableTopology Albert :=
  inferInstanceAs (SecondCountableTopology ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

private theorem continuous_chartOctNormSq : Continuous octNormSq := by
  have h : Continuous (fun x : Octonion => Quaternion.normSq x.1 + Quaternion.normSq x.2) :=
    (Quaternion.continuous_normSq.comp continuous_fst).add
      (Quaternion.continuous_normSq.comp continuous_snd)
  apply h.congr
  intro x
  rw [octNormSq_eq_coords, Quaternion.normSq_def', Quaternion.normSq_def']
  ring

set_option maxHeartbeats 2100000 in
private theorem exists_local_schur_scales (D : Albert) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ t ∈ Ioo (-ε) ε, ∃ (a b c : ℝ) (x y z : Octonion),
      schurMatrix a b c x y z = albertUnit - t • D ∧
        0 < b ∧ 0 < c - octNormSq z / b ∧ 0 < schurScalar a b c x y z := by
  let a (t : ℝ) := 1 - t * D.1 0
  let b (t : ℝ) := 1 - t * D.1 1
  let c (t : ℝ) := 1 - t * D.1 2
  let x (t : ℝ) := -t • octonionConj (D.2 0)
  let y (t : ℝ) := -t • octonionConj (D.2 1)
  let z (t : ℝ) := -t • D.2 2
  let r (t : ℝ) := c t - octNormSq (z t) / b t
  let s (t : ℝ) := schurScalar (a t) (b t) (c t) (x t) (y t) (z t)
  have hY (t : ℝ) : schurMatrix (a t) (b t) (c t) (x t) (y t) (z t) =
      albertUnit - t • D := by
    apply Prod.ext <;> funext i
    · fin_cases i <;> rfl
    · have he : (albertUnit - t • D).2 i = 0 - t • D.2 i := rfl
      rw [he, zero_sub]
      fin_cases i <;>
        simp [schurMatrix, x, y, z, octonionConj_neg, octonionConj_smul, octonionConj_conj]
  have ha : ContinuousAt a 0 := by dsimp [a]; fun_prop
  have hb : ContinuousAt b 0 := by dsimp [b]; fun_prop
  have hc : ContinuousAt c 0 := by dsimp [c]; fun_prop
  have hx : ContinuousAt x 0 := by dsimp [x]; fun_prop
  have hy : ContinuousAt y 0 := by dsimp [y]; fun_prop
  have hz : ContinuousAt z 0 := by dsimp [z]; fun_prop
  have hzero : octNormSq 0 = 0 := by simpa using octNormSq_smul (0 : ℝ) octOne
  have hb0 : b 0 = 1 := by simp [b]
  have hr0 : r 0 = 1 := by simp [r, b, c, z, hzero]
  have hs0 : s 0 = 1 := by
    simp [s, schurScalar, a, b, c, x, y, z, hzero, octonionConj_zero,
      octonionMul_zero_left]
  have hn := continuous_chartOctNormSq
  have hr : ContinuousAt r 0 := hc.sub ((hn.continuousAt.comp hz).div hb (by simp [hb0]))
  have hmul : ContinuousAt (fun t : ℝ => octonionMul (octonionConj (z t)) (x t)) 0 :=
    NativeAnalysis.continuous_octonionMul.continuousAt.comp
      ((NativeAnalysis.continuous_octonionConj.continuousAt.comp hz).prodMk hx)
  have hcore : ContinuousAt (fun t : ℝ => y t - (b t)⁻¹ • octonionMul (octonionConj (z t)) (x t)) 0 :=
    hy.sub ((hb.inv₀ (by simp [hb0])).smul hmul)
  have hs : ContinuousAt s 0 :=
    (ha.sub ((hn.continuousAt.comp hx).div hb (by simp [hb0]))).sub
      ((hn.continuousAt.comp hcore).div hr (by change r 0 ≠ 0; rw [hr0]; exact one_ne_zero))
  have hbpos := hb.eventually (isOpen_Ioi.mem_nhds (show b 0 ∈ Ioi (0 : ℝ) by simp [hb0]))
  have hrpos := hr.eventually (isOpen_Ioi.mem_nhds (show r 0 ∈ Ioi (0 : ℝ) by simp [hr0]))
  have hspos := hs.eventually (isOpen_Ioi.mem_nhds (show s 0 ∈ Ioi (0 : ℝ) by simp [hs0]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hbpos.and (hrpos.and hspos))
  use ε
  refine ⟨hε, ?_⟩
  intro t ht
  have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using ht
  have hpos : 0 < b t ∧ 0 < r t ∧ 0 < s t := hball hmem
  exact ⟨a t, b t, c t, x t, y t, z t, hY t, hpos.1, hpos.2.1, hpos.2.2⟩

/-- The local exponential transform of the actual chart probability is
the inverse fourth power of the native cubic in every trace direction. -/
theorem exists_local_albertChartRayMeasure_transform (D : Albert) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ t ∈ Ioo (-ε) ε,
      Integrable (fun X : Albert => exp (t * tracePairing D X)) albertChartRayMeasure ∧
      (∫ X, exp (t * tracePairing D X) ∂albertChartRayMeasure) =
        ((albertCubicNorm (albertUnit - t • D))^4)⁻¹ := by
  obtain ⟨ε, hε, hscale⟩ := exists_local_schur_scales D
  refine ⟨ε, hε, ?_⟩
  intro t ht
  obtain ⟨a, b, c, x, y, z, hY, hb, hr, hs⟩ := hscale t ht
  have hT := integral_albertChartRayMeasure_exp_trace a b c x y z hb hr hs
  have hN : 0 < albertCubicNorm (albertUnit - t • D) := by
    rw [← hY, ← schurScalar_cubicNorm a b c x y z hb.ne' hr.ne']
    exact mul_pos (mul_pos hb hr) hs
  have hexp : (fun X : Albert => exp (-(tracePairing ((albertUnit - t • D) - albertUnit) X))) =
      (fun X : Albert => exp (t * tracePairing D X)) := by
    funext X
    rw [tracePairing_sub_left, tracePairing_sub_left, tracePairing_smul_left t D X]
    congr 1
    ring
  rw [hY, hexp] at hT
  have hnz : (∫ X : Albert, exp (t * tracePairing D X) ∂albertChartRayMeasure) ≠ 0 :=
    fun hz => (inv_ne_zero (pow_ne_zero 4 hN.ne')) (hT.symm.trans hz)
  have hI : Integrable (fun X : Albert => exp (t * tracePairing D X)) albertChartRayMeasure :=
    Integrable.of_integral_ne_zero hnz
  exact ⟨hI, hT⟩

/-- The full unnormalized octonionic chart probability is invariant under
every native unital Jordan automorphism. -/
theorem map_nativeAutomorphism_albertChartRayMeasure (g : NativeAlbertAutomorphism) :
    albertChartRayMeasure.map g.linearEquiv = albertChartRayMeasure := by
  have hg : Measurable g.linearEquiv :=
    g.linearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  apply measure_eq_of_local_exponential_transforms
  intro L
  let D := NativeAnalysis.traceRepresentative L.toLinearMap
  let E := g.linearEquiv.symm D
  have hD (X : Albert) : tracePairing D X = L X := NativeAnalysis.traceRepresentative_pairing _ _
  have hE (X : Albert) : tracePairing E X = L (g.linearEquiv X) := by
    rw [← g.map_tracePairing E X]
    change tracePairing (g.linearEquiv (g.linearEquiv.symm D)) (g.linearEquiv X) = _
    rw [LinearEquiv.apply_symm_apply, hD]
  obtain ⟨δ, hδ, hd⟩ := exists_local_albertChartRayMeasure_transform D
  obtain ⟨ξ, hξ, he⟩ := exists_local_albertChartRayMeasure_transform E
  let ε := min δ ξ
  have hδ' : Ioo (-ε) ε ⊆ Ioo (-δ) δ := Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hξ' : Ioo (-ε) ε ⊆ Ioo (-ξ) ξ := Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hm (t : ℝ) : Measurable (fun X : Albert => exp (t * L X)) := by fun_prop
  refine ⟨ε, lt_min hδ hξ, ?_, ?_, ?_⟩
  · intro t ht
    change Integrable (fun X => exp (t * L X)) (albertChartRayMeasure.map g.linearEquiv)
    rw [integrable_map_measure (hm t).aestronglyMeasurable hg.aemeasurable]
    simpa only [Function.comp_def, hE] using (he t (hξ' ht)).1
  · intro t ht
    change Integrable (fun X => exp (t * L X)) albertChartRayMeasure
    simpa only [hD] using (hd t (hδ' ht)).1
  · intro t ht
    have hdet : albertCubicNorm (albertUnit - t • E) =
        albertCubicNorm (albertUnit - t • D) := by
      rw [← g.map_cubicNorm, map_sub, map_smul, g.preserves_unit]
      change albertCubicNorm (albertUnit - t • g.linearEquiv (g.linearEquiv.symm D)) = _
      rw [LinearEquiv.apply_symm_apply]
    change (∫ X, exp (t * L X) ∂(albertChartRayMeasure.map g.linearEquiv)) =
      (∫ X, exp (t * L X) ∂albertChartRayMeasure)
    rw [integral_map hg.aemeasurable (hm t).aestronglyMeasurable]
    simp_rw [← hE]
    simp_rw [← hD]
    rw [(he t (hξ' ht)).2, (hd t (hδ' ht)).2, hdet]

/-- The probability on normalized native chart atoms is invariant under
the same automorphisms. -/
theorem map_nativeAutomorphism_albertChartAtomMeasure (g : NativeAlbertAutomorphism) :
    albertChartAtomMeasure.map g.linearEquiv = albertChartAtomMeasure := by
  have hg : Measurable g.linearEquiv :=
    g.linearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hc : g.linearEquiv ∘ normalizeAlbert = normalizeAlbert ∘ g.linearEquiv := by
    funext X
    simp [normalizeAlbert, map_smul, g.preserves_trace]
  have h : albertChartAtomMeasure = albertChartRayMeasure.map normalizeAlbert := by
    unfold albertChartAtomMeasure albertChartRayMeasure
    rw [Measure.map_map measurable_normalizeAlbert measurable_sampleAlbertChartRay]
  rw [h, Measure.map_map hg measurable_normalizeAlbert, hc,
    ← Measure.map_map measurable_normalizeAlbert hg, map_nativeAutomorphism_albertChartRayMeasure]

/-- For every native complex window, the projected octonionic ray law
has the determinant transform on genuine local convergence intervals for
all Hermitian test matrices. -/
theorem exists_local_projected_albertChartRayMeasure_transform (W : ComplexWindow) (H : Hermitian3) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ t ∈ Ioo (-ε) ε,
      Integrable (fun M : ComplexMatrix3 => exp (t * ((H : ComplexMatrix3) * M).trace.re))
        (albertChartRayMeasure.map (projectedMatrix W)) ∧
      (∫ M, exp (t * ((H : ComplexMatrix3) * M).trace.re)
        ∂(albertChartRayMeasure.map (projectedMatrix W))) =
        ((((1 : ComplexMatrix3) - t • (H : ComplexMatrix3)).det.re)^4)⁻¹ := by
  obtain ⟨ε, hε, h⟩ := exists_local_albertChartRayMeasure_transform (W.embedding H)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  let f (M : ComplexMatrix3) := exp (t * ((H : ComplexMatrix3) * M).trace.re)
  have hf : Measurable f := by
    dsimp only [f, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hcomp : f ∘ projectedMatrix W = (fun X => exp (t * tracePairing (W.embedding H) X)) := by
    funext X
    change exp (t * ((H : ComplexMatrix3) * (windowProj W X : ComplexMatrix3)).trace.re) = _
    rw [(complexWindow_laplace_integrand W H X).1, tracePairing_comm]
  have hn : albertCubicNorm (albertUnit - t • W.embedding H) =
      ((1 : ComplexMatrix3) - t • (H : ComplexMatrix3)).det.re := by
    have hh := (complexWindow_laplace_integrand W ((-t) • H) albertUnit).2.1
    rw [map_smul, neg_smul, ← sub_eq_add_neg] at hh
    change albertCubicNorm (albertUnit - t • W.embedding H) =
      ((1 : ComplexMatrix3) + (-t) • (H : ComplexMatrix3)).det.re at hh
    simpa only [neg_smul, ← sub_eq_add_neg] using hh
  have hp := (measurable_projectedMatrix W).aemeasurable (μ := albertChartRayMeasure)
  change Integrable f (albertChartRayMeasure.map (projectedMatrix W)) ∧
    (∫ M, f M ∂(albertChartRayMeasure.map (projectedMatrix W))) = _
  constructor
  · rw [integrable_map_measure hf.aestronglyMeasurable hp, hcomp]
    exact (h t ht).1
  · rw [integral_map hp hf.aestronglyMeasurable]
    change (∫ X, (f ∘ projectedMatrix W) X ∂albertChartRayMeasure) = _
    rw [hcomp, (h t ht).2, hn]

/-- The normalized octonionic chart sampling law is exactly the unique
invariant Borel probability on the native Albert atoms. -/
theorem existsUnique_invariantAlbertAtomProbability :
    ∃! μ : Measure Albert, IsProbabilityMeasure μ ∧
      (∀ᵐ p ∂μ, IsAtom p) ∧
      ∀ g : NativeAlbertAutomorphism, μ.map g.linearEquiv = μ := by
  refine ⟨albertChartAtomMeasure, ⟨inferInstance, ae_albertChartAtomMeasure_isAtom,
    map_nativeAutomorphism_albertChartAtomMeasure⟩, ?_⟩
  intro μ hμ
  have : IsProbabilityMeasure μ := hμ.1
  exact invariantAlbertAtomMeasure_unique μ albertChartAtomMeasure hμ.2.1
    ae_albertChartAtomMeasure_isAtom hμ.2.2 map_nativeAutomorphism_albertChartAtomMeasure

/-- The complement of the first affine chart is null for the native
invariant atom law. -/
theorem ae_albertChartAtomMeasure_firstDiagonal_pos :
    ∀ᵐ p ∂albertChartAtomMeasure, 0 < p.1 0 := by
  have hc : Continuous (fun p : Albert => p.1 0) :=
    (continuous_apply 0).comp (continuous_fst : Continuous (fun p : Albert => p.1))
  have hdiag : Measurable (fun p : Albert => p.1 0) := hc.measurable
  rw [albertChartAtomMeasure, ae_map_iff
    (measurable_normalizeAlbert.comp measurable_sampleAlbertChartRay).aemeasurable
    (measurableSet_lt measurable_const hdiag)]
  filter_upwards [ae_albertChartSamplingMeasure_positive_ray] with p hp
  let u := (√p.1)⁻¹ • octonionChartCoordinates p.2.1
  let w := (√p.1)⁻¹ • octonionChartCoordinates p.2.2
  have hd := chartDyad_trace_pos u w
  change 0 < (albertTrace (p.1 • chartDyad u w))⁻¹ * (p.1 * octNormSq octOne)
  rw [albertTrace_smul, octNormSq_one]
  positivity

end AlbertSequential.WindowProbability
