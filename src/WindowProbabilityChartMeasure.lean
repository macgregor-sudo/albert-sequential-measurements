/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityChart
public import WindowProbabilityTransport
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! An explicit sampling measure on the native octonionic rank-one cone.
The chart is parameterized by a Gamma ray variable and two real Gaussian
coordinate vectors rescaled by the square root of that variable. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory ProbabilityTheory Set
open scoped AlbertSequential.WindowProbability NNReal

local instance : MeasurableSpace Octonion := borel Octonion
local instance : BorelSpace Octonion := ⟨rfl⟩
local instance : SecondCountableTopology Octonion :=
  inferInstanceAs (SecondCountableTopology (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

private theorem continuous_octChartNormSq : Continuous octNormSq := by
  have h : Continuous (fun x : Octonion =>
      Quaternion.normSq x.1 + Quaternion.normSq x.2) :=
    (Quaternion.continuous_normSq.comp continuous_fst).add
      (Quaternion.continuous_normSq.comp continuous_snd)
  apply h.congr
  intro x
  rw [octNormSq_eq_coords, Quaternion.normSq_def', Quaternion.normSq_def']
  ring

private theorem continuous_chartDyad : Continuous (fun p : Octonion × Octonion => chartDyad p.1 p.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun _ : Octonion × Octonion => octNormSq octOne)
      exact continuous_const
    · change Continuous (fun p : Octonion × Octonion => octNormSq p.1)
      exact continuous_octChartNormSq.comp continuous_fst
    · change Continuous (fun p : Octonion × Octonion => octNormSq p.2)
      exact continuous_octChartNormSq.comp continuous_snd
  · apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : Octonion × Octonion => octonionMul octOne (octonionConj p.1))
      simp_rw [octonionMul_one_left]
      exact NativeAnalysis.continuous_octonionConj.comp continuous_fst
    · change Continuous (fun p : Octonion × Octonion => octonionMul octOne (octonionConj p.2))
      simp_rw [octonionMul_one_left]
      exact NativeAnalysis.continuous_octonionConj.comp continuous_snd
    · change Continuous (fun p : Octonion × Octonion => octonionMul p.1 (octonionConj p.2))
      have hfst : Continuous (fun p : Octonion × Octonion => p.1) := continuous_fst
      exact NativeAnalysis.continuous_octonionMul.comp
        (hfst.prodMk (NativeAnalysis.continuous_octonionConj.comp continuous_snd))

/-- The real coordinates for a ray variable and the two octonionic entries. -/
abbrev AlbertChartSamplingSpace :=
  ℝ × ((Fin 8 → ℝ) × (Fin 8 → ℝ))

/-- The declared Gamma and Gaussian sampling measure for the native chart. -/
def albertChartSamplingMeasure : Measure AlbertChartSamplingSpace :=
  let g := Measure.pi fun _ : Fin 8 => gaussianReal 0 (1 / 2)
  (gammaMeasure 4 1).prod (g.prod g)

instance : IsProbabilityMeasure albertChartSamplingMeasure := by
  let := isProbabilityMeasure_gammaMeasure (a := 4) (r := 1) (by norm_num) zero_lt_one
  unfold albertChartSamplingMeasure
  infer_instance

theorem ae_albertChartSamplingMeasure_positive_ray :
    ∀ᵐ p ∂albertChartSamplingMeasure, 0 < p.1 := by
  have h0 : (gammaMeasure 4 1) (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio,
      lintegral_gammaPDF_of_nonpos le_rfl]
  have h1 : (gammaMeasure 4 1) ({0} : Set ℝ) = 0 := by
    rw [gammaMeasure]
    simp
  have hγ : ∀ᵐ t ∂gammaMeasure 4 1, 0 < t := by
    rw [ae_iff]
    have he : {t : ℝ | ¬0 < t} = Iio 0 ∪ {0} := by
      ext t
      simp only [mem_ofPred_eq, not_lt, mem_union, mem_Iio, mem_singleton_iff]
      exact le_iff_lt_or_eq
    rw [he]
    exact measure_union_null h0 h1
  unfold albertChartSamplingMeasure
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
  simpa only [Filter.eventually_const] using hγ

/-- The unnormalized native rank-one sample in the first affine chart. -/
def sampleAlbertChartRay (p : AlbertChartSamplingSpace) : Albert :=
  p.1 • chartDyad ((Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.1)
    ((Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.2)

theorem measurable_sampleAlbertChartRay : Measurable sampleAlbertChartRay := by
  have he : Continuous octonionChartCoordinates :=
    octonionChartCoordinates.toLinearMap.continuous_of_finiteDimensional
  have ht : Measurable (fun p : AlbertChartSamplingSpace => (Real.sqrt p.1)⁻¹) :=
    (Real.continuous_sqrt.measurable.comp measurable_fst).inv
  have hh : Measurable (fun p : AlbertChartSamplingSpace => p.1) := measurable_fst
  have hu : Measurable (fun p : AlbertChartSamplingSpace =>
      octonionChartCoordinates p.2.1) := he.measurable.comp measurable_snd.fst
  have hw : Measurable (fun p : AlbertChartSamplingSpace =>
      octonionChartCoordinates p.2.2) := he.measurable.comp measurable_snd.snd
  have hscaleO : Measurable (fun p : ℝ × Octonion => p.1 • p.2) :=
    (continuous_fst.smul continuous_snd).measurable
  have hscaleA : Measurable (fun p : ℝ × Albert => p.1 • p.2) :=
    (continuous_fst.smul continuous_snd).measurable
  have hp : Measurable (fun p : AlbertChartSamplingSpace =>
      ((Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.1,
       (Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.2)) :=
    (hscaleO.comp (ht.prodMk hu)).prodMk (hscaleO.comp (ht.prodMk hw))
  exact hscaleA.comp (hh.prodMk (continuous_chartDyad.measurable.comp hp))

/-- A normalized candidate atom measure from the native octonionic chart. -/
def albertChartAtomMeasure : Measure Albert :=
  albertChartSamplingMeasure.map (normalizeAlbert ∘ sampleAlbertChartRay)

instance : IsProbabilityMeasure albertChartAtomMeasure := by
  unfold albertChartAtomMeasure
  infer_instance

theorem ae_albertChartAtomMeasure_isAtom : ∀ᵐ p ∂albertChartAtomMeasure, IsAtom p := by
  rw [albertChartAtomMeasure, ae_map_iff
    (measurable_normalizeAlbert.comp measurable_sampleAlbertChartRay).aemeasurable measurableSet_atomSet]
  filter_upwards [ae_albertChartSamplingMeasure_positive_ray] with p hp
  let u := (Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.1
  let w := (Real.sqrt p.1)⁻¹ • octonionChartCoordinates p.2.2
  change IsAtom (normalizeAlbert (p.1 • chartDyad u w))
  unfold normalizeAlbert
  rw [albertTrace_smul, smul_smul]
  have hd : albertTrace (chartDyad u w) ≠ 0 := (chartDyad_trace_pos u w).ne'
  rw [show (p.1 * albertTrace (chartDyad u w))⁻¹ * p.1 =
      (albertTrace (chartDyad u w))⁻¹ by field_simp [hp.ne', hd]]
  exact chartDyad_normalize_isAtom u w

end AlbertSequential.WindowProbability
