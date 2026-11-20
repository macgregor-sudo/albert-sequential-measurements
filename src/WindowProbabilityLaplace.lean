/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Local exponential-transform uniqueness, for comparing the finite tilted
rank-one law and the complex Gram law in companion Proposition 5.1. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-- Equality near the origin on the real axis suffices at the imaginary point `I`.
The integrability hypotheses ensure the identities concern actual transforms. -/
theorem complexMGF_I_eq_of_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ ν : Measure Ω) {ε : ℝ} (hε : 0 < ε)
    (hμ : Ioo (-ε) ε ⊆ integrableExpSet X μ)
    (hν : Ioo (-ε) ε ⊆ integrableExpSet X ν)
    (h : EqOn (mgf X μ) (mgf X ν) (Ioo (-ε) ε)) :
    complexMGF X μ I = complexMGF X ν I := by
  let strip : Set ℂ := reLm ⁻¹' Ioo (-ε) ε
  have am : AnalyticOnNhd ℂ (complexMGF X μ) strip :=
    analyticOnNhd_complexMGF.mono fun _ hz => interior_maximal hμ isOpen_Ioo hz
  have an : AnalyticOnNhd ℂ (complexMGF X ν) strip :=
    analyticOnNhd_complexMGF.mono fun _ hz => interior_maximal hν isOpen_Ioo hz
  have hp : IsPreconnected strip := ((convex_Ioo (-ε) ε).linear_preimage reLm).isPreconnected
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have h0c : (0 : ℂ) ∈ strip := by simpa [strip] using h0
  have hIc : I ∈ strip := by simpa [strip] using h0
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-ε) ε := isOpen_Ioo.mem_nhds h0
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Ioo (-ε) ε := hmem.filter_mono nhdsWithin_le_nhds
  have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0,
      complexMGF X μ (t : ℂ) = complexMGF X ν (t : ℂ) :=
    (hnear.mono fun t ht => by
      simpa only [complexMGF_ofReal] using congrArg Complex.ofReal (h ht)).frequently
  have hcoe : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, complexMGF X μ z = complexMGF X ν z :=
    hcoe.frequently hreal
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq am an hp h0c hfreq hIc

/-- Finite measures are equal if all their one-dimensional transforms agree
on genuine convergence intervals about zero. The interval may depend on the direction. -/
theorem measure_eq_of_local_exponential_transforms {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ L : StrongDual ℝ E, ∃ ε > 0,
      Ioo (-ε) ε ⊆ integrableExpSet (fun x => L x) μ ∧
      Ioo (-ε) ε ⊆ integrableExpSet (fun x => L x) ν ∧
      EqOn (mgf (fun x => L x) μ) (mgf (fun x => L x) ν) (Ioo (-ε) ε)) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  obtain ⟨ε, hε, hμ, hν, heq⟩ := h L
  have hi := complexMGF_I_eq_of_local_mgf (fun x => L x) μ ν hε hμ hν heq
  simpa only [charFunDual_apply, complexMGF, mul_comm I] using hi

end AlbertSequential.WindowProbability
