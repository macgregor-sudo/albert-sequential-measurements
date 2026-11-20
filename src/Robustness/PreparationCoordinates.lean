/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.PreparationHull
public import NativeHankelRank
public import ThreeAtomAndFourPoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite native word coordinates for the state associated to a preparation. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.PreparationHull

open NativeAnalysis Filter SharpDisturbance
open scoped Topology

variable {I : Type*}

/-- A generating atomic menu admits 27 actual word readouts which linearly determine the
entire native operator. -/
theorem exists_native_word_coordinates (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : GeneratesAlbert p) :
    ∃ w : Fin 27 → Word I, ∃ e : Albert ≃ₗ[ℝ] (Fin 27 → ℝ),
      ∀ ρ i, e ρ i = nativeWordProbability p ρ (w i) := by
  let : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional
  obtain ⟨w, hw⟩ := exists_independent_native_word_effects p hp hg
  have hspan : Submodule.span ℝ (Set.range fun i => nativeWordEffect p (w i)) = ⊤ :=
    hw.span_eq_top_of_card_eq_finrank (by simp [native_finrank])
  let L : Albert →ₗ[ℝ] (Fin 27 → ℝ) :=
    LinearMap.pi fun i =>
      { toFun := fun ρ => nativeWordProbability p ρ (w i)
        map_add' := fun x y => nativeWordProbability_add p x y (w i)
        map_smul' := fun r ρ => nativeWordProbability_smul p r ρ (w i) }
  have hL : Function.Injective L := by
    intro x y he
    let f := nativePairingFunctional (x - y)
    have hker : Submodule.span ℝ (Set.range fun i => nativeWordEffect p (w i)) ≤ f.ker := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      have hi := congrFun he i
      change nativeWordProbability p x (w i) = nativeWordProbability p y (w i) at hi
      rw [nativeWordProbability_eq_pairing, nativeWordProbability_eq_pairing] at hi
      change tracePairing (x - y) (nativeWordEffect p (w i)) = 0
      rw [tracePairing_sub_left, hi, sub_self]
    have hd : x - y ∈ Submodule.span ℝ (Set.range fun i => nativeWordEffect p (w i)) := by
      rw [hspan]
      exact Submodule.mem_top
    have hz := hker hd
    change tracePairing (x - y) (x - y) = 0 at hz
    exact sub_eq_zero.mp ((tracePairing_self_eq_zero _).mp hz)
  have hdim : Module.finrank ℝ Albert = Module.finrank ℝ (Fin 27 → ℝ) := by
    rw [native_finrank, Module.finrank_fintype_fun_eq_card]
    simp
  refine ⟨w, LinearMap.linearEquivOfInjective L hL hdim, ?_⟩
  intro ρ i
  rfl

/-- The four tests in the positive-invariant disturbance theorem admit the finite native
word coordinates used to identify their associated preparation state. -/
theorem exists_native_word_coordinates_of_positive_invariant (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (h : 0 < fourPointInvariant p) :
    ∃ w : Fin 27 → Word (Fin 4), ∃ e : Albert ≃ₗ[ℝ] (Fin 27 → ℝ),
      ∀ ρ i, e ρ i = nativeWordProbability p ρ (w i) :=
  exists_native_word_coordinates p hp ((fourPointInvariant_pos_iff p hp).mp h)

local instance : IsTopologicalAddGroup Octonion :=
  inferInstanceAs (IsTopologicalAddGroup (Quaternion ℝ × Quaternion ℝ))
local instance : ContinuousSMul ℝ Octonion :=
  inferInstanceAs (ContinuousSMul ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : IsTopologicalAddGroup Albert :=
  inferInstanceAs (IsTopologicalAddGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : ContinuousSMul ℝ Albert :=
  inferInstanceAs (ContinuousSMul ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

/-- Convergence of matching physical preparations in trace norm implies convergence of their
native representatives, by the finite actual word coordinates. -/
theorem native_representative_tendsto_of_traceNorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : I → Albert) (w : Fin 27 → Word I) (e : Albert ≃ₗ[ℝ] (Fin 27 → ℝ))
    (he : ∀ ρ i, e ρ i = nativeWordProbability p ρ (w i))
    (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E) (traceNorm : E → ℝ)
    (hlip : ∀ x y u, |tr (wordMap F u x) - tr (wordMap F u y)| ≤ traceNorm (x - y))
    (x : ℕ → E) (z : E) (ρn : ℕ → Albert) (ρ : Albert)
    (htrace : Tendsto (fun n => traceNorm (x n - z)) atTop (𝓝 0))
    (hseq : ∀ n i, tr (wordMap F (w i) (x n)) = nativeWordProbability p (ρn n) (w i))
    (hlim : ∀ i, tr (wordMap F (w i) z) = nativeWordProbability p ρ (w i)) :
    Tendsto ρn atTop (𝓝 ρ) := by
  have hcoord : Tendsto (fun n => e (ρn n)) atTop (𝓝 (e ρ)) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg) _ htrace
    intro n
    rw [Real.dist_eq, he, he, ← hseq n i, ← hlim i]
    exact hlip (x n) z (w i)
  have hc : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  have ht := hc.continuousAt.tendsto.comp hcoord
  change Tendsto (fun n => e.symm (e (ρn n))) atTop (𝓝 (e.symm (e ρ))) at ht
  simpa only [LinearEquiv.symm_apply_apply] using ht

end AlbertSequential.PreparationHull
