/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeReachableDensity
public import Mathlib.Topology.Sequences

/-! The cone over a compact trace-one section is closed. Compact subsequences
avoid a choice of native norm and treat the zero-trace boundary uniformly. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis Filter
open scoped Topology

local instance : T2Space Octonion :=
  inferInstanceAs (T2Space (Quaternion ℝ × Quaternion ℝ))
local instance : T2Space Albert :=
  inferInstanceAs (T2Space ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : IsTopologicalAddGroup Octonion :=
  inferInstanceAs (IsTopologicalAddGroup (Quaternion ℝ × Quaternion ℝ))
local instance : ContinuousSMul ℝ Octonion :=
  inferInstanceAs (ContinuousSMul ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : IsTopologicalAddGroup Albert :=
  inferInstanceAs (IsTopologicalAddGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : ContinuousSMul ℝ Albert :=
  inferInstanceAs (ContinuousSMul ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FirstCountableTopology Octonion :=
  inferInstanceAs (FirstCountableTopology (Quaternion ℝ × Quaternion ℝ))
local instance : FirstCountableTopology Albert :=
  inferInstanceAs (FirstCountableTopology ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem stateSpaceCone_zero {C : Set Albert} (hC : C.Nonempty) :
    (0 : Albert) ∈ stateSpaceCone C := by
  obtain ⟨y, hy⟩ := hC
  exact ⟨0, y, le_rfl, hy, (zero_smul ℝ y).symm⟩

theorem stateSpaceCone_smul {C : Set Albert} {z : Albert}
    (hz : z ∈ stateSpaceCone C) {r : ℝ} (hr : 0 ≤ r) :
    r • z ∈ stateSpaceCone C := by
  rcases hz with ⟨t, y, ht, hy, rfl⟩
  exact ⟨r * t, y, mul_nonneg hr ht, hy, smul_smul r t y⟩

theorem stateSpaceCone_add {C : Set Albert} (hc : Convex ℝ C) (hne : C.Nonempty)
    {x z : Albert} (hx : x ∈ stateSpaceCone C) (hz : z ∈ stateSpaceCone C) :
    x + z ∈ stateSpaceCone C := by
  rcases hx with ⟨s, x, hs, hx, rfl⟩
  rcases hz with ⟨t, z, ht, hz, rfl⟩
  by_cases hzero : s + t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simpa only [hs0, ht0, zero_smul, add_zero] using stateSpaceCone_zero hne
  · have hst : 0 < s + t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hzero)
    refine ⟨s + t, (s / (s + t)) • x + (t / (s + t)) • z, hst.le,
      hc hx hz (div_nonneg hs hst.le) (div_nonneg ht hst.le) ?_, ?_⟩
    · field_simp
    · rw [smul_add, smul_smul, smul_smul]
      have h1 : (s + t) * (s / (s + t)) = s := by field_simp
      have h2 : (s + t) * (t / (s + t)) = t := by field_simp
      rw [h1, h2]

theorem stateSpaceCone_convex {C : Set Albert} (hc : Convex ℝ C) (hne : C.Nonempty) :
    Convex ℝ (stateSpaceCone C) := by
  intro x hx z hz a b ha hb hab
  exact stateSpaceCone_add hc hne (stateSpaceCone_smul hx ha) (stateSpaceCone_smul hz hb)

theorem isClosed_stateSpaceCone {C : Set Albert} (hC : IsCompact C)
    (htrace : ∀ y ∈ C, albertTrace y = 1) : IsClosed (stateSpaceCone C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro w z hw hz
  choose t y ht hy heq using hw
  have htr : ∀ n, albertTrace (w n) = t n := by
    intro n
    rw [heq n, albertTrace_smul, htrace _ (hy n), mul_one]
  have htl : Tendsto t atTop (𝓝 (albertTrace z)) := by
    have h := (continuous_albertTrace.tendsto z).comp hz
    simpa only [Function.comp_def, htr] using h
  have hnonneg : 0 ≤ albertTrace z := ge_of_tendsto htl (Eventually.of_forall ht)
  obtain ⟨y0, hy0, φ, hφ, hyl⟩ := hC.tendsto_subseq hy
  have hprod := (htl.comp hφ.tendsto_atTop).smul hyl
  have hwφ := hz.comp hφ.tendsto_atTop
  have hprod' : Tendsto (w ∘ φ) atTop (𝓝 ((albertTrace z) • y0)) := by
    simpa only [Function.comp_def, heq] using hprod
  exact ⟨albertTrace z, y0, hnonneg, hy0, tendsto_nhds_unique hwφ hprod'⟩

theorem native_reachableCone_closed {X : Type*} (p : X → Albert) :
    IsClosed (stateSpaceCone (nativeReachableStateSpace p)) :=
  isClosed_stateSpaceCone (native_reachableStateSpace_compact p)
    (fun _ h => (native_reachableStateSpace_density p h).2)

theorem native_reachableCone_convex {X : Type*} (p : X → Albert) :
    Convex ℝ (stateSpaceCone (nativeReachableStateSpace p)) :=
  stateSpaceCone_convex (native_reachableStateSpace_convex p)
    (native_reachableStateSpace_nonempty p)

end AlbertSequential
