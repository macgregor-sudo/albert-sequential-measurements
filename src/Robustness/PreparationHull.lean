/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.SharpDisturbance
public import NativeReachableDensity
public import NativeWordPurity
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The normalized preparations and the compact native image of their trace-norm hull. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.PreparationHull

open Filter NativeAnalysis SharpDisturbance
open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual positive-mass chronological outputs from the single prescribed initial state. -/
def preparedStates (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E) (initial : E) : Set E :=
  {z | ∃ v : Word I, 0 < tr (wordMap F v initial) ∧
    z = (tr (wordMap F v initial))⁻¹ • wordMap F v initial}

/-- The trace-norm closure of the real convex hull, in its epsilon-ball form. -/
def traceNormPreparationHull (traceNorm : E → ℝ) (tr : E →ₗ[ℝ] ℝ)
    (F : Outcome I → E →ₗ[ℝ] E) (initial : E) : Set E :=
  {z | ∀ ε : ℝ, 0 < ε → ∃ y ∈ convexHull ℝ (preparedStates tr F initial), traceNorm (y - z) < ε}

/-- With the corresponding norm topology, the epsilon-ball definition is the ordinary closure. -/
theorem traceNormPreparationHull_eq_closure {G : Type*} [NormedAddCommGroup G] [Module ℝ G]
    (traceNorm : G → ℝ) (tr : G →ₗ[ℝ] ℝ) (F : Outcome I → G →ₗ[ℝ] G) (initial : G)
    (hn : ∀ x : G, traceNorm x = ‖x‖) :
    traceNormPreparationHull traceNorm tr F initial = closure (convexHull ℝ (preparedStates tr F initial)) := by
  ext z
  rw [Metric.mem_closure_iff]
  constructor <;> intro hz ε hε
  · obtain ⟨y, hy, hd⟩ := hz ε hε
    refine ⟨y, hy, ?_⟩
    rwa [dist_comm, dist_eq_norm, ← hn]
  · obtain ⟨y, hy, hd⟩ := hz ε hε
    refine ⟨y, hy, ?_⟩
    rwa [hn, ← dist_eq_norm, dist_comm]

def wordProfile (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E) : E →ₗ[ℝ] (Word I → ℝ) :=
  LinearMap.pi fun w => tr.comp (wordMap F w)

def nativeWordProfile (p : I → Albert) : Albert →ₗ[ℝ] (Word I → ℝ) where
  toFun ρ := nativeWordProbability p ρ
  map_add' x y := funext (nativeWordProbability_add p x y)
  map_smul' r x := funext (nativeWordProbability_smul p r x)

theorem wordMap_append (F : Outcome I → E →ₗ[ℝ] E) (v w : Word I) (x : E) :
    wordMap F (v ++ w) x = wordMap F w (wordMap F v x) := by
  induction v generalizing x with
  | nil => rfl
  | cons q v ih => exact ih (F q x)

theorem initial_mem_preparedStates (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E)
    (initial : E) (h : tr initial = 1) : initial ∈ preparedStates tr F initial := by
  refine ⟨[], ?_, ?_⟩
  · change 0 < tr initial
    rw [h]
    norm_num
  · change initial = (tr initial)⁻¹ • initial
    rw [h, inv_one, one_smul]

theorem prepared_trace_one (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E) (initial : E)
    {z : E} (hz : z ∈ preparedStates tr F initial) : tr z = 1 := by
  obtain ⟨v, hv, rfl⟩ := hz
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv.ne']

theorem prepared_native_table (p : I → Albert) (tr : E →ₗ[ℝ] ℝ)
    (F : Outcome I → E →ₗ[ℝ] E) (initial : E)
    (hmatch : ∀ w, tr (wordMap F w initial) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    {z : E} (hz : z ∈ preparedStates tr F initial) :
    ∃ ρ ∈ nativeReachableStates p, ∀ w, tr (wordMap F w z) = nativeWordProbability p ρ w := by
  obtain ⟨v, hv, rfl⟩ := hz
  let e3 := (1 / 3 : ℝ) • albertUnit
  let Z := nativeBranchState p e3 v
  have hZ : tr (wordMap F v initial) = albertTrace Z := hmatch v
  refine ⟨(albertTrace Z)⁻¹ • Z, ⟨v, hZ ▸ hv, rfl⟩, fun w => ?_⟩
  have happend : nativeWordProbability p Z w = nativeWordProbability p e3 (v ++ w) := by
    change albertTrace (nativeBranchState p (nativeBranchState p e3 v) w) =
      albertTrace (nativeBranchState p e3 (v ++ w))
    rw [nativeBranchState_append]
  rw [map_smul, map_smul, smul_eq_mul, ← wordMap_append F v w initial, hmatch (v ++ w), hZ,
    nativeWordProbability_smul p (albertTrace Z)⁻¹ Z w, happend]

/-- A state in the physical trace-norm preparation hull has the entire word table of one
native state in the compact convex reachable state space. -/
theorem native_table_of_mem_traceNormPreparationHull (p : I → Albert) (tr : E →ₗ[ℝ] ℝ)
    (F : Outcome I → E →ₗ[ℝ] E) (initial : E) (traceNorm : E → ℝ)
    (hmatch : ∀ w, tr (wordMap F w initial) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hlip : ∀ x y w, |tr (wordMap F w x) - tr (wordMap F w y)| ≤ traceNorm (x - y))
    {z : E} (hz : z ∈ traceNormPreparationHull traceNorm tr F initial) :
    ∃ ρ ∈ nativeReachableStateSpace p, ∀ w, tr (wordMap F w z) = nativeWordProbability p ρ w := by
  let P := wordProfile tr F
  let N := nativeWordProfile p
  let K := N '' nativeReachableStateSpace p
  have hc : Convex ℝ K := (native_reachableStateSpace_convex p).linear_image N
  have hclosed : IsClosed K := ((native_reachableStateSpace_compact p).image
    (continuous_pi fun w => continuous_nativeWordProbability p w)).isClosed
  have hprep : preparedStates tr F initial ⊆ P ⁻¹' K := by
    intro x hx
    obtain ⟨ρ, hr, ht⟩ := prepared_native_table p tr F initial hmatch hx
    exact ⟨ρ, native_reachable_mem_stateSpace p hr, (funext ht).symm⟩
  have hhull := convexHull_min hprep (hc.linear_preimage P)
  have happrox (n : ℕ) : ∃ y ∈ convexHull ℝ (preparedStates tr F initial),
      traceNorm (y - z) < 1 / ((n : ℝ) + 1) := hz _ (by positivity)
  choose y hy hd using happrox
  have hlim : Tendsto (fun n => P (y n)) atTop (𝓝 (P z)) := by
    apply tendsto_pi_nhds.2
    intro w
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Real.dist_eq]
    exact (hlip (y n) z w).trans (hd n).le
  have hmem : P z ∈ closure K := mem_closure_of_tendsto hlim (.of_forall fun n => hhull (hy n))
  rw [hclosed.closure_eq] at hmem
  obtain ⟨ρ, hρ, h⟩ := hmem
  exact ⟨ρ, hρ, fun w => (congrFun h w).symm⟩

/-- Certainty in the physical preparation hull preserves every suffix readout. -/
theorem certainty_in_traceNormPreparationHull (p : I → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (tr : E →ₗ[ℝ] ℝ)
    (F : Outcome I → E →ₗ[ℝ] E) (initial : E) (traceNorm : E → ℝ)
    (hmatch : ∀ w, tr (wordMap F w initial) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hlip : ∀ x y w, |tr (wordMap F w x) - tr (wordMap F w y)| ≤ traceNorm (x - y))
    {z : E} (hz : z ∈ traceNormPreparationHull traceNorm tr F initial)
    (q : Outcome I) (hq : tr (wordMap F [q] z) = 1) (u : Word I) :
    tr (wordMap F (q :: u) z) = tr (wordMap F u z) := by
  obtain ⟨ρ, hρ, ht⟩ := native_table_of_mem_traceNormPreparationHull p tr F initial traceNorm hmatch hlip hz
  have hc := (ht [q]).symm.trans hq
  rw [nativeWordProbability_eq_pairing, nativeWordEffect_singleton p hp] at hc
  have hf := native_reachable_certainty_ideality p hp q ρ hρ hc
  rw [ht (q :: u), ht u]
  change nativeWordProbability p (quadraticMap (nativeOutcome p q) ρ) u = nativeWordProbability p ρ u
  rw [hf]

/-- The physical trace norm controls each word readout using the actual positive/negative
decomposition and the trace decrease of every positive branch. -/
theorem word_readout_lipschitz_of_decomposition {C : Set E} (tr : E →ₗ[ℝ] ℝ)
    (F : Outcome I → E →ₗ[ℝ] E) (traceNorm : E → ℝ)
    (hn : ∀ x ∈ C, 0 ≤ tr x) (hp : ∀ q x, x ∈ C → F q x ∈ C)
    (hd : ∀ q x, x ∈ C → tr (F q x) ≤ tr x)
    (hdecomp : ∀ x : E, ∃ u ∈ C, ∃ v ∈ C, x = u - v ∧ tr u + tr v = traceNorm x)
    (x y : E) (w : Word I) : |tr (wordMap F w x) - tr (wordMap F w y)| ≤ traceNorm (x - y) := by
  obtain ⟨u, hu, v, hv, he, hn'⟩ := hdecomp (x - y)
  have hu' := word_trace_bounds tr hn F hp hd w hu
  have hv' := word_trace_bounds tr hn F hp hd w hv
  rw [← hn', ← map_sub tr, ← map_sub (wordMap F w), he, map_sub, map_sub, abs_le]
  exact ⟨by linarith [hu'.1, hv'.2, hn u hu], by linarith [hu'.2, hv'.1, hn v hv]⟩

end AlbertSequential.PreparationHull
