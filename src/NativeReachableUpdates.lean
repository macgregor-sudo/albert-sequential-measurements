/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeReachableCone

/-! Every outcome map preserves the closed reachable cone, including zero
branches. This conclusion even holds without idempotence of the menu. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

local instance : IsTopologicalAddGroup Octonion :=
  inferInstanceAs (IsTopologicalAddGroup (Quaternion ℝ × Quaternion ℝ))
local instance : ContinuousSMul ℝ Octonion :=
  inferInstanceAs (ContinuousSMul ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : IsTopologicalAddGroup Albert :=
  inferInstanceAs (IsTopologicalAddGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : ContinuousSMul ℝ Albert :=
  inferInstanceAs (ContinuousSMul ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem native_reachable_outcome_in_cone {X : Type*} (p : X → Albert) (a : Outcome X)
    {ρ : Albert} (hρ : ρ ∈ nativeReachableStates p) :
    quadraticMap (nativeOutcome p a) ρ ∈ stateSpaceCone (nativeReachableStateSpace p) := by
  rcases hρ with ⟨w, ht, rfl⟩
  let z := nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w
  let z' := nativeBranchState p ((1 / 3 : ℝ) • albertUnit) (w ++ [a])
  have heq : quadraticMap (nativeOutcome p a) z = z' := by
    dsimp [z, z']
    rw [nativeBranchState_append]
    rfl
  have hpos : IsPositive z' :=
    nativeBranchState_positive p _ native_maximally_mixed_density.1 _
  have ht' : 0 ≤ albertTrace z' := isPositive_trace_nonnegative _ hpos
  change quadraticMap (nativeOutcome p a) ((albertTrace z)⁻¹ • z) ∈ _
  rw [quadraticMap_smul_right, heq]
  by_cases hz : albertTrace z' = 0
  · have hz' := (isPositive_trace_eq_zero z' hpos).mp hz
    rw [hz', smul_zero]
    exact stateSpaceCone_zero (native_reachableStateSpace_nonempty p)
  · have hpositive : 0 < albertTrace z' := lt_of_le_of_ne ht' (Ne.symm hz)
    have hnorm : (albertTrace z')⁻¹ • z' ∈ nativeReachableStates p :=
      ⟨w ++ [a], hpositive, rfl⟩
    refine ⟨(albertTrace z)⁻¹ * albertTrace z', (albertTrace z')⁻¹ • z',
      mul_nonneg (inv_nonneg.mpr ht.le) ht', native_reachable_mem_stateSpace p hnorm, ?_⟩
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hz, mul_one]

theorem native_stateSpace_outcome_in_cone {X : Type*} (p : X → Albert) (a : Outcome X)
    {ρ : Albert} (hρ : ρ ∈ nativeReachableStateSpace p) :
    quadraticMap (nativeOutcome p a) ρ ∈ stateSpaceCone (nativeReachableStateSpace p) := by
  let K := stateSpaceCone (nativeReachableStateSpace p)
  let L := quadraticMapLinear (nativeOutcome p a)
  have hconv : Convex ℝ (L ⁻¹' K) := (native_reachableCone_convex p).linear_preimage L
  have hcontinuous : Continuous L := by
    change Continuous (fun z : Albert => quadraticMap (nativeOutcome p a) z)
    have hc : Continuous (fun z : Albert => (nativeOutcome p a, z)) :=
      (continuous_const : Continuous (fun _ : Albert => nativeOutcome p a)).prodMk continuous_id
    simpa only [Function.comp_def] using continuous_quadraticMap.comp hc
  have hclosed : IsClosed (L ⁻¹' K) := (native_reachableCone_closed p).preimage hcontinuous
  have hsub : nativeReachableStates p ⊆ L ⁻¹' K :=
    fun _ h => native_reachable_outcome_in_cone p a h
  exact (closure_minimal (convexHull_min hsub hconv) hclosed) hρ

theorem native_reachableCone_outcome {X : Type*} (p : X → Albert) (a : Outcome X)
    {z : Albert} (hz : z ∈ stateSpaceCone (nativeReachableStateSpace p)) :
    quadraticMap (nativeOutcome p a) z ∈ stateSpaceCone (nativeReachableStateSpace p) := by
  rcases hz with ⟨t, ρ, ht, hρ, rfl⟩
  rw [quadraticMap_smul_right]
  exact stateSpaceCone_smul (native_stateSpace_outcome_in_cone p a hρ) ht

end AlbertSequential
