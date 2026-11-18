/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeSupport
public import NativeWordPositivity
public import Interfaces.OperationalBoundaries

/-! Positivity, normalization and certainty ideality on the ACTUAL closed convex
reachable state space; arbitrary idempotents include zero and the unit. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

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

theorem native_trace_unit : albertTrace albertUnit = 3 := by
  norm_num [albertTrace, albertUnit]

theorem native_maximally_mixed_density : IsDensity ((1 / 3 : ℝ) • albertUnit) := by
  constructor
  · exact isPositive_smul _ _ (by norm_num)
      (isPositive_idempotent _ (jordanMul_albertUnit_left albertUnit))
  · rw [albertTrace_smul, native_trace_unit]
    norm_num

theorem native_normalized_positive_density (z : Albert) (hz : IsPositive z)
    (ht : 0 < albertTrace z) : IsDensity ((albertTrace z)⁻¹ • z) := by
  constructor
  · exact isPositive_smul _ _ (inv_nonneg.mpr ht.le) hz
  · rw [albertTrace_smul, inv_mul_cancel₀ ht.ne']

theorem native_reachable_density {X : Type*} (p : X → Albert)
    {ρ : Albert} (hρ : ρ ∈ nativeReachableStates p) : IsDensity ρ := by
  rcases hρ with ⟨w, ht, rfl⟩
  exact native_normalized_positive_density _
    (nativeBranchState_positive p _ native_maximally_mixed_density.1 w) ht

theorem native_reachableStateSpace_density {X : Type*} (p : X → Albert)
    {ρ : Albert} (hρ : ρ ∈ nativeReachableStateSpace p) : IsDensity ρ := by
  have hsub : convexHull ℝ (nativeReachableStates p) ⊆ {x | IsDensity x} :=
    convexHull_min (fun _ h => native_reachable_density p h) convex_density_set
  exact (closure_minimal hsub isCompact_density_set.isClosed) hρ

theorem native_maximally_mixed_reachable {X : Type*} (p : X → Albert) :
    (1 / 3 : ℝ) • albertUnit ∈ nativeReachableStates p := by
  refine ⟨[], ?_, ?_⟩
  · change (0 : ℝ) < albertTrace ((1 / 3 : ℝ) • albertUnit)
    rw [native_maximally_mixed_density.2]
    norm_num
  · change (1 / 3 : ℝ) • albertUnit =
      (albertTrace ((1 / 3 : ℝ) • albertUnit))⁻¹ • ((1 / 3 : ℝ) • albertUnit)
    rw [native_maximally_mixed_density.2, inv_one, one_smul]

theorem native_reachable_mem_stateSpace {X : Type*} (p : X → Albert)
    {ρ : Albert} (hρ : ρ ∈ nativeReachableStates p) : ρ ∈ nativeReachableStateSpace p :=
  subset_closure (subset_convexHull ℝ _ hρ)

theorem native_reachableStateSpace_nonempty {X : Type*} (p : X → Albert) :
    (nativeReachableStateSpace p).Nonempty :=
  ⟨_, native_reachable_mem_stateSpace p (native_maximally_mixed_reachable p)⟩

theorem native_reachableStateSpace_convex {X : Type*} (p : X → Albert) :
    Convex ℝ (nativeReachableStateSpace p) := (convex_convexHull ℝ _).closure

theorem native_reachableStateSpace_compact {X : Type*} (p : X → Albert) :
    IsCompact (nativeReachableStateSpace p) :=
  isCompact_density_set.of_isClosed_subset isClosed_closure
    (fun _ h => native_reachableStateSpace_density p h)

theorem native_reachable_certainty_ideality {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (a : Outcome X) (ρ : Albert)
    (hρ : ρ ∈ nativeReachableStateSpace p) (hc : tracePairing ρ (nativeOutcome p a) = 1) :
    quadraticMap (nativeOutcome p a) ρ = ρ :=
  native_idempotent_certainty_ideality _ _ (nativeOutcome_idempotent p hp a)
    (native_reachableStateSpace_density p hρ) hc

end AlbertSequential
