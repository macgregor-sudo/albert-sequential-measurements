/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeReachableSharpness

/-! The literal reachable-state Id/Sh contract, for arbitrary idempotents and
all affine operational effects on the closed reachable state space. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

theorem native_idempotent_normalized_reachable {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (a : Outcome X)
    (ht : 0 < albertTrace (nativeOutcome p a)) :
    (albertTrace (nativeOutcome p a))⁻¹ • nativeOutcome p a ∈ nativeReachableStates p := by
  have hb : nativeBranchState p ((1 / 3 : ℝ) • albertUnit) [a] =
      (1 / 3 : ℝ) • nativeOutcome p a := by
    change quadraticMap (nativeOutcome p a) ((1 / 3 : ℝ) • albertUnit) = _
    rw [quadraticMap_smul_right,
      native_idempotent_quadratic_unit _ (nativeOutcome_idempotent p hp a)]
  refine ⟨[a], ?_, ?_⟩
  · rw [hb, albertTrace_smul]
    exact mul_pos (by norm_num) ht
  · rw [hb, albertTrace_smul, smul_smul]
    congr 1
    field_simp

theorem affine_effect_zero_from_certainty_faces {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (i : X) (f : Albert → ℝ)
    (hf : IsAffineOperationalEffect (nativeReachableStateSpace p) f)
    (hfaces : ∀ ρ ∈ nativeReachableStateSpace p,
      (tracePairing ρ (p i) = 0 ∨ tracePairing ρ (p i) = 1) → f ρ = 0) :
    f ((1 / 3 : ℝ) • albertUnit) = 0 := by
  have hr0 := native_reachable_mem_stateSpace p (native_maximally_mixed_reachable p)
  have hposp := isPositive_idempotent (p i) (hp i)
  have hposq := isPositive_idempotent (albertUnit - p i) (native_idempotent_complement _ (hp i))
  have htp := isPositive_trace_nonnegative _ hposp
  have htq := isPositive_trace_nonnegative _ hposq
  by_cases hzeroP : albertTrace (p i) = 0
  · have hp0 := (isPositive_trace_eq_zero _ hposp).mp hzeroP
    apply hfaces _ hr0 (Or.inl ?_)
    rw [hp0]
    change albertTrace (jordanMul _ 0) = 0
    rw [jordanMul_zero_right, albertTrace_zero]
  by_cases hzeroQ : albertTrace (albertUnit - p i) = 0
  · have hq0 := (isPositive_trace_eq_zero _ hposq).mp hzeroQ
    have hpe : p i = albertUnit := (sub_eq_zero.mp hq0).symm
    apply hfaces _ hr0 (Or.inr ?_)
    rw [hpe, tracePairing_unit_right, native_maximally_mixed_density.2]
  have hpPositive : 0 < albertTrace (p i) := lt_of_le_of_ne htp (Ne.symm hzeroP)
  have hqPositive : 0 < albertTrace (albertUnit - p i) := lt_of_le_of_ne htq (Ne.symm hzeroQ)
  let ρp := (albertTrace (p i))⁻¹ • p i
  let ρq := (albertTrace (albertUnit - p i))⁻¹ • (albertUnit - p i)
  have hρp : ρp ∈ nativeReachableStateSpace p := native_reachable_mem_stateSpace p
    (native_idempotent_normalized_reachable p hp (i, true) hpPositive)
  have hρq : ρq ∈ nativeReachableStateSpace p := native_reachable_mem_stateSpace p
    (native_idempotent_normalized_reachable p hp (i, false) hqPositive)
  have hpp : tracePairing (p i) (p i) = albertTrace (p i) := congrArg albertTrace (hp i)
  have hqp : tracePairing (albertUnit - p i) (p i) = 0 := by
    rw [tracePairing_sub_left, tracePairing_comm albertUnit (p i), tracePairing_unit_right,
      hpp, sub_self]
  have hfp : f ρp = 0 := hfaces _ hρp (Or.inr (by
    change tracePairing ((albertTrace (p i))⁻¹ • p i) (p i) = 1
    rw [tracePairing_smul_left, hpp, inv_mul_cancel₀ hzeroP]))
  have hfq : f ρq = 0 := hfaces _ hρq (Or.inl (by
    change tracePairing ((albertTrace (albertUnit - p i))⁻¹ • (albertUnit - p i)) (p i) = 0
    rw [tracePairing_smul_left, hqp, mul_zero]))
  have hsum : albertTrace (p i) + albertTrace (albertUnit - p i) = 3 := by
    rw [albertTrace_sub, native_trace_unit]
    ring
  have hcoefp : (albertTrace (p i) / 3) * (albertTrace (p i))⁻¹ = (1 / 3 : ℝ) := by
    field_simp
  have hcoefq : (1 - albertTrace (p i) / 3) * (albertTrace (albertUnit - p i))⁻¹ =
      (1 / 3 : ℝ) := by
    field_simp
    linarith
  have heq : (albertTrace (p i) / 3) • ρp + (1 - albertTrace (p i) / 3) • ρq =
      (1 / 3 : ℝ) • albertUnit := by
    dsimp [ρp, ρq]
    rw [smul_smul, smul_smul, hcoefp, hcoefq]
    module
  have h := hf.2 ρp hρp ρq hρq (albertTrace (p i) / 3)
    (div_nonneg htp (by norm_num)) (by linarith)
  rw [heq, hfp, hfq, mul_zero, mul_zero, add_zero] at h
  exact h

theorem native_reachable_sharpness {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (i : X) :
    ¬ ∃ (σ : Albert) (f : Albert → ℝ),
      σ ∈ nativeReachableStateSpace p ∧ IsAffineOperationalEffect (nativeReachableStateSpace p) f ∧
      f σ = 1 ∧ ∀ ρ ∈ nativeReachableStateSpace p,
        (tracePairing ρ (p i) = 0 ∨ tracePairing ρ (p i) = 1) → f ρ = 0 := by
  rintro ⟨σ, f, hσ, hf, hfσ, hfaces⟩
  have hzero := affine_effect_zero_from_certainty_faces p hp i f hf hfaces
  have h := affine_operational_zero_stateSpace p hp f hf hzero σ hσ
  rw [hfσ] at h
  norm_num at h

theorem nativeReachableIdealityObligations (X : Type*) : ReachableIdealityObligations X where
  states_are_density p _ ρ hρ := native_reachableStateSpace_density p hρ
  branch_linear p a := ⟨quadraticMapLinear (nativeOutcome p a), fun _ => rfl⟩
  branch_positive p _ a z hz := native_reachableCone_outcome p a hz
  normalized p hp i z := native_idempotent_instrument_trace (p i) z (hp i)
  ideality p hp a ρ hρ hc := native_reachable_certainty_ideality p hp a ρ hρ hc
  sharpness p hp i := native_reachable_sharpness p hp i

end AlbertSequential
