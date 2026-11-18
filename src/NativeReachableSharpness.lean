/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeReachableUpdates
public import AffineEffectClosure

/-! Reachable-state sharpness for ALL affine operational effects. Finite-
dimensional affine closure is used without assuming continuity of the effect.
Every reachable branch is a positive summand of e/3 in the actual reachable cone. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

theorem native_idempotent_nonselective_e3 (q : Albert) (hq : jordanMul q q = q) :
    quadraticMap q ((1 / 3 : ℝ) • albertUnit) +
      quadraticMap (albertUnit - q) ((1 / 3 : ℝ) • albertUnit) =
        (1 / 3 : ℝ) • albertUnit := by
  rw [quadraticMap_smul_right, quadraticMap_smul_right,
    native_idempotent_quadratic_unit q hq,
    native_idempotent_quadratic_unit _ (native_idempotent_complement q hq)]
  module

theorem nativeOutcome_opposite {X : Type*} (p : X → Albert) (a : Outcome X) :
    nativeOutcome p (a.1, !a.2) = albertUnit - nativeOutcome p a := by
  rcases a with ⟨i, b⟩
  cases b
  · change p i = albertUnit - (albertUnit - p i)
    abel
  · rfl

theorem native_branch_complement_in_cone {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (w : Word X) :
    (1 / 3 : ℝ) • albertUnit - nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w ∈
      stateSpaceCone (nativeReachableStateSpace p) := by
  induction w using List.reverseRecOn with
  | nil =>
      change ((1 / 3 : ℝ) • albertUnit - (1 / 3 : ℝ) • albertUnit) ∈ _
      rw [sub_self]
      exact stateSpaceCone_zero (native_reachableStateSpace_nonempty p)
  | append_singleton w a ih =>
      let z := nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w
      have hfirst := native_reachableCone_outcome p a ih
      have hr0 : (1 / 3 : ℝ) • albertUnit ∈
          stateSpaceCone (nativeReachableStateSpace p) :=
        ⟨1, _, by norm_num, native_reachable_mem_stateSpace p (native_maximally_mixed_reachable p),
          (one_smul ℝ _).symm⟩
      have hsecond := native_reachableCone_outcome p (a.1, !a.2) hr0
      rw [nativeOutcome_opposite] at hsecond
      have hfix := native_idempotent_nonselective_e3 (nativeOutcome p a)
        (nativeOutcome_idempotent p hp a)
      have heq : (1 / 3 : ℝ) • albertUnit - quadraticMap (nativeOutcome p a) z =
          quadraticMap (nativeOutcome p a) ((1 / 3 : ℝ) • albertUnit - z) +
          quadraticMap (albertUnit - nativeOutcome p a) ((1 / 3 : ℝ) • albertUnit) := by
        calc
          _ = (quadraticMap (nativeOutcome p a) ((1 / 3 : ℝ) • albertUnit) +
              quadraticMap (albertUnit - nativeOutcome p a) ((1 / 3 : ℝ) • albertUnit)) -
              quadraticMap (nativeOutcome p a) z :=
            congrArg (fun v => v - quadraticMap (nativeOutcome p a) z) hfix.symm
          _ = _ := by rw [quadraticMap_sub_argument]; abel
      rw [nativeBranchState_append]
      change (1 / 3 : ℝ) • albertUnit - quadraticMap (nativeOutcome p a) z ∈ _
      rw [heq]
      exact stateSpaceCone_add (native_reachableStateSpace_convex p)
        (native_reachableStateSpace_nonempty p) hfirst hsecond

theorem affine_operational_zero_reachable {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (f : Albert → ℝ)
    (hf : IsAffineOperationalEffect (nativeReachableStateSpace p) f)
    (hzero : f ((1 / 3 : ℝ) • albertUnit) = 0) :
    ∀ ρ ∈ nativeReachableStates p, f ρ = 0 := by
  rintro ρ ⟨w, ht, hρ⟩
  let z := nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w
  have hρC : ρ ∈ nativeReachableStateSpace p :=
    native_reachable_mem_stateSpace p ⟨w, ht, hρ⟩
  obtain ⟨s, σ, hs, hσ, hcomp⟩ := native_branch_complement_in_cone p hp w
  have hz : z = (albertTrace z) • ρ := by
    rw [hρ, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hsum : albertTrace z + s = 1 := by
    have h := congrArg albertTrace hcomp
    rw [albertTrace_sub, native_maximally_mixed_density.2, albertTrace_smul,
      (native_reachableStateSpace_density p hσ).2, mul_one] at h
    linarith
  have heq : (albertTrace z) • ρ + (1 - albertTrace z) • σ =
      (1 / 3 : ℝ) • albertUnit := by
    have hsEq : 1 - albertTrace z = s := by linarith
    rw [hsEq, ← hz, ← hcomp]
    abel
  have h := hf.2 ρ hρC σ hσ (albertTrace z) ht.le (by linarith)
  rw [heq, hzero] at h
  have hρnonneg := (hf.1 ρ hρC).1
  have hσnonneg := (hf.1 σ hσ).1
  have : (albertTrace z) * f ρ = 0 := by nlinarith
  exact (mul_eq_zero.mp this).resolve_left ht.ne'

theorem affine_operational_zero_stateSpace {X : Type*} (p : X → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (f : Albert → ℝ)
    (hf : IsAffineOperationalEffect (nativeReachableStateSpace p) f)
    (hzero : f ((1 / 3 : ℝ) • albertUnit) = 0) :
    ∀ ρ ∈ nativeReachableStateSpace p, f ρ = 0 := by
  let C := nativeReachableStateSpace p
  let Z : Set Albert := {ρ | ρ ∈ C ∧ f ρ = 0}
  have hconv : Convex ℝ Z := by
    intro x hx y hy a b ha hb hab
    refine ⟨native_reachableStateSpace_convex p hx.1 hy.1 ha hb hab, ?_⟩
    have hbEq : 1 - a = b := by linarith
    have h := hf.2 x hx.1 y hy.1 a ha (by linarith)
    rw [hbEq, hx.2, hy.2, mul_zero, mul_zero, add_zero] at h
    exact h
  have hgen : nativeReachableStates p ⊆ Z := by
    intro ρ hρ
    exact ⟨native_reachable_mem_stateSpace p hρ,
      affine_operational_zero_reachable p hp f hf hzero ρ hρ⟩
  have hzeroHull : ∀ ρ ∈ convexHull ℝ (nativeReachableStates p), f ρ = 0 :=
    fun _ h => (convexHull_min hgen hconv h).2
  exact affine_zero_on_convex_closure (convex_convexHull ℝ _)
    ⟨_, subset_convexHull ℝ _ (native_maximally_mixed_reachable p)⟩ f hf.2 hzeroHull

end AlbertSequential
