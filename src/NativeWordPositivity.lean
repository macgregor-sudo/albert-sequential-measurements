module

public import NativeSquareCone

/-! Native operational positivity for idempotent binary tests, including null
histories. All probabilities are unconditional; no history is discarded. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem complementary_idempotent (p : Albert) (hp : jordanMul p p = p) :
    jordanMul (albertUnit - p) (albertUnit - p) = albertUnit - p := by
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right, hp, sub_self, sub_zero]

theorem nativeOutcome_idempotent {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (a : Outcome ι) :
    jordanMul (nativeOutcome p a) (nativeOutcome p a) = nativeOutcome p a := by
  rcases a with ⟨i, b⟩
  cases b
  · exact complementary_idempotent (p i) (hp i)
  · exact hp i

theorem quadraticMap_unit_argument (a : Albert) :
    quadraticMap a albertUnit = jordanMul a a := by
  unfold quadraticMap
  rw [jordanMul_albertUnit_right, jordanMul_albertUnit_right]
  module

theorem albertTrace_quadraticMap (a x : Albert) :
    albertTrace (quadraticMap a x) = tracePairing (jordanMul a a) x := by
  rw [← tracePairing_unit_right, quadraticMap_self_adjoint,
    quadraticMap_unit_argument, tracePairing_comm]

theorem quadraticMap_sub_argument (a x y : Albert) :
    quadraticMap a (x - y) = quadraticMap a x - quadraticMap a y := by
  unfold quadraticMap
  simp only [jordanMul_sub_right, smul_sub]
  abel

theorem idempotent_nonselective_trace (p x : Albert) (hp : jordanMul p p = p) :
    albertTrace (quadraticMap p x + quadraticMap (albertUnit - p) x) = albertTrace x := by
  rw [albertTrace_add, albertTrace_quadraticMap, albertTrace_quadraticMap,
    hp, complementary_idempotent p hp, ← tracePairing_add_left, add_sub_cancel,
    tracePairing_comm, tracePairing_unit_right]

theorem quadraticMap_trace_bounds (p x : Albert)
    (hp : jordanMul p p = p) (hx : IsPositive x) :
    0 ≤ albertTrace (quadraticMap p x) ∧ albertTrace (quadraticMap p x) ≤ albertTrace x := by
  have hp0 := isPositive_idempotent p hp
  have hq0 := isPositive_idempotent (albertUnit - p) (complementary_idempotent p hp)
  rw [albertTrace_quadraticMap, hp]
  refine ⟨tracePairing_positive_nonnegative p x hp0 hx, ?_⟩
  have h := tracePairing_positive_nonnegative (albertUnit - p) x hq0 hx
  rw [tracePairing_sub_left, tracePairing_comm albertUnit x, tracePairing_unit_right] at h
  linarith

theorem nativeBranchState_positive {ι : Type*} (p : ι → Albert)
    (ρ : Albert) (hρ : IsPositive ρ)
    (w : Word ι) : IsPositive (nativeBranchState p ρ w) := by
  induction w generalizing ρ with
  | nil => exact hρ
  | cons a w ih =>
    rw [nativeBranchState_cons]
    exact ih _ (isPositive_quadraticMap _ _ hρ)

theorem nativeWordProbability_bounds {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (ρ : Albert) (hρ : IsPositive ρ)
    (w : Word ι) :
    0 ≤ nativeWordProbability p ρ w ∧ nativeWordProbability p ρ w ≤ albertTrace ρ := by
  induction w generalizing ρ with
  | nil => exact ⟨isPositive_trace_nonnegative ρ hρ, le_rfl⟩
  | cons a w ih =>
    change 0 ≤ nativeWordProbability p (quadraticMap (nativeOutcome p a) ρ) w ∧
      nativeWordProbability p (quadraticMap (nativeOutcome p a) ρ) w ≤ albertTrace ρ
    have ht := ih (quadraticMap (nativeOutcome p a) ρ)
      (isPositive_quadraticMap (nativeOutcome p a) ρ hρ)
    have hs := quadraticMap_trace_bounds (nativeOutcome p a) ρ (nativeOutcome_idempotent p hp a) hρ
    exact ⟨ht.1, ht.2.trans hs.2⟩

theorem nativeWordProbability_density_bounds {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (ρ : Albert) (hρ : IsDensity ρ)
    (w : Word ι) :
    0 ≤ nativeWordProbability p ρ w ∧ nativeWordProbability p ρ w ≤ 1 := by
  simpa only [hρ.2] using nativeWordProbability_bounds p hp ρ hρ.1 w

theorem nativeBranchState_zero {ι : Type*} (p : ι → Albert) (w : Word ι) :
    nativeBranchState p 0 w = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [nativeBranchState_cons, quadraticMap_zero_right]
    exact ih

theorem native_zero_probability_branch {ι : Type*} (p : ι → Albert)
    (ρ : Albert) (hρ : IsPositive ρ)
    (w : Word ι) (hw : nativeWordProbability p ρ w = 0) :
    nativeBranchState p ρ w = 0 :=
  (isPositive_trace_eq_zero _ (nativeBranchState_positive p ρ hρ w)).mp hw

/-- Only chronological extension is asserted; this does not delete a middle test. -/
theorem native_zero_probability_extension {ι : Type*} (p : ι → Albert)
    (ρ : Albert) (hρ : IsPositive ρ)
    (u v : Word ι) (hu : nativeWordProbability p ρ u = 0) :
    nativeWordProbability p ρ (u ++ v) = 0 := by
  unfold nativeWordProbability
  rw [nativeBranchState_append, native_zero_probability_branch p ρ hρ u hu,
    nativeBranchState_zero, albertTrace_zero]

theorem nativeWordEffect_positive_and_complement {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (w : Word ι) :
    IsPositive (nativeWordEffect p w) ∧ IsPositive (albertUnit - nativeWordEffect p w) := by
  induction w with
  | nil =>
    refine ⟨isPositive_idempotent albertUnit (jordanMul_albertUnit_left albertUnit), ?_⟩
    simpa only [nativeWordEffect, sub_self] using isPositive_zero
  | cons a w ih =>
    let q := nativeOutcome p a
    have hq : jordanMul q q = q := nativeOutcome_idempotent p hp a
    refine ⟨isPositive_quadraticMap q _ ih.1, ?_⟩
    have hcomp := isPositive_add (albertUnit - q)
      (quadraticMap q (albertUnit - nativeWordEffect p w))
      (isPositive_idempotent _ (complementary_idempotent q hq))
      (isPositive_quadraticMap q _ ih.2)
    rw [quadraticMap_sub_argument, quadraticMap_unit_argument, hq] at hcomp
    have heq : albertUnit - q + (q - quadraticMap q (nativeWordEffect p w)) =
        albertUnit - quadraticMap q (nativeWordEffect p w) := by abel
    rw [heq] at hcomp
    exact hcomp

end AlbertSequential.NativeAnalysis
