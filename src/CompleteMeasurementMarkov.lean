/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHankelRank
public import NativeReachableDensity

/-! Complete THREE-outcome frame measurements, not binary no-updates, have an
exact finite classical model. No mutual-unbiased-bases existence is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators

abbrev FrameOutcome (m : ℕ) := Fin m × Fin 3
abbrev FrameMemory (m : ℕ) := Option (FrameOutcome m)

def frameAtom {m : ℕ} (F : Fin m → NativeJordanFrame) (a : FrameOutcome m) : Albert :=
  (F a.1).atom a.2

theorem frameAtom_isAtom {m : ℕ} (F : Fin m → NativeJordanFrame) (a : FrameOutcome m) :
    IsAtom (frameAtom F a) := (F a.1).atoms a.2

def completeMeasurementProbability {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (w : List (FrameOutcome m)) : ℝ :=
  nativeWordProbability (frameAtom F) ρ (w.map (fun a => (a, true)))

def frameTransitionProduct {m : ℕ} (F : Fin m → NativeJordanFrame) :
    FrameOutcome m → List (FrameOutcome m) → ℝ
  | _, [] => 1
  | a, b :: w => tracePairing (frameAtom F a) (frameAtom F b) * frameTransitionProduct F b w

theorem completeMeasurementProbability_cons {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (a : FrameOutcome m) (w : List (FrameOutcome m)) :
    completeMeasurementProbability F ρ (a :: w) = tracePairing ρ (frameAtom F a) *
      completeMeasurementProbability F (frameAtom F a) w := by
  change nativeWordProbability (frameAtom F)
    (quadraticMap (frameAtom F a) ρ) (w.map (fun b => (b, true))) = _
  rw [quadraticMap_atom _ _ (frameAtom_isAtom F a), nativeWordProbability_smul,
    tracePairing_comm]
  rfl

theorem completeMeasurementProbability_product {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (a : FrameOutcome m) (w : List (FrameOutcome m)) :
    completeMeasurementProbability F ρ (a :: w) =
      tracePairing ρ (frameAtom F a) * frameTransitionProduct F a w := by
  induction w generalizing a ρ with
  | nil =>
      rw [completeMeasurementProbability_cons]
      change _ * albertTrace (frameAtom F a) = _ * 1
      rw [(frameAtom_isAtom F a).2]
  | cons b w ih =>
      rw [completeMeasurementProbability_cons, ih]
      rfl

theorem completeMeasurementProbability_nil {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) : completeMeasurementProbability F ρ [] = 1 := hρ.2

def frameMemoryState {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert) :
    FrameMemory m → Albert
  | none => ρ
  | some a => frameAtom F a

theorem frameMemoryState_density {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (h : FrameMemory m) : IsDensity (frameMemoryState F ρ h) := by
  cases h with
  | none => exact hρ
  | some a => exact ⟨isPositive_idempotent _ ((F a.1).atoms a.2).1, ((F a.1).atoms a.2).2⟩

def frameClassicalInitial (m : ℕ) : FrameMemory m → ℝ := fun h => if h = none then 1 else 0

def frameClassicalUpdate {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert)
    (a : FrameOutcome m) (μ : FrameMemory m → ℝ) : FrameMemory m → ℝ :=
  fun h' => if h' = some a then
    ∑ h, μ h * tracePairing (frameMemoryState F ρ h) (frameAtom F a) else 0

def frameClassicalEncoding {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert)
    (μ : FrameMemory m → ℝ) : Albert := ∑ h, μ h • frameMemoryState F ρ h

def frameClassicalUpdateLinear {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert)
    (a : FrameOutcome m) : (FrameMemory m → ℝ) →ₗ[ℝ] (FrameMemory m → ℝ) where
  toFun := frameClassicalUpdate F ρ a
  map_add' μ ν := by
    funext h'
    by_cases h : h' = some a <;>
      simp [frameClassicalUpdate, h, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r μ := by
    funext h'
    by_cases h : h' = some a <;>
      simp [frameClassicalUpdate, h, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]

theorem frameMemory_card (m : ℕ) : Fintype.card (FrameMemory m) = 3 * m + 1 := by
  simp [FrameMemory, FrameOutcome, Fintype.card_option, Fintype.card_prod]
  omega

theorem frameClassicalInitial_nonneg (m : ℕ) (h : FrameMemory m) :
    0 ≤ frameClassicalInitial m h := by simp [frameClassicalInitial]; split_ifs <;> norm_num

theorem frameClassicalInitial_sum (m : ℕ) : ∑ h, frameClassicalInitial m h = 1 := by
  simp [frameClassicalInitial]

theorem frameClassicalEncoding_initial {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert) :
    frameClassicalEncoding F ρ (frameClassicalInitial m) = ρ := by
  simp [frameClassicalEncoding, frameClassicalInitial, frameMemoryState]

theorem frameClassicalUpdate_nonneg {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (a : FrameOutcome m) (μ : FrameMemory m → ℝ)
    (hμ : ∀ h, 0 ≤ μ h) (h' : FrameMemory m) : 0 ≤ frameClassicalUpdate F ρ a μ h' := by
  simp only [frameClassicalUpdate]
  split_ifs
  · exact Finset.sum_nonneg fun h _ => mul_nonneg (hμ h)
      (tracePairing_positive_nonnegative _ _ (frameMemoryState_density F ρ hρ h).1
        (isPositive_idempotent _ ((F a.1).atoms a.2).1))
  · exact le_rfl

theorem tracePairing_frame_sum {m : ℕ} (F : Fin m → NativeJordanFrame) (j : Fin m)
    (x : Albert) : ∑ a : Fin 3, tracePairing x ((F j).atom a) = albertTrace x := by
  have h := map_sum (nativePairingFunctional x) (fun a : Fin 3 => (F j).atom a) Finset.univ
  change tracePairing x (∑ a, (F j).atom a) = ∑ a, tracePairing x ((F j).atom a) at h
  rw [(F j).sum_unit, tracePairing_unit_right] at h
  exact h.symm

theorem frameClassicalUpdate_sum {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (j : Fin m) (μ : FrameMemory m → ℝ) :
    (∑ a : Fin 3, ∑ h', frameClassicalUpdate F ρ (j, a) μ h') = ∑ h, μ h := by
  simp only [frameClassicalUpdate, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  congr 1
  funext h
  rw [← Finset.mul_sum]
  change μ h * (∑ a : Fin 3, tracePairing (frameMemoryState F ρ h) ((F j).atom a)) = μ h
  rw [tracePairing_frame_sum, (frameMemoryState_density F ρ hρ h).2, mul_one]

theorem frameClassicalEncoding_trace {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (μ : FrameMemory m → ℝ) :
    albertTrace (frameClassicalEncoding F ρ μ) = ∑ h, μ h := by
  change albertTrace (∑ h, μ h • frameMemoryState F ρ h) = _
  rw [← tracePairing_unit_right, tracePairing_sum_smul_left]
  simp only [tracePairing_unit_right, (frameMemoryState_density F ρ hρ _).2, mul_one]

theorem frameClassicalEncoding_update {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (a : FrameOutcome m) (μ : FrameMemory m → ℝ) :
    frameClassicalEncoding F ρ (frameClassicalUpdate F ρ a μ) =
      quadraticMap (frameAtom F a) (frameClassicalEncoding F ρ μ) := by
  rw [quadraticMap_atom _ _ (frameAtom_isAtom F a), tracePairing_comm]
  dsimp only [frameClassicalEncoding]
  rw [tracePairing_sum_smul_left]
  simp [frameClassicalEncoding, frameClassicalUpdate, frameMemoryState]

def frameClassicalWordState {m : ℕ} (F : Fin m → NativeJordanFrame) (ρ : Albert)
    (w : List (FrameOutcome m)) : FrameMemory m → ℝ :=
  w.foldl (fun μ a => frameClassicalUpdate F ρ a μ) (frameClassicalInitial m)

theorem frameClassicalWordState_nonneg {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (w : List (FrameOutcome m)) :
    ∀ h, 0 ≤ frameClassicalWordState F ρ w h := by
  induction w using List.reverseRecOn with
  | nil => exact frameClassicalInitial_nonneg m
  | append_singleton w a ih =>
      have heq : frameClassicalWordState F ρ (w ++ [a]) =
          frameClassicalUpdate F ρ a (frameClassicalWordState F ρ w) := by
        simp only [frameClassicalWordState, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [heq]
      exact frameClassicalUpdate_nonneg F ρ hρ a _ ih

theorem frameClassicalWordState_encoding {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (w : List (FrameOutcome m)) :
    frameClassicalEncoding F ρ (frameClassicalWordState F ρ w) =
      nativeBranchState (frameAtom F) ρ (w.map (fun a => (a, true))) := by
  induction w using List.reverseRecOn with
  | nil => exact frameClassicalEncoding_initial F ρ
  | append_singleton w a ih =>
      have heq : frameClassicalWordState F ρ (w ++ [a]) =
          frameClassicalUpdate F ρ a (frameClassicalWordState F ρ w) := by
        simp only [frameClassicalWordState, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [heq]
      rw [frameClassicalEncoding_update, ih, List.map_append, nativeBranchState_append]
      rfl

theorem frameClassicalWordProbability_eq {m : ℕ} (F : Fin m → NativeJordanFrame)
    (ρ : Albert) (hρ : IsDensity ρ) (w : List (FrameOutcome m)) :
    (∑ h, frameClassicalWordState F ρ w h) = completeMeasurementProbability F ρ w := by
  rw [← frameClassicalEncoding_trace F ρ hρ, frameClassicalWordState_encoding]
  rfl

end AlbertSequential
