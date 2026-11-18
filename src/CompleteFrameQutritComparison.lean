/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritProjectiveStatistics

/-! The m≤4 mutually-unbiased clause of the COMPLETE-measurement theorem.
An actual family of qutrit projectors and the normalized state I/3 is built.
The conclusion compares literal chronological PXP folds for every word. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators Matrix ComplexOrder

theorem completeFrame_statistics_match_of_overlaps {m : ℕ} (F : Fin m → NativeJordanFrame)
    (v : FrameOutcome m → Fin 3 → ℂ)
    (hnorm : ∀ a, qutritInner (v a) (v a) = 1)
    (htransition : ∀ a b, Matrix.trace (qutritRankOneProjection (v a) * qutritRankOneProjection (v b)) =
      (tracePairing (frameAtom F a) (frameAtom F b) : ℂ))
    (ρ : Albert) (σ : ComplexMatrix3)
    (htrace : Matrix.trace σ = (albertTrace ρ : ℂ))
    (hinit : ∀ a, Matrix.trace (qutritRankOneProjection (v a) * σ) =
      (tracePairing ρ (frameAtom F a) : ℂ)) (w : List (FrameOutcome m)) :
    qutritCompleteTrace (fun a => qutritRankOneProjection (v a)) σ w =
      (completeMeasurementProbability F ρ w : ℂ) := by
  induction w generalizing ρ σ with
  | nil => exact htrace
  | cons a w ih =>
      rw [qutritCompleteTrace_cons, completeMeasurementProbability_cons, hinit a]
      have hchildTrace : Matrix.trace (qutritRankOneProjection (v a)) =
          (albertTrace (frameAtom F a) : ℂ) := by
        rw [qutritRankOneProjection_trace, hnorm, (frameAtom_isAtom F a).2]
        rfl
      have hchildInit : ∀ b, Matrix.trace (qutritRankOneProjection (v b) *
          qutritRankOneProjection (v a)) = (tracePairing (frameAtom F a) (frameAtom F b) : ℂ) := by
        intro b
        rw [htransition b a, tracePairing_comm]
      rw [ih _ _ hchildTrace hchildInit, Complex.ofReal_mul]

def qutritMixedState : ComplexMatrix3 := (1 / 3 : ℂ) • (1 : ComplexMatrix3)

theorem qutritMixedState_density : IsComplexDensity3 qutritMixedState := by
  constructor
  · exact (Matrix.PosSemidef.one : (1 : ComplexMatrix3).PosSemidef).smul
      (show (0 : ℂ) ≤ 1 / 3 by norm_num [Complex.nonneg_iff])
  · change Matrix.trace ((1 / 3 : ℂ) • (1 : ComplexMatrix3)) = 1
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num

def chosenQutritVector {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) : Fin 3 → ℂ :=
  qutritBasisVector (Fin.castLE hm a.1) a.2

def chosenQutritProjection {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) : ComplexMatrix3 :=
  qutritRankOneProjection (chosenQutritVector hm a)

theorem chosenQutritProjection_normalized {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) :
    qutritInner (chosenQutritVector hm a) (chosenQutritVector hm a) = 1 := by
  simpa only [chosenQutritVector, ↓reduceIte] using
    qutritBasisVector_orthonormal (Fin.castLE hm a.1) a.2 a.2

theorem chosenQutritProjection_rankOne {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) :
    IsComplexRankOneProjection (chosenQutritProjection hm a) :=
  qutritMUBProjection_rankOne _ _

theorem chosenQutritProjection_positive {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) :
    (chosenQutritProjection hm a).PosSemidef := qutritRankOneProjection_positive _

theorem chosenQutritProjection_idempotent {m : ℕ} (hm : m ≤ 4) (a : FrameOutcome m) :
    chosenQutritProjection hm a * chosenQutritProjection hm a = chosenQutritProjection hm a :=
  qutritRankOneProjection_idempotent _ (chosenQutritProjection_normalized hm a)

theorem chosenQutritProjection_frame_sum {m : ℕ} (hm : m ≤ 4) (j : Fin m) :
    ∑ b : Fin 3, chosenQutritProjection hm (j, b) = 1 := qutritMUBProjection_sum _

theorem chosenQutritProjection_transition {m : ℕ} (hm : m ≤ 4) (F : Fin m → NativeJordanFrame)
    (hF : ∀ j k, j ≠ k → ∀ b c, tracePairing ((F j).atom b) ((F k).atom c) = 1 / 3)
    (a b : FrameOutcome m) :
    Matrix.trace (chosenQutritProjection hm a * chosenQutritProjection hm b) =
      (tracePairing (frameAtom F a) (frameAtom F b) : ℂ) := by
  rcases a with ⟨j, c⟩
  rcases b with ⟨k, d⟩
  change Matrix.trace (qutritMUBProjection (Fin.castLE hm j) c *
    qutritMUBProjection (Fin.castLE hm k) d) =
      (tracePairing ((F j).atom c) ((F k).atom d) : ℂ)
  by_cases hjk : j = k
  · subst k
    rw [qutritMUBProjection_transition_same, nativeFrame_transition_same]
    split_ifs <;> norm_num
  · have hinj : Fin.castLE hm j ≠ Fin.castLE hm k := by
      intro h
      exact hjk (Fin.ext (congrArg (fun i : Fin 4 => i.val) h))
    rw [qutritMUBProjection_transition_distinct _ _ hinj, hF j k hjk]
    norm_num

theorem chosenQutritProjection_initial_overlap {m : ℕ} (hm : m ≤ 4)
    (F : Fin m → NativeJordanFrame) (a : FrameOutcome m) :
    Matrix.trace (chosenQutritProjection hm a * qutritMixedState) =
      (tracePairing ((1 / 3 : ℝ) • albertUnit) (frameAtom F a) : ℂ) := by
  change Matrix.trace (qutritRankOneProjection (chosenQutritVector hm a) *
    ((1 / 3 : ℂ) • (1 : ComplexMatrix3))) = _
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    qutritRankOneProjection_trace, chosenQutritProjection_normalized,
    smul_eq_mul, mul_one, tracePairing_smul_left, tracePairing_comm albertUnit _,
    tracePairing_unit_right, (frameAtom_isAtom F a).2, mul_one]
  norm_num

theorem mutuallyUnbiasedFrames_qutrit_word_statistics {m : ℕ} (hm : m ≤ 4)
    (F : Fin m → NativeJordanFrame)
    (hF : ∀ j k, j ≠ k → ∀ b c, tracePairing ((F j).atom b) ((F k).atom c) = 1 / 3)
    (w : List (FrameOutcome m)) :
    (qutritCompleteTrace (chosenQutritProjection hm) qutritMixedState w).re =
      completeMeasurementProbability F ((1 / 3 : ℝ) • albertUnit) w := by
  have htrace : Matrix.trace qutritMixedState =
      (albertTrace ((1 / 3 : ℝ) • albertUnit) : ℂ) := by
    rw [qutritMixedState_density.2, native_maximally_mixed_density.2]
    rfl
  have h := completeFrame_statistics_match_of_overlaps F (chosenQutritVector hm)
    (chosenQutritProjection_normalized hm) (chosenQutritProjection_transition hm F hF)
    _ _ htrace (chosenQutritProjection_initial_overlap hm F) w
  exact congrArg Complex.re h

end AlbertSequential
