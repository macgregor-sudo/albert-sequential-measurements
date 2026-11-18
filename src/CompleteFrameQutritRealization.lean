/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompleteFrameQutritComparison

/-! A constructed complete-projective qutrit realization, including actual
state positivity, rank-one effects, orthogonality, frame sums and all words. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators Matrix ComplexOrder

theorem chosenQutritProjection_orthogonal {m : ℕ} (hm : m ≤ 4) (j : Fin m)
    (b c : Fin 3) (hbc : b ≠ c) :
    chosenQutritProjection hm (j, b) * chosenQutritProjection hm (j, c) = 0 := by
  ext i k
  change (qutritRankOneProjection (qutritBasisVector (Fin.castLE hm j) b) *
    qutritRankOneProjection (qutritBasisVector (Fin.castLE hm j) c)) i k = 0
  rw [qutritRankOneProjection_mul_apply, qutritBasisVector_orthonormal, ite_eq_right hbc,
    mul_zero, zero_mul]

theorem exists_complete_qutrit_realization_of_mutuallyUnbiasedFrames {m : ℕ} (hm : m ≤ 4)
    (F : Fin m → NativeJordanFrame)
    (hF : ∀ j k, j ≠ k → ∀ b c, tracePairing ((F j).atom b) ((F k).atom c) = 1 / 3) :
    ∃ (σ : ComplexMatrix3) (P : FrameOutcome m → ComplexMatrix3),
      IsComplexDensity3 σ ∧
      (∀ a, IsComplexRankOneProjection (P a) ∧ (P a).PosSemidef ∧ P a * P a = P a) ∧
      (∀ j b c, b ≠ c → P (j, b) * P (j, c) = 0) ∧
      (∀ j, ∑ b : Fin 3, P (j, b) = 1) ∧
      (∀ w, (qutritCompleteTrace P σ w).re =
        completeMeasurementProbability F ((1 / 3 : ℝ) • albertUnit) w) := by
  refine ⟨qutritMixedState, chosenQutritProjection hm, qutritMixedState_density,
    ?_, chosenQutritProjection_orthogonal hm, chosenQutritProjection_frame_sum hm,
    mutuallyUnbiasedFrames_qutrit_word_statistics hm F hF⟩
  intro a
  exact ⟨chosenQutritProjection_rankOne hm a, chosenQutritProjection_positive hm a,
    chosenQutritProjection_idempotent hm a⟩

end AlbertSequential
