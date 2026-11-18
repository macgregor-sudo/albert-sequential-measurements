/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritMutuallyUnbiasedBases
public import CompleteMeasurementMarkov

/-! Actual rank-one matrix compression and complete three-outcome chronological
statistics. Every matrix update is PXP, never a coarse-grained binary no-map. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators Matrix ComplexOrder

theorem qutritRankOneProjection_compression (v : Fin 3 → ℂ) (X : ComplexMatrix3) :
    qutritRankOneProjection v * X * qutritRankOneProjection v =
      Matrix.trace (qutritRankOneProjection v * X) • qutritRankOneProjection v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.trace, Matrix.diag, qutritRankOneProjection, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem qutritRankOneProjection_trace_product (v w : Fin 3 → ℂ) :
    Matrix.trace (qutritRankOneProjection v * qutritRankOneProjection w) =
      (Complex.normSq (qutritInner v w) : ℂ) := by
  have heq : Matrix.trace (qutritRankOneProjection v * qutritRankOneProjection w) =
      qutritInner v w * qutritInner w v := by
    simp only [Matrix.trace, Matrix.diag, qutritRankOneProjection_mul_apply]
    change (∑ i, v i * qutritInner v w * star (w i)) =
      qutritInner v w * (∑ i, star (w i) * v i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, ← qutritInner_star v w]
  exact Complex.mul_conj _

theorem qutritMUBProjection_transition_same (k : Fin 4) (b c : Fin 3) :
    Matrix.trace (qutritMUBProjection k b * qutritMUBProjection k c) =
      if b = c then 1 else 0 := by
  unfold qutritMUBProjection
  rw [qutritRankOneProjection_trace_product, qutritBasisVector_orthonormal]
  split_ifs <;> norm_num

theorem qutritMUBProjection_transition_distinct (k l : Fin 4) (hkl : k ≠ l) (b c : Fin 3) :
    Matrix.trace (qutritMUBProjection k b * qutritMUBProjection l c) = (1 / 3 : ℂ) := by
  unfold qutritMUBProjection
  rw [qutritRankOneProjection_trace_product, qutritBasisVector_unbiased k l hkl]
  norm_num

def qutritCompleteWordState {A : Type*} (P : A → ComplexMatrix3)
    (σ : ComplexMatrix3) (w : List A) : ComplexMatrix3 :=
  w.foldl (fun Y a => P a * Y * P a) σ

def qutritCompleteTrace {A : Type*} (P : A → ComplexMatrix3)
    (σ : ComplexMatrix3) (w : List A) : ℂ := Matrix.trace (qutritCompleteWordState P σ w)

theorem qutritCompleteWordState_smul {A : Type*} (P : A → ComplexMatrix3)
    (σ : ComplexMatrix3) (w : List A) (r : ℂ) :
    qutritCompleteWordState P (r • σ) w = r • qutritCompleteWordState P σ w := by
  induction w generalizing σ with
  | nil => rfl
  | cons a w ih =>
      change qutritCompleteWordState P (P a * (r • σ) * P a) w = _
      rw [Matrix.mul_smul, Matrix.smul_mul, ih]
      rfl

theorem qutritCompleteTrace_smul {A : Type*} (P : A → ComplexMatrix3)
    (σ : ComplexMatrix3) (w : List A) (r : ℂ) :
    qutritCompleteTrace P (r • σ) w = r * qutritCompleteTrace P σ w := by
  unfold qutritCompleteTrace
  rw [qutritCompleteWordState_smul, Matrix.trace_smul, smul_eq_mul]

theorem qutritCompleteTrace_cons {A : Type*} (v : A → Fin 3 → ℂ)
    (σ : ComplexMatrix3) (a : A) (w : List A) :
    qutritCompleteTrace (fun b => qutritRankOneProjection (v b)) σ (a :: w) =
      Matrix.trace (qutritRankOneProjection (v a) * σ) *
        qutritCompleteTrace (fun b => qutritRankOneProjection (v b))
          (qutritRankOneProjection (v a)) w := by
  change qutritCompleteTrace _ (qutritRankOneProjection (v a) * σ * qutritRankOneProjection (v a)) w = _
  rw [qutritRankOneProjection_compression, qutritCompleteTrace_smul]

theorem nativeFrame_transition_same {m : ℕ} (F : Fin m → NativeJordanFrame)
    (j : Fin m) (b c : Fin 3) : tracePairing ((F j).atom b) ((F j).atom c) =
      if b = c then 1 else 0 := by
  by_cases hbc : b = c
  · subst c
    have h := congrArg albertTrace ((F j).atoms b).1
    change tracePairing ((F j).atom b) ((F j).atom b) = albertTrace ((F j).atom b) at h
    rw [h, ((F j).atoms b).2]
    simp
  · rw [ite_eq_right hbc]
    change albertTrace (jordanMul ((F j).atom b) ((F j).atom c)) = 0
    rw [(F j).orthogonal b c hbc, albertTrace_zero]

end AlbertSequential
