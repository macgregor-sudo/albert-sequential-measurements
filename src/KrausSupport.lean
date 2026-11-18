/- SPDX-License-Identifier: Apache-2.0 -/
module
public import MeasurePrepareKraus

/-! A Kraus map annihilates the kernel of its effect. The proof uses positivity
of the trace of each square, so it includes singular and zero effects. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

theorem krausEffect_positive {d : ℕ} (K : List (ComplexMatrix d)) :
    (krausEffect K).PosSemidef := by
  induction K with
  | nil => simpa [krausEffect] using (Matrix.PosSemidef.zero : (0 : ComplexMatrix d).PosSemidef)
  | cons V K ih =>
      simpa [krausEffect] using (Matrix.posSemidef_conjTranspose_mul_self V).add ih

theorem krausEffect_trace_zero_iff {d : ℕ} (K : List (ComplexMatrix d)) :
    Matrix.trace (krausEffect K) = 0 ↔ ∀ V ∈ K, V = 0 := by
  induction K with
  | nil => simp [krausEffect]
  | cons V K ih =>
      change Matrix.trace (V.conjTranspose * V + krausEffect K) = 0 ↔ _
      rw [Matrix.trace_add, add_eq_zero_iff_of_nonneg
        (Matrix.posSemidef_conjTranspose_mul_self V).trace_nonneg
        (krausEffect_positive K).trace_nonneg,
        Matrix.trace_conjTranspose_mul_self_eq_zero_iff, ih]
      simp

theorem krausEffect_right_multiply {d : ℕ} (K : List (ComplexMatrix d))
    (Q : ComplexMatrix d) :
    krausEffect (K.map (fun V => V * Q)) = Q.conjTranspose * krausEffect K * Q := by
  induction K with
  | nil => simp [krausEffect]
  | cons V K ih =>
      simpa only [List.map_cons, krausEffect, List.sum_cons, Matrix.conjTranspose_mul,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using
        congrArg (fun X => (V * Q).conjTranspose * (V * Q) + X) ih

theorem kraus_annihilates_effect_kernel {d : ℕ} (K : List (ComplexMatrix d))
    (Q : ComplexMatrix d) (hQ : krausEffect K * Q = 0) :
    ∀ V ∈ K, V * Q = 0 := by
  have he : krausEffect (K.map (fun V => V * Q)) = 0 := by
    rw [krausEffect_right_multiply, Matrix.mul_assoc, hQ, Matrix.mul_zero]
  have h := (krausEffect_trace_zero_iff (K.map (fun V => V * Q))).mp (by simp [he])
  intro V hV
  exact h (V * Q) (List.mem_map.mpr ⟨V, hV, rfl⟩)

theorem kraus_support_right {d : ℕ} (K : List (ComplexMatrix d))
    (P : ComplexMatrix d) (hP : krausEffect K * (1 - P) = 0) :
    ∀ V ∈ K, V * P = V := by
  intro V hV
  have h := kraus_annihilates_effect_kernel K (1 - P) hP V hV
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
  exact h.symm

#print axioms kraus_annihilates_effect_kernel
#print axioms kraus_support_right
end AlbertSequential
