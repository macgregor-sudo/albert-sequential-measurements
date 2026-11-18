/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ChoiCompletePositivity

/-! Explicit finite Kraus matrices for measure-and-prepare maps. The algebraic
identities hold on all input matrices, not only positive or normalized ones. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

section Rectangular
variable {𝕜 m n r s : Type*} [RCLike 𝕜]
  [Fintype m] [Fintype n] [Fintype r] [Fintype s]

def measurePrepareMatrix (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜)
    (a : r) (b : s) : Matrix m n 𝕜 :=
  fun i j => B i a * Q b j

omit [Fintype m] [Fintype r] [Fintype s] in
theorem measurePrepareMatrix_action (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜)
    (Y : Matrix n n 𝕜) (a : r) (b : s) :
    measurePrepareMatrix B Q a b * Y * (measurePrepareMatrix B Q a b).conjTranspose =
      ((Q * Y * Q.conjTranspose) b b) •
        Matrix.vecMulVec (fun i => B i a) (fun j => star (B j a)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, measurePrepareMatrix,
    Finset.sum_mul, star_mul, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring

omit [Fintype m] in
theorem sum_column_outer (B : Matrix m r 𝕜) :
    ∑ a, Matrix.vecMulVec (fun i => B i a) (fun j => star (B j a)) =
      B * B.conjTranspose := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

omit [Fintype m] in
/-- The Kraus sum of the literal rectangular matrices has its exact trace form. -/
theorem measurePrepare_sum_action (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜)
    (Y : Matrix n n 𝕜) :
    ∑ a, ∑ b, measurePrepareMatrix B Q a b * Y *
      (measurePrepareMatrix B Q a b).conjTranspose =
      Matrix.trace (Q * Y * Q.conjTranspose) • (B * B.conjTranspose) := by
  simp_rw [measurePrepareMatrix_action]
  simp_rw [← Finset.sum_smul]
  rw [← Finset.smul_sum, sum_column_outer]
  rfl

omit [Fintype m] [Fintype n] [Fintype r] [Fintype s] in
theorem measurePrepareMatrix_conjTranspose (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜)
    (a : r) (b : s) :
    (measurePrepareMatrix B Q a b).conjTranspose =
      measurePrepareMatrix Q.conjTranspose B.conjTranspose b a := by
  ext i j
  simp only [Matrix.conjTranspose_apply, measurePrepareMatrix, star_mul]

omit [Fintype n] in
/-- The effect of the rectangular preparation map, including empty indices. -/
theorem measurePrepare_sum_effect [DecidableEq m]
    (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜) :
    ∑ a, ∑ b, (measurePrepareMatrix B Q a b).conjTranspose *
      measurePrepareMatrix B Q a b =
      Matrix.trace (B * B.conjTranspose) • (Q.conjTranspose * Q) := by
  have h := measurePrepare_sum_action Q.conjTranspose B.conjTranspose (1 : Matrix m m 𝕜)
  simp only [← measurePrepareMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_one] at h
  rw [Finset.sum_comm]
  rw [h, Matrix.trace_mul_comm]

end Rectangular

def measurePrepareKraus {d : ℕ} (B Q : ComplexMatrix d) : List (ComplexMatrix d) :=
  Finset.univ.toList.map (fun a : Fin d × Fin d => measurePrepareMatrix B Q a.1 a.2)

set_option backward.isDefEq.respectTransparency false in
theorem measurePrepareKraus_action {d : ℕ} (B Q Y : ComplexMatrix d) :
    krausAction (measurePrepareKraus B Q) Y =
      Matrix.trace (Q * Y * Q.conjTranspose) • (B * B.conjTranspose) := by
  unfold krausAction measurePrepareKraus
  rw [List.map_map, Finset.sum_map_toList]
  rw [Fintype.sum_prod_type]
  exact measurePrepare_sum_action B Q Y

set_option backward.isDefEq.respectTransparency false in
theorem measurePrepareKraus_effect {d : ℕ} (B Q : ComplexMatrix d) :
    krausEffect (measurePrepareKraus B Q) =
      Matrix.trace (B * B.conjTranspose) • (Q.conjTranspose * Q) := by
  unfold krausEffect measurePrepareKraus
  rw [List.map_map, Finset.sum_map_toList, Fintype.sum_prod_type]
  exact measurePrepare_sum_effect B Q

#print axioms measurePrepareKraus_action
#print axioms measurePrepareKraus_effect
end AlbertSequential
