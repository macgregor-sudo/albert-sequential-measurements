/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MeasurePrepareKraus

/-! Finite rectangular Kraus lists over real or complex scalars. No trace
normalization or positive input is needed for the algebraic identities. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

def rectangularKrausAction (K : List (Matrix m n 𝕜)) (Y : Matrix n n 𝕜) : Matrix m m 𝕜 :=
  (K.map (fun V => V * Y * V.conjTranspose)).sum

def rectangularKrausEffect (K : List (Matrix m n 𝕜)) : Matrix n n 𝕜 :=
  (K.map (fun V => V.conjTranspose * V)).sum

omit [Fintype m] in
@[simp] theorem rectangularKrausAction_nil (Y : Matrix n n 𝕜) :
    rectangularKrausAction ([] : List (Matrix m n 𝕜)) Y = 0 := rfl

omit [Fintype m] in
@[simp] theorem rectangularKrausAction_cons (V : Matrix m n 𝕜)
    (K : List (Matrix m n 𝕜)) (Y : Matrix n n 𝕜) :
    rectangularKrausAction (V :: K) Y = V * Y * V.conjTranspose + rectangularKrausAction K Y := rfl

omit [Fintype n] in
@[simp] theorem rectangularKrausEffect_nil :
    rectangularKrausEffect ([] : List (Matrix m n 𝕜)) = 0 := rfl

omit [Fintype n] in
@[simp] theorem rectangularKrausEffect_cons (V : Matrix m n 𝕜) (K : List (Matrix m n 𝕜)) :
    rectangularKrausEffect (V :: K) = V.conjTranspose * V + rectangularKrausEffect K := rfl

omit [Fintype m] in
theorem rectangularKrausAction_append (K L : List (Matrix m n 𝕜)) (Y : Matrix n n 𝕜) :
    rectangularKrausAction (K ++ L) Y = rectangularKrausAction K Y + rectangularKrausAction L Y := by
  simp [rectangularKrausAction]

omit [Fintype n] in
theorem rectangularKrausEffect_append (K L : List (Matrix m n 𝕜)) :
    rectangularKrausEffect (K ++ L) = rectangularKrausEffect K + rectangularKrausEffect L := by
  simp [rectangularKrausEffect]

omit [Fintype m] in
theorem rectangularKrausAction_add (K : List (Matrix m n 𝕜)) (Y Z : Matrix n n 𝕜) :
    rectangularKrausAction K (Y + Z) = rectangularKrausAction K Y + rectangularKrausAction K Z := by
  induction K with
  | nil => simp
  | cons V K ih =>
    simp only [rectangularKrausAction_cons, Matrix.mul_add, Matrix.add_mul, ih]
    abel

omit [Fintype m] in
theorem rectangularKrausAction_smul (K : List (Matrix m n 𝕜)) (r : 𝕜) (Y : Matrix n n 𝕜) :
    rectangularKrausAction K (r • Y) = r • rectangularKrausAction K Y := by
  induction K with
  | nil => simp
  | cons V K ih =>
    simp only [rectangularKrausAction_cons, Matrix.mul_smul, Matrix.smul_mul, ih, smul_add]

theorem rectangularKrausAction_positive (K : List (Matrix m n 𝕜))
    {Y : Matrix n n 𝕜} (hY : Y.PosSemidef) : (rectangularKrausAction K Y).PosSemidef := by
  induction K with
  | nil => exact Matrix.PosSemidef.zero
  | cons V K ih =>
    exact (hY.mul_mul_conjTranspose_same V).add ih

theorem rectangularKrausAction_trace (K : List (Matrix m n 𝕜)) (Y : Matrix n n 𝕜) :
    Matrix.trace (rectangularKrausAction K Y) = Matrix.trace (rectangularKrausEffect K * Y) := by
  induction K with
  | nil => simp
  | cons V K ih =>
    simp only [rectangularKrausAction_cons, rectangularKrausEffect_cons,
      Matrix.trace_add, Matrix.add_mul, ih]
    rw [Matrix.trace_mul_comm (V * Y), Matrix.mul_assoc]

def rectangularMeasurePrepare {r s : Type*} [Fintype r] [Fintype s]
    (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜) : List (Matrix m n 𝕜) :=
  Finset.univ.toList.map (fun i : r × s => measurePrepareMatrix B Q i.1 i.2)

set_option backward.isDefEq.respectTransparency false in
omit [Fintype m] in
theorem rectangularMeasurePrepare_action {r s : Type*} [Fintype r] [Fintype s]
    (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜) (Y : Matrix n n 𝕜) :
    rectangularKrausAction (rectangularMeasurePrepare B Q) Y =
      Matrix.trace (Q * Y * Q.conjTranspose) • (B * B.conjTranspose) := by
  unfold rectangularKrausAction rectangularMeasurePrepare
  rw [List.map_map, Finset.sum_map_toList, Fintype.sum_prod_type]
  exact measurePrepare_sum_action B Q Y

set_option backward.isDefEq.respectTransparency false in
omit [Fintype n] in
theorem rectangularMeasurePrepare_effect [DecidableEq m]
    {r s : Type*} [Fintype r] [Fintype s] (B : Matrix m r 𝕜) (Q : Matrix s n 𝕜) :
    rectangularKrausEffect (rectangularMeasurePrepare B Q) =
      Matrix.trace (B * B.conjTranspose) • (Q.conjTranspose * Q) := by
  unfold rectangularKrausEffect rectangularMeasurePrepare
  rw [List.map_map, Finset.sum_map_toList, Fintype.sum_prod_type]
  exact measurePrepare_sum_effect B Q

end AlbertSequential
