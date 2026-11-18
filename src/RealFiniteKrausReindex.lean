/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealFiniteKrausModel

/-! Literal finite-coordinate renaming preserves effects and every word.
No dimension padding or loss of zero-dimensional cases occurs. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def renameRealMatrix (e : I ≃ J) (M : Matrix I I ℝ) : Matrix J J ℝ := M.submatrix e.symm e.symm

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem renameRealMatrix_add (e : I ≃ J) (M N : Matrix I I ℝ) :
    renameRealMatrix e (M + N) = renameRealMatrix e M + renameRealMatrix e N := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem renameRealMatrix_zero (e : I ≃ J) : renameRealMatrix e (0 : Matrix I I ℝ) = 0 := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem renameRealMatrix_mul (e : I ≃ J) (M N : Matrix I I ℝ) :
    renameRealMatrix e (M * N) = renameRealMatrix e M * renameRealMatrix e N :=
  (Matrix.submatrix_mul_equiv M N e.symm e.symm e.symm).symm

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem renameRealMatrix_conjTranspose (e : I ≃ J) (M : Matrix I I ℝ) :
    renameRealMatrix e M.conjTranspose = (renameRealMatrix e M).conjTranspose := rfl

omit [Fintype I] [Fintype J] in
theorem renameRealMatrix_one (e : I ≃ J) : renameRealMatrix e (1 : Matrix I I ℝ) = 1 := by
  ext i j
  simp [renameRealMatrix, Matrix.one_apply]

omit [DecidableEq I] [DecidableEq J] in
theorem renameRealMatrix_trace (e : I ≃ J) (M : Matrix I I ℝ) :
    Matrix.trace (renameRealMatrix e M) = Matrix.trace M :=
  e.symm.sum_comp (fun i => M i i)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem renameRealMatrix_positive (e : I ≃ J) (M : Matrix I I ℝ) (hM : M.PosSemidef) :
    (renameRealMatrix e M).PosSemidef := hM.submatrix e.symm

omit [DecidableEq I] [DecidableEq J] in
theorem renameRectangularKrausAction (e : I ≃ J) (K : List (Matrix I I ℝ)) (Y : Matrix I I ℝ) :
    renameRealMatrix e (rectangularKrausAction K Y) =
      rectangularKrausAction (K.map (renameRealMatrix e)) (renameRealMatrix e Y) := by
  induction K with
  | nil => exact renameRealMatrix_zero e
  | cons V K ih =>
    simp only [List.map_cons, rectangularKrausAction_cons]
    rw [renameRealMatrix_add, renameRealMatrix_mul, renameRealMatrix_mul,
      renameRealMatrix_conjTranspose, ih]

omit [DecidableEq I] [DecidableEq J] in
theorem renameRectangularKrausEffect (e : I ≃ J) (K : List (Matrix I I ℝ)) :
    renameRealMatrix e (rectangularKrausEffect K) =
      rectangularKrausEffect (K.map (renameRealMatrix e)) := by
  induction K with
  | nil => exact renameRealMatrix_zero e
  | cons V K ih =>
    simp only [List.map_cons, rectangularKrausEffect_cons]
    rw [renameRealMatrix_add, renameRealMatrix_mul, renameRealMatrix_conjTranspose, ih]

def renameRealFiniteKrausModel (e : I ≃ J) (r : RealFiniteKrausModel I X) :
    RealFiniteKrausModel J X where
  initial := renameRealMatrix e r.initial
  positive := renameRealMatrix_positive e r.initial r.positive
  trace_one := (renameRealMatrix_trace e r.initial).trans r.trace_one
  kraus x b := (r.kraus x b).map (renameRealMatrix e)
  normalized x := by
    rw [← renameRectangularKrausEffect, ← renameRectangularKrausEffect,
      ← renameRealMatrix_add, r.normalized, renameRealMatrix_one]

theorem renameRealKrausWordState (e : I ≃ J) (K : X → Bool → List (Matrix I I ℝ))
    (Y : Matrix I I ℝ) (w : Word X) :
    w.foldl (fun Z a => rectangularKrausAction ((K a.1 a.2).map (renameRealMatrix e)) Z)
      (renameRealMatrix e Y) =
      renameRealMatrix e (w.foldl (fun Z a => rectangularKrausAction (K a.1 a.2) Z) Y) := by
  induction w generalizing Y with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons]
    rw [← renameRectangularKrausAction, ih]

theorem renameRealFiniteKrausModel_probability (e : I ≃ J) (r : RealFiniteKrausModel I X)
    (w : Word X) :
    realFiniteKrausProbability J X (renameRealFiniteKrausModel e r) w =
      realFiniteKrausProbability I X r w := by
  change Matrix.trace (w.foldl (fun Z a => rectangularKrausAction
    ((r.kraus a.1 a.2).map (renameRealMatrix e)) Z) (renameRealMatrix e r.initial)) = _
  rw [renameRealKrausWordState, renameRealMatrix_trace]
  rfl

end AlbertSequential
