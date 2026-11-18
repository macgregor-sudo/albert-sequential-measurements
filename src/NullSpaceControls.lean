module

public import Interfaces.WordsAndCertificates
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases

/-! Concrete controls for nonfaithful states and chronological products.
No contract hypothesis or Challenge statement is used. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.Controls

abbrev RealMatrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The vector state at the first coordinate, not the normalized trace. -/
def vectorState (M : RealMatrix2) : ℝ := M 0 0

def vectorStateLinear : RealMatrix2 →ₗ[ℝ] ℝ where
  toFun := vectorState
  map_add' := by intro X Y; rfl
  map_smul' := by intro a X; rfl

theorem vectorState_transpose (M : RealMatrix2) :
    vectorState M.transpose = vectorState M := rfl

theorem vectorState_normalized : vectorState (1 : RealMatrix2) = 1 := by
  norm_num [vectorState]

theorem vectorState_transpose_square (M : RealMatrix2) :
    vectorState (M.transpose * M) = (M 0 0) ^ 2 + (M 1 0) ^ 2 := by
  simp [vectorState, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

theorem vectorState_positive (M : RealMatrix2) :
    0 ≤ vectorState (M.transpose * M) := by
  rw [vectorState_transpose_square]
  positivity

def nullDiagonal : RealMatrix2 := fun i j => if i = 1 ∧ j = 1 then 1 else 0

def lowerMatrixUnit : RealMatrix2 := fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem nullDiagonal_nonzero : nullDiagonal ≠ 0 := by
  intro h
  have h11 := congrArg (fun M : RealMatrix2 => M 1 1) h
  norm_num [nullDiagonal] at h11

theorem nonfaithful_null_control :
    vectorState (nullDiagonal.transpose * nullDiagonal) = 0 := by
  norm_num [vectorState_transpose_square, nullDiagonal]

theorem right_product_not_null_control :
    vectorState ((nullDiagonal * lowerMatrixUnit).transpose *
      (nullDiagonal * lowerMatrixUnit)) = 1 := by
  rw [vectorState_transpose_square]
  norm_num [nullDiagonal, lowerMatrixUnit,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- A positive normalized vector state's null space need not be a right ideal.
Thus treating it as a two-sided ideal would fail even in real dimension two. -/
theorem null_space_not_right_ideal :
    ¬ (∀ X Y : RealMatrix2, vectorState (X.transpose * X) = 0 →
      vectorState ((X * Y).transpose * (X * Y)) = 0) := by
  intro h
  have bad := h nullDiagonal lowerMatrixUnit nonfaithful_null_control
  rw [right_product_not_null_control] at bad
  norm_num at bad

def firstProjection : RealMatrix2 := fun i j => if i = 0 ∧ j = 0 then 1 else 0

def plusProjection : RealMatrix2 := fun _ _ => 1 / 2

def chronologicalProjections (b : Bool) : RealMatrix2 :=
  if b then plusProjection else firstProjection

theorem firstProjection_idempotent : firstProjection * firstProjection = firstProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem plusProjection_idempotent : plusProjection * plusProjection = plusProjection := by
  ext i j
  norm_num [plusProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- Actual shared wordAmplitude: the last chronological outcome acts first
on the left of the amplitude, giving probability one half here. -/
theorem chronological_probability_control :
    vectorState ((wordAmplitude chronologicalProjections
      [(false, true), (true, true)]).transpose *
      wordAmplitude chronologicalProjections [(false, true), (true, true)]) = 1 / 2 := by
  norm_num [wordAmplitude, algebraicOutcome, chronologicalProjections,
    vectorState, firstProjection, plusProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem reversed_probability_control :
    vectorState ((wordAmplitude chronologicalProjections
      [(true, true), (false, true)]).transpose *
      wordAmplitude chronologicalProjections [(true, true), (false, true)]) = 1 / 4 := by
  norm_num [wordAmplitude, algebraicOutcome, chronologicalProjections,
    vectorState, firstProjection, plusProjection, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms vectorState_positive
#print axioms null_space_not_right_ideal
#print axioms chronological_probability_control
#print axioms reversed_probability_control

end AlbertSequential.Controls
