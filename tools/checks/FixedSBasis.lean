module

import MatchingModels.DfailsModel
import ChronologicalWords

noncomputable section

open scoped Matrix
open AlbertSequential AlbertSequential.MatchingModels

namespace FixedSSignPeer

def sign4 : Fin 4 → ℂ := ![1, -1, -1, 1]
def flip4 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal sign4
def flip12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.diagonal fun r => sign4 (fin3ProdFin4Equiv12.symm r).2

theorem sign4_square (j : Fin 4) : sign4 j * sign4 j = 1 := by
  fin_cases j <;> norm_num [sign4]

theorem sign4_star (j : Fin 4) : star (sign4 j) = sign4 j := by
  fin_cases j <;> simp [sign4]

theorem flip4_hermitian : flip4ᴴ = flip4 := by
  rw [flip4, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  exact sign4_star j

theorem flip12_hermitian : flip12ᴴ = flip12 := by
  rw [flip12, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  exact sign4_star _

theorem flip4_sq : flip4 * flip4 = 1 := by
  simp only [flip4, Matrix.diagonal_mul_diagonal, sign4_square, Matrix.diagonal_one]

theorem flip12_sq : flip12 * flip12 = 1 := by
  simp only [flip12, Matrix.diagonal_mul_diagonal, sign4_square, Matrix.diagonal_one]

theorem flip_C1 : flip4 * dfailsC1 * flip4 = -dfailsC1 := by
  ext i j
  rw [flip4, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [sign4, dfailsC1]

theorem flip_C2 : flip4 * dfailsC2 * flip4 = -dfailsC2 := by
  ext i j
  rw [flip4, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [sign4, dfailsC2]

theorem flip_C3 : flip4 * dfailsC3 * flip4 = -dfailsC3 := by
  ext i j
  rw [flip4, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [sign4, dfailsC3]

theorem flip_volume : flip4 * dfailsJ * flip4 = -dfailsJ := by
  ext i j
  rw [flip4, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [sign4, dfailsJ]

def positiveColumn : Fin 4 → Matrix (Fin 12) (Fin 4) ℂ
  | 0 => blockCol12 1 0 0
  | 1 => invSqrt2C • blockCol12 1 1 0
  | 2 => invSqrt3C • blockCol12 1 dfailsC1 1
  | 3 => invSqrt3C • blockCol12 1 dfailsC2 dfailsC3

def positiveProj (j : Fin 4) : Matrix (Fin 12) (Fin 12) ℂ :=
  positiveColumn j * (positiveColumn j)ᴴ

theorem flip_column (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    flip12 * blockCol12 A B C * flip4 =
      blockCol12 (flip4 * A * flip4) (flip4 * B * flip4) (flip4 * C * flip4) := by
  ext i j
  simp only [flip12, flip4, Matrix.mul_diagonal, Matrix.diagonal_mul, blockCol12, Matrix.of_apply]
  rcases fin3ProdFin4Equiv12.symm i with ⟨r, c⟩
  fin_cases r <;> rfl

theorem flip_positiveColumn (j : Fin 4) :
    flip12 * positiveColumn j * flip4 = dfailsIsometry j := by
  fin_cases j <;> simp [positiveColumn, dfailsIsometry, flip_column, flip4_sq,
    flip_C1, flip_C2, flip_C3, Matrix.mul_smul, Matrix.smul_mul]

theorem exact_projection_conjugacy (j : Fin 4) :
    flip12 * positiveProj j * flip12ᴴ = dfailsProj j := by
  rw [positiveProj, dfailsProj, ← flip_positiveColumn, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, flip4_hermitian]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc flip4 flip4, flip4_sq, Matrix.one_mul]

theorem positive_C_entry : positiveProj 2 4 2 = (1 / 3 : ℂ) * Complex.I := by
  have h4 : fin3ProdFin4Equiv12.symm 4 = (1, 0) := rfl
  have h2 : fin3ProdFin4Equiv12.symm 2 = (0, 2) := rfl
  rw [positiveProj, show positiveColumn 2 = invSqrt3C • blockCol12 1 dfailsC1 1 from rfl,
    Matrix.conjTranspose_smul, star_invSqrt3C, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    invSqrt3C_mul_self]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, blockCol12, h4, h2,
    dfailsC1, Matrix.one_apply]

theorem printed_C_entry : dfailsProj 2 4 2 = -((1 / 3 : ℂ) * Complex.I) := by
  rw [← exact_projection_conjugacy, flip12_hermitian, flip12, Matrix.mul_diagonal,
    Matrix.diagonal_mul, positive_C_entry]
  have h4 : fin3ProdFin4Equiv12.symm 4 = (1, 0) := rfl
  have h2 : fin3ProdFin4Equiv12.symm 2 = (0, 2) := rfl
  simp [h4, h2, sign4]

theorem literal_projection_inequality : positiveProj 2 ≠ dfailsProj 2 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 12) (Fin 12) ℂ => A 4 2) h
  rw [positive_C_entry, printed_C_entry] at he
  have him := congrArg Complex.im he
  norm_num [Complex.mul_im, Complex.div_im, Complex.div_re] at him

local notation "M12" => Matrix (Fin 12) (Fin 12) ℂ

private theorem flip_mul (A B : M12) : (flip12 * A * flip12) * (flip12 * B * flip12) =
    flip12 * (A * B) * flip12 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc flip12 flip12, flip12_sq, Matrix.one_mul]

private theorem flip_one : flip12 * (1 : M12) * flip12 = 1 := by
  rw [Matrix.mul_one, flip12_sq]

private theorem flip_outcome (q : Outcome (Fin 4)) : algebraicOutcome dfailsProj q =
    flip12 * algebraicOutcome positiveProj q * flip12 := by
  obtain ⟨j, a⟩ := q
  have hj := exact_projection_conjugacy j
  rw [flip12_hermitian] at hj
  cases a
  · change 1 - dfailsProj j = flip12 * (1 - positiveProj j) * flip12
    rw [Matrix.mul_sub, Matrix.sub_mul, flip_one, hj]
  · exact hj.symm

private theorem flip_amplitude (w : Word (Fin 4)) : wordAmplitude dfailsProj w =
    flip12 * wordAmplitude positiveProj w * flip12 := by
  induction w with
  | nil => simpa only [wordAmplitude_nil] using flip_one.symm
  | cons q w ih =>
    rw [wordAmplitude_cons, wordAmplitude_cons, ih, flip_outcome, flip_mul]

theorem exact_word_trace (w : Word (Fin 4)) : Matrix.trace (wordOperator positiveProj w) =
    Matrix.trace (wordOperator dfailsProj w) := by
  rw [wordOperator, wordOperator, flip_amplitude]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, flip12_hermitian]
  rw [← Matrix.mul_assoc flip12 _ flip12, flip_mul]
  rw [Matrix.trace_mul_comm _ flip12, ← Matrix.mul_assoc, flip12_sq, Matrix.one_mul]

#print axioms flip_C1
#print axioms flip_C2
#print axioms flip_C3
#print axioms flip_volume
#print axioms exact_projection_conjugacy
#print axioms literal_projection_inequality
#print axioms exact_word_trace

end FixedSSignPeer
