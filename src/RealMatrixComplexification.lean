/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GramFactor
public import ComplexPositiveFactor
public import Interfaces.InstrumentsAndCompactness

/-! Literal real finite matrices embedded entrywise into complex matrices.
PSD and density are reflected, including singular/empty matrices. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped Matrix ComplexOrder BigOperators

def complexifyMatrix {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofRealHom

def realPartMatrix {m n : Type*} (X : Matrix m n ℂ) : Matrix m n ℝ :=
  X.map Complex.re

def imaginaryPartMatrix {m n : Type*} (X : Matrix m n ℂ) : Matrix m n ℝ :=
  X.map Complex.im

theorem realPart_complexifyMatrix {m n : Type*} (A : Matrix m n ℝ) :
    realPartMatrix (complexifyMatrix A) = A := by
  ext i j
  rfl

theorem complexifyMatrix_injective {m n : Type*} :
    Function.Injective (complexifyMatrix : Matrix m n ℝ → Matrix m n ℂ) := by
  intro A B h
  have hr := congrArg realPartMatrix h
  simpa only [realPart_complexifyMatrix] using hr

theorem complexifyMatrix_add {m n : Type*} (A B : Matrix m n ℝ) :
    complexifyMatrix (A+B) = complexifyMatrix A + complexifyMatrix B := by
  ext i j
  exact Complex.ofReal_add _ _

theorem complexifyMatrix_sub {m n : Type*} (A B : Matrix m n ℝ) :
    complexifyMatrix (A-B) = complexifyMatrix A - complexifyMatrix B := by
  ext i j
  exact Complex.ofReal_sub _ _

theorem complexifyMatrix_zero {m n : Type*} :
    complexifyMatrix (0 : Matrix m n ℝ) = 0 := by
  ext i j
  exact Complex.ofReal_zero

theorem complexifyMatrix_one {n : Type*} [DecidableEq n] :
    complexifyMatrix (1 : Matrix n n ℝ) = 1 := by
  ext i j
  by_cases h : i=j <;> simp [complexifyMatrix, Matrix.one_apply, h]

theorem complexifyMatrix_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    complexifyMatrix (A*B) = complexifyMatrix A * complexifyMatrix B := by
  exact Matrix.map_mul

theorem complexifyMatrix_transpose {m n : Type*} (A : Matrix m n ℝ) :
    complexifyMatrix A.transpose = (complexifyMatrix A).conjTranspose := by
  ext i j
  simp only [complexifyMatrix, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Complex.ofRealHom_eq_coe, Complex.star_def,
    Complex.conj_ofReal]

theorem complexifyMatrix_real_smul {m n : Type*} (r : ℝ) (A : Matrix m n ℝ) :
    complexifyMatrix (r • A) = (r : ℂ) • complexifyMatrix A := by
  ext i j
  exact Complex.ofReal_mul _ _

theorem complexifyMatrix_trace {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
    Matrix.trace (complexifyMatrix A) = ((Matrix.trace A : ℝ) : ℂ) := by
  change (∑ i, Complex.ofRealHom (A i i)) = Complex.ofRealHom (∑ i, A i i)
  exact (map_sum Complex.ofRealHom _ _).symm

theorem complexify_realPart_of_imag_eq_zero {m n : Type*} (X : Matrix m n ℂ)
    (h : ∀ i j, (X i j).im=0) : complexifyMatrix (realPartMatrix X) = X := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (h i j).symm

theorem complexifyMatrix_hasRealEntries {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    HasRealEntries (complexifyMatrix A) := fun _ _ => rfl

theorem complexify_realPart_of_hasRealEntries {d : ℕ} (X : ComplexMatrix d)
    (h : HasRealEntries X) : complexifyMatrix (realPartMatrix X) = X :=
  complexify_realPart_of_imag_eq_zero X h

theorem complexMatrix_real_imaginary_decomposition {m n : Type*} (X : Matrix m n ℂ) :
    X = complexifyMatrix (realPartMatrix X) +
      Complex.I • complexifyMatrix (imaginaryPartMatrix X) := by
  ext i j
  apply Complex.ext <;> simp [complexifyMatrix, realPartMatrix, imaginaryPartMatrix,
    Complex.mul_re, Complex.mul_im]

/-- Real part of a complex square Gram is a sum of two actual real Grams. -/
theorem realPartMatrix_self_gram {m n : Type*} [Fintype n] (B : Matrix m n ℂ) :
    realPartMatrix (B*B.conjTranspose) =
      realPartMatrix B * (realPartMatrix B).transpose +
        imaginaryPartMatrix B * (imaginaryPartMatrix B).transpose := by
  ext i j
  change (∑ k, B i k * star (B j k)).re =
    (∑ k, (B i k).re * (B j k).re) + (∑ k, (B i k).im * (B j k).im)
  have hs := map_sum Complex.reAddGroupHom (fun k => B i k * star (B j k)) Finset.univ
  change (∑ k, B i k * star (B j k)).re = ∑ k, (B i k * star (B j k)).re at hs
  rw [hs]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add, Finset.sum_add_distrib]

theorem complexifyMatrix_posSemidef_iff {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : (complexifyMatrix A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    obtain ⟨B,hB⟩ := exists_complexPositiveFactor h
    have he := congrArg realPartMatrix hB
    rw [realPart_complexifyMatrix, realPartMatrix_self_gram] at he
    rw [he]
    change (realPartMatrix B * (realPartMatrix B).conjTranspose +
      imaginaryPartMatrix B * (imaginaryPartMatrix B).conjTranspose).PosSemidef
    exact (Matrix.posSemidef_self_mul_conjTranspose _).add
      (Matrix.posSemidef_self_mul_conjTranspose _)
  · intro h
    obtain ⟨B,hB⟩ := exists_realGramFactor h
    rw [hB, complexifyMatrix_mul, complexifyMatrix_transpose]
    exact Matrix.posSemidef_conjTranspose_mul_self _

theorem realPartMatrix_positive_of_real {d : ℕ} {X : ComplexMatrix d}
    (hX : X.PosSemidef) (hreal : HasRealEntries X) : (realPartMatrix X).PosSemidef := by
  apply (complexifyMatrix_posSemidef_iff _).mp
  rwa [complexify_realPart_of_hasRealEntries X hreal]

theorem complexifyMatrix_density_iff {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    IsMatrixDensity (complexifyMatrix A) ↔ A.PosSemidef ∧ Matrix.trace A = 1 := by
  rw [IsMatrixDensity, complexifyMatrix_posSemidef_iff, complexifyMatrix_trace]
  constructor
  · rintro ⟨hA,htr⟩
    exact ⟨hA, Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using htr)⟩
  · rintro ⟨hA,htr⟩
    exact ⟨hA, by rw [htr, Complex.ofReal_one]⟩

theorem realPartMatrix_density {d : ℕ} {X : ComplexMatrix d}
    (hX : IsMatrixDensity X) (hreal : HasRealEntries X) :
    (realPartMatrix X).PosSemidef ∧ Matrix.trace (realPartMatrix X) = 1 := by
  apply (complexifyMatrix_density_iff _).mp
  rwa [complexify_realPart_of_hasRealEntries X hreal]

/-- An actual REAL factor is chosen; no arbitrary complex eigenbasis is
declared real. Normalization can be used separately by the reset channel. -/
theorem exists_real_positiveFactor {d : ℕ} {X : ComplexMatrix d}
    (hX : X.PosSemidef) (hreal : HasRealEntries X) :
    ∃ B : ComplexMatrix d, HasRealEntries B ∧ B*B.conjTranspose=X := by
  obtain ⟨D,hD⟩ := exists_realGramFactor (realPartMatrix_positive_of_real hX hreal)
  refine ⟨complexifyMatrix D.transpose, complexifyMatrix_hasRealEntries _, ?_⟩
  rw [← complexifyMatrix_transpose, Matrix.transpose_transpose,
    ← complexifyMatrix_mul, ← hD, complexify_realPart_of_hasRealEntries X hreal]

end AlbertSequential
