/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.InstrumentsAndCompactness
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Linarith

/-!
A real d²-coordinate space for complex Hermitian matrices, using the full
ordered-pair index. Diagonal/upper slots store real parts, strict lower slots
store imaginary parts. No positivity or invertibility assumption is needed.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev HermitianCoordinates (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def hermitianCoordinates {d : ℕ} (X : ComplexMatrix d) : HermitianCoordinates d :=
  fun i j => if i ≤ j then (X i j).re else (X i j).im

def matrixFromHermitianCoordinates {d : ℕ} (r : HermitianCoordinates d) : ComplexMatrix d :=
  fun i j => if i = j then ⟨r i j, 0⟩ else
    if i < j then ⟨r i j, -r j i⟩ else ⟨r j i, r i j⟩

def hermitianCoordinatesLinear (d : ℕ) : ComplexMatrix d →ₗ[ℝ] HermitianCoordinates d where
  toFun := hermitianCoordinates
  map_add' X Y := by
    apply Matrix.ext
    intro i j
    by_cases h : i ≤ j <;> simp [hermitianCoordinates, h, Matrix.add_apply]
  map_smul' r X := by
    apply Matrix.ext
    intro i j
    by_cases h : i ≤ j <;> simp [hermitianCoordinates, h, Matrix.smul_apply]

def matrixFromHermitianCoordinatesLinear (d : ℕ) : HermitianCoordinates d →ₗ[ℝ] ComplexMatrix d where
  toFun := matrixFromHermitianCoordinates
  map_add' r s := by
    apply Matrix.ext
    intro i j
    by_cases he : i = j
    · apply Complex.ext <;> simp [matrixFromHermitianCoordinates, he, Matrix.add_apply]
    · by_cases hl : i < j <;> apply Complex.ext <;>
        simp [matrixFromHermitianCoordinates, he, hl, Matrix.add_apply, add_comm]
  map_smul' t r := by
    apply Matrix.ext
    intro i j
    by_cases he : i = j
    · apply Complex.ext <;> simp [matrixFromHermitianCoordinates, he, Matrix.smul_apply]
    · by_cases hl : i < j <;> apply Complex.ext <;>
        simp [matrixFromHermitianCoordinates, he, hl, Matrix.smul_apply]

theorem matrixFromHermitianCoordinates_inverse {d : ℕ} (X : ComplexMatrix d)
    (hX : X.IsHermitian) : matrixFromHermitianCoordinates (hermitianCoordinates X) = X := by
  apply Matrix.ext
  intro i j
  have he : star (X j i) = X i j := congrFun (congrFun hX i) j
  have hre : (X j i).re = (X i j).re := by
    simpa only [Complex.star_def, Complex.conj_re] using congrArg Complex.re he
  have him : -(X j i).im = (X i j).im := by
    simpa only [Complex.star_def, Complex.conj_im] using congrArg Complex.im he
  rcases lt_trichotomy i j with hl | hij | hg
  · apply Complex.ext
    · simp [matrixFromHermitianCoordinates, hermitianCoordinates, ne_of_lt hl, hl,
        le_of_lt hl, not_le.mpr hl]
    · simpa [matrixFromHermitianCoordinates, hermitianCoordinates, ne_of_lt hl, hl,
        le_of_lt hl, not_le.mpr hl] using him
  · subst j
    have hi : (X i i).im = 0 := by linarith
    apply Complex.ext <;> simp [matrixFromHermitianCoordinates, hermitianCoordinates, hi]
  · have hne : i ≠ j := Ne.symm (ne_of_lt hg)
    have hnlt : ¬ i < j := not_lt.mpr (le_of_lt hg)
    apply Complex.ext
    · simpa [matrixFromHermitianCoordinates, hermitianCoordinates, hne, hnlt,
        le_of_lt hg, not_le.mpr hg] using hre
    · simp [matrixFromHermitianCoordinates, hermitianCoordinates, hne, hnlt,
        le_of_lt hg, not_le.mpr hg]

end AlbertSequential
