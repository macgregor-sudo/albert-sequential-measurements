/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FrameSlotNormalizers
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The finite-dimensional spectral linearization in the companion's
three-eigenvalue density. The geometric change of variables is separate. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open scoped Matrix

/-- The three real diagonal coordinates followed by real and imaginary
coordinates of the upper entries in order 01, 02, 12. -/
def hermitianMatrixRealCoordinates (H : ComplexMatrix3) : Fin 9 → ℝ :=
  ![(H 0 0).re, (H 1 1).re, (H 2 2).re, (H 0 1).re, (H 0 1).im,
    (H 0 2).re, (H 0 2).im, (H 1 2).re, (H 1 2).im]

/-- The skew-Hermitian matrix with zero diagonal and the supplied upper
entries. Multiplication by the imaginary unit converts a Hermitian matrix
with upper entries pre-rotated by its inverse. -/
def spectralSkewMatrix (v : Fin 3 → ℂ) : ComplexMatrix3 :=
  Complex.I • mkHerm3Matrix 0 (fun i => -Complex.I * v i)

theorem spectralSkewMatrix_conjTranspose (v : Fin 3 → ℂ) :
    (spectralSkewMatrix v).conjTranspose = -spectralSkewMatrix v := by
  let H : Hermitian3 := hermitian3Equiv.symm (0, fun i => -Complex.I * v i)
  have hH : (H : ComplexMatrix3).conjTranspose = (H : ComplexMatrix3) := H.prop
  change (Complex.I • (H : ComplexMatrix3)).conjTranspose =
    -(Complex.I • (H : ComplexMatrix3))
  rw [Matrix.conjTranspose_smul, hH, Complex.star_def, Complex.conj_I, neg_smul]

/-- Coordinate weights for the commutator of a zero-diagonal
skew-Hermitian tangent with the real eigenvalue diagonal. -/
def spectralLinearizationWeights (eigenvalue : Fin 3 → ℝ) : Fin 9 → ℝ :=
  ![1, 1, 1,
    eigenvalue 1 - eigenvalue 0, eigenvalue 1 - eigenvalue 0,
    eigenvalue 2 - eigenvalue 0, eigenvalue 2 - eigenvalue 0,
    eigenvalue 2 - eigenvalue 1, eigenvalue 2 - eigenvalue 1]

/-- In eigenvalue and off-diagonal orbit coordinates the linearization
of the matrix conjugation map is diagonal over the real numbers. -/
theorem spectralLinearization_coordinates (eigenvalue variation : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (eigenvalue i : ℂ)
    let K := spectralSkewMatrix v
    hermitianMatrixRealCoordinates
      (Matrix.diagonal (fun i => (variation i : ℂ)) + K * D - D * K) =
    (Matrix.diagonal (spectralLinearizationWeights eigenvalue)).mulVec
      ![variation 0, variation 1, variation 2, (v 0).re, (v 0).im,
        (v 1).re, (v 1).im, (v 2).re, (v 2).im] := by
  intro D K
  funext i
  fin_cases i <;>
    simp [hermitianMatrixRealCoordinates, spectralLinearizationWeights,
      D, K, spectralSkewMatrix, mkHerm3Matrix, Matrix.mulVec_diagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The real determinant of the linearized spectral map is the square
Vandermonde factor. -/
theorem spectralLinearization_det (eigenvalue : Fin 3 → ℝ) :
    (Matrix.diagonal (spectralLinearizationWeights eigenvalue)).det =
      (eigenvalue 1 - eigenvalue 0)^2 * (eigenvalue 2 - eigenvalue 0)^2 *
        (eigenvalue 2 - eigenvalue 1)^2 := by
  rw [Matrix.det_diagonal]
  simp [spectralLinearizationWeights, Fin.prod_univ_succ]
  ring

end AlbertSequential.WindowProbability
