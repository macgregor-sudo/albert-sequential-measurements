/- SPDX-License-Identifier: Apache-2.0 -/
module
public import BinarySpectralSupport
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! The standard doubled-space projection, constructed from complementary
positive square roots in the same spectral basis. The sum-index coordinates
are explicit; no finite-dimensional representation is assumed as an input. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

def firstSummandInclusion : Matrix (n ⊕ n) n 𝕜 := fromRows 1 0

def binaryYesIsometry {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    Matrix (n ⊕ n) n 𝕜 := fromRows s.yes.root s.no.root

def binaryNoIsometry {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    Matrix (n ⊕ n) n 𝕜 := fromRows s.no.root (-s.yes.root)

def binaryDilationProjection {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    Matrix (n ⊕ n) (n ⊕ n) 𝕜 := binaryYesIsometry s * (binaryYesIsometry s)ᴴ

theorem firstSummandInclusion_isometry :
    (firstSummandInclusion (𝕜 := 𝕜) (n := n))ᴴ * (firstSummandInclusion (𝕜 := 𝕜) (n := n)) = 1 := by
  simp [firstSummandInclusion, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows]

theorem binaryYesIsometry_isometry {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    (binaryYesIsometry s)ᴴ * binaryYesIsometry s = 1 := by
  simpa [binaryYesIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, s.yes.root_hermitian, s.no.root_hermitian] using
    binarySpectralSupport_sum_squares s

theorem binaryNoIsometry_isometry {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    (binaryNoIsometry s)ᴴ * binaryNoIsometry s = 1 := by
  simpa [binaryNoIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, s.yes.root_hermitian, s.no.root_hermitian, add_comm] using
    binarySpectralSupport_sum_squares s

theorem binaryIsometries_orthogonal {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    (binaryYesIsometry s)ᴴ * binaryNoIsometry s = 0 := by
  simp [binaryYesIsometry, binaryNoIsometry,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
    s.yes.root_hermitian, s.no.root_hermitian, s.roots_commute]

theorem binaryIsometries_complete {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    binaryYesIsometry s * (binaryYesIsometry s)ᴴ +
      binaryNoIsometry s * (binaryNoIsometry s)ᴴ = 1 := by
  simp only [binaryYesIsometry, binaryNoIsometry,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_neg,
    s.yes.root_hermitian, s.no.root_hermitian, fromRows_mul_fromCols,
    fromBlocks_add, mul_neg, neg_mul, neg_neg]
  rw [binarySpectralSupport_sum_squares s,
    add_comm (s.no.root * s.no.root), binarySpectralSupport_sum_squares s]
  simp [s.roots_commute, Matrix.fromBlocks_one]

theorem binaryDilationProjection_hermitian {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) :
    (binaryDilationProjection s)ᴴ = binaryDilationProjection s := by
  simp [binaryDilationProjection]

theorem binaryDilationProjection_idempotent {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) :
    binaryDilationProjection s * binaryDilationProjection s = binaryDilationProjection s := by
  unfold binaryDilationProjection
  calc
    _ = binaryYesIsometry s * ((binaryYesIsometry s)ᴴ * binaryYesIsometry s) *
        (binaryYesIsometry s)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [binaryYesIsometry_isometry, Matrix.mul_one]

theorem binaryNoIsometry_range {A : Matrix n n 𝕜} (s : BinarySpectralSupport A) :
    binaryNoIsometry s * (binaryNoIsometry s)ᴴ = 1 - binaryDilationProjection s := by
  have h := binaryIsometries_complete s
  change binaryDilationProjection s + _ = 1 at h
  exact eq_sub_of_add_eq' h

theorem binaryYesIsometry_firstSummand {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) :
    (binaryYesIsometry s)ᴴ * firstSummandInclusion = s.yes.root := by
  simp [binaryYesIsometry, firstSummandInclusion,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
    s.yes.root_hermitian, s.no.root_hermitian]

theorem binaryNoIsometry_firstSummand {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) :
    (binaryNoIsometry s)ᴴ * firstSummandInclusion = s.no.root := by
  simp [binaryNoIsometry, firstSummandInclusion,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
    s.yes.root_hermitian, s.no.root_hermitian]

theorem binaryDilationProjection_compression {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) :
    firstSummandInclusionᴴ * binaryDilationProjection s * firstSummandInclusion = A := by
  have hleft : (firstSummandInclusion (𝕜 := 𝕜) (n := n))ᴴ * binaryYesIsometry s =
      s.yes.root := by
    simpa [s.yes.root_hermitian] using congrArg Matrix.conjTranspose (binaryYesIsometry_firstSummand s)
  unfold binaryDilationProjection
  rw [← Matrix.mul_assoc, hleft, Matrix.mul_assoc, binaryYesIsometry_firstSummand, s.yes.root_sq]

#print axioms binaryDilationProjection_compression
#print axioms binaryDilationProjection_idempotent
end AlbertSequential
