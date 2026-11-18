/- SPDX-License-Identifier: Apache-2.0 -/
module
public import BinaryProjectionDilation
public import Interfaces.OperationalBoundaries

/-! The sum-coordinate construction is bound to the literal first-block
inclusion and Fin(d+d) coordinates of the core operational contract. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix

theorem firstSummand_reindex (d : ℕ) :
    (firstSummandInclusion (𝕜 := ℂ) (n := Fin d)).submatrix
      (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).symm id = firstBlockInclusion d := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).surjective i
  cases i with
  | inl i =>
      rw [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      simp [firstSummandInclusion, firstBlockInclusion, Matrix.one_apply, Fin.ext_iff]
      rfl
  | inr i =>
      rw [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      have h' : i.val + d ≠ j.val := by omega
      simp [firstSummandInclusion, firstBlockInclusion, h']

theorem reindexRows_isometry {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] (V : Matrix m n ℂ) (e : k ≃ m) (hV : Vᴴ * V = 1) :
    (V.submatrix e id)ᴴ * V.submatrix e id = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV]
  rfl

theorem firstBlockInclusion_isometry (d : ℕ) :
    (firstBlockInclusion d)ᴴ * firstBlockInclusion d = 1 := by
  rw [← firstSummand_reindex]
  exact reindexRows_isometry _ _ firstSummandInclusion_isometry

def finiteBinaryYesIsometry {d : ℕ} {A : ComplexMatrix d} (s : BinarySpectralSupport A) :
    Matrix (Fin (d+d)) (Fin d) ℂ :=
  (binaryYesIsometry s).submatrix finSumFinEquiv.symm id

def finiteBinaryNoIsometry {d : ℕ} {A : ComplexMatrix d} (s : BinarySpectralSupport A) :
    Matrix (Fin (d+d)) (Fin d) ℂ :=
  (binaryNoIsometry s).submatrix finSumFinEquiv.symm id

def finiteBinaryProjection {d : ℕ} {A : ComplexMatrix d} (s : BinarySpectralSupport A) :
    ComplexMatrix (d+d) := finiteBinaryYesIsometry s * (finiteBinaryYesIsometry s)ᴴ

theorem finiteBinaryYesIsometry_isometry {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    (finiteBinaryYesIsometry s)ᴴ * finiteBinaryYesIsometry s = 1 :=
  reindexRows_isometry _ _ (binaryYesIsometry_isometry s)

theorem finiteBinaryNoIsometry_isometry {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    (finiteBinaryNoIsometry s)ᴴ * finiteBinaryNoIsometry s = 1 :=
  reindexRows_isometry _ _ (binaryNoIsometry_isometry s)

theorem finiteBinaryProjection_eq_reindex {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    finiteBinaryProjection s = (binaryDilationProjection s).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold finiteBinaryProjection finiteBinaryYesIsometry binaryDilationProjection
  rw [Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _

theorem finiteBinaryProjection_hermitian {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) : (finiteBinaryProjection s)ᴴ = finiteBinaryProjection s := by
  simp [finiteBinaryProjection]

theorem finiteBinaryProjection_idempotent {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    finiteBinaryProjection s * finiteBinaryProjection s = finiteBinaryProjection s := by
  rw [finiteBinaryProjection_eq_reindex, Matrix.submatrix_mul_equiv,
    binaryDilationProjection_idempotent]

theorem finiteBinaryNoIsometry_range {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    finiteBinaryNoIsometry s * (finiteBinaryNoIsometry s)ᴴ = 1 - finiteBinaryProjection s := by
  unfold finiteBinaryNoIsometry
  rw [Matrix.conjTranspose_submatrix]
  calc
    _ = (binaryNoIsometry s * (binaryNoIsometry s)ᴴ).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm :=
      Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin d)) _
    _ = _ := by
      rw [binaryNoIsometry_range]
      change (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm -
        (binaryDilationProjection s).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = _
      rw [Matrix.submatrix_one_equiv, ← finiteBinaryProjection_eq_reindex]

theorem finiteBinaryYesIsometry_inclusion {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    (finiteBinaryYesIsometry s)ᴴ * firstBlockInclusion d = s.yes.root := by
  rw [← firstSummand_reindex]
  unfold finiteBinaryYesIsometry
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    binaryYesIsometry_firstSummand]
  rfl

theorem finiteBinaryNoIsometry_inclusion {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) :
    (finiteBinaryNoIsometry s)ᴴ * firstBlockInclusion d = s.no.root := by
  rw [← firstSummand_reindex]
  unfold finiteBinaryNoIsometry
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    binaryNoIsometry_firstSummand]
  rfl

theorem finiteBinaryProjection_compression {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) : compressFirstBlock (finiteBinaryProjection s) = A := by
  have hl : (firstBlockInclusion d)ᴴ * finiteBinaryYesIsometry s = s.yes.root := by
    simpa [s.yes.root_hermitian] using
      congrArg Matrix.conjTranspose (finiteBinaryYesIsometry_inclusion s)
  unfold compressFirstBlock finiteBinaryProjection
  rw [← Matrix.mul_assoc, hl, Matrix.mul_assoc, finiteBinaryYesIsometry_inclusion,
    s.yes.root_sq]

#print axioms firstBlockInclusion_isometry
#print axioms finiteBinaryProjection_compression
end AlbertSequential
