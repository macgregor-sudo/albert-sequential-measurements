/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
namespace AlbertSequential
open Matrix
/-- Companion Proposition 6.4, converse. The defect of a compressed idempotent
factors through its ancillary space. This also applies to every orthogonal projection. -/
theorem sharpDilation_defect_rank_le {d m : ℕ}
    (P : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℂ) (hP : P * P = P) :
    (P.toBlocks₁₁ - P.toBlocks₁₁ ^ 2).rank ≤ m := by
  let A := P.toBlocks₁₁
  let B := P.toBlocks₁₂
  let C := P.toBlocks₂₁
  let D := P.toBlocks₂₂
  have h : fromBlocks A B C D * fromBlocks A B C D = fromBlocks A B C D := by
    simpa only [A, B, C, D, fromBlocks_toBlocks] using hP
  rw [fromBlocks_multiply] at h
  have h₁ : A * A + B * C = A := (fromBlocks_inj.mp h).1
  have hfactor : A - A^2 = B * C := by rw [pow_two]; exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm (B * C)] using h₁.symm)
  change (A - A^2).rank ≤ m
  rw [hfactor]
  exact (rank_mul_le_left B C).trans B.rank_le_width

end AlbertSequential
