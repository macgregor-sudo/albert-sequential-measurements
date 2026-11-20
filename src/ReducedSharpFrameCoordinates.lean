/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SharpDilationChannelFrame
public import FiniteBinaryProjection

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix

/-- Change only the coordinates of the dilated space of an outcome. -/
def SharpDilationChannelFrame.reindexOutput {i o p : Type*}
    [Fintype i] [Fintype o] [Fintype p] {J : Matrix o i ℂ} {R : Matrix o o ℂ}
    {S : Matrix i i ℂ} (f : SharpDilationChannelFrame J R S) (e : p ≃ o) :
    SharpDilationChannelFrame (J.submatrix e id) (R.submatrix e e) S where
  frame := f.frame.submatrix e id
  range_idempotent := by
    have hr : f.frame.submatrix e id * (f.frame.submatrix e id)ᴴ =
        (f.frame*f.frameᴴ).submatrix e e := by
      rw [conjTranspose_submatrix]
      exact submatrix_mul_equiv _ _ _ (Equiv.refl _) _
    rw [hr, submatrix_mul_equiv, f.range_idempotent]
  projection_frame := by rw [submatrix_mul_equiv, f.projection_frame]
  frame_inclusion := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv, f.frame_inclusion]; rfl
  projection_inclusion := by
    rw [submatrix_mul_equiv, f.projection_inclusion]
    exact (submatrix_mul_equiv _ _ _ (Equiv.refl i) id).symm

def optimalCornerInclusion (d m : ℕ) : Matrix (Fin (d+m)) (Fin d) ℂ :=
  (fromRows (1 : ComplexMatrix d) (0 : Matrix (Fin m) (Fin d) ℂ)).submatrix finSumFinEquiv.symm id

theorem optimalCornerInclusion_isometry (d m : ℕ) :
    (optimalCornerInclusion d m)ᴴ * optimalCornerInclusion d m = 1 := by
  apply reindexRows_isometry
  simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

theorem optimalCornerInclusion_real (d m : ℕ) (i : Fin (d+m)) (j : Fin d) :
    (optimalCornerInclusion d m i j).im = 0 := by
  unfold optimalCornerInclusion
  rw [submatrix_apply]
  cases finSumFinEquiv.symm i with
  | inl k => simp [Matrix.one_apply]; split <;> simp
  | inr k => simp

end AlbertSequential
