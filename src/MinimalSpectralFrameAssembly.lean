/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SharpDilationChannelFrame
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Assemble the two outcome frames of a reduced sharp dilation. All unused
output directions belong to the complement of the yes range. -/

@[expose] public section
set_option autoImplicit false

namespace AlbertSequential

open Matrix

/-- Compressing a block matrix by the first-summand inclusion extracts its upper-left block. -/
theorem sharpDilation_firstSummand_compression {𝕜 n m : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] [Fintype m] (P : Matrix (n ⊕ m) (n ⊕ m) 𝕜) :
    let J : Matrix (n ⊕ m) n 𝕜 := fromRows 1 0
    Jᴴ * P * J = P.toBlocks₁₁ := by
  dsimp only
  conv_lhs => rw [← fromBlocks_toBlocks P]
  simp only [conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
    conjTranspose_zero, fromCols_mul_fromBlocks, fromCols_mul_fromRows,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero]

variable {input output : Type*} [Fintype input] [Fintype output]

/-- A rectangular partial isometry has an idempotent range matrix. -/
theorem frameRange_idempotent_of_mul_gram {V : Matrix output input ℂ}
    (hV : V * (Vᴴ * V) = V) : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc
    _ = (V * (Vᴴ * V)) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV]

/-- The range projection of the yes frame and its complement are the two sharp outcomes. -/
theorem sharpDilationProjectors_of_partialFrame [DecidableEq output]
    {V : Matrix output input ℂ} (hV : V * (Vᴴ * V) = V) :
    let P := V * Vᴴ
    Pᴴ = P ∧ P * P = P ∧ (1 - P)ᴴ = (1 - P) ∧ (1 - P) * (1 - P) = (1 - P) := by
  dsimp only
  have hP : (V * Vᴴ)ᴴ = V * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hPP := frameRange_idempotent_of_mul_gram hV
  refine ⟨hP, hPP, ?_, ?_⟩
  · rw [conjTranspose_sub, conjTranspose_one, hP]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel

/-- Orthogonal yes/no frames whose root-weighted sum is the input inclusion
supply the two complementary instances of `SharpDilationChannelFrame`. -/
def pairedSharpDilationChannelFrame_of_partialFrames [DecidableEq output]
    (J V W : Matrix output input ℂ) (S T : Matrix input input ℂ)
    (hV : V * (Vᴴ * V) = V) (hW : W * (Wᴴ * W) = W)
    (hVW : Vᴴ * W = 0) (hVJ : Vᴴ * J = S) (hWJ : Wᴴ * J = T)
    (hJ : J = V * S + W * T) :
    SharpDilationChannelFrame J (V * Vᴴ) S × SharpDilationChannelFrame J (1 - V * Vᴴ) T := by
  have hPJ : (V * Vᴴ) * J = V * S := by rw [Matrix.mul_assoc, hVJ]
  refine ⟨⟨V, frameRange_idempotent_of_mul_gram hV, ?_, hVJ, hPJ⟩,
    ⟨W, frameRange_idempotent_of_mul_gram hW, ?_, hWJ, ?_⟩⟩
  · rw [Matrix.mul_assoc, hV]
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hVW, Matrix.mul_zero, sub_zero]
  · rw [Matrix.sub_mul, Matrix.one_mul, hPJ]
    rw [hJ, add_sub_cancel_left]

/-- The unused component of the no outcome is an orthogonal projection, and
it annihilates the input inclusion. -/
theorem sharpDilationResidual_of_partialFrames [DecidableEq output]
    (J V W : Matrix output input ℂ) (S T : Matrix input input ℂ)
    (hV : V * (Vᴴ * V) = V) (hW : W * (Wᴴ * W) = W)
    (hVW : Vᴴ * W = 0) (hVJ : Vᴴ * J = S) (hWJ : Wᴴ * J = T)
    (hJ : J = V * S + W * T) :
    let Q := 1 - V * Vᴴ - W * Wᴴ
    Qᴴ = Q ∧ Q * Q = Q ∧ Q * J = 0 := by
  dsimp only
  let R := 1 - V * Vᴴ
  let F := (pairedSharpDilationChannelFrame_of_partialFrames J V W S T hV hW hVW hVJ hWJ hJ).2
  have hR : Rᴴ = R := (sharpDilationProjectors_of_partialFrame hV).2.2.1
  have hRR : R * R = R := (sharpDilationProjectors_of_partialFrame hV).2.2.2
  have hWW : (W * Wᴴ)ᴴ = W * Wᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hWR : Wᴴ * R = Wᴴ := by
    have hRW : R * W = W := F.projection_frame
    simpa only [conjTranspose_mul, hR] using congrArg Matrix.conjTranspose hRW
  have hRRW : R * (W * Wᴴ) = W * Wᴴ := by
    have hRW : R * W = W := F.projection_frame
    rw [← Matrix.mul_assoc, hRW]
  have hWWR : (W * Wᴴ) * R = W * Wᴴ := by rw [Matrix.mul_assoc, hWR]
  change (R - W * Wᴴ)ᴴ = (R - W * Wᴴ) ∧
    (R - W * Wᴴ) * (R - W * Wᴴ) = R - W * Wᴴ ∧ (R - W * Wᴴ) * J = 0
  refine ⟨by rw [conjTranspose_sub, hR, hWW], ?_, F.residual_annihilates_inclusion⟩
  simp only [Matrix.sub_mul, Matrix.mul_sub, hRR, hRRW, hWWR, frameRange_idempotent_of_mul_gram hW]
  abel

end AlbertSequential
