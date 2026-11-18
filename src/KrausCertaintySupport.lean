/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RectangularKrausFamilies

/-! Algebraic certainty support on individual Kraus ranges implies support
of every output matrix, without a positivity or nonzero-output restriction. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
variable {𝕜 I X : Type*} [RCLike 𝕜] [Fintype I]

def HasKrausCertaintySupport (K : X → Bool → List (Matrix I I 𝕜)) : Prop :=
  ∀ x, (∀ V ∈ K x true, rectangularKrausEffect (K x true) * V = V) ∧
    (∀ V ∈ K x false, rectangularKrausEffect (K x true) * V = 0)

theorem rectangularKrausAction_fixed_left (A : Matrix I I 𝕜) (K : List (Matrix I I 𝕜))
    (h : ∀ V ∈ K, A * V = V) (Y : Matrix I I 𝕜) :
    A * rectangularKrausAction K Y = rectangularKrausAction K Y := by
  induction K with
  | nil => exact Matrix.mul_zero A
  | cons V K ih =>
    rw [rectangularKrausAction_cons, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h V (by simp)]
    rw [ih (fun W hW => h W (by simp [hW]))]

theorem rectangularKrausAction_zero_left (A : Matrix I I 𝕜) (K : List (Matrix I I 𝕜))
    (h : ∀ V ∈ K, A * V = 0) (Y : Matrix I I 𝕜) : A * rectangularKrausAction K Y = 0 := by
  induction K with
  | nil => exact Matrix.mul_zero A
  | cons V K ih =>
    rw [rectangularKrausAction_cons, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h V (by simp), Matrix.zero_mul, Matrix.zero_mul,
      ih (fun W hW => h W (by simp [hW])), add_zero]

theorem HasKrausCertaintySupport.outputs {K : X → Bool → List (Matrix I I 𝕜)}
    (h : HasKrausCertaintySupport K) (x : X) (Y : Matrix I I 𝕜) :
    rectangularKrausEffect (K x true) * rectangularKrausAction (K x true) Y =
      rectangularKrausAction (K x true) Y ∧
    rectangularKrausEffect (K x true) * rectangularKrausAction (K x false) Y = 0 :=
  ⟨rectangularKrausAction_fixed_left _ _ (h x).1 Y,
    rectangularKrausAction_zero_left _ _ (h x).2 Y⟩

end AlbertSequential
