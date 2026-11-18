/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ChronologicalWords
public import Mathlib.Tactic.Linarith

/-! Unconditional probabilities, terminal branch splitting and word contraction
for exactly AlgebraicProjectiveData. No tracial or faithful state is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace AlgebraicProjectiveData

variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData ι A)

/-- The positive functional's square mass, without a square root or quotient. -/
def squareMass (x : A) : ℝ := M.state (star x * x)

theorem squareMass_nonneg (x : A) : 0 ≤ M.squareMass x := M.state_positive x

theorem squareMass_one : M.squareMass 1 = 1 := by
  simp only [squareMass, star_one, mul_one, M.state_unit]

theorem squareMass_projection_split (i : ι) (x : A) :
    M.squareMass (M.projection i * x) + M.squareMass ((1 - M.projection i) * x) =
      M.squareMass x := by
  unfold squareMass
  rw [← map_add, projection_square_split M.projection M.idempotent M.selfAdjoint]

theorem squareMass_outcome_le (a : Outcome ι) (x : A) :
    M.squareMass (algebraicOutcome M.projection a * x) ≤ M.squareMass x := by
  rcases a with ⟨i, b⟩
  have hs := M.squareMass_projection_split i x
  have ht := M.squareMass_nonneg (M.projection i * x)
  have hf := M.squareMass_nonneg ((1 - M.projection i) * x)
  cases b <;> simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem squareMass_word_le (w : Word ι) (x : A) :
    M.squareMass (wordAmplitude M.projection w * x) ≤ M.squareMass x := by
  induction w generalizing x with
  | nil => simp only [wordAmplitude_nil, one_mul, le_refl]
  | cons a w ih =>
      rw [wordAmplitude_cons, mul_assoc]
      exact (ih (algebraicOutcome M.projection a * x)).trans (M.squareMass_outcome_le a x)

theorem squareMass_word_nonneg (w : Word ι) (x : A) :
    0 ≤ M.squareMass (wordAmplitude M.projection w * x) :=
  M.squareMass_nonneg _

theorem squareMass_word_eq_zero (w : Word ι) (x : A) (hx : M.squareMass x = 0) :
    M.squareMass (wordAmplitude M.projection w * x) = 0 := by
  apply le_antisymm
  · simpa only [hx] using M.squareMass_word_le w x
  · exact M.squareMass_word_nonneg w x

theorem probability_eq_squareMass (w : Word ι) :
    M.probability w = M.squareMass (wordAmplitude M.projection w) := rfl

theorem probability_nil : M.probability [] = 1 := by
  simp only [probability, wordOperator_nil, M.state_unit]

theorem probability_nonneg (w : Word ι) : 0 ≤ M.probability w :=
  M.state_positive (wordAmplitude M.projection w)

theorem probability_le_one (w : Word ι) : M.probability w ≤ 1 := by
  have h := M.squareMass_word_le w 1
  simpa only [mul_one, ← probability_eq_squareMass, squareMass_one] using h

theorem probability_mem_Icc (w : Word ι) : M.probability w ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨M.probability_nonneg w, M.probability_le_one w⟩

theorem probability_terminal_split (w : Word ι) (i : ι) :
    M.probability (w ++ [(i, true)]) + M.probability (w ++ [(i, false)]) =
      M.probability w := by
  unfold probability
  rw [← map_add, wordOperator_terminal_split M.projection M.idempotent M.selfAdjoint]

theorem probability_append_le (u v : Word ι) :
    M.probability (u ++ v) ≤ M.probability u := by
  change M.squareMass (wordAmplitude M.projection (u ++ v)) ≤
    M.squareMass (wordAmplitude M.projection u)
  rw [wordAmplitude_append]
  exact M.squareMass_word_le v _

theorem probability_append_eq_zero (u v : Word ι) (h : M.probability u = 0) :
    M.probability (u ++ v) = 0 := by
  apply le_antisymm
  · simpa only [h] using M.probability_append_le u v
  · exact M.probability_nonneg _

theorem probability_repeat_context (u v : Word ι) (a : Outcome ι) :
    M.probability (u ++ a :: a :: v) = M.probability (u ++ a :: v) := by
  simp only [probability, wordOperator_repeat_context M.projection M.idempotent]

theorem probability_opposite_context (u v : Word ι) (i : ι) (b : Bool) :
    M.probability (u ++ (i, b) :: (i, !b) :: v) = 0 := by
  simp only [probability, wordOperator_opposite_context M.projection M.idempotent, map_zero]

end AlgebraicProjectiveData
end AlbertSequential
