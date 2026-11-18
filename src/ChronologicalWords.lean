/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.WordsAndCertificates
public import Mathlib.Tactic.NoncommRing

/-! Chronological products and projection/complement identities for the actual
shared word definitions. No state or native Albert law is used here. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

section RingWords
variable {ι A : Type*} [Ring A] (P : ι → A)

private theorem foldl_outcomes_mul (w : Word ι) (x y : A) :
    w.foldl (fun z a => algebraicOutcome P a * z) (x * y) =
      w.foldl (fun z a => algebraicOutcome P a * z) x * y := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
      simp only [List.foldl_cons, ← mul_assoc]
      exact ih _

theorem wordAmplitude_foldl (w : Word ι) (x : A) :
    w.foldl (fun z a => algebraicOutcome P a * z) x = wordAmplitude P w * x := by
  simpa only [one_mul, wordAmplitude] using foldl_outcomes_mul P w 1 x

@[simp] theorem wordAmplitude_nil : wordAmplitude P [] = 1 := rfl

theorem wordAmplitude_append (u v : Word ι) :
    wordAmplitude P (u ++ v) = wordAmplitude P v * wordAmplitude P u := by
  rw [wordAmplitude, List.foldl_append, wordAmplitude_foldl]
  rfl

theorem wordAmplitude_cons (a : Outcome ι) (w : Word ι) :
    wordAmplitude P (a :: w) = wordAmplitude P w * algebraicOutcome P a := by
  rw [wordAmplitude, List.foldl_cons, wordAmplitude_foldl, mul_one]

@[simp] theorem wordAmplitude_singleton (a : Outcome ι) :
    wordAmplitude P [a] = algebraicOutcome P a := by
  rw [wordAmplitude_cons, wordAmplitude_nil, one_mul]

theorem wordAmplitude_append_singleton (w : Word ι) (a : Outcome ι) :
    wordAmplitude P (w ++ [a]) = algebraicOutcome P a * wordAmplitude P w := by
  rw [wordAmplitude_append, wordAmplitude_singleton]

theorem algebraicOutcome_add_complement (i : ι) :
    algebraicOutcome P (i, true) + algebraicOutcome P (i, false) = 1 := by
  simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte]
  abel

theorem algebraicOutcome_idempotent
    (hp : ∀ i, P i * P i = P i) (a : Outcome ι) :
    algebraicOutcome P a * algebraicOutcome P a = algebraicOutcome P a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte]
  · noncomm_ring [hp i]
  · exact hp i

theorem algebraicOutcome_opposite_mul
    (hp : ∀ i, P i * P i = P i) (i : ι) (b : Bool) :
    algebraicOutcome P (i, !b) * algebraicOutcome P (i, b) = 0 := by
  cases b <;> simp only [Bool.not_false, Bool.not_true, algebraicOutcome, Bool.false_eq_true, ↓reduceIte] <;>
    noncomm_ring [hp i]

theorem wordAmplitude_repeat_context
    (hp : ∀ i, P i * P i = P i) (u v : Word ι) (a : Outcome ι) :
    wordAmplitude P (u ++ a :: a :: v) = wordAmplitude P (u ++ a :: v) := by
  rw [wordAmplitude_append, wordAmplitude_cons, wordAmplitude_cons,
    wordAmplitude_append, wordAmplitude_cons]
  rw [mul_assoc (wordAmplitude P v), algebraicOutcome_idempotent P hp]

theorem wordAmplitude_opposite_context
    (hp : ∀ i, P i * P i = P i) (u v : Word ι) (i : ι) (b : Bool) :
    wordAmplitude P (u ++ (i, b) :: (i, !b) :: v) = 0 := by
  rw [wordAmplitude_append, wordAmplitude_cons, wordAmplitude_cons,
    mul_assoc (wordAmplitude P v), algebraicOutcome_opposite_mul P hp,
    mul_zero, zero_mul]

end RingWords

section StarWords
variable {ι A : Type*} [Ring A] [StarRing A] (P : ι → A)

theorem algebraicOutcome_star (hstar : ∀ i, star (P i) = P i) (a : Outcome ι) :
    star (algebraicOutcome P a) = algebraicOutcome P a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [algebraicOutcome, hstar]

@[simp] theorem wordOperator_nil : wordOperator P [] = 1 := by
  simp [wordOperator]

theorem wordOperator_append (u v : Word ι) :
    wordOperator P (u ++ v) =
      star (wordAmplitude P u) * wordOperator P v * wordAmplitude P u := by
  simp only [wordOperator, wordAmplitude_append, star_mul, mul_assoc]

theorem wordOperator_cons (hstar : ∀ i, star (P i) = P i)
    (a : Outcome ι) (w : Word ι) :
    wordOperator P (a :: w) =
      algebraicOutcome P a * wordOperator P w * algebraicOutcome P a := by
  simp only [wordOperator, wordAmplitude_cons, star_mul,
    algebraicOutcome_star P hstar, mul_assoc]

theorem wordOperator_singleton
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (a : Outcome ι) : wordOperator P [a] = algebraicOutcome P a := by
  simp only [wordOperator, wordAmplitude_singleton, algebraicOutcome_star P hstar,
    algebraicOutcome_idempotent P hp]

theorem wordOperator_star (w : Word ι) : star (wordOperator P w) = wordOperator P w := by
  simp only [wordOperator, star_mul, star_star]

theorem wordOperator_repeat_context
    (hp : ∀ i, P i * P i = P i) (u v : Word ι) (a : Outcome ι) :
    wordOperator P (u ++ a :: a :: v) = wordOperator P (u ++ a :: v) := by
  simp only [wordOperator, wordAmplitude_repeat_context P hp]

theorem wordOperator_opposite_context
    (hp : ∀ i, P i * P i = P i) (u v : Word ι) (i : ι) (b : Bool) :
    wordOperator P (u ++ (i, b) :: (i, !b) :: v) = 0 := by
  simp only [wordOperator, wordAmplitude_opposite_context P hp, star_zero, mul_zero]

theorem star_outcome_mul_square
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (a : Outcome ι) (x : A) :
    star (algebraicOutcome P a * x) * (algebraicOutcome P a * x) =
      star x * algebraicOutcome P a * x := by
  rw [star_mul, algebraicOutcome_star P hstar]
  calc
    star x * algebraicOutcome P a * (algebraicOutcome P a * x) =
        star x * (algebraicOutcome P a * algebraicOutcome P a) * x := by
      simp only [mul_assoc]
    _ = _ := by rw [algebraicOutcome_idempotent P hp]

theorem projection_square_split
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (i : ι) (x : A) :
    star (P i * x) * (P i * x) +
      star ((1 - P i) * x) * ((1 - P i) * x) = star x * x := by
  have ht := star_outcome_mul_square P hp hstar (i, true) x
  have hf := star_outcome_mul_square P hp hstar (i, false) x
  simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte] at ht hf
  rw [ht, hf]
  noncomm_ring

theorem wordOperator_terminal_split
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (w : Word ι) (i : ι) :
    wordOperator P (w ++ [(i, true)]) + wordOperator P (w ++ [(i, false)]) =
      wordOperator P w := by
  simp only [wordOperator, wordAmplitude_append_singleton, algebraicOutcome,
    Bool.false_eq_true, ↓reduceIte]
  exact projection_square_split P hp hstar i _

end StarWords
end AlbertSequential
