/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.SeparationAndConverse
public import ChronologicalWords
public import Mathlib.Tactic.Module

/-! Evaluation of the actual list-encoded projection monomials/polynomials.
Concatenation is algebra order; chronological amplitudes use reversed words. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Monomials
variable {n : ℕ} {A : Type*} [Ring A] (P : Fin n → A)

theorem evaluateMonomial_nil : evaluateMonomial P [] = 1 := rfl

theorem evaluateMonomial_cons (i : Fin n) (w : ProjectionMonomial n) :
    evaluateMonomial P (i :: w) = P i * evaluateMonomial P w := rfl

theorem evaluateMonomial_singleton (i : Fin n) : evaluateMonomial P [i] = P i := by
  simp only [evaluateMonomial_cons, evaluateMonomial_nil, mul_one]

theorem evaluateMonomial_append (u v : ProjectionMonomial n) :
    evaluateMonomial P (u ++ v) = evaluateMonomial P u * evaluateMonomial P v := by
  induction u with
  | nil => simp only [List.nil_append, evaluateMonomial_nil, one_mul]
  | cons i u ih =>
      simp only [List.cons_append, evaluateMonomial_cons, ih, mul_assoc]

theorem evaluateMonomial_idempotent_context (hp : ∀ i, P i * P i = P i)
    (u v : ProjectionMonomial n) (i : Fin n) :
    evaluateMonomial P (u ++ [i, i] ++ v) = evaluateMonomial P (u ++ [i] ++ v) := by
  simp only [evaluateMonomial_append, evaluateMonomial_cons,
    evaluateMonomial_nil, mul_one, hp]

theorem evaluateMonomial_eq_reversed_yes_amplitude (w : ProjectionMonomial n) :
    evaluateMonomial P w = wordAmplitude P (w.reverse.map (fun i => (i, true))) := by
  induction w with
  | nil => simp only [List.reverse_nil, List.map_nil, wordAmplitude_nil, evaluateMonomial_nil]
  | cons i w ih =>
      rw [List.reverse_cons, List.map_append, List.map_singleton, wordAmplitude_append_singleton,
        evaluateMonomial_cons, ih]
      rfl

end Monomials

theorem evaluateMonomial_reverse
    {n : ℕ} {A : Type*} [Ring A] [StarRing A]
    (P : Fin n → A) (hstar : ∀ i, star (P i) = P i) (w : ProjectionMonomial n) :
    evaluateMonomial P w.reverse = star (evaluateMonomial P w) := by
  induction w with
  | nil => simp only [List.reverse_nil, evaluateMonomial_nil, star_one]
  | cons i w ih =>
      simp only [List.reverse_cons, evaluateMonomial_append, evaluateMonomial_cons,
        evaluateMonomial_nil, mul_one, ih, star_mul, hstar]

/-- Ordinary evaluation of the existing list polynomial, retaining cancellations. -/
def evaluateProjectionPolynomial
    {n : ℕ} {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (c : ProjectionPolynomial n) : A :=
  (c.map (fun t => t.1 • evaluateMonomial P t.2)).sum

section Polynomials
variable {n : ℕ} {A : Type*} [Ring A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (P : Fin n → A)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluateProjectionPolynomial_nil : evaluateProjectionPolynomial P [] = 0 := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluateProjectionPolynomial_cons (r : ℝ) (w : ProjectionMonomial n)
    (c : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P ((r, w) :: c) =
      r • evaluateMonomial P w + evaluateProjectionPolynomial P c := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluateProjectionPolynomial_append (a b : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P (a ++ b) =
      evaluateProjectionPolynomial P a + evaluateProjectionPolynomial P b := by
  simp only [evaluateProjectionPolynomial, List.map_append, List.sum_append]

private theorem evaluateProjectionPolynomial_term_mul (r : ℝ) (w : ProjectionMonomial n)
    (b : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P (b.map (fun y => (r * y.1, w ++ y.2))) =
      (r • evaluateMonomial P w) * evaluateProjectionPolynomial P b := by
  induction b with
  | nil => simp only [List.map_nil, evaluateProjectionPolynomial_nil, mul_zero]
  | cons y b ih =>
      rcases y with ⟨s, v⟩
      simp only [List.map_cons, evaluateProjectionPolynomial_cons, evaluateMonomial_append,
        ih, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
      module

theorem evaluateProjectionPolynomial_multiply (a b : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P (polynomialMultiply a b) =
      evaluateProjectionPolynomial P a * evaluateProjectionPolynomial P b := by
  induction a with
  | nil => simp only [polynomialMultiply, List.flatMap_nil, evaluateProjectionPolynomial_nil, zero_mul]
  | cons x a ih =>
      rcases x with ⟨r, w⟩
      change evaluateProjectionPolynomial P
        ((b.map (fun y => (r * y.1, w ++ y.2))) ++ polynomialMultiply a b) = _
      rw [evaluateProjectionPolynomial_append, evaluateProjectionPolynomial_term_mul, ih,
        evaluateProjectionPolynomial_cons, add_mul]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluate_outcomePolynomial (a : Outcome (Fin n)) :
    evaluateProjectionPolynomial P (outcomePolynomial a) = algebraicOutcome P a := by
  rcases a with ⟨i, b⟩
  cases b
  all_goals
    simp only [outcomePolynomial, algebraicOutcome, Bool.false_eq_true, ↓reduceIte,
      evaluateProjectionPolynomial_cons, evaluateProjectionPolynomial_nil,
      evaluateMonomial_nil, evaluateMonomial_singleton, add_zero]
    module

private theorem evaluate_amplitude_foldl (w : Word (Fin n)) (c : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P
      (w.foldl (fun acc a => polynomialMultiply (outcomePolynomial a) acc) c) =
      w.foldl (fun acc a => algebraicOutcome P a * acc) (evaluateProjectionPolynomial P c) := by
  induction w generalizing c with
  | nil => rfl
  | cons a w ih =>
      simp only [List.foldl_cons, ih, evaluateProjectionPolynomial_multiply,
        evaluate_outcomePolynomial]

theorem evaluate_amplitudePolynomial (w : Word (Fin n)) :
    evaluateProjectionPolynomial P (amplitudePolynomial w) = wordAmplitude P w := by
  rw [amplitudePolynomial, evaluate_amplitude_foldl]
  simp only [evaluateProjectionPolynomial_cons, evaluateProjectionPolynomial_nil,
    evaluateMonomial_nil, one_smul, add_zero]
  rfl

end Polynomials

section StarPolynomials
variable {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin n → A) (hstar : ∀ i, star (P i) = P i)

include hstar in
omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluateProjectionPolynomial_star (c : ProjectionPolynomial n) :
    evaluateProjectionPolynomial P (polynomialStar c) =
      star (evaluateProjectionPolynomial P c) := by
  induction c with
  | nil => simp only [polynomialStar, List.map_nil, evaluateProjectionPolynomial_nil, star_zero]
  | cons x c ih =>
      rcases x with ⟨r, w⟩
      change evaluateProjectionPolynomial P ((r, w.reverse) :: polynomialStar c) = _
      simp only [evaluateProjectionPolynomial_cons, evaluateMonomial_reverse P hstar,
        ih, star_add, star_smul, star_trivial]

include hstar in
theorem evaluate_effectPolynomial (w : Word (Fin n)) :
    evaluateProjectionPolynomial P (effectPolynomial w) = wordOperator P w := by
  simp only [effectPolynomial, evaluateProjectionPolynomial_multiply,
    evaluateProjectionPolynomial_star P hstar, evaluate_amplitudePolynomial, wordOperator]

end StarPolynomials

theorem polynomialMoment_append {n : ℕ} (m : ProjectionMoments n)
    (a b : ProjectionPolynomial n) :
    polynomialMoment m (a ++ b) = polynomialMoment m a + polynomialMoment m b := by
  simp only [polynomialMoment, List.map_append, List.sum_append]

theorem polynomialMoment_multiply {n : ℕ} (m : ProjectionMoments n)
    (a b : ProjectionPolynomial n) :
    polynomialMoment m (polynomialMultiply a b) =
      (a.map (fun x => (b.map (fun y => x.1 * y.1 * m (x.2 ++ y.2))).sum)).sum := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      change polynomialMoment m
        ((b.map (fun y => (x.1 * y.1, x.2 ++ y.2))) ++ polynomialMultiply a b) = _
      rw [polynomialMoment_append, ih]
      simp only [polynomialMoment, List.map_map, List.map_cons, List.sum_cons, Function.comp_def]

theorem polynomialMoment_star_square {n : ℕ} (m : ProjectionMoments n)
    (c : ProjectionPolynomial n) :
    polynomialMoment m (polynomialMultiply (polynomialStar c) c) =
      (c.map (fun a =>
        (c.map (fun b => a.1 * b.1 * m (a.2.reverse ++ b.2))).sum)).sum := by
  rw [polynomialMoment_multiply]
  simp only [polynomialStar, List.map_map, Function.comp_def]

end AlbertSequential
