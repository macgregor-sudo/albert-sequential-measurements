/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectionPolynomialEvaluation
public import ProjectiveWordProbabilities
public import Mathlib.Tactic.Linarith

/-! Every actual algebraic projective model yields admissible projection
moments and exactly the same all-word probabilities. This is one-way soundness,
not a quotient/Hilbert realization of an arbitrary admissible moment family. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData (Fin n) A)

theorem polynomialMoment_eq_state_evaluation (c : ProjectionPolynomial n) :
    polynomialMoment (momentsOfProjectiveData M) c =
      M.state (evaluateProjectionPolynomial M.projection c) := by
  induction c with
  | nil => simp only [polynomialMoment, List.map_nil, List.sum_nil,
      evaluateProjectionPolynomial_nil, map_zero]
  | cons x c ih =>
      rcases x with ⟨r, w⟩
      change r * momentsOfProjectiveData M w +
        polynomialMoment (momentsOfProjectiveData M) c = _
      rw [evaluateProjectionPolynomial_cons, map_add, map_smul, ← ih]
      rfl

theorem squareMass_evaluateMonomial_le_one (w : ProjectionMonomial n) :
    M.squareMass (evaluateMonomial M.projection w) ≤ 1 := by
  rw [evaluateMonomial_eq_reversed_yes_amplitude]
  have h := M.squareMass_word_le (w.reverse.map (fun i => (i, true))) 1
  simpa only [mul_one, M.squareMass_one] using h

theorem momentsOfProjectiveData_bounded (w : ProjectionMonomial n) :
    -1 ≤ momentsOfProjectiveData M w ∧ momentsOfProjectiveData M w ≤ 1 := by
  let x := evaluateMonomial M.projection w
  have hq : M.squareMass x ≤ 1 := squareMass_evaluateMonomial_le_one M w
  have hp := M.state_positive (1 + x)
  have hm := M.state_positive (1 - x)
  have hep : M.state (star (1 + x) * (1 + x)) =
      1 + 2 * M.state x + M.squareMass x := by
    simp only [star_add, star_one, add_mul, mul_add, one_mul, mul_one,
      map_add, M.state_star, M.state_unit, AlgebraicProjectiveData.squareMass]
    ring
  have hem : M.state (star (1 - x) * (1 - x)) =
      1 - 2 * M.state x + M.squareMass x := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
      map_sub, M.state_star, M.state_unit, AlgebraicProjectiveData.squareMass]
    ring
  rw [hep] at hp
  rw [hem] at hm
  change -1 ≤ M.state x ∧ M.state x ≤ 1
  constructor <;> linarith

theorem momentsOfProjectiveData_admissible :
    AdmissibleProjectionMoments n (momentsOfProjectiveData M) where
  normalized := by simp only [momentsOfProjectiveData, evaluateMonomial_nil, M.state_unit]
  reversal := by
    intro w
    change M.state (evaluateMonomial M.projection w.reverse) =
      M.state (evaluateMonomial M.projection w)
    rw [evaluateMonomial_reverse M.projection M.selfAdjoint, M.state_star]
  idempotent_context := by
    intro u v i
    change M.state (evaluateMonomial M.projection (u ++ [i, i] ++ v)) =
      M.state (evaluateMonomial M.projection (u ++ [i] ++ v))
    rw [evaluateMonomial_idempotent_context M.projection M.idempotent]
  positive_polynomial_squares := by
    intro c
    rw [← polynomialMoment_star_square,
      polynomialMoment_eq_state_evaluation M,
      evaluateProjectionPolynomial_multiply,
      evaluateProjectionPolynomial_star M.projection M.selfAdjoint]
    exact M.state_positive _
  bounded := momentsOfProjectiveData_bounded M

theorem momentWordProbability_eq_probability (w : Word (Fin n)) :
    momentWordProbability (momentsOfProjectiveData M) w = M.probability w := by
  change polynomialMoment (momentsOfProjectiveData M) (effectPolynomial w) =
    M.state (wordOperator M.projection w)
  rw [polynomialMoment_eq_state_evaluation,
    evaluate_effectPolynomial M.projection M.selfAdjoint]

theorem algebraicMomentBinding : AlgebraicMomentBinding M where
  admissible := momentsOfProjectiveData_admissible M
  probabilities := momentWordProbability_eq_probability M

end AlbertSequential
