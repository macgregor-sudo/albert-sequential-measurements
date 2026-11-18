/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectiveWordProbabilities
public import Interfaces.AlgebraicReconstruction
public import Mathlib.Tactic.Module

/-! Exact algebraic three-history purity identity, including zero histories.
The paper's mirror omits the final outcome before reversing. Native residual
vanishing/primitive-outcome hypotheses are separate and are not assumed here. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def purityMirror {ι : Type*} (v : Word ι) : Word ι := v.dropLast.reverse

def outcomePurityElement {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : ι → A) (q : Outcome ι) (v : Word ι) (c : ℝ) : A :=
  algebraicOutcome P q * wordOperator P v * algebraicOutcome P q -
    c • algebraicOutcome P q

theorem outcomePurityElement_yes {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : ι → A) (i : ι) (v : Word ι) (c : ℝ) :
    outcomePurityElement P (i, true) v c = purityElement P i v c := rfl

section ProjectionAlgebra
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : ι → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)

include hstar in
omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem wordAmplitude_reverse (w : Word ι) :
    wordAmplitude P w.reverse = star (wordAmplitude P w) := by
  induction w with
  | nil => simp only [List.reverse_nil, wordAmplitude_nil, star_one]
  | cons a w ih =>
      simp only [List.reverse_cons, wordAmplitude_append_singleton,
        wordAmplitude_cons, ih, star_mul, algebraicOutcome_star P hstar]

include hp hstar in
omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem purityMirror_amplitude (v : Word ι) :
    wordAmplitude P (purityMirror v) * wordAmplitude P v = wordOperator P v := by
  induction v with
  | nil => simp only [purityMirror, List.dropLast_nil, List.reverse_nil,
      wordAmplitude_nil, wordOperator_nil, mul_one]
  | cons a v ih =>
      cases v with
      | nil =>
          simp only [purityMirror, List.dropLast_singleton, List.reverse_nil,
            wordAmplitude_nil, one_mul, wordAmplitude_singleton,
            wordOperator_singleton P hp hstar]
      | cons b v =>
          have hmirror : purityMirror (a :: b :: v) = purityMirror (b :: v) ++ [a] := by
            simp only [purityMirror, List.dropLast_cons_cons, List.reverse_cons]
          rw [hmirror, wordAmplitude_append_singleton, wordAmplitude_cons,
            wordOperator_cons P hstar]
          calc
            (algebraicOutcome P a * wordAmplitude P (purityMirror (b :: v))) *
                (wordAmplitude P (b :: v) * algebraicOutcome P a) =
                algebraicOutcome P a *
                  (wordAmplitude P (purityMirror (b :: v)) * wordAmplitude P (b :: v)) *
                  algebraicOutcome P a := by simp only [mul_assoc]
            _ = _ := by rw [ih]

include hp hstar in
omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem purityLong_amplitude (q : Outcome ι) (v t : Word ι) :
    wordAmplitude P (t ++ [q] ++ v ++ purityMirror v ++ [q]) =
      (algebraicOutcome P q * wordOperator P v * algebraicOutcome P q) *
        wordAmplitude P t := by
  simp only [wordAmplitude_append, wordAmplitude_singleton]
  calc
    algebraicOutcome P q *
        (wordAmplitude P (purityMirror v) *
          (wordAmplitude P v * (algebraicOutcome P q * wordAmplitude P t))) =
        (algebraicOutcome P q *
          (wordAmplitude P (purityMirror v) * wordAmplitude P v) *
          algebraicOutcome P q) * wordAmplitude P t := by simp only [mul_assoc]
    _ = _ := by rw [purityMirror_amplitude P hp hstar]

include hstar in
omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem purityMiddle_operator (q : Outcome ι) (v t : Word ι) :
    wordOperator P (t ++ [q] ++ v) =
      star (wordAmplitude P t) *
        (algebraicOutcome P q * wordOperator P v * algebraicOutcome P q) *
        wordAmplitude P t := by
  simp only [wordOperator_append, wordAmplitude_append, wordAmplitude_singleton,
    star_mul, algebraicOutcome_star P hstar, mul_assoc]

include hp hstar in
omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem purityShort_operator (q : Outcome ι) (t : Word ι) :
    wordOperator P (t ++ [q]) = star (wordAmplitude P t) *
      algebraicOutcome P q * wordAmplitude P t := by
  rw [wordOperator_append, wordOperator_singleton P hp hstar]

include hstar in
omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem outcomePurityElement_star (q : Outcome ι) (v : Word ι) (c : ℝ) :
    star (outcomePurityElement P q v c) = outcomePurityElement P q v c := by
  simp only [outcomePurityElement, star_sub, star_mul, star_smul, star_trivial,
    algebraicOutcome_star P hstar, wordOperator_star, mul_assoc]

include hp in
omit [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem outcomePurityElement_right_support (q : Outcome ι) (v : Word ι) (c : ℝ) :
    outcomePurityElement P q v c * algebraicOutcome P q = outcomePurityElement P q v c := by
  simp only [outcomePurityElement, sub_mul, smul_mul_assoc]
  rw [mul_assoc (algebraicOutcome P q * wordOperator P v), algebraicOutcome_idempotent P hp]

include hp in
omit [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem outcomePurityElement_append_base (q : Outcome ι) (v t : Word ι) (c : ℝ) :
    outcomePurityElement P q v c * wordAmplitude P (t ++ [q]) =
      outcomePurityElement P q v c * wordAmplitude P t := by
  rw [wordAmplitude_append_singleton, ← mul_assoc, outcomePurityElement_right_support P hp]

include hp hstar in
theorem purityResidual_operator (q : Outcome ι) (v t : Word ι) (c : ℝ) :
    star (outcomePurityElement P q v c * wordAmplitude P t) *
      (outcomePurityElement P q v c * wordAmplitude P t) =
      wordOperator P (t ++ [q] ++ v ++ purityMirror v ++ [q]) -
      (2 * c) • wordOperator P (t ++ [q] ++ v) +
      (c ^ 2) • wordOperator P (t ++ [q]) := by
  let Q := algebraicOutcome P q
  let B := Q * wordOperator P v * Q
  have hQQ : Q * Q = Q := algebraicOutcome_idempotent P hp q
  have hBQ : B * Q = B := by
    dsimp only [B]
    rw [mul_assoc (Q * wordOperator P v), hQQ]
  have hQB : Q * B = B := by
    dsimp only [B]
    calc
      Q * (Q * wordOperator P v * Q) = (Q * Q) * wordOperator P v * Q := by
        simp only [mul_assoc]
      _ = _ := by rw [hQQ]
  have hBstar : star B = B := by
    dsimp only [B, Q]
    simp only [star_mul, algebraicOutcome_star P hstar, wordOperator_star, mul_assoc]
  have hsquare : outcomePurityElement P q v c * outcomePurityElement P q v c =
      B * B - (2 * c) • B + (c ^ 2) • Q := by
    change (B - c • Q) * (B - c • Q) = _
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hBQ, hQB, hQQ]
    module
  have hlong : wordOperator P (t ++ [q] ++ v ++ purityMirror v ++ [q]) =
      star (wordAmplitude P t) * (B * B) * wordAmplitude P t := by
    change star (wordAmplitude P (t ++ [q] ++ v ++ purityMirror v ++ [q])) *
      wordAmplitude P (t ++ [q] ++ v ++ purityMirror v ++ [q]) = _
    rw [purityLong_amplitude P hp hstar]
    change star (B * wordAmplitude P t) * (B * wordAmplitude P t) = _
    rw [star_mul, hBstar]
    simp only [mul_assoc]
  rw [star_mul, outcomePurityElement_star P hstar]
  calc
    (star (wordAmplitude P t) * outcomePurityElement P q v c) *
        (outcomePurityElement P q v c * wordAmplitude P t) =
        star (wordAmplitude P t) *
          (outcomePurityElement P q v c * outcomePurityElement P q v c) *
          wordAmplitude P t := by simp only [mul_assoc]
    _ = _ := by
      rw [hsquare, hlong, purityMiddle_operator P hstar, purityShort_operator P hp hstar]
      simp only [B, Q, mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc]

end ProjectionAlgebra

theorem purityResidual_threeHistories
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v t : Word ι) (c : ℝ) :
    M.squareMass (outcomePurityElement M.projection q v c * wordAmplitude M.projection t) =
      M.probability (t ++ [q] ++ v ++ purityMirror v ++ [q]) -
      2 * c * M.probability (t ++ [q] ++ v) +
      c ^ 2 * M.probability (t ++ [q]) := by
  unfold AlgebraicProjectiveData.squareMass
  rw [purityResidual_operator M.projection M.idempotent M.selfAdjoint]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, AlgebraicProjectiveData.probability]

/-- A null history stays null under the full residual, with no positive-history
conditioning and no inference that its amplitude itself vanishes. -/
theorem purityResidual_zero_history
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v t : Word ι) (c : ℝ) (ht : M.probability t = 0) :
    M.squareMass (outcomePurityElement M.projection q v c * wordAmplitude M.projection t) = 0 := by
  rw [purityResidual_threeHistories]
  have hl := M.probability_append_eq_zero t ([q] ++ v ++ purityMirror v ++ [q]) ht
  have hm := M.probability_append_eq_zero t ([q] ++ v) ht
  have hs := M.probability_append_eq_zero t [q] ht
  rw [show M.probability (t ++ [q] ++ v ++ purityMirror v ++ [q]) = 0 by
    simpa only [List.append_assoc] using hl]
  rw [show M.probability (t ++ [q] ++ v) = 0 by
    simpa only [List.append_assoc] using hm, hs]
  ring

end AlbertSequential
