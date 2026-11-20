/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritProjectiveStatistics
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! Rank-one trace readouts for the examples in the introduction. -/

@[expose] public section
namespace AlbertSequential
open Matrix
open scoped Matrix

/-- The forward-and-back sequence through a second rank-one projection
multiplies the one-test probability by the square of the transition overlap. -/
theorem rankOne_return_trace {n : Type*} [Fintype n] [DecidableEq n]
    (ρ P Q : Matrix n n ℂ) (o : ℝ)
    (hPQ : P * Q * P = (o : ℂ) • P) :
    (ρ * (P * Q * P * Q * P)).trace.re = (ρ * P).trace.re * o ^ 2 := by
  rw [hPQ, Matrix.smul_mul, Matrix.smul_mul, hPQ, smul_smul, Matrix.mul_smul, Matrix.trace_smul]
  simp [Complex.mul_re, pow_two]
  ring

/-- The rank-one compression premise above follows for the two actual qubit dyads. -/
theorem qubit_return_trace (ρ : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ) :
    let P := vecMulVec u (star u)
    let Q := vecMulVec v (star v)
    (ρ * (P * Q * P * Q * P)).trace.re =
      (ρ * P).trace.re * (Complex.normSq (star u ⬝ᵥ v)) ^ 2 := by
  apply rankOne_return_trace
  simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul, smul_smul]
  congr 1
  rw [← Complex.mul_conj]
  congr 1
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  change star (v i) * u i = star (star (u i)) * star (v i)
  rw [star_star, mul_comm]

private theorem trace_three_dyads (a b c : Fin 3 → ℂ) :
    (qutritRankOneProjection a * qutritRankOneProjection b * qutritRankOneProjection c).trace =
      qutritInner a b * qutritInner b c * qutritInner c a := by
  change ((vecMulVec a (star a) * vecMulVec b (star b)) * vecMulVec c (star c)).trace = _
  simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul, trace_smul,
    trace_vecMulVec, smul_eq_mul]
  rw [dotProduct_comm a (star c), ← mul_assoc]
  rfl

/-- Reading the real triangle phase from two all-yes words and one word with
a middle no. The matrices in the trace expressions are the chronological
updates from the maximally mixed qutrit after cyclically moving the endpoints. -/
theorem qutrit_triangle_readout (a b c : Fin 3 → ℂ) :
    let A := qutritRankOneProjection a
    let B := qutritRankOneProjection b
    let C := qutritRankOneProjection c
    (qutritInner a b * qutritInner b c * qutritInner c a).re =
      3/2 * ((A*C).trace.re/3 + (B*A*B*C).trace.re/3 -
        ((1-B)*A*(1-B)*C).trace.re/3) := by
  dsimp only
  have hforward := trace_three_dyads a b c
  have hback := trace_three_dyads b a c
  have hrev : (qutritInner b a * qutritInner a c * qutritInner c b).re =
      (qutritInner a b * qutritInner b c * qutritInner c a).re := by
    have h : qutritInner b a * qutritInner a c * qutritInner c b =
        star (qutritInner a b * qutritInner b c * qutritInner c a) := by
      simp only [star_mul, qutritInner_star]
      ring
    rw [h]
    rfl
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.trace_sub, Complex.sub_re, hforward, hback, hrev]
  ring

private theorem trace_sandwich (X P : ComplexMatrix3) (hP : P * P = P) :
    (P * X * P).trace = (X * P).trace := by
  rw [Matrix.trace_mul_cycle P X P, hP, Matrix.trace_mul_comm P X]

/-- The printed triangle readout with its three chronological Lüders word probabilities. -/
theorem qutrit_triangle_from_words (a b c : Fin 3 → ℂ)
    (ha : qutritInner a a = 1) (hc : qutritInner c c = 1) :
    let A := qutritRankOneProjection a
    let B := qutritRankOneProjection b
    let C := qutritRankOneProjection c
    let prob := fun w => (qutritCompleteTrace id ((1 / 3 : ℂ) • 1) w).re
    (qutritInner a b * qutritInner b c * qutritInner c a).re =
      3/2 * (prob [A,C] + prob [A,B,C] - prob [A,1-B,C]) := by
  let A := qutritRankOneProjection a
  let B := qutritRankOneProjection b
  let C := qutritRankOneProjection c
  have hA : A * A = A := qutritRankOneProjection_idempotent a ha
  have hC : C * C = C := qutritRankOneProjection_idempotent c hc
  have two : (qutritCompleteTrace id ((1/3 : ℂ) • 1) [A,C]).re = (A*C).trace.re/3 := by
    change (C * (A * ((1/3 : ℂ) • 1) * A) * C).trace.re = _
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hA, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.trace_smul, trace_sandwich _ _ hC]
    norm_num [smul_eq_mul, Complex.mul_re]; ring
  have three (X : ComplexMatrix3) : (qutritCompleteTrace id ((1/3 : ℂ) • 1) [A,X,C]).re =
      (X*A*X*C).trace.re/3 := by
    change (C * (X * (A * ((1/3 : ℂ) • 1) * A) * X) * C).trace.re = _
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hA, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      trace_sandwich _ _ hC]
    norm_num [smul_eq_mul, Complex.mul_re]; ring
  change _ = 3/2 * ((qutritCompleteTrace id _ [A,C]).re +
      (qutritCompleteTrace id _ [A,B,C]).re - (qutritCompleteTrace id _ [A,1-B,C]).re)
  rw [two, three, three]
  exact qutrit_triangle_readout a b c

end AlbertSequential
