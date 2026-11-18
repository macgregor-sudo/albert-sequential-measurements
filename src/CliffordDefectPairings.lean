/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CliffordDefectData

/-! Exact defect pairings for skew-adjoint left multiplication. The functional
is star-symmetric but need not be positive, normalized, faithful or tracial. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
section DefectPairings
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_skew_left (N : A) (hN : star N = -N) (x y : A) :
    realStarPairing φ (N * x) y = -realStarPairing φ x (N * y) := by
  simp only [realStarPairing, star_mul, hN, mul_neg, neg_mul, map_neg, mul_assoc]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_skew_inner (N : A) (hN : star N = -N) (x y : A) :
    realStarPairing φ x (N * y) = -realStarPairing φ (N * x) y := by
  rw [realStarPairing_skew_left φ N hN]
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_skew_square (N : A) (hN : star N = -N) (x : A) (m : ℝ) :
    realStarPairing φ (N * x) (N * x) =
      m * realStarPairing φ x x - realStarPairing φ x (N * (N * x) + m • x) := by
  rw [realStarPairing_skew_left φ N hN, realStarPairing_add_right,
    realStarPairing_smul_right]
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem cliffordGramDefect_pair (hstar : ∀ x, φ (star x) = φ x)
    (N : Fin 3 → A) (hN : ∀ i, star (N i) = -N i) (ξ : A)
    (s : CliffordScalarParameters) (i j : Fin 3) :
    cliffordGramDefect φ N ξ s i j =
      -(1 / 2 : ℝ) * realStarPairing φ ξ (cliffordPairDefect N s i j ξ) := by
  have hi := realStarPairing_skew_inner φ (N i) (hN i) ξ (N j * ξ)
  have hj := realStarPairing_skew_inner φ (N j) (hN j) ξ (N i * ξ)
  unfold cliffordGramDefect cliffordPairDefect
  rw [realStarPairing_add_right, realStarPairing_add_right, realStarPairing_smul_right,
    hi, hj, realStarPairing_symmetric φ hstar (N j * ξ) (N i * ξ)]
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem cliffordGramDefect_diagonal (N : Fin 3 → A)
    (hN : ∀ i, star (N i) = -N i) (ξ : A) (s : CliffordScalarParameters) (i : Fin 3) :
    cliffordGramDefect φ N ξ s i i =
      -realStarPairing φ ξ (cliffordSquareDefect N s i ξ) := by
  unfold cliffordGramDefect cliffordSquareDefect
  rw [realStarPairing_skew_square φ (N i) (hN i) ξ (s.diagonal i), s.gramMatrix_diagonal]
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem cliffordCrossDefect_first (hstar : ∀ x, φ (star x) = φ x)
    (N : Fin 3 → A) (hN : ∀ i, star (N i) = -N i) (ξ : A)
    (s : CliffordScalarParameters) :
    cliffordCrossDefect φ N ξ s 0 =
      -s.m1 * cliffordGramDefect φ N ξ s 1 2 -
        realStarPairing φ (N 1 * N 2 * ξ) (cliffordSquareDefect N s 0 ξ) := by
  have hz : realStarPairing φ (cliffordTripleVector N ξ) (N 0 * ξ) =
      -realStarPairing φ (N 1 * N 2 * ξ) (N 0 * (N 0 * ξ)) := by
    simpa only [cliffordTripleVector, mul_assoc] using
      realStarPairing_skew_left φ (N 0) (hN 0) (N 1 * (N 2 * ξ)) (N 0 * ξ)
  have h23 : realStarPairing φ (N 1 * N 2 * ξ) ξ =
      -realStarPairing φ (N 1 * ξ) (N 2 * ξ) := by
    simpa only [mul_assoc, realStarPairing_symmetric φ hstar (N 2 * ξ) (N 1 * ξ)] using
      realStarPairing_skew_left φ (N 1) (hN 1) (N 2 * ξ) ξ
  simp only [cliffordCrossDefect, cliffordGramDefect, cliffordSquareDefect,
    CliffordScalarParameters.expectedCross, CliffordScalarParameters.gramMatrix,
    CliffordScalarParameters.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [realStarPairing_add_right, realStarPairing_smul_right, hz, h23]
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem cliffordCrossDefect_second (hstar : ∀ x, φ (star x) = φ x)
    (N : Fin 3 → A) (hN : ∀ i, star (N i) = -N i) (ξ : A)
    (s : CliffordScalarParameters) :
    cliffordCrossDefect φ N ξ s 1 =
      s.m2 * cliffordGramDefect φ N ξ s 0 2 -
        2 * s.u * cliffordGramDefect φ N ξ s 1 2 -
        realStarPairing φ (N 2 * ξ) (cliffordSquareDefect N s 1 (N 0 * ξ)) -
        realStarPairing φ (N 1 * N 2 * ξ) (cliffordPairDefect N s 0 1 ξ) := by
  have hz : realStarPairing φ (cliffordTripleVector N ξ) (N 1 * ξ) =
      -realStarPairing φ (N 1 * N 2 * ξ) (N 0 * (N 1 * ξ)) := by
    simpa only [cliffordTripleVector, mul_assoc] using
      realStarPairing_skew_left φ (N 0) (hN 0) (N 1 * (N 2 * ξ)) (N 1 * ξ)
  have hc : N 0 * (N 1 * ξ) =
      cliffordPairDefect N s 0 1 ξ - N 1 * (N 0 * ξ) - (2 * s.u) • ξ := by
    simp only [cliffordPairDefect, CliffordScalarParameters.gramMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  have hnn : realStarPairing φ (N 1 * N 2 * ξ) (N 1 * (N 0 * ξ)) =
      -realStarPairing φ (N 2 * ξ) (N 1 * (N 1 * (N 0 * ξ))) := by
    simpa only [mul_assoc] using
      realStarPairing_skew_left φ (N 1) (hN 1) (N 2 * ξ) (N 1 * (N 0 * ξ))
  have h23 : realStarPairing φ (N 1 * N 2 * ξ) ξ =
      -realStarPairing φ (N 1 * ξ) (N 2 * ξ) := by
    simpa only [mul_assoc, realStarPairing_symmetric φ hstar (N 2 * ξ) (N 1 * ξ)] using
      realStarPairing_skew_left φ (N 1) (hN 1) (N 2 * ξ) ξ
  rw [hc, realStarPairing_sub_right, realStarPairing_sub_right,
    realStarPairing_smul_right, hnn, h23] at hz
  simp only [cliffordCrossDefect, cliffordGramDefect, cliffordSquareDefect,
    CliffordScalarParameters.expectedCross, CliffordScalarParameters.gramMatrix,
    CliffordScalarParameters.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [realStarPairing_add_right, realStarPairing_smul_right, hz,
    realStarPairing_symmetric φ hstar (N 2 * ξ) (N 0 * ξ)]
  ring

theorem cliffordCrossDefect_third (hstar : ∀ x, φ (star x) = φ x)
    (N : Fin 3 → A) (hN : ∀ i, star (N i) = -N i) (ξ : A)
    (s : CliffordScalarParameters) :
    cliffordCrossDefect φ N ξ s 2 =
      -s.m3 * cliffordGramDefect φ N ξ s 0 1 +
        2 * s.v * cliffordGramDefect φ N ξ s 1 2 -
        2 * s.w * cliffordGramDefect φ N ξ s 0 2 -
        realStarPairing φ (N 0 * N 1 * ξ) (cliffordSquareDefect N s 2 ξ) +
        realStarPairing φ
          (N 0 * cliffordPairDefect N s 1 2 ξ - cliffordPairDefect N s 0 2 (N 1 * ξ))
          (N 2 * ξ) := by
  let V := N 0 * cliffordPairDefect N s 1 2 ξ - cliffordPairDefect N s 0 2 (N 1 * ξ)
  have hz : cliffordTripleVector N ξ = N 2 * (N 0 * N 1 * ξ) +
      (2 * s.v) • (N 1 * ξ) - (2 * s.w) • (N 0 * ξ) + V := by
    simp only [V, cliffordTripleVector, cliffordPairDefect,
      CliffordScalarParameters.gramMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      mul_add, mul_smul_comm, mul_assoc]
    module
  have hnn := realStarPairing_skew_left φ (N 2) (hN 2) (N 0 * N 1 * ξ) (N 2 * ξ)
  have h12 : realStarPairing φ (N 0 * N 1 * ξ) ξ =
      -realStarPairing φ (N 0 * ξ) (N 1 * ξ) := by
    simpa only [mul_assoc, realStarPairing_symmetric φ hstar (N 1 * ξ) (N 0 * ξ)] using
      realStarPairing_skew_left φ (N 0) (hN 0) (N 1 * ξ) ξ
  unfold cliffordCrossDefect cliffordGramDefect
  rw [hz, realStarPairing_add_left, realStarPairing_sub_left,
    realStarPairing_add_left, realStarPairing_smul_left, realStarPairing_smul_left, hnn]
  simp only [cliffordSquareDefect, CliffordScalarParameters.diagonal,
    CliffordScalarParameters.expectedCross, CliffordScalarParameters.gramMatrix,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [realStarPairing_add_right, realStarPairing_smul_right, h12]
  change _ = _ + realStarPairing φ V (N 2 * ξ)
  ring

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem cliffordNormDefect_reduction (N : Fin 3 → A)
    (hN : ∀ i, star (N i) = -N i) (ξ : A) (s : CliffordScalarParameters) :
    cliffordNormDefect φ N ξ s =
      -realStarPairing φ (N 1 * N 2 * ξ) (cliffordSquareDefect N s 0 (N 1 * N 2 * ξ)) -
        s.m1 * realStarPairing φ (N 2 * ξ) (cliffordSquareDefect N s 1 (N 2 * ξ)) -
        s.m1 * s.m2 * realStarPairing φ ξ (cliffordSquareDefect N s 2 ξ) := by
  have h0 : realStarPairing φ (cliffordTripleVector N ξ) (cliffordTripleVector N ξ) =
      s.m1 * realStarPairing φ (N 1 * N 2 * ξ) (N 1 * N 2 * ξ) -
        realStarPairing φ (N 1 * N 2 * ξ) (cliffordSquareDefect N s 0 (N 1 * N 2 * ξ)) := by
    simpa only [cliffordTripleVector, cliffordSquareDefect, CliffordScalarParameters.diagonal,
      Matrix.cons_val_zero, mul_assoc] using
      realStarPairing_skew_square φ (N 0) (hN 0) (N 1 * N 2 * ξ) s.m1
  have h1 : realStarPairing φ (N 1 * N 2 * ξ) (N 1 * N 2 * ξ) =
      s.m2 * realStarPairing φ (N 2 * ξ) (N 2 * ξ) -
        realStarPairing φ (N 2 * ξ) (cliffordSquareDefect N s 1 (N 2 * ξ)) := by
    simpa only [cliffordSquareDefect, CliffordScalarParameters.diagonal,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_assoc] using
      realStarPairing_skew_square φ (N 1) (hN 1) (N 2 * ξ) s.m2
  have h2 : realStarPairing φ (N 2 * ξ) (N 2 * ξ) =
      s.m3 * realStarPairing φ ξ ξ - realStarPairing φ ξ (cliffordSquareDefect N s 2 ξ) := by
    simpa only [cliffordSquareDefect, CliffordScalarParameters.diagonal,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      realStarPairing_skew_square φ (N 2) (hN 2) ξ s.m3
  rw [cliffordNormDefect, h0, h1, h2]
  ring

end DefectPairings
end AlbertSequential
