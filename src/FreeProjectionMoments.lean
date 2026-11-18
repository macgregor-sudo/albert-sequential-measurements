/- SPDX-License-Identifier: Apache-2.0 -/
module
public import UniversalProjectionAlgebra
public import ProjectionPolynomialEvaluation

/-! The actual moment functional on the free algebra, before quotienting.
Finite list polynomials are used for proof expansions, not computational data. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

instance projectionFreeStarModule (n : ℕ) : StarModule ℝ (ProjectionFreeAlgebra n) where
  star_smul r x := by simpa only [star_trivial] using projectionFreeAlgebra_star_smul r x

def freeMomentFunctional {n : ℕ} (m : ProjectionMoments n) :
    ProjectionFreeAlgebra n →ₗ[ℝ] ℝ :=
  ((MonoidAlgebra.basis (FreeMonoid (Fin n)) ℝ).constr ℝ
    (fun w => m w.toList)).comp
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℝ) (X := Fin n)).toLinearMap

theorem freeAlgebra_equiv_monomial {n : ℕ} (w : ProjectionMonomial n) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (evaluateMonomial (FreeAlgebra.ι ℝ) w) =
    MonoidAlgebra.of ℝ (FreeMonoid (Fin n)) (FreeMonoid.ofList w) := by
  induction w with
  | nil => simp only [evaluateMonomial_nil, map_one, FreeMonoid.ofList_nil]
  | cons i w ih =>
      rw [evaluateMonomial_cons, map_mul, ih, FreeMonoid.ofList_cons, map_mul]
      congr 1
      simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

theorem freeMomentFunctional_monomial {n : ℕ} (m : ProjectionMoments n)
    (w : ProjectionMonomial n) :
    freeMomentFunctional m (evaluateMonomial (FreeAlgebra.ι ℝ) w) = m w := by
  simp only [freeMomentFunctional, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    freeAlgebra_equiv_monomial]
  exact (MonoidAlgebra.basis (FreeMonoid (Fin n)) ℝ).constr_basis ℝ
    (fun v => m v.toList) (FreeMonoid.ofList w)

theorem freeMomentFunctional_polynomial {n : ℕ} (m : ProjectionMoments n)
    (c : ProjectionPolynomial n) :
    freeMomentFunctional m (evaluateProjectionPolynomial (FreeAlgebra.ι ℝ) c) =
    polynomialMoment m c := by
  induction c with
  | nil => simp only [evaluateProjectionPolynomial_nil, map_zero,
      polynomialMoment, List.map_nil, List.sum_nil]
  | cons x c ih =>
      rcases x with ⟨r, w⟩
      rw [evaluateProjectionPolynomial_cons, map_add, map_smul, ih,
        freeMomentFunctional_monomial]
      rfl

/-- Every free algebra element has a finite list-polynomial expression. -/
theorem freeAlgebra_exists_polynomial {n : ℕ} (x : ProjectionFreeAlgebra n) :
    ∃ c : ProjectionPolynomial n,
      evaluateProjectionPolynomial (FreeAlgebra.ι ℝ) c = x := by
  induction x using FreeAlgebra.induction with
  | grade0 r =>
      refine ⟨[(r, [])], ?_⟩
      simp only [evaluateProjectionPolynomial_cons, evaluateProjectionPolynomial_nil,
        evaluateMonomial_nil, add_zero, Algebra.smul_def, mul_one]
  | grade1 i =>
      refine ⟨[(1, [i])], ?_⟩
      simp only [evaluateProjectionPolynomial_cons, evaluateProjectionPolynomial_nil,
        evaluateMonomial_singleton, one_smul, add_zero]
  | mul a b ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨polynomialMultiply c d, evaluateProjectionPolynomial_multiply _ c d⟩
  | add a b ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c ++ d, evaluateProjectionPolynomial_append _ c d⟩

theorem freeMomentFunctional_one {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) : freeMomentFunctional m 1 = 1 := by
  exact (freeMomentFunctional_monomial m []).trans hm.normalized

theorem freeMomentFunctional_star {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : ProjectionFreeAlgebra n) :
    freeMomentFunctional m (star x) = freeMomentFunctional m x := by
  obtain ⟨c, rfl⟩ := freeAlgebra_exists_polynomial x
  rw [← evaluateProjectionPolynomial_star _ (fun i => FreeAlgebra.star_ι i),
    freeMomentFunctional_polynomial, freeMomentFunctional_polynomial]
  simp only [polynomialMoment, polynomialStar, List.map_map, Function.comp_def, hm.reversal]

theorem freeMomentFunctional_positive {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : ProjectionFreeAlgebra n) :
    0 ≤ freeMomentFunctional m (star x * x) := by
  obtain ⟨c, rfl⟩ := freeAlgebra_exists_polynomial x
  rw [← evaluateProjectionPolynomial_star _ (fun i => FreeAlgebra.star_ι i),
    ← evaluateProjectionPolynomial_multiply, freeMomentFunctional_polynomial,
    polynomialMoment_star_square]
  exact hm.positive_polynomial_squares c

end AlbertSequential
