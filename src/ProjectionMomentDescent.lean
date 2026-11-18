/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FreeProjectionMoments
import all Mathlib.Algebra.RingQuot

/-! A linear state descends through all contextual idempotence relations.
The state is not multiplicative; no ring-homomorphism lift is used for it. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

private theorem freeMoment_monomial_context {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (u v : ProjectionMonomial n) (i : Fin n) :
    freeMomentFunctional m ((evaluateMonomial (FreeAlgebra.ι ℝ) u *
      (FreeAlgebra.ι ℝ i * FreeAlgebra.ι ℝ i)) * evaluateMonomial (FreeAlgebra.ι ℝ) v) =
    freeMomentFunctional m ((evaluateMonomial (FreeAlgebra.ι ℝ) u *
      FreeAlgebra.ι ℝ i) * evaluateMonomial (FreeAlgebra.ι ℝ) v) := by
  have h := hm.idempotent_context u v i
  rw [← freeMomentFunctional_monomial m (u ++ [i, i] ++ v),
    ← freeMomentFunctional_monomial m (u ++ [i] ++ v)] at h
  simpa only [evaluateMonomial_append, evaluateMonomial_cons,
    evaluateMonomial_nil, mul_one] using h

theorem freeMomentFunctional_generator_context {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (a b : ProjectionFreeAlgebra n) (i : Fin n) :
    freeMomentFunctional m (a * (FreeAlgebra.ι ℝ i * FreeAlgebra.ι ℝ i) * b) =
    freeMomentFunctional m (a * FreeAlgebra.ι ℝ i * b) := by
  obtain ⟨c, rfl⟩ := freeAlgebra_exists_polynomial a
  obtain ⟨d, rfl⟩ := freeAlgebra_exists_polynomial b
  induction c with
  | nil => simp only [evaluateProjectionPolynomial_nil, zero_mul, map_zero]
  | cons x c ih =>
      rcases x with ⟨r, u⟩
      simp only [evaluateProjectionPolynomial_cons, add_mul, smul_mul_assoc,
        map_add, map_smul, ih]
      congr 1
      congr 1
      clear ih
      induction d with
      | nil => simp only [evaluateProjectionPolynomial_nil, mul_zero, map_zero]
      | cons y d ihd =>
          rcases y with ⟨s, v⟩
          simp only [evaluateProjectionPolynomial_cons, mul_add, mul_smul_comm,
            map_add, map_smul, ihd, freeMoment_monomial_context hm]

theorem freeMomentFunctional_relation_context {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) {x y : ProjectionFreeAlgebra n}
    (h : RingQuot.Rel (ProjectionIdempotence n) x y) (a b : ProjectionFreeAlgebra n) :
    freeMomentFunctional m (a * x * b) = freeMomentFunctional m (a * y * b) := by
  induction h generalizing a b with
  | of h =>
      cases h with
      | generator i => exact freeMomentFunctional_generator_context hm a b i
  | add_left h ih =>
      simpa only [mul_add, add_mul, map_add] using
        congrArg (fun z => z + freeMomentFunctional m (a * _ * b)) (ih a b)
  | mul_left h ih => simpa only [mul_assoc] using ih a (_ * b)
  | mul_right h ih => simpa only [mul_assoc] using ih (a * _) b

def descendedMomentFunction {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : UniversalProjectionAlgebra n) : ℝ :=
  Quot.lift (freeMomentFunctional m) (fun a b h => by
    simpa only [one_mul, mul_one] using freeMomentFunctional_relation_context hm h 1 1) x.toQuot

private theorem descendedMomentFunction_mk {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : ProjectionFreeAlgebra n) :
    descendedMomentFunction hm (projectionQuotient n x) = freeMomentFunctional m x := by
  simp only [descendedMomentFunction, projectionQuotient,
    RingQuot.mkAlgHom, RingQuot.mkRingHom]
  rfl

def projectionMomentState {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) : UniversalProjectionAlgebra n →ₗ[ℝ] ℝ where
  toFun := descendedMomentFunction hm
  map_add' x y := by
    obtain ⟨a, rfl⟩ := projectionQuotient_surjective n x
    obtain ⟨b, rfl⟩ := projectionQuotient_surjective n y
    rw [← map_add, descendedMomentFunction_mk, descendedMomentFunction_mk,
      descendedMomentFunction_mk, map_add]
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := projectionQuotient_surjective n x
    rw [← map_smul, descendedMomentFunction_mk, descendedMomentFunction_mk, map_smul]
    rfl

theorem projectionMomentState_quotient {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : ProjectionFreeAlgebra n) :
    projectionMomentState hm (projectionQuotient n x) = freeMomentFunctional m x :=
  descendedMomentFunction_mk hm x

theorem projectionMomentState_one {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) : projectionMomentState hm 1 = 1 := by
  rw [← map_one (projectionQuotient n), projectionMomentState_quotient,
    freeMomentFunctional_one hm]

theorem projectionMomentState_star {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : UniversalProjectionAlgebra n) :
    projectionMomentState hm (star x) = projectionMomentState hm x := by
  obtain ⟨a, rfl⟩ := projectionQuotient_surjective n x
  rw [projectionQuotient_star, projectionMomentState_quotient,
    projectionMomentState_quotient, freeMomentFunctional_star hm]

theorem projectionMomentState_positive {n : ℕ} {m : ProjectionMoments n}
    (hm : AdmissibleProjectionMoments n m) (x : UniversalProjectionAlgebra n) :
    0 ≤ projectionMomentState hm (star x * x) := by
  obtain ⟨a, rfl⟩ := projectionQuotient_surjective n x
  rw [projectionQuotient_star, ← map_mul, projectionMomentState_quotient]
  exact freeMomentFunctional_positive hm a

end AlbertSequential
