module

import AppF.SecondOrderCoefficientIdeal

open AlbertSequential AlbertSequential.AppF

example (x y z : SecondOrderCoefficients) :
    coefficientProduct (coefficientProduct x y) z - coefficientProduct x (coefficientProduct y z)
      ∈ secondOrderCoefficientIdeal := coefficientAssociator_mem x y z

example :
    Submodule.span ℝ (Set.range fun t : SecondOrderCoefficients × SecondOrderCoefficients × SecondOrderCoefficients =>
      coefficientProduct (coefficientProduct t.1 t.2.1) t.2.2 -
        coefficientProduct t.1 (coefficientProduct t.2.1 t.2.2)) = secondOrderCoefficientIdeal :=
  span_coefficientAssociators

example (x y : SecondOrderCoefficients) :
    coefficientQuotientEquiv (Submodule.Quotient.mk (coefficientProduct x y)) =
      coefficientQuotientEquiv (Submodule.Quotient.mk x) * coefficientQuotientEquiv (Submodule.Quotient.mk y) :=
  coefficientQuotient_product x y

example (x : E2) (hx : x.val ∈ Kso) {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] (f : E2 →ₗ[ℝ] A) (hf : IsE2JordanHom f) : f x = 0 :=
  E2_jordanHom_kills_K f hf x hx

example (x : E2) :
    x.val ∈ Kso ↔ ∀ (A : Type) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A]
      [SMulCommClass ℝ A A] (f : E2 →ₗ[ℝ] A), IsE2JordanHom f → f x = 0 :=
  secondOrder_universal_kernel x

example (x : SecondOrderCoefficients) (hx : x ∈ secondOrderCoefficientIdeal) :
    (star x.1, octonionConj x.2.1, octonionConj x.2.2) ∈ secondOrderCoefficientIdeal := by
  obtain ⟨h0, h1, hre, him⟩ := (mem_secondOrderCoefficientIdeal x).mp hx
  apply (mem_secondOrderCoefficientIdeal _).mpr
  exact ⟨by rw [h0, star_zero], by rw [h1, octonionConj_zero],
    by simpa [octonionConj] using hre, by simp [octonionConj, him]⟩

#print axioms coefficientReduction_product
#print axioms mem_secondOrderCoefficientIdeal
#print axioms secondOrderCoefficientIdeal_twoSided
#print axioms coefficientQuotient_product
#print axioms span_coefficientAssociators
#print axioms secondOrder_universal_kernel
#print axioms E2_jordanHom_kills_K
