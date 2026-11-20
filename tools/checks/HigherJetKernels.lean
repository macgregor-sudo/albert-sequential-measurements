module

import AppF.HigherJetNativeOrthogonality

open AlbertSequential AlbertSequential.AppF HigherJetCoefficients

example : Module.finrank ℝ (higherJetHermitianKernel .real) = 21 :=
  higherJetHermitianKernel_finrank .real

example : Module.finrank ℝ (higherJetHermitianKernel .quaternionic) = 12 :=
  higherJetHermitianKernel_finrank .quaternionic

example (M : HigherJetHermitian .real 3) :
    (∀ n : Fin 4, n ≠ 3 → higherJetAlbertCoefficient M n = 0) ∧
      (∀ w : Albert, w ∈ (H3Subalgebra .R).carrier → tracePairing w (higherJetAlbertCoefficient M 3) = 0) ↔
    ∀ (A : Type) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
      (f : HigherJetHermitian .real 3 →ₗ[ℝ] A),
      IsCoefficientJordanMap (conjugate .real 3) bilinear (conjugate_product .real 3) f → f M = 0 :=
  (higherJetHermitianKernel_iff_top_orthogonal .real M).symm.trans
    (higherJetHermitian_universal_kernel .real M)

example (M : HigherJetHermitian .quaternionic 1) :
    (∀ n : Fin 4, n ≠ 1 → higherJetAlbertCoefficient M n = 0) ∧
      (∀ w : Albert, w ∈ (H3Subalgebra .H).carrier → tracePairing w (higherJetAlbertCoefficient M 1) = 0) ↔
    ∀ (A : Type) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
      (f : HigherJetHermitian .quaternionic 1 →ₗ[ℝ] A),
      IsCoefficientJordanMap (conjugate .quaternionic 1) bilinear (conjugate_product .quaternionic 1) f →
        f M = 0 :=
  (higherJetHermitianKernel_iff_top_orthogonal .quaternionic M).symm.trans
    (higherJetHermitian_universal_kernel .quaternionic M)

example (m : Fin 4) (hm : m < 3) :
    ∃ f : HigherJetHermitian .real m →ₗ[ℝ]
        CoefficientMatrix (Module.End ℝ (HigherJetCoefficients .real m ⧸
          (⊥ : Submodule ℝ (HigherJetCoefficients .real m)))),
      Function.Injective f ∧ IsCoefficientJordanMap (conjugate .real m) bilinear (conjugate_product .real m) f :=
  higherJetHermitian_special_below .real m hm

example :
    ∃ f : HigherJetHermitian .quaternionic 0 →ₗ[ℝ]
        CoefficientMatrix (Module.End ℝ (HigherJetCoefficients .quaternionic 0 ⧸
          (⊥ : Submodule ℝ (HigherJetCoefficients .quaternionic 0)))),
      Function.Injective f ∧
        IsCoefficientJordanMap (conjugate .quaternionic 0) bilinear (conjugate_product .quaternionic 0) f :=
  higherJetHermitian_special_below .quaternionic 0 (by decide)

#print axioms octAssociator_real_extra_direction
#print axioms span_real_leadingAssociators
#print axioms span_quaternionic_leadingAssociators
#print axioms directedCorner_associator
#print axioms associator_eq_zero_below
#print axioms span_associators_eq_leadingIdeal
#print axioms exists_specialCoefficientMap_at_threshold
#print axioms coefficientJordanMap_kills_associatorIdeal
#print axioms higherJetHermitian_special_below
#print axioms higherJetHermitian_universal_kernel
#print axioms higherJetHermitianKernel_finrank
#print axioms higherJetHermitianKernel_iff_top_orthogonal
