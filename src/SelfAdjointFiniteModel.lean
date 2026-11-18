/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SelfAdjointStateGram
public import FiniteGramEquivalence

/-! Finite real realization of projection-word data from an arbitrary positive
real functional on self-adjoint elements of the stated real star algebra. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem algebraicData_finiteRealModel {n : ℕ}
    (M : AlgebraicProjectiveData (Fin n) A) (L : ℕ) :
    ∃ d, ∃ R : FiniteRealVectorProjectiveModel n d,
      ∀ w, w.length ≤ L → IsReducedWord w → R.probability w = M.probability w :=
  finiteGram_iff_finiteRealModel.mp (M.finiteGram L)

theorem selfAdjointState_finiteRealModel {n : ℕ}
    (P : Fin n → A) (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ x : A, 0 ≤ ψ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩) (L : ℕ) :
    ∃ d, ∃ R : FiniteRealVectorProjectiveModel n d,
      ∀ w, w.length ≤ L → IsReducedWord w →
        R.probability w = selfAdjointWordProbability P ψ w :=
  finiteGram_iff_finiteRealModel.mp (selfAdjointState_finiteGram P hP hstar ψ hunit hpositive L)

end AlbertSequential
