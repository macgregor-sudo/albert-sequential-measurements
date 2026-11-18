/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlgebraicGramNecessity
public import Mathlib.Algebra.Star.Module

/-! A state need only be defined on self-adjoint elements.
The real-linear self-adjoint-part extension gives the existing algebraic
comparator and finite Gram data without a completed GNS construction.

Readable proof: extend by φ(x)=ψ((x+star x)/2). This is real-linear,
star-invariant, fixes self-adjoint inputs, and preserves ψ on star(x)*x.
Normalization and positivity on those squares therefore give the exact fields
of AlgebraicProjectiveData. Concrete bounded R/C/H operator instances remain
separate bindings; none is postulated by this generic star-algebra theorem. -/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace AlbertSequential

section
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
variable [StarModule ℝ A]

def extendSelfAdjointState (ψ : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℝ] ℝ :=
  ψ.comp (selfAdjointPart ℝ)

theorem extendSelfAdjointState_star (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (x : A) :
    extendSelfAdjointState ψ (star x) = extendSelfAdjointState ψ x := by
  have h : selfAdjointPart ℝ (star x) = selfAdjointPart ℝ x := by
    apply Subtype.ext
    simp only [selfAdjointPart_apply_coe, star_star, add_comm]
  exact congrArg ψ h

theorem extendSelfAdjointState_on_selfAdjoint (ψ : selfAdjoint A →ₗ[ℝ] ℝ)
    (x : A) (hx : IsSelfAdjoint x) :
    extendSelfAdjointState ψ x = ψ ⟨x, hx⟩ := by
  exact congrArg ψ (hx.selfAdjointPart_apply ℝ)

variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

def algebraicProjectiveDataOfSelfAdjointState {ι : Type*}
    (P : ι → A) (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ x : A, 0 ≤ ψ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩) :
    AlgebraicProjectiveData ι A where
  projection := P
  idempotent := hP
  selfAdjoint := hstar
  state := extendSelfAdjointState ψ
  state_unit := by
    rw [extendSelfAdjointState_on_selfAdjoint ψ 1 (IsSelfAdjoint.one A)]
    exact hunit
  state_star := extendSelfAdjointState_star ψ
  state_positive x := by
    rw [extendSelfAdjointState_on_selfAdjoint ψ (star x * x) (IsSelfAdjoint.star_mul_self x)]
    exact hpositive x

def selfAdjointWordProbability {ι : Type*} (P : ι → A)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (w : Word ι) : ℝ :=
  ψ ⟨wordOperator P w, wordOperator_star P w⟩

theorem algebraicProjectiveDataOfSelfAdjointState_probability {ι : Type*}
    (P : ι → A) (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ x : A, 0 ≤ ψ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩)
    (w : Word ι) :
    (algebraicProjectiveDataOfSelfAdjointState P hP hstar ψ hunit hpositive).probability w =
      selfAdjointWordProbability P ψ w := by
  exact extendSelfAdjointState_on_selfAdjoint ψ _ (wordOperator_star P w)

theorem selfAdjointState_finiteGram {n : ℕ}
    (P : Fin n → A) (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ x : A, 0 ≤ ψ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩) (L : ℕ) :
    Nonempty (FiniteGramWitness n L (selfAdjointWordProbability P ψ)) := by
  let M := algebraicProjectiveDataOfSelfAdjointState P hP hstar ψ hunit hpositive
  have hprob : M.probability = selfAdjointWordProbability P ψ := by
    funext w
    exact algebraicProjectiveDataOfSelfAdjointState_probability P hP hstar ψ hunit hpositive w
  simpa only [hprob] using M.finiteGram L

end
end AlbertSequential
