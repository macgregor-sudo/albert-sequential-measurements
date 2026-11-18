/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicHilbertModel
public import QuaternionicProjectiveData
public import Robustness.BoundedOperatorOrderUnit

/-! Exact ORIGINAL operator-norm domination for actual R/C and quaternionic
commutant states. The coefficient bound is only an earlier intermediate step.
Canonical positivity is tested within the ORIGINAL self-adjoint state domain. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential

section AbstractBound
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem cyclicHilbertRepresentation_norm_le_of_squareMass
    (M : AlgebraicProjectiveData ι A) (z : CyclicWordAlgebra M) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ y : wordSubalgebra M.projection,
      M.squareMass ((z : A)*(y : A)) ≤ c^2*M.squareMass (y : A)) :
    ‖cyclicHilbertRepresentation M z‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  exact UniformSpace.Completion.induction_on v
    (isClosed_le (continuous_norm.comp (cyclicHilbertRepresentation M z).continuous)
      (continuous_const.mul continuous_norm)) (fun q => by
      obtain ⟨y,rfl⟩ := cyclicPreHilbertMk_surjective M q
      change ‖cyclicHilbertAction M z (cyclicPreHilbertMk M y : CyclicHilbert M)‖ ≤
        c*‖(cyclicPreHilbertMk M y : CyclicHilbert M)‖
      rw [cyclicHilbertAction_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
      rw [mul_pow,cyclicPreRepresentation_mk,cyclicPreHilbert_norm_sq,cyclicPreHilbert_norm_sq]
      exact hbound y)

theorem cyclicHilbert_word_norm_le_one (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    ‖wordAmplitude (cyclicHilbertProjection M) w‖ ≤ 1 := by
  rw [← cyclicHilbertRepresentation_word]
  apply cyclicHilbertRepresentation_norm_le_of_squareMass M (cyclicWordElement M w) 1 zero_le_one
  intro y
  change M.squareMass (wordAmplitude M.projection w*(y : A)) ≤ 1^2*M.squareMass (y : A)
  simpa only [one_pow,one_mul] using M.squareMass_word_le w (y : A)

theorem cyclicHilbert_outcome_norm_le_one (M : AlgebraicProjectiveData ι A) (a : Outcome ι) :
    ‖algebraicOutcome (cyclicHilbertProjection M) a‖ ≤ 1 := by
  simpa only [wordAmplitude_singleton] using cyclicHilbert_word_norm_le_one M [a]

theorem cyclicHilbertProjection_norm_le_one (M : AlgebraicProjectiveData ι A) (i : ι) :
    ‖cyclicHilbertProjection M i‖ ≤ 1 :=
  cyclicHilbert_outcome_norm_le_one M (i,true)

theorem cyclicHilbertProjection_complement_norm_le_one (M : AlgebraicProjectiveData ι A) (i : ι) :
    ‖1-cyclicHilbertProjection M i‖ ≤ 1 :=
  cyclicHilbert_outcome_norm_le_one M (i,false)

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A reusable actual-operator specialization. Its positivity premise is about
the input state's evaluation on actual positive self-adjoint operator images;
the public R/C/Q corollaries derive it from their ORIGINAL state fields. -/
theorem cyclicHilbertRepresentation_norm_le_of_positive_operator_image
    (M : AlgebraicProjectiveData ι A) (J : A →+* (H →L[𝕜] H))
    (hreal : ∀ (r : ℝ) a, J (r • a)=(r : 𝕜) • J a)
    (hstar : ∀ a, J (star a)=star (J a))
    (hpositive : ∀ a, IsSelfAdjoint a → (J a).IsPositive → 0 ≤ M.state a)
    (z : CyclicWordAlgebra M) :
    ‖cyclicHilbertRepresentation M z‖ ≤ ‖J (z : A)‖ := by
  let X := J (z : A)
  let c := ‖X‖
  apply cyclicHilbertRepresentation_norm_le_of_squareMass M z c (norm_nonneg X)
  intro y
  let Y := J (y : A)
  let D := c^2 • (star (y : A)*(y : A))-star ((z : A)*(y : A))*((z : A)*(y : A))
  have hDstar : IsSelfAdjoint D := by
    change star D=D
    simp only [D,star_sub,star_smul,star_trivial,star_mul,star_star]
  have hn : ‖star X*X‖=c^2 := by
    change ‖ContinuousLinearMap.adjoint X ∘L X‖=‖X‖^2
    simpa only [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self X
  have hp : ((((c^2 : ℝ) : 𝕜) • (1 : H →L[𝕜] H))-star X*X).IsPositive := by
    have h := isPositive_norm_identity_sub (star X*X) (IsSelfAdjoint.star_mul_self X)
    rwa [hn] at h
  have hconj : (star Y*((((c^2 : ℝ) : 𝕜) • (1 : H →L[𝕜] H))-star X*X)*Y).IsPositive := by
    have h := hp.conj_adjoint (star Y)
    change (star Y*((((c^2 : ℝ) : 𝕜) • (1 : H →L[𝕜] H))-star X*X)*star (star Y)).IsPositive at h
    simpa only [star_star] using h
  have hD : J D=star Y*((((c^2 : ℝ) : 𝕜) • (1 : H →L[𝕜] H))-star X*X)*Y := by
    simp only [D,map_sub,hreal,map_mul,hstar,star_mul,X,Y,
      mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,mul_assoc]
  have hstate := hpositive D hDstar (by rw [hD]; exact hconj)
  change 0 ≤ M.state (c^2 • (star (y : A)*(y : A))-
    star ((z : A)*(y : A))*((z : A)*(y : A))) at hstate
  simp only [map_sub,map_smul,smul_eq_mul] at hstate
  change M.state (star ((z : A)*(y : A))*((z : A)*(y : A))) ≤
    c^2*M.state (star (y : A)*(y : A))
  linarith
end AbstractBound

namespace HilbertProjectiveData
variable {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem cyclicRepresentation_norm_le (M : HilbertProjectiveData ι 𝕜 H)
    (z : CyclicWordAlgebra M.toAlgebraic) :
    ‖cyclicHilbertRepresentation M.toAlgebraic z‖ ≤ ‖operatorValue 𝕜 H z.val‖ := by
  apply cyclicHilbertRepresentation_norm_le_of_positive_operator_image M.toAlgebraic
    (operatorValue 𝕜 H).toRingHom (operatorValue_real_smul 𝕜 H) (operatorValue_star 𝕜 H)
  intro a ha hpositive
  rw [M.toAlgebraic_state_selfAdjoint ⟨a,ha⟩]
  exact M.positive ⟨a,ha⟩ hpositive
end HilbertProjectiveData

namespace QuaternionicProjectiveData
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Q : QuaternionicOperatorStructure H}

theorem cyclicRepresentation_norm_le (M : QuaternionicProjectiveData ι Q)
    (z : CyclicWordAlgebra M.toAlgebraic) :
    ‖cyclicHilbertRepresentation M.toAlgebraic z‖ ≤ ‖Q.operatorValue z.val‖ := by
  apply cyclicHilbertRepresentation_norm_le_of_positive_operator_image M.toAlgebraic
    Q.operatorValue.toAlgHom.toRingHom Q.operatorValue_real_smul Q.operatorValue_star
  intro a ha hpositive
  change 0 ≤ extendSelfAdjointState M.state a
  rw [extendSelfAdjointState_on_selfAdjoint M.state a ha]
  exact M.positive ⟨a,ha⟩ hpositive
end QuaternionicProjectiveData
end AlbertSequential
