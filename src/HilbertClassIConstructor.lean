/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BoundedWordEffects

/-! Direct construction from actual bounded projections and a positive state,
with all word values expressed using the concrete Heisenberg effect. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {ι 𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem inverse_operatorValue_isSelfAdjoint (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint ((operatorValue 𝕜 H).symm T) := by
  apply (operatorValue 𝕜 H).injective
  simp only [operatorValue_star, RingEquiv.apply_symm_apply]
  exact hT

/-- A subtype wrapper around the one concrete boundedWordEffect definition. -/
def boundedSelfAdjointWordEffect (P : ι → H →L[𝕜] H)
    (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    selfAdjoint (HilbertOperatorAlgebra 𝕜 H) :=
  ⟨(operatorValue 𝕜 H).symm (boundedWordEffect P w),
    inverse_operatorValue_isSelfAdjoint _
      (boundedWordEffect_isPositive P hstar w).isSelfAdjoint⟩

namespace HilbertProjectiveData

def ofBoundedProjections (P : ι → H →L[𝕜] H) (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ ψ T) :
    HilbertProjectiveData ι 𝕜 H where
  projection i := (operatorValue 𝕜 H).symm (P i)
  isStarProjection i := by
    apply (operatorValue_isStarProjection 𝕜 H _).mp
    simpa only [RingEquiv.apply_symm_apply] using hP i
  state := ψ
  normalized := hunit
  positive := hpositive

theorem ofBoundedProjections_operatorProjection
    (P : ι → H →L[𝕜] H) (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ ψ T) (i : ι) :
    (ofBoundedProjections P hP ψ hunit hpositive).operatorProjection i = P i :=
  (operatorValue 𝕜 H).apply_symm_apply _

theorem ofBoundedProjections_probability
    (P : ι → H →L[𝕜] H) (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ ψ T) (w : Word ι) :
    (ofBoundedProjections P hP ψ hunit hpositive).toAlgebraic.probability w =
      ψ (boundedSelfAdjointWordEffect P (fun i => (hP i).isSelfAdjoint) w) := by
  let M := ofBoundedProjections P hP ψ hunit hpositive
  rw [M.toAlgebraic_probability]
  change ψ (M.wordEffect w) = ψ _
  apply congrArg ψ
  apply Subtype.ext
  apply (operatorValue 𝕜 H).injective
  rw [M.wordEffect_operatorValue]
  have hmenu : M.operatorProjection = P :=
    funext (ofBoundedProjections_operatorProjection P hP ψ hunit hpositive)
  rw [hmenu]
  exact ((operatorValue 𝕜 H).apply_symm_apply (boundedWordEffect P w)).symm

theorem ofBoundedProjections_matches_iff
    (P : ι → H →L[𝕜] H) (hP : ∀ i, IsStarProjection (P i))
    (ψ : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ ψ T)
    (p : ι → Albert) (ρ : Albert) :
    (ofBoundedProjections P hP ψ hunit hpositive).toAlgebraic.Matches p ρ ↔
      ∀ w, ψ (boundedSelfAdjointWordEffect P (fun i => (hP i).isSelfAdjoint) w) =
        nativeWordProbability p ρ w := by
  simp only [AlgebraicProjectiveData.Matches,
    ofBoundedProjections_probability P hP ψ hunit hpositive]

end HilbertProjectiveData
end AlbertSequential
