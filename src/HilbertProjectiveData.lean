/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertOperatorAlgebra
public import SelfAdjointStateGram

/-! Actual bounded orthogonal projections and arbitrary normalized positive
real-linear states on their Hilbert-space self-adjoint operators. No continuity,
normality, faithfulness, rank, separability or finite-dimensional assumption
on the state/model is added. RCLike specializes to the real and complex fields;
it is not a quaternionic Hilbert-space implementation. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

structure HilbertProjectiveData (ι 𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  projection : ι → HilbertOperatorAlgebra 𝕜 H
  isStarProjection : ∀ i, IsStarProjection (projection i)
  state : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ
  normalized : state 1 = 1
  positive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
    (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ state T

namespace HilbertProjectiveData
variable {ι 𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

def toAlgebraic (M : HilbertProjectiveData ι 𝕜 H) :
    AlgebraicProjectiveData ι (HilbertOperatorAlgebra 𝕜 H) :=
  algebraicProjectiveDataOfSelfAdjointState M.projection
    (fun i => (M.isStarProjection i).isIdempotentElem)
    (fun i => (M.isStarProjection i).isSelfAdjoint)
    M.state M.normalized
    (fun x => M.positive ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩
      (operatorValue_star_mul_positive 𝕜 H x))

theorem toAlgebraic_projection (M : HilbertProjectiveData ι 𝕜 H) (i : ι) :
    M.toAlgebraic.projection i = M.projection i := rfl

theorem toAlgebraic_state_selfAdjoint (M : HilbertProjectiveData ι 𝕜 H)
    (T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H)) :
    M.toAlgebraic.state T.val = M.state T := by
  exact extendSelfAdjointState_on_selfAdjoint M.state T.val T.property

def operatorProjection (M : HilbertProjectiveData ι 𝕜 H) (i : ι) : H →L[𝕜] H :=
  operatorValue 𝕜 H (M.projection i)

theorem operatorProjection_isStarProjection (M : HilbertProjectiveData ι 𝕜 H) (i : ι) :
    IsStarProjection (M.operatorProjection i) :=
  (operatorValue_isStarProjection 𝕜 H (M.projection i)).mpr (M.isStarProjection i)

/-- This is an actual orthogonal projection onto a Hilbert subspace. -/
theorem operatorProjection_eq_starProjection (M : HilbertProjectiveData ι 𝕜 H) (i : ι) :
    ∃ (U : Submodule 𝕜 H) (_ : U.HasOrthogonalProjection),
      M.operatorProjection i = U.starProjection :=
  isStarProjection_iff_eq_starProjection.mp
    (M.operatorProjection_isStarProjection i)

end HilbertProjectiveData
end AlbertSequential
