/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Star.Module

/-! The same actual bounded 𝕜-linear operators, regarded as a real algebra.
Multiplication remains composition; star remains the Hilbert adjoint. The
scalar restriction changes neither the Hilbert space nor its linear operators. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable (𝕜 H : Type*) [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

abbrev HilbertOperatorAlgebra := RestrictScalars ℝ 𝕜 (H →L[𝕜] H)

omit [CompleteSpace H] in
-- RestrictScalars has separate ring/additive instances. Use the additive group
-- of this same ring so the standard self-adjoint subtype module matches it.
instance hilbertOperatorAddCommGroup : AddCommGroup (HilbertOperatorAlgebra 𝕜 H) :=
  (inferInstance : Ring (HilbertOperatorAlgebra 𝕜 H)).toAddCommGroup

omit [CompleteSpace H] in
-- Choose the real module from the same ring's real algebra as well. This
-- keeps LinearMap coercions and self-adjoint subtype scalars on one path.
instance hilbertOperatorRealModule : Module ℝ (HilbertOperatorAlgebra 𝕜 H) :=
  (inferInstance : Algebra ℝ (HilbertOperatorAlgebra 𝕜 H)).toModule

instance hilbertOperatorStarRing : StarRing (HilbertOperatorAlgebra 𝕜 H) :=
  inferInstanceAs (StarRing (H →L[𝕜] H))

instance hilbertOperatorStarModule : StarModule ℝ (HilbertOperatorAlgebra 𝕜 H) where
  star_smul r T := by
    let V : H →L[𝕜] H := RestrictScalars.ringEquiv ℝ 𝕜 (H →L[𝕜] H) T
    change ContinuousLinearMap.adjoint ((r : 𝕜) • V) =
      (r : 𝕜) • ContinuousLinearMap.adjoint V
    simp only [map_smulₛₗ, RCLike.conj_ofReal]

omit [CompleteSpace H] in
def operatorValue : HilbertOperatorAlgebra 𝕜 H ≃+* (H →L[𝕜] H) :=
  RestrictScalars.ringEquiv ℝ 𝕜 (H →L[𝕜] H)

omit [CompleteSpace H] in
theorem operatorValue_mul_apply (S T : HilbertOperatorAlgebra 𝕜 H) (x : H) :
    operatorValue 𝕜 H (S * T) x = operatorValue 𝕜 H S (operatorValue 𝕜 H T x) := rfl

omit [CompleteSpace H] in
theorem operatorValue_one_apply (x : H) :
    operatorValue 𝕜 H 1 x = x := rfl

theorem operatorValue_star (T : HilbertOperatorAlgebra 𝕜 H) :
    operatorValue 𝕜 H (star T) = ContinuousLinearMap.adjoint (operatorValue 𝕜 H T) := rfl

omit [CompleteSpace H] in
theorem operatorValue_norm (T : HilbertOperatorAlgebra 𝕜 H) :
    ‖operatorValue 𝕜 H T‖ = ‖T‖ := rfl

omit [CompleteSpace H] in
theorem operatorValue_real_smul (r : ℝ) (T : HilbertOperatorAlgebra 𝕜 H) :
    operatorValue 𝕜 H (r • T) = (r : 𝕜) • operatorValue 𝕜 H T := rfl

theorem operatorValue_isStarProjection (T : HilbertOperatorAlgebra 𝕜 H) :
    IsStarProjection (operatorValue 𝕜 H T) ↔ IsStarProjection T := Iff.rfl

theorem operatorValue_star_mul_positive (T : HilbertOperatorAlgebra 𝕜 H) :
    (operatorValue 𝕜 H (star T * T)).IsPositive := by
  change (ContinuousLinearMap.adjoint (operatorValue 𝕜 H T) ∘L
    operatorValue 𝕜 H T).IsPositive
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

end AlbertSequential
