module

public import Robustness.ComplexifiedBoundedOperators
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! Canonical positivity is preserved and reflected by the actual diagonal
complexification. No state extension, dimension or spectrum assumption. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem complexifyBoundedOperator_isPositive_iff (T : H →L[ℝ] H) :
    (complexifyBoundedOperator T).IsPositive ↔ T.IsPositive := by
  constructor
  · intro hT
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨?_, ?_⟩
    · change star T = T
      apply (complexifyBoundedOperator_isometry (H := H)).injective
      rw [map_star]
      exact hT.isSelfAdjoint
    · intro x
      have hx := hT.re_inner_nonneg_left (pair x 0)
      change 0 ≤ (inner ℂ (complexifyBoundedOperator T (pair x 0)) (pair x 0)).re at hx
      change 0 ≤ RCLike.re (inner ℝ (T x) x)
      simpa only [complex_inner_re, complexifyBoundedOperator_apply,
        realPart_pair, imagPart_pair, map_zero, inner_zero_left, add_zero,
        RCLike.re_to_real] using hx
  · intro hT
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hT.isSelfAdjoint.map complexifyBoundedOperator, ?_⟩
    intro u
    change 0 ≤ (inner ℂ (complexifyBoundedOperator T u) u).re
    rw [complex_inner_re]
    simp only [complexifyBoundedOperator_apply, realPart_pair, imagPart_pair]
    simpa only [RCLike.re_to_real] using
      add_nonneg (hT.re_inner_nonneg_left (realPart u))
        (hT.re_inner_nonneg_left (imagPart u))

end AlbertSequential
