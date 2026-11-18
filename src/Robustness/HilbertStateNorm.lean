module

public import HilbertOperatorAlgebra
public import Robustness.BoundedOperatorOrderUnit
public import Robustness.OrderUnitStates
public import Mathlib.Analysis.CStarAlgebra.Basic

/-! Norm control on the existing actual real/complex Hilbert SA state carrier.
The state is an arbitrary positive normalized REAL-linear functional; there is
no continuity, normality, density representation or state extension hypothesis.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem hilbertOperator_order_unit_positive
    (T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H)) :
    (operatorValue 𝕜 H ((‖T.val‖ : ℝ) • (1 : HilbertOperatorAlgebra 𝕜 H) + T.val)).IsPositive ∧
    (operatorValue 𝕜 H ((‖T.val‖ : ℝ) • (1 : HilbertOperatorAlgebra 𝕜 H) - T.val)).IsPositive := by
  -- Self-adjointness of the operator value comes from `operatorValue_star`
  -- (wrapper transport of the adjoint).
  have hv : IsSelfAdjoint (operatorValue 𝕜 H T.val) := by
    change (operatorValue 𝕜 H T.val).adjoint = operatorValue 𝕜 H T.val
    rw [← operatorValue_star, T.property]
  constructor
  · rw [map_add, operatorValue_real_smul, map_one]
    simpa only [operatorValue_norm] using isPositive_norm_identity_add (operatorValue 𝕜 H T.val) hv
  · rw [map_sub, operatorValue_real_smul, map_one]
    simpa only [operatorValue_norm] using isPositive_norm_identity_sub (operatorValue 𝕜 H T.val) hv

theorem hilbert_positive_state_abs_le_norm
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    (T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H)) : |psi T| ≤ ‖T.val‖ := by
  -- Use the inherited actual operator norm explicitly. No extra normed-module
  -- instance is imposed on the already fixed self-adjoint state carrier.
  have hp := hpositive (‖T.val‖ • 1 + T) (hilbertOperator_order_unit_positive T).1
  have hm := hpositive (‖T.val‖ • 1 - T) (hilbertOperator_order_unit_positive T).2
  simp only [map_add, map_sub, map_smul, hnormalized, smul_eq_mul, mul_one] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem hilbert_positive_state_error_le_norm
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    (X Y : selfAdjoint (HilbertOperatorAlgebra 𝕜 H)) :
    |psi X - psi Y| ≤ ‖(X - Y).val‖ := by
  simpa only [map_sub] using
    hilbert_positive_state_abs_le_norm psi hnormalized hpositive (X - Y)

end AlbertSequential
