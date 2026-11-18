module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.Linarith

/-! Norm bounds for positive unital states follow from the order-unit cone
inequality, without assuming normality, continuity or a density representation.
Actual bounded-operator order-unit bindings are in `BoundedOperatorOrderUnit`.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem positiveUnitalFunctional_abs_le_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : Set E) (e : E)
    (horder : ∀ x : E, ‖x‖ • e + x ∈ C ∧ ‖x‖ • e - x ∈ C)
    (phi : E →ₗ[ℝ] ℝ) (hphi : ∀ x ∈ C, 0 ≤ phi x) (hunit : phi e = 1)
    (x : E) : |phi x| ≤ ‖x‖ := by
  have hp := hphi _ (horder x).1
  have hm := hphi _ (horder x).2
  simp only [map_add, map_sub, map_smul, hunit, smul_eq_mul, mul_one] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem positiveUnitalFunctional_error_le_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : Set E) (e : E)
    (horder : ∀ x : E, ‖x‖ • e + x ∈ C ∧ ‖x‖ • e - x ∈ C)
    (phi : E →ₗ[ℝ] ℝ) (hphi : ∀ x ∈ C, 0 ≤ phi x) (hunit : phi e = 1)
    (x y : E) : |phi x - phi y| ≤ ‖x - y‖ := by
  simpa only [map_sub] using positiveUnitalFunctional_abs_le_norm C e horder phi hphi hunit (x - y)

end AlbertSequential
