module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Tactic.Linarith

/-! Actual operator order-unit bounds over arbitrary real/complex Hilbert spaces.
The canonical positive-operator predicate is used, with no state extension.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem abs_bounded_operator_quadratic_form_le_norm (T : H →L[𝕜] H) (x : H) :
    |RCLike.re (inner 𝕜 (T x) x)| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖inner 𝕜 (T x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

variable [CompleteSpace H]

theorem isPositive_norm_identity_add (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) :
    ContinuousLinearMap.IsPositive ((‖T‖ : 𝕜) • (1 : H →L[𝕜] H) + T) := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  have hscalar : IsSelfAdjoint (‖T‖ : 𝕜) := by simp [isSelfAdjoint_iff]
  refine ⟨(hscalar.smul (IsSelfAdjoint.one _)).add hT, ?_⟩
  intro x
  change 0 ≤ RCLike.re (inner 𝕜 ((‖T‖ : 𝕜) • x + T x) x)
  simp only [inner_add_left, inner_smul_real_left,
    map_add, RCLike.smul_re, inner_self_eq_norm_sq]
  have h := (abs_le.mp (abs_bounded_operator_quadratic_form_le_norm T x)).1
  linarith

theorem isPositive_norm_identity_sub (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) :
    ContinuousLinearMap.IsPositive ((‖T‖ : 𝕜) • (1 : H →L[𝕜] H) - T) := by
  simpa only [norm_neg, sub_eq_add_neg] using isPositive_norm_identity_add (-T) hT.neg

end AlbertSequential
