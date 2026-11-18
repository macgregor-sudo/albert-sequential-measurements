module

public import Robustness.RealHilbertComplexification
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Concrete diagonal complexification of actual bounded real Hilbert
operators. This is neither a finite-dimensional model nor a state extension.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def complexifyLinearMap (T : H →ₗ[ℝ] H) :
    RealHilbertComplexification H →ₗ[ℂ] RealHilbertComplexification H where
  toFun u := pair (T (realPart u)) (T (imagPart u))
  map_add' u v := by
    apply real_imag_ext <;> simp only [realPart_pair, imagPart_pair,
      realPart_add, imagPart_add, map_add]
  map_smul' z u := by
    change pair (T (realPart (z • u))) (T (imagPart (z • u))) =
      z • pair (T (realPart u)) (T (imagPart u))
    apply real_imag_ext <;> simp only [realPart_pair, imagPart_pair,
      RealHilbertComplexification.realPart_smul,
      RealHilbertComplexification.imagPart_smul, map_sub, map_add, map_smul]

theorem norm_complexifyLinearMap_le (T : H →L[ℝ] H)
    (u : RealHilbertComplexification H) :
    ‖complexifyLinearMap T.toLinearMap u‖ ≤ ‖T‖ * ‖u‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg T) (norm_nonneg u))
  have hre := T.le_opNorm (realPart u)
  have him := T.le_opNorm (imagPart u)
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
    (norm_nonneg (realPart u)))).mpr hre
  have hi2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
    (norm_nonneg (imagPart u)))).mpr him
  rw [RealHilbertComplexification.norm_sq, mul_pow, RealHilbertComplexification.norm_sq]
  change ‖T (realPart u)‖ ^ 2 + ‖T (imagPart u)‖ ^ 2 ≤
    ‖T‖ ^ 2 * (‖realPart u‖ ^ 2 + ‖imagPart u‖ ^ 2)
  nlinarith

def complexifyBoundedOperatorValue (T : H →L[ℝ] H) :
    RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H :=
  (complexifyLinearMap T.toLinearMap).mkContinuous ‖T‖ (norm_complexifyLinearMap_le T)

@[simp] theorem complexifyBoundedOperatorValue_apply (T : H →L[ℝ] H)
    (u : RealHilbertComplexification H) :
    complexifyBoundedOperatorValue T u = pair (T (realPart u)) (T (imagPart u)) := rfl

theorem norm_complexifyBoundedOperatorValue (T : H →L[ℝ] H) :
    ‖complexifyBoundedOperatorValue T‖ = ‖T‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
      (norm_complexifyLinearMap_le T)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (complexifyBoundedOperatorValue T).le_opNorm (pair x 0)
    simpa only [complexifyBoundedOperatorValue_apply, realPart_pair, imagPart_pair,
      map_zero, norm_pair_zero] using h

variable [CompleteSpace H]

theorem complexifyBoundedOperatorValue_adjoint (T : H →L[ℝ] H) :
    complexifyBoundedOperatorValue T.adjoint = (complexifyBoundedOperatorValue T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  apply Complex.ext <;> simp only [complex_inner_re, complex_inner_im,
    complexifyBoundedOperatorValue_apply, realPart_pair, imagPart_pair,
    ContinuousLinearMap.adjoint_inner_left]

def complexifyBoundedOperator : (H →L[ℝ] H) →⋆ₐ[ℝ]
    (RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) where
  toFun := complexifyBoundedOperatorValue
  map_zero' := by ext u <;> rfl
  map_one' := by ext u <;> rfl
  map_add' T S := by ext u <;> rfl
  map_mul' T S := by ext u <;> rfl
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro u
    apply real_imag_ext <;> simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    simp only [ContinuousLinearMap.star_eq_adjoint, complexifyBoundedOperatorValue_adjoint]

@[simp] theorem complexifyBoundedOperator_apply (T : H →L[ℝ] H)
    (u : RealHilbertComplexification H) :
    complexifyBoundedOperator T u = pair (T (realPart u)) (T (imagPart u)) := rfl

theorem complexifyBoundedOperator_norm (T : H →L[ℝ] H) :
    ‖complexifyBoundedOperator T‖ = ‖T‖ := norm_complexifyBoundedOperatorValue T

theorem complexifyBoundedOperator_isometry : Isometry (complexifyBoundedOperator (H := H)) :=
  AddMonoidHomClass.isometry_of_norm _ complexifyBoundedOperator_norm

end AlbertSequential
