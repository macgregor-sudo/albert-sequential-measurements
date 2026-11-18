module

public import Robustness.ComplexifiedBoundedOperators

/-! Actual conjugation of bounded complex operators on the L2 complexification.
The fixed-range/descent route does not extend a state to the complex space.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace RealHilbertComplexification

theorem conjugatePair_add (u v : RealHilbertComplexification H) :
    conjugatePair (u + v) = conjugatePair u + conjugatePair v :=
  map_add (complexConjugation (H := H)) u v

theorem conjugatePair_real_smul (r : ℝ) (u : RealHilbertComplexification H) :
    conjugatePair (r • u) = r • conjugatePair u :=
  map_smul (complexConjugation (H := H)) r u

theorem conjugatePair_inner (u v : RealHilbertComplexification H) :
    inner ℂ (conjugatePair u) (conjugatePair v) = conj (inner ℂ u v) := by
  apply Complex.ext <;> simp only [complex_inner_re, complex_inner_im,
    realPart_conjugatePair, imagPart_conjugatePair, inner_neg_left, inner_neg_right,
    neg_neg, Complex.conj_re, Complex.conj_im]
  all_goals ring

theorem conjugatePair_inner_left (u v : RealHilbertComplexification H) :
    inner ℂ (conjugatePair u) v = conj (inner ℂ u (conjugatePair v)) := by
  simpa only [conjugatePair_involutive] using conjugatePair_inner u (conjugatePair v)

omit [InnerProductSpace ℝ H] in
theorem norm_realPart_le (u : RealHilbertComplexification H) : ‖realPart u‖ ≤ ‖u‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg u)
  rw [RealHilbertComplexification.norm_sq]
  nlinarith [sq_nonneg ‖imagPart u‖]

def realPartLinearMap : RealHilbertComplexification H →ₗ[ℝ] H where
  toFun := realPart
  map_add' := realPart_add
  map_smul' := realPart_real_smul

def realPartContinuousLinearMap : RealHilbertComplexification H →L[ℝ] H :=
  realPartLinearMap.mkContinuous 1 (fun u => by
    change ‖realPart u‖ ≤ (1 : ℝ) * ‖u‖
    simpa only [one_mul] using norm_realPart_le u)

@[simp] theorem realPartContinuousLinearMap_apply (u : RealHilbertComplexification H) :
    realPartContinuousLinearMap u = realPart u := rfl

end RealHilbertComplexification

def conjugateOperatorLinearMap
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    RealHilbertComplexification H →ₗ[ℂ] RealHilbertComplexification H where
  toFun u := conjugatePair (M (conjugatePair u))
  map_add' u v := by rw [conjugatePair_add, map_add, conjugatePair_add]
  map_smul' z u := by
    change conjugatePair (M (conjugatePair (z • u))) =
      z • conjugatePair (M (conjugatePair u))
    rw [conjugatePair_complex_smul, map_smul, conjugatePair_complex_smul]
    simp

theorem norm_conjugateOperatorLinearMap_le
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (u : RealHilbertComplexification H) :
    ‖conjugateOperatorLinearMap M u‖ ≤ ‖M‖ * ‖u‖ := by
  change ‖conjugatePair (M (conjugatePair u))‖ ≤ ‖M‖ * ‖u‖
  simpa only [conjugatePair_norm] using M.le_opNorm (conjugatePair u)

def conjugateBoundedOperatorValue
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H :=
  (conjugateOperatorLinearMap M).mkContinuous ‖M‖ (norm_conjugateOperatorLinearMap_le M)

@[simp] theorem conjugateBoundedOperatorValue_apply
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (u : RealHilbertComplexification H) :
    conjugateBoundedOperatorValue M u = conjugatePair (M (conjugatePair u)) := rfl

theorem conjugateBoundedOperatorValue_involutive
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    conjugateBoundedOperatorValue (conjugateBoundedOperatorValue M) = M := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [conjugateBoundedOperatorValue_apply, conjugatePair_involutive]

theorem conjugateBoundedOperatorValue_norm
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    ‖conjugateBoundedOperatorValue M‖ = ‖M‖ := by
  have h (N : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
      ‖conjugateBoundedOperatorValue N‖ ≤ ‖N‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_conjugateOperatorLinearMap_le N)
  exact le_antisymm (h M) (by
    simpa only [conjugateBoundedOperatorValue_involutive] using h (conjugateBoundedOperatorValue M))

variable [CompleteSpace H]

theorem conjugateBoundedOperatorValue_adjoint
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    conjugateBoundedOperatorValue M.adjoint = (conjugateBoundedOperatorValue M).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [conjugateBoundedOperatorValue_apply, conjugateBoundedOperatorValue_apply,
    conjugatePair_inner_left, ContinuousLinearMap.adjoint_inner_left, conjugatePair_inner_left]
  simp

def conjugateBoundedOperator :
    (RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) ≃⋆ₐ[ℝ]
    (RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) where
  toFun := conjugateBoundedOperatorValue
  invFun := conjugateBoundedOperatorValue
  left_inv := conjugateBoundedOperatorValue_involutive
  right_inv := conjugateBoundedOperatorValue_involutive
  map_add' M N := by
    apply ContinuousLinearMap.ext
    intro u
    change conjugatePair (M (conjugatePair u) + N (conjugatePair u)) =
      conjugatePair (M (conjugatePair u)) + conjugatePair (N (conjugatePair u))
    exact conjugatePair_add _ _
  map_mul' M N := by
    apply ContinuousLinearMap.ext
    intro u
    change conjugatePair (M (N (conjugatePair u))) =
      conjugatePair (M (conjugatePair (conjugatePair (N (conjugatePair u)))))
    rw [conjugatePair_involutive]
  map_smul' r M := by
    apply ContinuousLinearMap.ext
    intro u
    change conjugatePair (r • M (conjugatePair u)) =
      r • conjugatePair (M (conjugatePair u))
    exact conjugatePair_real_smul _ _
  map_star' M := by
    simp only [ContinuousLinearMap.star_eq_adjoint, conjugateBoundedOperatorValue_adjoint]

@[simp] theorem conjugateBoundedOperator_apply
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (u : RealHilbertComplexification H) :
    conjugateBoundedOperator M u = conjugatePair (M (conjugatePair u)) := rfl

theorem conjugateBoundedOperator_norm
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    ‖conjugateBoundedOperator M‖ = ‖M‖ := conjugateBoundedOperatorValue_norm M

theorem conjugateBoundedOperator_isometry : Isometry (conjugateBoundedOperator (H := H)) :=
  AddMonoidHomClass.isometry_of_norm _ conjugateBoundedOperator_norm

theorem complexified_operator_fixed_by_conjugation (T : H →L[ℝ] H) :
    conjugateBoundedOperator (complexifyBoundedOperator T) = complexifyBoundedOperator T := by
  apply ContinuousLinearMap.ext
  intro u
  apply real_imag_ext <;> simp only [conjugateBoundedOperator_apply,
    complexifyBoundedOperator_apply, realPart_conjugatePair, imagPart_conjugatePair,
    realPart_pair, imagPart_pair, map_neg, neg_neg]

def restrictOperatorRealPart
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) : H →L[ℝ] H :=
  realPartContinuousLinearMap.comp
    ((M.restrictScalars ℝ).comp (embedRealHilbertSpace (H := H)).toContinuousLinearMap)

def restrictFixedBoundedOperator
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (_hM : conjugateBoundedOperator M = M) : H →L[ℝ] H := restrictOperatorRealPart M

@[simp] theorem restrictFixedBoundedOperator_apply
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hM : conjugateBoundedOperator M = M) (x : H) :
    restrictFixedBoundedOperator M hM x = realPart (M (pair x 0)) := rfl

theorem fixed_operator_preserves_real_axis
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hM : conjugateBoundedOperator M = M) (x : H) :
    M (pair x 0) = pair (realPart (M (pair x 0))) 0 := by
  have hj : conjugatePair (pair x (0 : H)) = pair x 0 := by
    apply real_imag_ext <;> simp
  have hval : conjugatePair (M (pair x 0)) = M (pair x 0) := by
    simpa only [conjugateBoundedOperator_apply, hj] using
      congrArg (fun F => F (pair x 0)) hM
  have him := congrArg imagPart hval
  simp only [imagPart_conjugatePair] at him
  have htwo : (2 : ℝ) • imagPart (M (pair x 0)) = 0 := by
    calc
      _ = imagPart (M (pair x 0)) + imagPart (M (pair x 0)) := two_smul ℝ _
      _ = imagPart (M (pair x 0)) + -imagPart (M (pair x 0)) :=
        congrArg (fun z => imagPart (M (pair x 0)) + z) him.symm
      _ = 0 := add_neg_cancel _
  have hz : imagPart (M (pair x 0)) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply real_imag_ext
  · rfl
  · simpa only [imagPart_pair] using hz

theorem complexify_restrictFixedBoundedOperator
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hM : conjugateBoundedOperator M = M) :
    complexifyBoundedOperator (restrictFixedBoundedOperator M hM) = M := by
  apply ContinuousLinearMap.ext
  intro u
  change pair (realPart (M (pair (realPart u) 0)))
    (realPart (M (pair (imagPart u) 0))) = M u
  calc
    _ = pair (realPart (M (pair (realPart u) 0))) 0 +
        Complex.I • pair (realPart (M (pair (imagPart u) 0))) 0 := by
      apply real_imag_ext <;> simp
    _ = M (pair (realPart u) 0) + Complex.I • M (pair (imagPart u) 0) := by
      rw [← fixed_operator_preserves_real_axis M hM (realPart u),
        ← fixed_operator_preserves_real_axis M hM (imagPart u)]
    _ = M u := by
      simpa only [map_add, map_smul] using congrArg M (pair_real_imag_decomposition u).symm

theorem restrictFixedBoundedOperator_complexify (T : H →L[ℝ] H) :
    restrictFixedBoundedOperator (complexifyBoundedOperator T)
      (complexified_operator_fixed_by_conjugation T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [restrictFixedBoundedOperator_apply, complexifyBoundedOperator_apply,
    realPart_pair, imagPart_pair]

theorem fixed_operator_iff_complexified
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) :
    conjugateBoundedOperator M = M ↔ ∃ T : H →L[ℝ] H, complexifyBoundedOperator T = M := by
  constructor
  · intro hM
    exact ⟨restrictFixedBoundedOperator M hM, complexify_restrictFixedBoundedOperator M hM⟩
  · rintro ⟨T, rfl⟩
    exact complexified_operator_fixed_by_conjugation T

theorem restrictFixedBoundedOperator_norm
    (M : RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)
    (hM : conjugateBoundedOperator M = M) : ‖restrictFixedBoundedOperator M hM‖ = ‖M‖ := by
  rw [← complexifyBoundedOperator_norm (restrictFixedBoundedOperator M hM),
    complexify_restrictFixedBoundedOperator M hM]

end AlbertSequential
