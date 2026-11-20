/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceComplex
public import ComplexStateCompression
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Descent of the positive square root to the original real Hilbert space. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

open RealHilbertComplexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem complexify_isPositive {T : H →L[ℝ] H} (hT : T.IsPositive) :
    (complexifyBoundedOperator T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨?_, ?_⟩
  · change star (complexifyBoundedOperator T) = complexifyBoundedOperator T
    rw [← map_star, hT.isSelfAdjoint.star_eq]
  · intro u
    change 0 ≤ (inner ℂ ((complexifyBoundedOperator T) u) u).re
    rw [complex_inner_re, complexifyBoundedOperator_apply, realPart_pair, imagPart_pair]
    exact add_nonneg (hT.re_inner_nonneg_left (realPart u)) (hT.re_inner_nonneg_left (imagPart u))

private theorem conjugate_isPositive {T : RealHilbertComplexification H →L[ℂ]
    RealHilbertComplexification H} (hT : T.IsPositive) : (conjugateBoundedOperator T).IsPositive := by
  obtain ⟨A, _, hA, _⟩ := exists_selfAdjoint_factor hT
  change star A * A = T at hA
  rw [← hA, map_mul, map_star]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The complex positive square root of the complexified operator descends to a real one. -/
theorem exists_real_positive_square_root {T : H →L[ℝ] H} (hT : T.IsPositive) :
    ∃ A : H →L[ℝ] H, A.IsPositive ∧ A * A = T := by
  let U := complexifyBoundedOperator T
  let R := CFC.sqrt U
  have hu : 0 ≤ U := ContinuousLinearMap.nonneg_iff_isPositive.mpr (complexify_isPositive hT)
  have hr : 0 ≤ R := CFC.sqrt_nonneg U
  have hrsq : R * R = U := CFC.sqrt_mul_sqrt_self U hu
  have hconj : 0 ≤ conjugateBoundedOperator R :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (conjugate_isPositive (ContinuousLinearMap.nonneg_iff_isPositive.mp hr))
  have hfixed : conjugateBoundedOperator R = R := by
    symm
    apply (CFC.sqrt_eq_iff U (conjugateBoundedOperator R) hu hconj).mpr
    rw [← map_mul, hrsq]
    exact complexified_operator_fixed_by_conjugation T
  let A := restrictFixedBoundedOperator R hfixed
  have hA : complexifyBoundedOperator A = R := complexify_restrictFixedBoundedOperator R hfixed
  refine ⟨A, restrictOperatorRealPart_isPositive R
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hr), ?_⟩
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  rw [map_mul, hA, hrsq]

/-- The basis-independent extended diagonal trace of an actual positive real operator. -/
theorem real_positiveTrace_basis_independent {ι κ : Type*}
    (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H) {T : H →L[ℝ] H} (hT : T.IsPositive) :
    positiveTrace b T = positiveTrace c T := by
  obtain ⟨A, hA, hsq⟩ := exists_real_positive_square_root hT
  have h : ContinuousLinearMap.adjoint A ∘L A = T := by
    change star A * A = T
    rw [hA.isSelfAdjoint.star_eq, hsq]
  rw [← h, positiveTrace_adjoint_comp_self, positiveTrace_adjoint_comp_self]
  exact hilbertSchmidtMassSq_basis_independent b c A

/-- An actual positive real operator of finite trace has an absolute dyad expansion. -/
theorem real_positiveTrace_hasSum_rankOne {ι : Type*} (b : HilbertBasis ι ℝ H)
    {T : H →L[ℝ] H} (hT : T.IsPositive) (hfin : positiveTrace b T ≠ ∞) :
    ∃ u : ι → H, Summable (fun i => ‖u i‖ ^ 2) ∧
      HasSum (fun i => InnerProductSpace.rankOne ℝ (u i) (u i)) T := by
  obtain ⟨A, hA, hsq⟩ := exists_real_positive_square_root hT
  have hl : ContinuousLinearMap.adjoint A ∘L A = T := by
    change star A * A = T
    rw [hA.isSelfAdjoint.star_eq, hsq]
  have hr : A ∘L ContinuousLinearMap.adjoint A = T := by
    change A * star A = T
    rw [hA.isSelfAdjoint.star_eq, hsq]
  rw [← hl, positiveTrace_adjoint_comp_self] at hfin
  refine ⟨fun i => A (b i), ?_, hr ▸ hasSum_rankOne_of_hilbertSchmidt b A hfin⟩
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using (ENNReal.summable_toReal hfin)

end AlbertSequential.HilbertTrace
