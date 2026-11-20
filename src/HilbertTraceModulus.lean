/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceSandwich
public import Robustness.ComplexificationPositivity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-! The signed finite-trace carrier and the operator modulus. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
variable (b : HilbertBasis ι 𝕜 H)

private theorem leftPart_mem_signedFiniteTrace
    (sandwich : ∀ (P : H →L[𝕜] H) (T : signedFiniteTrace b),
      P ∘L T.val ∘L ContinuousLinearMap.adjoint P ∈ signedFiniteTrace b)
    {T U V : H →L[𝕜] H} (hm : T ∈ signedFiniteTrace b) (hU : U.IsPositive)
    (hVU : V * U = 0) (hT : T = U - V) : U ∈ signedFiniteTrace b := by
  let K := V.ker
  let : CompleteSpace K := V.isComplete_ker.completeSpace_coe
  let P := K.starProjection
  have hp : IsStarProjection P := isStarProjection_starProjection
  have hPU : P * U = U := by
    ext x
    apply Submodule.starProjection_eq_self_iff.mpr
    have hx := congrArg (fun A : H →L[𝕜] H => A x) hVU
    exact hx
  have hUP : U * P = U := by
    have hs := congrArg star hPU
    simpa only [star_mul, hU.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] using hs
  have hVP : V * P = 0 := by
    ext x
    exact K.starProjection_apply_mem x
  have hcomp : P * T * star P = U := by
    rw [hT, hp.isSelfAdjoint.star_eq, mul_sub, sub_mul, hPU, hUP, mul_assoc, hVP,
      mul_zero, sub_zero]
  have hs := sandwich P ⟨T, hm⟩
  change P * T * star P ∈ signedFiniteTrace b at hs
  rwa [hcomp] at hs

private theorem signedFiniteTrace_iff_finiteTrace_parts
    (sandwich : ∀ (P : H →L[𝕜] H) (T : signedFiniteTrace b),
      P ∘L T.val ∘L ContinuousLinearMap.adjoint P ∈ signedFiniteTrace b)
    {T U V : H →L[𝕜] H} (hU : U.IsPositive) (hV : V.IsPositive)
    (hUV : U * V = 0) (hVU : V * U = 0) (hT : T = U - V) :
    T ∈ signedFiniteTrace b ↔ positiveTrace b (U + V) ≠ ∞ := by
  rw [positiveTrace_add b hU hV, ENNReal.add_ne_top]
  constructor
  · intro hm
    have hu := leftPart_mem_signedFiniteTrace b sandwich hm hU hVU hT
    have hv : -T = V - U := by rw [hT, neg_sub]
    have hv := leftPart_mem_signedFiniteTrace b sandwich ((signedFiniteTrace b).neg_mem hm) hV hUV hv
    exact ⟨(IsPositiveFiniteTrace.of_mem_signedFiniteTrace b hu hU).2,
      (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b hv hV).2⟩
  · rintro ⟨hu, hv⟩
    exact ⟨U, V, ⟨hU, hu⟩, ⟨hV, hv⟩, hT⟩

/-- For a self-adjoint complex Hilbert operator the signed carrier is exactly `Tr |T| < ∞`. -/
theorem complex_mem_signedFiniteTrace_iff_modulus [InnerProductSpace ℂ H] (c : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    T ∈ signedFiniteTrace c ↔ positiveTrace c (CFC.abs T) ≠ ∞ := by
  rw [← CFC.posPart_add_negPart T hT]
  apply signedFiniteTrace_iff_finiteTrace_parts c (complex_signedFiniteTrace_sandwich c)
  · exact ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.posPart_nonneg T)
  · exact ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.negPart_nonneg T)
  · exact CFC.posPart_mul_negPart T
  · exact CFC.negPart_mul_posPart T
  · exact (CFC.posPart_sub_negPart T hT).symm

section Real

open RealHilbertComplexification

variable [InnerProductSpace ℝ H]

theorem real_positive_square_root_unique {D E : H →L[ℝ] H}
    (hD : D.IsPositive) (hE : E.IsPositive) (h : D * D = E * E) : D = E := by
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  have hd := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    ((complexifyBoundedOperator_isPositive_iff D).mpr hD)
  have he := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    ((complexifyBoundedOperator_isPositive_iff E).mpr hE)
  apply (CFC.mul_self_eq_mul_self_iff _ _ hd he).mp
  rw [← map_mul, ← map_mul, h]

/-- The positive and negative parts of a real self-adjoint bounded operator,
expressed using the positive square root of its square. -/
theorem real_operator_parts (T D : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (hD : D.IsPositive) (hDsq : D * D = T * T) :
    ∃ U V : H →L[ℝ] H, U.IsPositive ∧ V.IsPositive ∧ U * V = 0 ∧ V * U = 0 ∧
      T = U - V ∧ D = U + V := by
  let C := complexifyBoundedOperator T
  have hC : IsSelfAdjoint C := hT.map complexifyBoundedOperator
  have hDc : 0 ≤ complexifyBoundedOperator D := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    ((complexifyBoundedOperator_isPositive_iff D).mpr hD)
  have hC2 : 0 ≤ star C * C := star_mul_self_nonneg C
  have hAbs : complexifyBoundedOperator D = CFC.abs C := by
    symm
    apply (CFC.sqrt_eq_iff (star C * C) (complexifyBoundedOperator D) hC2 hDc).mpr
    rw [← map_mul, hDsq, map_mul, hC.star_eq]
  let U := (1 / 2 : ℝ) • (D + T)
  let V := (1 / 2 : ℝ) • (D - T)
  have hu : complexifyBoundedOperator U = C⁺ := by
    change complexifyBoundedOperator ((1 / 2 : ℝ) • (D + T)) = C⁺
    rw [map_smul, map_add, hAbs, CFC.abs_add_self C hC,
      ← Nat.cast_smul_eq_nsmul ℝ (2 : ℕ), smul_smul]
    norm_num
  have hv : complexifyBoundedOperator V = C⁻ := by
    change complexifyBoundedOperator ((1 / 2 : ℝ) • (D - T)) = C⁻
    rw [map_smul, map_sub, hAbs, CFC.abs_sub_self C hC,
      ← Nat.cast_smul_eq_nsmul ℝ (2 : ℕ), smul_smul]
    norm_num
  have hUp : U.IsPositive := (complexifyBoundedOperator_isPositive_iff U).mp (by
    rw [hu]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.posPart_nonneg C))
  have hVp : V.IsPositive := (complexifyBoundedOperator_isPositive_iff V).mp (by
    rw [hv]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.negPart_nonneg C))
  have hUV : U * V = 0 := by
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_mul, hu, hv, CFC.posPart_mul_negPart, map_zero]
  have hVU : V * U = 0 := by
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_mul, hv, hu, CFC.negPart_mul_posPart, map_zero]
  have hTparts : T = U - V := by
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_sub, hu, hv, CFC.posPart_sub_negPart C hC]
  have hDparts : D = U + V := by
    apply (complexifyBoundedOperator_isometry (H := H)).injective
    rw [map_add, hu, hv, CFC.posPart_add_negPart C hC, hAbs]
  exact ⟨U,V,hUp,hVp,hUV,hVU,hTparts,hDparts⟩

/-- For a self-adjoint real Hilbert operator, the actual positive root of `T²` tests trace class. -/
theorem real_mem_signedFiniteTrace_iff_modulus (c : HilbertBasis ι ℝ H)
    (T D : H →L[ℝ] H) (hT : IsSelfAdjoint T) (hD : D.IsPositive) (hDsq : D * D = T * T) :
    T ∈ signedFiniteTrace c ↔ positiveTrace c D ≠ ∞ := by
  obtain ⟨U,V,hUp,hVp,hUV,hVU,hTparts,hDparts⟩ := real_operator_parts T D hT hD hDsq
  rw [hDparts]
  exact signedFiniteTrace_iff_finiteTrace_parts c (real_signedFiniteTrace_sandwich c)
    hUp hVp hUV hVU hTparts

/-- Actual trace-norm mass of the Jordan decomposition of a real trace-class increment. -/
theorem real_signedTrace_jordan_decomposition (c : HilbertBasis ι ℝ H)
    (X : signedFiniteTrace c) (D : H →L[ℝ] H) (hD : D.IsPositive)
    (hDsq : D * D = X.val * X.val) :
    ∃ U V : signedFiniteTrace c, U.val.IsPositive ∧ V.val.IsPositive ∧ X = U-V ∧
      signedTrace c U + signedTrace c V = (positiveTrace c D).toReal := by
  have hX := signedFiniteTrace_isSelfAdjoint c X
  obtain ⟨U,V,hU,hV,hUV,hVU,hsub,hadd⟩ := real_operator_parts X.val D hX hD hDsq
  have hf := (real_mem_signedFiniteTrace_iff_modulus c X.val D hX hD hDsq).mp X.property
  rw [hadd, positiveTrace_add c hU hV, ENNReal.add_ne_top] at hf
  let u : signedFiniteTrace c := ⟨U,(IsPositiveFiniteTrace.mem_signedFiniteTrace c ⟨hU,hf.1⟩)⟩
  let v : signedFiniteTrace c := ⟨V,(IsPositiveFiniteTrace.mem_signedFiniteTrace c ⟨hV,hf.2⟩)⟩
  refine ⟨u,v,hU,hV,Subtype.ext hsub,?_⟩
  rw [signedTrace_eq_positiveTrace_toReal c u hU, signedTrace_eq_positiveTrace_toReal c v hV,
    hadd, positiveTrace_add c hU hV, ENNReal.toReal_add hf.1 hf.2]

end Real

end AlbertSequential.HilbertTrace
