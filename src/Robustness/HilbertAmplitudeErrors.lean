module

public import Robustness.HilbertStateNorm
public import Robustness.EffectPerturbation
public import HilbertClassIConstructor

/-! Actual R/C Hilbert amplitude errors on the already fixed self-adjoint
state carrier. Factors may be arbitrary contractions, including unsharp
square-root factors; they are not required to be projections. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The actual A* A effect, wrapped on the existing real state domain. -/
def hilbertAmplitudeEffect (a : H →L[𝕜] H) :
    selfAdjoint (HilbertOperatorAlgebra 𝕜 H) :=
  ⟨(operatorValue 𝕜 H).symm (star a * a),
    inverse_operatorValue_isSelfAdjoint _ (IsSelfAdjoint.star_mul_self a)⟩

theorem hilbertAmplitudeEffect_value (a : H →L[𝕜] H) :
    operatorValue 𝕜 H (hilbertAmplitudeEffect a).val = star a * a :=
  (operatorValue 𝕜 H).apply_symm_apply _

theorem hilbertAmplitudeEffect_zero :
    hilbertAmplitudeEffect (0 : H →L[𝕜] H) = 0 := by
  apply Subtype.ext
  change (hilbertAmplitudeEffect (0 : H →L[𝕜] H)).val = (0 : HilbertOperatorAlgebra 𝕜 H)
  apply (operatorValue 𝕜 H).injective
  simp only [hilbertAmplitudeEffect_value, map_zero, star_zero, mul_zero]

theorem hilbertAmplitudeEffect_one :
    hilbertAmplitudeEffect (1 : H →L[𝕜] H) = 1 := by
  apply Subtype.ext
  change (hilbertAmplitudeEffect (1 : H →L[𝕜] H)).val = (1 : HilbertOperatorAlgebra 𝕜 H)
  apply (operatorValue 𝕜 H).injective
  simp only [hilbertAmplitudeEffect_value, map_one, star_one, one_mul]

theorem hilbert_amplitude_probability_mem_Icc
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    {a : H →L[𝕜] H} (ha : ‖a‖ ≤ 1) :
    psi (hilbertAmplitudeEffect a) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply hpositive
    rw [hilbertAmplitudeEffect_value]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self a
  · calc
      _ ≤ |psi (hilbertAmplitudeEffect a)| := le_abs_self _
      _ ≤ ‖(hilbertAmplitudeEffect a).val‖ :=
        hilbert_positive_state_abs_le_norm psi hnormalized hpositive _
      _ = ‖star a * a‖ := by rw [← operatorValue_norm, hilbertAmplitudeEffect_value]
      _ ≤ ‖star a‖ * ‖a‖ := norm_mul_le _ _
      _ = ‖a‖ * ‖a‖ := congrArg (fun t : ℝ => t * ‖a‖) (norm_star a)
      _ ≤ 1 * 1 := mul_le_mul ha ha (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem hilbert_state_amplitude_error
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    {a b : H →L[𝕜] H} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |psi (hilbertAmplitudeEffect a) - psi (hilbertAmplitudeEffect b)| ≤
      2 * ‖a - b‖ := by
  calc
    _ ≤ ‖(hilbertAmplitudeEffect a - hilbertAmplitudeEffect b).val‖ :=
      hilbert_positive_state_error_le_norm psi hnormalized hpositive _ _
    _ = ‖star a * a - star b * b‖ := by
      rw [← operatorValue_norm]
      congr 1
    _ ≤ 2 * ‖a - b‖ := norm_star_mul_self_sub_le ha hb

theorem hilbert_state_word_error
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    (a b : I → H →L[𝕜] H) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hab : ∀ i, ‖a i - b i‖ ≤ epsilon) (w : List I) :
    |psi (hilbertAmplitudeEffect (chronologicalProduct a w)) -
      psi (hilbertAmplitudeEffect (chronologicalProduct b w))| ≤
      2 * (w.length : ℝ) * epsilon := by
  have hunit : ‖(1 : H →L[𝕜] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    _ ≤ 2 * ‖chronologicalProduct a w - chronologicalProduct b w‖ :=
      hilbert_state_amplitude_error psi hnormalized hpositive
        (norm_chronologicalProduct_le_one hunit a ha w)
        (norm_chronologicalProduct_le_one hunit b hb w)
    _ ≤ 2 * ((w.length : ℝ) * epsilon) :=
      mul_le_mul_of_nonneg_left
        (norm_chronologicalProduct_sub_le hunit a b ha hb hepsilon hab w) (by norm_num)
    _ = 2 * (w.length : ℝ) * epsilon := by ring

end AlbertSequential
