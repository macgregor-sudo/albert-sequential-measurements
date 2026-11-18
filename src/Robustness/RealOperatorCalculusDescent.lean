module
public import Robustness.RealOperatorDescent
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! CONDITIONAL range preservation on actual Hilbert operators. The complex
operator isometric-CFC class remains explicit; this module does not construct
it or extend an original real state to the complexification. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [IsometricContinuousFunctionalCalculus ℝ
  (RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H) IsSelfAdjoint]

theorem complexified_cfc_fixed_by_conjugation
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) :
    conjugateBoundedOperator (cfc f (complexifyBoundedOperator T)) =
      cfc f (complexifyBoundedOperator T) := by
  have hCT : IsSelfAdjoint (complexifyBoundedOperator T) := hT.map complexifyBoundedOperator
  have hSCT : IsSelfAdjoint (conjugateBoundedOperator (complexifyBoundedOperator T)) :=
    hCT.map (conjugateBoundedOperator (H := H)).toStarAlgHom
  have h := (conjugateBoundedOperator (H := H)).toStarAlgHom.map_cfc
    f (complexifyBoundedOperator T) hf
    (conjugateBoundedOperator_isometry (H := H)).continuous hCT hSCT
  simpa only [StarAlgEquiv.toStarAlgHom_apply,
    complexified_operator_fixed_by_conjugation] using h

def realOperatorCalculusValue
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) : H →L[ℝ] H :=
  restrictFixedBoundedOperator (cfc f (complexifyBoundedOperator T))
    (complexified_cfc_fixed_by_conjugation T hT f hf)

theorem complexify_realOperatorCalculusValue
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) :
    complexifyBoundedOperator (realOperatorCalculusValue T hT f hf) =
      cfc f (complexifyBoundedOperator T) :=
  complexify_restrictFixedBoundedOperator _ _

theorem realOperatorCalculusValue_norm
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) :
    ‖realOperatorCalculusValue T hT f hf‖ = ‖cfc f (complexifyBoundedOperator T)‖ :=
  restrictFixedBoundedOperator_norm _ _

theorem realOperatorCalculusValue_error_norm
    (S T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) :
    ‖S - realOperatorCalculusValue T hT f hf‖ =
      ‖complexifyBoundedOperator S - cfc f (complexifyBoundedOperator T)‖ := by
  rw [← complexifyBoundedOperator_norm, map_sub, complexify_realOperatorCalculusValue]

theorem realOperatorCalculusValue_selfAdjoint
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T))) :
    IsSelfAdjoint (realOperatorCalculusValue T hT f hf) := by
  change star (realOperatorCalculusValue T hT f hf) = realOperatorCalculusValue T hT f hf
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  rw [map_star, complexify_realOperatorCalculusValue]
  exact cfc_predicate f (complexifyBoundedOperator T)

theorem realOperatorCalculusValue_projection
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (complexifyBoundedOperator T)))
    (hid : ∀ x ∈ spectrum ℝ (complexifyBoundedOperator T), f x * f x = f x) :
    IsStarProjection (realOperatorCalculusValue T hT f hf) := by
  refine ⟨?_, realOperatorCalculusValue_selfAdjoint T hT f hf⟩
  change realOperatorCalculusValue T hT f hf * realOperatorCalculusValue T hT f hf =
    realOperatorCalculusValue T hT f hf
  apply (complexifyBoundedOperator_isometry (H := H)).injective
  rw [map_mul, complexify_realOperatorCalculusValue,
    ← cfc_mul f f (complexifyBoundedOperator T) hf hf]
  exact cfc_congr hid

end AlbertSequential
