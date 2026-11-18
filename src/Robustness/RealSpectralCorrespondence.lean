module

public import Robustness.RealOperatorDescent
public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! Complexification preserves invertibility and the REAL scalar spectrum.
This does not identify a real spectrum with the full complex spectrum.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem isUnit_complexifyBoundedOperator_iff (T : H →L[ℝ] H) :
    IsUnit (complexifyBoundedOperator T) ↔ IsUnit T := by
  constructor
  · intro h
    obtain ⟨B, hright, hleft⟩ := isUnit_iff_exists.mp h
    have hright' : complexifyBoundedOperator T * conjugateBoundedOperator B = 1 := by
      simpa only [map_mul, map_one, complexified_operator_fixed_by_conjugation] using
        congrArg (conjugateBoundedOperator (H := H)) hright
    have hB : conjugateBoundedOperator B = B :=
      (left_inv_eq_right_inv hleft hright').symm
    let S := restrictFixedBoundedOperator B hB
    have hS : complexifyBoundedOperator S = B := complexify_restrictFixedBoundedOperator B hB
    apply isUnit_iff_exists.mpr
    refine ⟨S, ?_, ?_⟩
    · apply (complexifyBoundedOperator_isometry (H := H)).injective
      simpa only [map_mul, map_one, hS] using hright
    · apply (complexifyBoundedOperator_isometry (H := H)).injective
      simpa only [map_mul, map_one, hS] using hleft
  · intro h
    exact h.map (complexifyBoundedOperator (H := H)).toMonoidHom

theorem spectrum_real_complexifyBoundedOperator (T : H →L[ℝ] H) :
    spectrum ℝ (complexifyBoundedOperator T) = spectrum ℝ T := by
  ext r
  have hmap : complexifyBoundedOperator ((algebraMap ℝ (H →L[ℝ] H)) r - T) =
      (algebraMap ℝ (RealHilbertComplexification H →L[ℂ] RealHilbertComplexification H)) r -
        complexifyBoundedOperator T := by
    simp only [map_sub, AlgHomClass.commutes]
  rw [spectrum.mem_iff, spectrum.mem_iff, ← hmap, isUnit_complexifyBoundedOperator_iff]

end AlbertSequential
