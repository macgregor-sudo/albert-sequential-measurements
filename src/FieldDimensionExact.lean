/- SPDX-License-Identifier: Apache-2.0
Original owner-directed Lean from the frozen 2026-11-17 FieldExtensionExactDimension return. -/
module
public import FieldExtensionFiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.Equiv.Opposite

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

def complexScalarCoordinates : ℂ ≃ₗ[ℝ] ℝ × ℝ where
  toFun z := (z.re, z.im)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    apply Prod.ext <;> simp

theorem complexScalar_finrank : Module.finrank ℝ ℂ = 2 := by
  rw [complexScalarCoordinates.finrank_eq, Module.finrank_prod]
  norm_num

theorem realPair_finrank :
    Module.finrank ℝ (RealHilbertComplexification H) = 2 * Module.finrank ℝ H := by
  rw [(realPairLinearEquiv (H := H)).finrank_eq, Module.finrank_prod]
  omega

theorem complexification_finrank :
    Module.finrank ℂ (RealHilbertComplexification H) = Module.finrank ℝ H := by
  have h := Module.finrank_mul_finrank ℝ ℂ (RealHilbertComplexification H)
  rw [complexScalar_finrank, realPair_finrank] at h
  omega

theorem quaternionification_finrank_real :
    Module.finrank ℝ (RealHilbertQuaternionification H) = 4 * Module.finrank ℝ H := by
  let := realPair_finiteDimensional (H := H)
  change Module.finrank ℝ (RealHilbertComplexification (RealHilbertComplexification H)) = _
  rw [realPair_finrank, realPair_finrank]
  omega

theorem oppositeQuaternion_finrank_real : Module.finrank ℝ (Quaternion ℝ)ᵐᵒᵖ = 4 := by
  calc
    Module.finrank ℝ (Quaternion ℝ)ᵐᵒᵖ = Module.finrank ℝ (Quaternion ℝ) :=
      (MulOpposite.opLinearEquiv ℝ : Quaternion ℝ ≃ₗ[ℝ] (Quaternion ℝ)ᵐᵒᵖ).finrank_eq.symm
    _ = 4 := Quaternion.finrank_eq_four

variable [CompleteSpace H]

theorem quaternionification_finrank :
    letI := (fourCopyQuaternionicStructure (H := H)).toRightHilbertStructure.oppositeModule
    Module.finrank (Quaternion ℝ)ᵐᵒᵖ (RealHilbertQuaternionification H) =
      Module.finrank ℝ H := by
  let S := (fourCopyQuaternionicStructure (H := H)).toRightHilbertStructure
  let := S.oppositeModule
  let := S.oppositeModuleScalarTower
  have h := Module.finrank_mul_finrank ℝ (Quaternion ℝ)ᵐᵒᵖ (RealHilbertQuaternionification H)
  rw [oppositeQuaternion_finrank_real, quaternionification_finrank_real] at h
  omega

end AlbertSequential
