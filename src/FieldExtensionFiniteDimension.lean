/- SPDX-License-Identifier: Apache-2.0
Finite-dimensionality for the actual complex and right quaternion modules.
Quaternionic dimension uses the opposite division ring, as appropriate for
right scalar multiplication; it is not replaced by real dimension. -/
module
public import QuaternionicProjectiveExtension
public import ComplexProjectiveExtension

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def realPairLinearEquiv : RealHilbertComplexification H ≃ₗ[ℝ] H × H where
  toFun u := (realPart u, imagPart u)
  invFun u := pair u.1 u.2
  left_inv u := by apply real_imag_ext <;> rfl
  right_inv u := by cases u; rfl
  map_add' u v := rfl
  map_smul' r u := by
    apply Prod.ext <;> simp only [realPart_real_smul, imagPart_real_smul,
      Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]

theorem realPair_finiteDimensional [FiniteDimensional ℝ H] :
    FiniteDimensional ℝ (RealHilbertComplexification H) :=
  FiniteDimensional.of_injective realPairLinearEquiv.toLinearMap realPairLinearEquiv.injective

theorem complexification_finiteDimensional [FiniteDimensional ℝ H] :
    FiniteDimensional ℂ (RealHilbertComplexification H) := by
  letI := realPair_finiteDimensional (H := H)
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ (RealHilbertComplexification H)

theorem quaternionification_finiteDimensional_real [FiniteDimensional ℝ H] :
    FiniteDimensional ℝ (RealHilbertQuaternionification H) := by
  letI := realPair_finiteDimensional (H := H)
  exact realPair_finiteDimensional

variable [CompleteSpace H]

namespace RightQuaternionicHilbertStructure

@[instance_reducible] def oppositeModule (S : RightQuaternionicHilbertStructure H) :
    Module (Quaternion ℝ)ᵐᵒᵖ H where
  smul q x := S.rightScalar q.unop x
  one_smul x := by change S.rightScalar 1 x = x; rw [S.right_one]; rfl
  mul_smul q r x := by
    change S.rightScalar (r.unop * q.unop) x =
      S.rightScalar q.unop (S.rightScalar r.unop x)
    rw [S.right_mul]
    rfl
  smul_zero q := map_zero (S.rightScalar q.unop)
  smul_add q x y := map_add (S.rightScalar q.unop) x y
  add_smul q r x := by
    change S.rightScalar (q.unop + r.unop) x = _
    rw [map_add]
    rfl
  zero_smul x := by change S.rightScalar 0 x = 0; rw [map_zero]; rfl

@[instance_reducible] def oppositeModuleScalarTower (S : RightQuaternionicHilbertStructure H) :
    letI := S.oppositeModule
    IsScalarTower ℝ (Quaternion ℝ)ᵐᵒᵖ H := by
  letI := S.oppositeModule
  exact ⟨fun r q x => by
    change S.rightScalar (r • q.unop) x = r • S.rightScalar q.unop x
    rw [map_smul]
    rfl⟩

theorem oppositeModule_finiteDimensional (S : RightQuaternionicHilbertStructure H)
    [FiniteDimensional ℝ H] :
    letI := S.oppositeModule
    FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H := by
  letI := S.oppositeModule
  letI := S.oppositeModuleScalarTower
  exact Module.Finite.of_restrictScalars_finite ℝ (Quaternion ℝ)ᵐᵒᵖ H

theorem real_finiteDimensional_of_opposite (S : RightQuaternionicHilbertStructure H) :
    letI := S.oppositeModule
    FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H → FiniteDimensional ℝ H := by
  letI := S.oppositeModule
  letI := S.oppositeModuleScalarTower
  intro h
  letI := h
  exact Module.Finite.trans (Quaternion ℝ)ᵐᵒᵖ H

theorem finiteDimensional_opposite_iff_real (S : RightQuaternionicHilbertStructure H) :
    letI := S.oppositeModule
    FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H ↔ FiniteDimensional ℝ H := by
  letI := S.oppositeModule
  exact ⟨S.real_finiteDimensional_of_opposite, fun h => by
    letI := h
    exact S.oppositeModule_finiteDimensional⟩

end RightQuaternionicHilbertStructure

theorem quaternionification_finiteDimensional [FiniteDimensional ℝ H] :
    letI := (fourCopyQuaternionicStructure (H := H)).toRightHilbertStructure.oppositeModule
    FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ (RealHilbertQuaternionification H) := by
  letI := quaternionification_finiteDimensional_real (H := H)
  exact (fourCopyQuaternionicStructure (H := H)).toRightHilbertStructure.oppositeModule_finiteDimensional

end AlbertSequential
