/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AppF.SecondOrderKernel
public import NativeHankelRank
public import ComplexWindowDeterminantAndMax
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section
noncomputable section
namespace AlbertSequential.AppF

private def perpCoordinates : Wperp ≃ₗ[ℝ] (Fin 3 → ℝ × ℝ × Quaternion ℝ) where
  toFun v i := ((v.val.2 i).1.imJ, (v.val.2 i).1.imK, (v.val.2 i).2)
  invFun f := ⟨(0, fun i => (⟨0, 0, (f i).1, (f i).2.1⟩, (f i).2.2)),
    fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact funext fun i => (v.property.1 i).symm
    · funext i
      apply Prod.ext
      · apply Quaternion.ext
        · exact (v.property.2 i).1.symm
        · exact (v.property.2 i).2.symm
        · rfl
        · rfl
      · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kernelCoefficient : Kso ≃ₗ[ℝ] Wperp where
  toFun x := ⟨x.val.2.2, x.property.2.2⟩
  invFun v := ⟨(0, 0, v.val), rfl, rfl, v.property⟩
  left_inv x := Subtype.ext (Prod.ext x.property.1.symm (Prod.ext x.property.2.1.symm rfl))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def secondOrderCoefficients : E2 ≃ₗ[ℝ] Wso × Albert × Albert where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secondOrderKernel_finrank : Module.finrank ℝ Kso = 18 := by
  rw [kernelCoefficient.finrank_eq, perpCoordinates.finrank_eq]
  norm_num [Module.finrank_pi_fintype, Module.finrank_prod, Quaternion.finrank_eq_four]

theorem secondOrderNeighborhood_finrank : Module.finrank ℝ E2 = 63 := by
  let _ : Module.Finite ℝ Albert := Module.finite_of_finrank_pos (by rw [native_finrank]; decide)
  rw [secondOrderCoefficients.finrank_eq]
  have hw : Module.finrank ℝ Wso = 9 := complexWindow_finrank standardComplexWindow
  let _ : Module.Finite ℝ Wso := Module.finite_of_finrank_pos (by rw [hw]; decide)
  simp [Module.finrank_prod, hw, native_finrank]

theorem secondOrderQuotient_finrank :
    Module.finrank ℝ (E2 ⧸ Kso.comap E2.subtype) = 45 := by
  let _ : Module.Finite ℝ E2 := Module.finite_of_finrank_pos (by rw [secondOrderNeighborhood_finrank]; decide)
  let e : (Kso.comap E2.subtype) ≃ₗ[ℝ] Kso :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, Kso_le_E2 x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_smul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have h := (Kso.comap E2.subtype).finrank_quotient_add_finrank
  rw [e.finrank_eq, secondOrderKernel_finrank, secondOrderNeighborhood_finrank] at h
  omega

end AlbertSequential.AppF
