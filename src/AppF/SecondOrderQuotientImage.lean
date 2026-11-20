/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AppF.SecondOrderDimensions
public import AppF.SecondOrderQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
noncomputable section
namespace AlbertSequential.AppF

/-- The entrywise map of companion Proposition 3.2(c) on its actual domain. -/
def secondOrderReduction : E2 →ₗ[ℝ] Matrix (Fin 3) (Fin 3) Dq where
  toFun x := redq x.val
  map_add' x y := redq_add _ _
  map_smul' r x := redq_smul _ _

theorem secondOrderReduction_ker :
    LinearMap.ker secondOrderReduction = Kso.comap E2.subtype := by
  ext x
  exact redq_eq_zero_iff x.val x.property

/-- Linear identification of the actual quotient with its matrix image. -/
def secondOrderQuotientEquiv :
    (E2 ⧸ Kso.comap E2.subtype) ≃ₗ[ℝ] LinearMap.range secondOrderReduction :=
  ((Kso.comap E2.subtype).quotEquivOfEq _ secondOrderReduction_ker.symm).trans
    secondOrderReduction.quotKerEquivRange

@[simp] theorem secondOrderQuotientEquiv_mk (x : E2) :
    (secondOrderQuotientEquiv (Submodule.Quotient.mk x)).val = redq x.val := by
  simp only [secondOrderQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivRange_apply_mk]
  rfl

/-- The lifted map realizes the actual Jordan product of representatives. -/
theorem secondOrderQuotientEquiv_product (x y : E2) :
    (secondOrderQuotientEquiv (Submodule.Quotient.mk
      (⟨j3mul x.val y.val, E2_mul_mem x.property y.property⟩ : E2))).val =
      (1 / 2 : ℝ) • ((secondOrderQuotientEquiv (Submodule.Quotient.mk x)).val *
        (secondOrderQuotientEquiv (Submodule.Quotient.mk y)).val +
        (secondOrderQuotientEquiv (Submodule.Quotient.mk y)).val *
        (secondOrderQuotientEquiv (Submodule.Quotient.mk x)).val) := by
  simpa only [secondOrderQuotientEquiv_mk] using redq_jordan x.val y.val x.property y.property

theorem secondOrderQuotientEquiv_unit :
    (secondOrderQuotientEquiv (Submodule.Quotient.mk
      (⟨(albertUnit, 0, 0), standardComplexWindow.toSubalgebra.unit_mem⟩ : E2))).val = 1 := by
  rw [secondOrderQuotientEquiv_mk]
  exact redq_unit

end AlbertSequential.AppF
