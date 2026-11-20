/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Basic.Real.Basic

/-! The left regular representation detects the exact ideal of a coefficient quotient. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

variable {C : Type*} [AddCommGroup C] [Module ℝ C]
variable (prod : C →ₗ[ℝ] C →ₗ[ℝ] C) (I : Submodule ℝ C)
variable (hleft : ∀ x y, y ∈ I → prod x y ∈ I)

def leftRegularCoefficient (x : C) : Module.End ℝ (C ⧸ I) :=
  I.liftQ (I.mkQ.comp (prod x)) fun y hy => (Submodule.Quotient.mk_eq_zero I).mpr (hleft x y hy)

@[simp] private theorem leftRegularCoefficient_mk (x y : C) :
    leftRegularCoefficient prod I hleft x (I.mkQ y) = I.mkQ (prod x y) := rfl

/-- The coefficient algebra acts by left multiplication on the associative quotient. -/
def leftRegularQuotient : C →ₗ[ℝ] Module.End ℝ (C ⧸ I) where
  toFun := leftRegularCoefficient prod I hleft
  map_add' x y := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := I.mkQ_surjective z
    simp only [leftRegularCoefficient_mk, LinearMap.add_apply, map_add]
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := I.mkQ_surjective z
    simp only [leftRegularCoefficient_mk, LinearMap.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem leftRegularQuotient_mk (x y : C) :
    leftRegularQuotient prod I hleft x (I.mkQ y) = I.mkQ (prod x y) := rfl

theorem leftRegularQuotient_product
    (hassoc : ∀ x y z, prod (prod x y) z - prod x (prod y z) ∈ I) (x y : C) :
    leftRegularQuotient prod I hleft (prod x y) =
      leftRegularQuotient prod I hleft x * leftRegularQuotient prod I hleft y := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := I.mkQ_surjective z
  change leftRegularQuotient prod I hleft (prod x y) (I.mkQ w) =
    leftRegularQuotient prod I hleft x (leftRegularQuotient prod I hleft y (I.mkQ w))
  simp only [leftRegularQuotient_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero I).mpr (hassoc x y w)

theorem leftRegularQuotient_unit (u : C) (hu : ∀ x, prod u x = x) :
    leftRegularQuotient prod I hleft u = 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := I.mkQ_surjective z
  change leftRegularQuotient prod I hleft u (I.mkQ w) = I.mkQ w
  rw [leftRegularQuotient_mk, hu]

theorem leftRegularQuotient_ker (u : C) (hu : ∀ x, prod x u = x)
    (hright : ∀ x y, x ∈ I → prod x y ∈ I) :
    LinearMap.ker (leftRegularQuotient prod I hleft) = I := by
  ext x
  change leftRegularQuotient prod I hleft x = 0 ↔ x ∈ I
  constructor
  · intro hx
    have h := LinearMap.congr_fun hx (I.mkQ u)
    change leftRegularQuotient prod I hleft x (I.mkQ u) = 0 at h
    rw [leftRegularQuotient_mk, hu] at h
    exact (Submodule.Quotient.mk_eq_zero I).mp h
  · intro hx
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := I.mkQ_surjective z
    change leftRegularQuotient prod I hleft x (I.mkQ w) = 0
    rw [leftRegularQuotient_mk]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hright x w hx)

end AlbertSequential.AppF
