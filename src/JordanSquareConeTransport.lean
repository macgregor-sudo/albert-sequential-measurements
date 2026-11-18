/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanPrimitiveTransport
public import EuclideanJordanSquareCone

/-! The actual square cone is transported through the actual product;
no cone-preservation field or selected encoding is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] (P : UnitalJordanProduct E)

theorem transportProduct_squareCone_iff (e : F ≃ₗ[ℝ] E) (x : F) :
    x∈(P.transportProduct e).squareCone ↔ e x∈P.squareCone := by
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨e y,?_⟩
    simpa only [P.transportProduct_apply] using congrArg e hy
  · rintro ⟨y,hy⟩
    refine ⟨e.symm y,?_⟩
    apply e.injective
    simpa only [P.transportProduct_apply,LinearEquiv.apply_symm_apply] using hy

end AlbertSequential.UnitalJordanProduct
