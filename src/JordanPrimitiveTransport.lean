/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanProductTransport
public import JordanProductQuadratic

/-! Actual primitivity and quadratic maps under genuine product-preserving
linear equivalences. No assumed statement-library interface. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] (P : UnitalJordanProduct E)

theorem isPrimitive_linearEquiv_iff (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y)) (q : F) :
    Q.IsPrimitive q ↔ P.IsPrimitive (e q) := by
  constructor
  · rintro ⟨hq,hq0,hprim⟩
    refine ⟨?_,?_,?_⟩
    · exact (he q q).symm.trans (congrArg e hq)
    · intro hz
      exact hq0 (e.injective (hz.trans (map_zero e).symm))
    · intro r s hr hs hrs hsum
      have hr' : Q.product (e.symm r) (e.symm r)=e.symm r := by
        apply e.injective
        simpa only [he,LinearEquiv.apply_symm_apply] using hr
      have hs' : Q.product (e.symm s) (e.symm s)=e.symm s := by
        apply e.injective
        simpa only [he,LinearEquiv.apply_symm_apply] using hs
      have hrs' : Q.product (e.symm r) (e.symm s)=0 := by
        apply e.injective
        simpa only [he,LinearEquiv.apply_symm_apply,map_zero] using hrs
      have hsum' : e.symm r+e.symm s=q := by
        apply e.injective
        simpa only [map_add,LinearEquiv.apply_symm_apply] using hsum
      rcases hprim _ _ hr' hs' hrs' hsum' with hr0 | hs0
      · left
        simpa only [LinearEquiv.apply_symm_apply,map_zero] using congrArg e hr0
      · right
        simpa only [LinearEquiv.apply_symm_apply,map_zero] using congrArg e hs0
  · rintro ⟨hq,hq0,hprim⟩
    refine ⟨e.injective ((he q q).trans hq),?_,?_⟩
    · intro hz
      exact hq0 (by rw [hz,map_zero])
    · intro r s hr hs hrs hsum
      have hr' : P.product (e r) (e r)=e r := (he r r).symm.trans (congrArg e hr)
      have hs' : P.product (e s) (e s)=e s := (he s s).symm.trans (congrArg e hs)
      have hrs' : P.product (e r) (e s)=0 := by rw [← he,hrs,map_zero]
      have hsum' : e r+e s=e q := by rw [← map_add,hsum]
      rcases hprim _ _ hr' hs' hrs' hsum' with hr0 | hs0
      · exact Or.inl (e.injective (hr0.trans (map_zero e).symm))
      · exact Or.inr (e.injective (hs0.trans (map_zero e).symm))

theorem transportProduct_isPrimitive_iff (e : F ≃ₗ[ℝ] E) (q : F) :
    (P.transportProduct e).IsPrimitive q ↔ P.IsPrimitive (e q) :=
  P.isPrimitive_linearEquiv_iff (P.transportProduct e) e (P.transportProduct_apply e) q

theorem transportProduct_quadraticRepresentation (e : F ≃ₗ[ℝ] E) (q x : F) :
    e ((P.transportProduct e).quadraticRepresentation q x)=
      P.quadraticRepresentation (e q) (e x) := by
  simp only [quadraticRepresentation_apply,map_sub,map_smul,P.transportProduct_apply]

theorem transportProduct_inverse_apply (e : F ≃ₗ[ℝ] E) (x y : E) :
    (P.transportProduct e).product (e.symm x) (e.symm y)=e.symm (P.product x y) := by
  apply e.injective
  simp only [P.transportProduct_apply,LinearEquiv.apply_symm_apply]

end AlbertSequential.UnitalJordanProduct
