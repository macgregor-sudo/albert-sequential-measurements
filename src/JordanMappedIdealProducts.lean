/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdealTransport

/-! Actual image-ideal product with a mapped, verified local unit. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] (P : UnitalJordanProduct E)

def mappedIdealProduct (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,Q.product u.val x.val=x.val) :
    UnitalJordanProduct (I.map e.toLinearMap) :=
  P.idealProduct (I.map e.toLinearMap) (P.isJordanIdeal_map_equiv Q e he I hI)
    (e.submoduleMap I u) (fun x => by
      let f := e.submoduleMap I
      have h := congrArg e (hu (f.symm x))
      rw [he] at h
      have hx : e (f.symm x).val=x.val := congrArg Subtype.val (f.apply_symm_apply x)
      rw [hx] at h
      exact h)

theorem mappedIdealProduct_apply (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,Q.product u.val x.val=x.val)
    (x y : I.map e.toLinearMap) :
    ((P.mappedIdealProduct Q e he I hI u hu).product x y).val=P.product x.val y.val := rfl

theorem mappedIdealProduct_equiv_product (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,Q.product u.val x.val=x.val) (x y : I) :
    e.submoduleMap I ((Q.idealProduct I hI u hu).product x y)=
      (P.mappedIdealProduct Q e he I hI u hu).product (e.submoduleMap I x) (e.submoduleMap I y) :=
  Subtype.ext (he x.val y.val)

theorem mappedIdealProduct_simple (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,Q.product u.val x.val=x.val)
    (hsimple : (Q.idealProduct I hI u hu).IsSimpleJordan) :
    (P.mappedIdealProduct Q e he I hI u hu).IsSimpleJordan :=
  (P.mappedIdealProduct Q e he I hI u hu).isSimpleJordan_linearEquiv
    (Q.idealProduct I hI u hu) (e.submoduleMap I)
    (P.mappedIdealProduct_equiv_product Q e he I hI u hu) hsimple

end AlbertSequential.UnitalJordanProduct
