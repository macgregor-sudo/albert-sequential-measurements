/- SPDX-License-Identifier: Apache-2.0 -/
module
public import UnitalJordanProduct
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Literal linear-equivalence transport and an isolated carrier for a supplied
positive bilinear form. No global multiplication/norm is installed on E. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] (P : UnitalJordanProduct E)

def transportProduct (e : F ≃ₗ[ℝ] E) : UnitalJordanProduct F where
  product :=
    { toFun := fun x => e.symm.toLinearMap.comp ((P.product (e x)).comp e.toLinearMap)
      map_add' := by intros; ext; simp only [map_add,LinearMap.add_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearMap.coe_add,Pi.add_apply]
      map_smul' := by intros; ext; simp only [map_smul,LinearMap.smul_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,RingHom.id_apply] }
  unit := e.symm P.unit
  commutative x y := by
    change e.symm (P.product (e x) (e y))=e.symm (P.product (e y) (e x))
    exact congrArg e.symm (P.commutative (e x) (e y))
  unit_left x := by change e.symm (P.product (e (e.symm P.unit)) (e x))=x; simp [P.unit_left]
  jordan_identity x y := by
    change e.symm (P.product (e (e.symm (P.product (e x) (e y))))
      (e (e.symm (P.product (e x) (e x)))))=
      e.symm (P.product (e x) (e (e.symm (P.product (e y)
        (e (e.symm (P.product (e x) (e x))))))))
    simp only [LinearEquiv.apply_symm_apply]
    exact congrArg e.symm (P.jordan_identity (e x) (e y))

@[simp] theorem transportProduct_apply (e : F ≃ₗ[ℝ] E) (x y : F) :
    e ((P.transportProduct e).product x y)=P.product (e x) (e y) :=
  e.apply_symm_apply _

@[simp] theorem transportProduct_unit (e : F ≃ₗ[ℝ] E) :
    e (P.transportProduct e).unit=P.unit := e.apply_symm_apply _

theorem transportProduct_formallyReal (hfr : P.FormallyReal) (e : F ≃ₗ[ℝ] E) :
    (P.transportProduct e).FormallyReal := by
  intro n x hx i
  have he : (∑ j, P.product (e (x j)) (e (x j)))=0 := by
    have h := congrArg e hx
    simpa only [map_sum,P.transportProduct_apply,map_zero] using h
  exact e.injective ((hfr n (fun j => e (x j)) he i).trans (map_zero e).symm)

theorem spectral_resolution_transport (e : F ≃ₗ[ℝ] E) (a : E)
    (hspec : ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → F), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ (P.transportProduct e).product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → (P.transportProduct e).product (c i) (c j)=0) ∧
      (∑ i, c i)=(P.transportProduct e).unit ∧ e.symm a=∑ i, lam i • c i) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ P.product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  obtain ⟨n,lam,c,hlam,hc,ho,hs,ha⟩ := hspec
  refine ⟨n,lam,fun i => e (c i),hlam,?_,?_,?_,?_⟩
  · intro i
    refine ⟨fun hz => (hc i).1 (e.injective (hz.trans (map_zero e).symm)),?_⟩
    simpa only [P.transportProduct_apply] using congrArg e (hc i).2
  · intro i j hij
    simpa only [P.transportProduct_apply,map_zero] using congrArg e (ho i j hij)
  · simpa only [map_sum,P.transportProduct_unit] using congrArg e hs
  · simpa only [LinearEquiv.apply_symm_apply,map_sum,map_smul,RingHom.id_apply] using congrArg e ha

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.PositiveFormModel
variable (E : Type*) [AddCommGroup E] [Module ℝ E]

/-- An isolated copy with no norm until a particular positive form is chosen. -/
structure Model where
  value : E

def equiv : Model E ≃ E where
  toFun := Model.value
  invFun := Model.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Model E) := (equiv E).addCommGroup
def addEquiv : Model E ≃+ E := (equiv E).addEquiv
instance : Module ℝ (Model E) := (addEquiv E).module ℝ

def linearEquiv : Model E ≃ₗ[ℝ] E where
  __ := addEquiv E
  map_smul' _ _ := rfl

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ (Model E) :=
  Module.Finite.equiv (linearEquiv E).symm

def innerCore (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, B x y=B y x) (hpos : ∀ x, x≠0 → 0<B x x) :
    InnerProductSpace.Core ℝ (Model E) where
  inner x y := B x.value y.value
  conj_inner_symm x y := by simpa using hsym y.value x.value
  re_inner_nonneg x := by
    change 0≤B x.value x.value
    by_cases hx : x.value=0
    · simp [hx]
    · exact (hpos _ hx).le
  add_left x y z := by
    change B (x.value+y.value) z.value=_
    rw [map_add,LinearMap.add_apply]
  smul_left x y r := by
    change B (r • x.value) y.value=_
    simp only [map_smul,LinearMap.smul_apply,RCLike.conj_to_real,smul_eq_mul]
  definite x hx := by
    apply (equiv E).injective
    change x.value=0
    by_contra hne
    exact (ne_of_gt (hpos _ hne)) hx

end AlbertSequential.PositiveFormModel
