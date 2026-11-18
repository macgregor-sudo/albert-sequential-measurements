/- SPDX-License-Identifier: Apache-2.0
Conventions follow Physlib; see THIRD_PARTY_NOTICES. -/
module

public import RealJordanPeirce
public import Mathlib.Algebra.Module.TransferInstance

/-! Minimal explicit unital Jordan product over an existing real vector space.
No order, spectral theorem, positivity, trace, or corner-span axiom is a field.
Only a separate faithful wrapper receives multiplication typeclass instances. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

structure UnitalJordanProduct (E : Type*) [AddCommGroup E] [Module ℝ E] where
  product : E →ₗ[ℝ] E →ₗ[ℝ] E
  unit : E
  commutative : ∀ x y, product x y=product y x
  unit_left : ∀ x, product unit x=x
  jordan_identity : ∀ x y,
    product (product x y) (product x x)=product x (product y (product x x))

namespace UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- Exactly the paper's finite-sum formal-reality property. -/
def FormallyReal : Prop := ∀ (n : ℕ) (x : Fin n → E),
  (∑ i, P.product (x i) (x i))=0 → ∀ i, x i=0

/-- Standard primitivity spelled with the actual explicit product. -/
def IsPrimitive (q : E) : Prop := P.product q q=q ∧ q≠0 ∧
  ∀ r s, P.product r r=r → P.product s s=s → P.product r s=0 → r+s=q → r=0 ∨ s=0

structure Element (P : UnitalJordanProduct E) where
  value : E

def elementEquiv : P.Element ≃ E where
  toFun := Element.value
  invFun := Element.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup P.Element := P.elementEquiv.addCommGroup

def elementAddEquiv : P.Element ≃+ E := P.elementEquiv.addEquiv

instance : Module ℝ P.Element := P.elementAddEquiv.module ℝ

instance : NonUnitalNonAssocCommRing P.Element :=
  { (inferInstance : AddCommGroup P.Element) with
    mul x y := ⟨P.product x.value y.value⟩
    left_distrib x y z := by
      apply P.elementEquiv.injective
      exact (P.product x.value).map_add y.value z.value
    right_distrib x y z := by
      apply P.elementEquiv.injective
      exact LinearMap.congr_fun (P.product.map_add x.value y.value) z.value
    zero_mul x := by
      apply P.elementEquiv.injective
      exact LinearMap.congr_fun P.product.map_zero x.value
    mul_zero x := by
      apply P.elementEquiv.injective
      exact (P.product x.value).map_zero
    mul_comm x y := by
      apply P.elementEquiv.injective
      exact P.commutative x.value y.value }

instance : SMulCommClass ℝ P.Element P.Element where
  smul_comm r x y := by
    apply P.elementEquiv.injective
    exact ((P.product x.value).map_smul r y.value).symm

instance : IsCommJordan P.Element where
  lmul_comm_rmul_rmul x y := by
    apply P.elementEquiv.injective
    exact P.jordan_identity x.value y.value

@[simp] theorem element_value_mul (x y : P.Element) :
    (x*y).value=P.product x.value y.value := rfl

/-- Literal polarization consumer; no further algebraic property is assumed. -/
theorem cyclic_identity (a b c x : E) :
    (P.product a (P.product (P.product b c) x)-P.product (P.product b c) (P.product a x))+
      (P.product b (P.product (P.product c a) x)-P.product (P.product c a) (P.product b x))+
        (P.product c (P.product (P.product a b) x)-P.product (P.product a b) (P.product c x))=0 := by
  exact congrArg Element.value (RealJordan.cyclic_mulLeft_commutator
    (Element.mk a : P.Element) (Element.mk b) (Element.mk c) (Element.mk x))

/-- A first-polarization consequence: L_q commutes with L_x when q*x=x. -/
theorem peirceOne_commute (q x y : E) (hq : P.product q q=q)
    (hx : P.product q x=x) :
    P.product q (P.product x y)=P.product x (P.product q y) := by
  have h := P.cyclic_identity q q x y
  simp only [hq, P.commutative x q, hx] at h
  linear_combination (norm := module) h

/-- The actual Peirce-one eigenspace. -/
def peirceOne (q : E) : Submodule ℝ E := (P.product q-LinearMap.id).ker

@[simp] theorem mem_peirceOne (q x : E) : x∈P.peirceOne q ↔ P.product q x=x := by
  change P.product q x-x=0 ↔ P.product q x=x
  exact sub_eq_zero

theorem peirceOne_product_mem (q x y : E) (hq : P.product q q=q)
    (hx : x∈P.peirceOne q) (hy : y∈P.peirceOne q) :
    P.product x y ∈ P.peirceOne q := by
  rw [P.mem_peirceOne] at hx hy ⊢
  rw [P.peirceOne_commute q x y hq hx, hy]

/-- The corner receives a bilinear product from proved closure, not an assumed
subalgebra/spectral package. Its additive and scalar structures are inherited. -/
def cornerProduct (q : E) (hq : P.product q q=q) :
    P.peirceOne q →ₗ[ℝ] P.peirceOne q →ₗ[ℝ] P.peirceOne q where
  toFun x :=
    { toFun := fun y => ⟨P.product x.val y.val,
        P.peirceOne_product_mem q x.val y.val hq x.property y.property⟩
      map_add' := fun y z => Subtype.ext ((P.product x.val).map_add y.val z.val)
      map_smul' := fun r y => Subtype.ext ((P.product x.val).map_smul r y.val) }
  map_add' x y := LinearMap.ext fun z =>
    Subtype.ext (LinearMap.congr_fun (P.product.map_add x.val y.val) z.val)
  map_smul' r x := LinearMap.ext fun y =>
    Subtype.ext (LinearMap.congr_fun (P.product.map_smul r x.val) y.val)

@[simp] theorem cornerProduct_value (q : E) (hq : P.product q q=q)
    (x y : P.peirceOne q) : (P.cornerProduct q hq x y).val=P.product x.val y.val := rfl

end UnitalJordanProduct
end AlbertSequential
