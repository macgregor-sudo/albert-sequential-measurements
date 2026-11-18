/- SPDX-License-Identifier: Apache-2.0
Conventions follow Physlib; see THIRD_PARTY_NOTICES. -/
module

public import UnitalJordanProduct

/-! Literal quadratic operator for explicit bilinear product data, bound to
the generic quadratic representation through the wrapper. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

def quadraticRepresentation (a : E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • ((P.product a).comp (P.product a))-P.product (P.product a a)

@[simp] theorem quadraticRepresentation_apply (a x : E) :
    P.quadraticRepresentation a x=(2 : ℝ) • P.product a (P.product a x)-
      P.product (P.product a a) x := rfl

@[simp] theorem element_quadraticRepresentation (a x : P.Element) :
    (RealJordan.quadraticRepresentation a x).value=
      P.quadraticRepresentation a.value x.value := rfl

theorem quadraticRepresentation_fundamental (a b x : E) :
    P.quadraticRepresentation (P.quadraticRepresentation a b) x=
      P.quadraticRepresentation a (P.quadraticRepresentation b
        (P.quadraticRepresentation a x)) := by
  have h := congrArg Element.value (RealJordan.quadraticRepresentation_fundamental_apply
    (Element.mk a : P.Element) (Element.mk b) (Element.mk x))
  simpa only [P.element_quadraticRepresentation] using h

theorem quadraticRepresentation_mem_peirceOne (q x : E) (hq : P.product q q=q) :
    P.quadraticRepresentation q x∈P.peirceOne q := by
  have hq' : (Element.mk q : P.Element)*(Element.mk q)=Element.mk q := by
    apply P.elementEquiv.injective
    exact hq
  rw [P.mem_peirceOne]
  have h := congrArg Element.value (RealJordan.mul_quadraticRepresentation_idempotent
    (Element.mk q : P.Element) (Element.mk x) hq')
  simpa only [P.element_value_mul, P.element_quadraticRepresentation] using h

theorem quadraticRepresentation_idempotent_self (q : E) (hq : P.product q q=q) :
    P.quadraticRepresentation q q=q := by
  simp only [P.quadraticRepresentation_apply,hq,two_smul]
  abel

@[simp] theorem quadraticRepresentation_unit (a : E) :
    P.quadraticRepresentation a P.unit=P.product a a := by
  have hunit (x : E) : P.product x P.unit=x := by rw [P.commutative,P.unit_left]
  simp only [P.quadraticRepresentation_apply,hunit,two_smul]
  abel

end AlbertSequential.UnitalJordanProduct
