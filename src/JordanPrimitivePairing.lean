/- SPDX-License-Identifier: Apache-2.0 -/
module
public import EuclideanPrimitiveCorner
public import JordanPeircePositiveMultiplication
public import PrimitiveCompressionSymmetry

/-! Exact supplied-form primitive pairing. Different primitive lengths imply
zero product, without normalization, classification or a cone premise. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem idempotents_product_zero_of_inner_zero
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q r : E) (hq : P.product q q=q) (hr : P.product r r=r)
    (hqr : inner ℝ q r=0) : P.product q r=0 := by
  have hL : inner ℝ (P.product q r) r=0 := by rw [hinner,hr,hqr]
  have h := P.idempotent_leftMultiplication_inner_decomposition hinner q r hq
  rw [hL] at h
  have hQ : inner ℝ (P.quadraticRepresentation q r) (P.quadraticRepresentation q r)=0 := by
    nlinarith [real_inner_self_nonneg (x := P.quadraticRepresentation q r),
      real_inner_self_nonneg (x := P.peirceHalfProjection q r)]
  have hH : inner ℝ (P.peirceHalfProjection q r) (P.peirceHalfProjection q r)=0 := by
    nlinarith [real_inner_self_nonneg (x := P.quadraticRepresentation q r),
      real_inner_self_nonneg (x := P.peirceHalfProjection q r)]
  rw [P.leftMultiplication_projection_decomposition q r hq,
    inner_self_eq_zero.mp hQ,inner_self_eq_zero.mp hH,smul_zero,add_zero]

theorem primitive_normalized_pairing_symmetric
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q r : E) (hq : P.IsPrimitive q) (hr : P.IsPrimitive r) :
    inner ℝ q r/inner ℝ q q=inner ℝ r q/inner ℝ r r := by
  let q' : P.Element := Element.mk q
  let r' : P.Element := Element.mk r
  have hq' : q'*q'=q' := congrArg Element.mk hq.1
  have hr' : r'*r'=r' := congrArg Element.mk hr.1
  have hq0 : q'≠0 := fun hz => hq.2.1 (congrArg Element.value hz)
  have hr0 : r'≠0 := fun hz => hr.2.1 (congrArg Element.value hz)
  have hqr : RealJordan.quadraticRepresentation q' r'=(inner ℝ q r/inner ℝ q q) • q' := by
    apply P.elementEquiv.injective
    exact P.primitive_quadraticRepresentation_coefficient hinner q r hq
  have hrq : RealJordan.quadraticRepresentation r' q'=(inner ℝ r q/inner ℝ r r) • r' := by
    apply P.elementEquiv.injective
    exact P.primitive_quadraticRepresentation_coefficient hinner r q hr
  exact RealJordan.mutual_compression_coefficients_eq q' r' _ _ hq' hr' hq0 hr0 hqr hrq

theorem primitive_inner_zero_of_length_ne
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q r : E) (hq : P.IsPrimitive q) (hr : P.IsPrimitive r)
    (hne : inner ℝ q q≠inner ℝ r r) : inner ℝ q r=0 := by
  have h := P.primitive_normalized_pairing_symmetric hinner q r hq hr
  have hqpos : 0 < inner ℝ q q := real_inner_self_pos.mpr hq.2.1
  have hrpos : 0 < inner ℝ r r := real_inner_self_pos.mpr hr.2.1
  rw [real_inner_comm q r] at h
  have hc := (div_eq_div_iff hqpos.ne' hrpos.ne').mp h
  by_contra hz
  have heq : inner ℝ r r=inner ℝ q q := (mul_left_cancel₀ hz hc)
  exact hne heq.symm

theorem primitive_product_zero_of_length_ne
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q r : E) (hq : P.IsPrimitive q) (hr : P.IsPrimitive r)
    (hne : inner ℝ q q≠inner ℝ r r) : P.product q r=0 :=
  P.idempotents_product_zero_of_inner_zero hinner q r hq.1 hr.1
    (P.primitive_inner_zero_of_length_ne hinner q r hq hr hne)

end AlbertSequential.UnitalJordanProduct
