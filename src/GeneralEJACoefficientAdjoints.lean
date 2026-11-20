/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameComposition

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t

def peirceCoefficientConjugate : A →ₗ[ℝ] A :=
  (2 : ℝ) • ((B).flip C.unit).smulRight C.unit - LinearMap.id

theorem peirceCoefficientConjugate_apply (x : A) :
    P.peirceCoefficientConjugate hfr c C x = (2 * B x C.unit) • C.unit - x := by
  change (2 : ℝ) • (B x C.unit • C.unit) - x = _
  rw [smul_smul]

theorem peirceCoefficientConjugate_involutive :
    Function.Involutive (P.peirceCoefficientConjugate hfr c C) := by
  intro x
  have h : B (P.peirceCoefficientConjugate hfr c C x) C.unit = B x C.unit := by
    rw [P.peirceCoefficientConjugate_apply, (B).map_sub, LinearMap.sub_apply, (B).map_smul,
      LinearMap.smul_apply, C.unit_form, smul_eq_mul]
    ring
  rw [P.peirceCoefficientConjugate_apply, h, P.peirceCoefficientConjugate_apply, sub_sub_cancel]

include C in
theorem peirceCoefficient_form_ext {x y : A} (h : ∀ z, B x z = B y z) : x = y := by
  by_contra hxy
  have hpos := C.form_positive (x - y) (sub_ne_zero.mpr hxy)
  have hz : B (x - y) (x - y) = 0 := by
    rw [(B).map_sub, LinearMap.sub_apply, h, sub_self]
  exact (ne_of_gt hpos) hz

theorem peirceCoefficient_left_pairing (a b z : A) :
    B (C.product a b) (C.product a z) = B a a * B b z := by
  have h := C.form_composition a (b + z)
  simp only [map_add, LinearMap.add_apply] at h
  rw [C.form_symmetric (C.product a z) (C.product a b), C.form_symmetric z b,
    C.form_composition a b, C.form_composition a z] at h
  linear_combination (norm := ring) (1 / 2 : ℝ) * h

theorem peirceCoefficient_right_pairing (a b z : A) :
    B (C.product b a) (C.product z a) = B a a * B b z := by
  have h := C.form_composition (b + z) a
  simp only [map_add, LinearMap.add_apply] at h
  rw [C.form_symmetric (C.product z a) (C.product b a), C.form_symmetric z b,
    C.form_composition b a, C.form_composition z a] at h
  linear_combination (norm := ring) (1 / 2 : ℝ) * h

theorem peirceCoefficient_left_adjoint (a b z : A) :
    B (C.product a b) z = B b (C.product (P.peirceCoefficientConjugate hfr c C a) z) := by
  have h := P.peirceCoefficient_left_pairing hfr c C (a + C.unit) b z
  simp only [map_add, LinearMap.add_apply, C.unit_left] at h
  rw [P.peirceCoefficient_left_pairing hfr c C a b z,
    C.form_symmetric C.unit a, C.unit_form] at h
  rw [P.peirceCoefficientConjugate_apply, C.product.map_sub, LinearMap.sub_apply,
    C.product.map_smul, LinearMap.smul_apply, C.unit_left,
    (B b).map_sub, (B b).map_smul, smul_eq_mul]
  linear_combination (norm := ring) h

theorem peirceCoefficient_right_adjoint (a b z : A) :
    B (C.product b a) z = B b (C.product z (P.peirceCoefficientConjugate hfr c C a)) := by
  have h := P.peirceCoefficient_right_pairing hfr c C (a + C.unit) b z
  simp only [map_add, LinearMap.add_apply, C.unit_right] at h
  rw [P.peirceCoefficient_right_pairing hfr c C a b z,
    C.form_symmetric C.unit a, C.unit_form] at h
  rw [P.peirceCoefficientConjugate_apply, (C.product z).map_sub, (C.product z).map_smul, C.unit_right,
    (B b).map_sub, (B b).map_smul, smul_eq_mul]
  linear_combination (norm := ring) h

theorem peirceCoefficientConjugate_product_of_associative
    (hAssoc : ∀ a b z, C.product (C.product a b) z = C.product a (C.product b z))
    (a b : A) :
    P.peirceCoefficientConjugate hfr c C (C.product a b) =
      C.product (P.peirceCoefficientConjugate hfr c C b) (P.peirceCoefficientConjugate hfr c C a) := by
  let conj := P.peirceCoefficientConjugate hfr c C
  apply P.peirceCoefficient_form_ext hfr c C
  intro z
  rw [C.form_symmetric (conj (C.product a b)) z, C.form_symmetric (C.product (conj b) (conj a)) z]
  have hu (x : A) :
      B (C.product x z) C.unit = B z (conj x) := by
    simpa only [C.unit_right] using P.peirceCoefficient_left_adjoint hfr c C x z C.unit
  calc
    _ = B (C.product (C.product a b) z) C.unit := (hu _).symm
    _ = B (C.product a (C.product b z)) C.unit := by rw [hAssoc]
    _ = B (C.product b z) (conj a) := by
      simpa only [C.unit_right] using P.peirceCoefficient_left_adjoint hfr c C a (C.product b z) C.unit
    _ = _ := P.peirceCoefficient_left_adjoint hfr c C b z (conj a)

end AlbertSequential.UnitalJordanProduct
