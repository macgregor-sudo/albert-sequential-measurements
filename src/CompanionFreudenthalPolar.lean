/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionQuadrangleGeometry

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability

/-- The native cross is twice the Freudenthal product normalized in the paper. -/
theorem normalized_freudenthal_product_eq_polar {a b q : AlbertAtomSpace} (hab : a ≠ b)
    (hqa : tracePairing q.val a.val = 0) (hqb : tracePairing q.val b.val = 0) :
    (1 - tracePairing a.val b.val)⁻¹ • albertCross a.val b.val = q.val := by
  have hzero (x : AlbertAtomSpace) (h : tracePairing q.val x.val = 0) :
      jordanMul q.val x.val = 0 :=
    (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge q.property
      ⟨x.val, x.property.1.symm⟩ h).1
  obtain ⟨hlt, hsupport⟩ := eq_fiv_support _ _ _ q.property a.property b.property
    (hzero a hqa) (hzero b hqb) (fun he => hab (Subtype.ext he))
  have haa : tracePairing a.val a.val = 1 := by
    unfold tracePairing
    rw [a.property.1, a.property.2]
  have hbb : tracePairing b.val b.val = 1 := by
    unfold tracePairing
    rw [b.property.1, b.property.2]
  have hcross : albertCross a.val b.val =
      ((1 - tracePairing a.val b.val) : ℝ) • albertUnit -
        (a.val + b.val - (2 : ℝ) • jordanMul a.val b.val) := by
    rw [albertCross, albertSharp_atom_eq_zero _ a.property, albertSharp_atom_eq_zero _ b.property,
      sub_zero, sub_zero, albertSharp_eq_jordanMul, albertTrace_add, a.property.2, b.property.2,
      tracePairing_add_left, tracePairing_add_right, tracePairing_add_right,
      tracePairing_comm b.val a.val, haa, hbb, jordanMul_add_left, jordanMul_add_right,
      jordanMul_add_right, a.property.1, b.property.1, jordanMul_comm b.val a.val]
    module
  rw [hcross, smul_sub, smul_smul, inv_mul_cancel₀ (sub_pos.mpr hlt).ne', one_smul,
    ← hsupport]
  abel

theorem freudenthal_product_incidence_iff {a b q x : AlbertAtomSpace} (hab : a ≠ b)
    (hqa : tracePairing q.val a.val = 0) (hqb : tracePairing q.val b.val = 0) :
    tracePairing x.val (albertCross a.val b.val) = 0 ↔ tracePairing x.val q.val = 0 := by
  rw [← normalized_freudenthal_product_eq_polar hab hqa hqb, tracePairing_smul_right]
  have hzero (y : AlbertAtomSpace) (h : tracePairing q.val y.val = 0) :
      jordanMul q.val y.val = 0 :=
    (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge q.property
      ⟨y.val, y.property.1.symm⟩ h).1
  have hlt := (eq_fiv_support _ _ _ q.property a.property b.property
    (hzero a hqa) (hzero b hqb) (fun he => hab (Subtype.ext he))).1
  rw [mul_eq_zero, or_iff_right (inv_ne_zero (sub_pos.mpr hlt).ne')]

end AlbertSequential.ProjectiveMetricInvariant
