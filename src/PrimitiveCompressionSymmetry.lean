/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealJordanPeirce

/-! Symmetry of mutual scalar compressions is a nonunital Jordan consequence.
No inner product, trace, positivity, finite dimension or classification is used.
Actual existence of scalar compression remains an explicit hypothesis. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E] [Module ℝ E]
  [SMulCommClass ℝ E E] [IsCommJordan E]

/-- Evaluate the fundamental formula at q. This is valid without a unit. -/
theorem mutual_compression_coefficient_square (q r : E) (c d : ℝ)
    (hq : q*q=q) (hq0 : q≠0)
    (hqr : quadraticRepresentation q r=c • q)
    (hrq : quadraticRepresentation r q=d • r) : c*c=d*c := by
  have h := quadraticRepresentation_fundamental_apply q r q
  simp only [hqr,quadraticRepresentation_smul,LinearMap.smul_apply,
    quadraticRepresentation_idempotent_self q hq,hrq,map_smul,smul_smul] at h
  exact (smul_left_injective ℝ hq0) h

/-- Mutual scalar compressions of two nonzero idempotents have equal weights. -/
theorem mutual_compression_coefficients_eq (q r : E) (c d : ℝ)
    (hq : q*q=q) (hr : r*r=r) (hq0 : q≠0) (hr0 : r≠0)
    (hqr : quadraticRepresentation q r=c • q)
    (hrq : quadraticRepresentation r q=d • r) : c=d := by
  have hc := mutual_compression_coefficient_square q r c d hq hq0 hqr hrq
  have hd := mutual_compression_coefficient_square r q d c hr hr0 hrq hqr
  have hsq : (c-d)^2=0 := by nlinarith [hc,hd]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end AlbertSequential.RealJordan
