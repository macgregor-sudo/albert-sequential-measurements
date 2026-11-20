/- SPDX-License-Identifier: Apache-2.0 -/
module
public import EuclideanJordanQuadraticPositive
public import FormalRealityCanonicalTrace

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Rank preservation and the canonical trace-square identity of Lemma B.2. -/
theorem quadraticImage_primitive_ray_and_traceSq (P : UnitalJordanProduct E)
    (hfr : P.FormallyReal) (a x q : E) (hq : P.IsPrimitive q) {μ : ℝ} (hμ : 0 ≤ μ)
    (hx : x = μ • q) :
    let y := P.quadraticRepresentation a x
    (y = 0 ∨ ∃ (r : E) (t : ℝ), P.IsPrimitive r ∧ 0 < t ∧ y = t • r) ∧
      P.canonicalTraceFormOfFormallyReal hfr y y = (P.canonicalTraceOfFormallyReal hfr y) ^ 2 := by
  let V := PositiveFormModel.Model E
  let form := P.canonicalTraceFormOfFormallyReal hfr
  let core : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E form
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr)
    (P.canonicalTraceFormOfFormallyReal_positive hfr)
  let _ : InnerProductSpace.Core ℝ V := core
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hinner (u v w : V) : inner ℝ (Q.product u v) w = inner ℝ u (Q.product v w) := by
    change form (e (Q.product u v)) (e w) = form (e u) (e (Q.product v w))
    simpa only [Q, transportProduct_apply] using
      P.canonicalTraceFormOfFormallyReal_associative hfr (e u) (e v) (e w)
  have hq' : Q.IsPrimitive (e.symm q) :=
    (P.transportProduct_isPrimitive_iff e (e.symm q)).mpr (by simpa only [e.apply_symm_apply] using hq)
  have htransport : e (Q.quadraticRepresentation (e.symm a) (e.symm q)) =
      P.quadraticRepresentation a q := by
    simpa only [e.apply_symm_apply] using
      P.transportProduct_quadraticRepresentation e (e.symm a) (e.symm q)
  have hray : P.quadraticRepresentation a x = 0 ∨
      ∃ (r : E) (t : ℝ), P.IsPrimitive r ∧ 0 < t ∧ P.quadraticRepresentation a x = t • r := by
    rcases hμ.eq_or_lt with rfl | hμpos
    · left
      rw [hx, zero_smul, map_zero]
    rcases Q.primitive_image_zero_or_positive_ray hinner (e.symm a) (e.symm q) hq' with
      hzero | ⟨r, t, hr, ht, heq⟩
    · left
      have hzero' : P.quadraticRepresentation a q = 0 := by
        simpa only [htransport, map_zero] using congrArg e hzero
      rw [hx, map_smul, hzero', smul_zero]
    · right
      have heq' : P.quadraticRepresentation a q = t • e r := by
        simpa only [htransport, map_smul] using congrArg e heq
      refine ⟨e r, μ * t, (P.transportProduct_isPrimitive_iff e r).mp hr, mul_pos hμpos ht, ?_⟩
      rw [hx, map_smul, heq', smul_smul]
  refine ⟨hray, ?_⟩
  rcases hray with hzero | ⟨r, t, hr, _, heq⟩
  · simp [hzero]
  · rw [heq]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      P.canonicalTraceFormOfFormallyReal_primitive_norm hfr r hr,
      P.canonicalTraceOfFormallyReal_primitive hfr r hr, mul_one, pow_two]

end AlbertSequential.UnitalJordanProduct
