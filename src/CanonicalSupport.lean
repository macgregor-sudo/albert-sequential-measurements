/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FormalRealityCanonicalTrace
public import IdealTestFoundations
public import JordanSquareConeTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

private theorem quadraticSupport_of_pairing_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)
    (hinner : ∀ a b d, inner ℝ (P.product a b) d = inner ℝ a (P.product b d))
    (c x : E) (hc : P.product c c = c) (hx : x ∈ P.squareCone) (hpair : inner ℝ x c = 0) :
    P.quadraticRepresentation c x = 0 ∧ x = P.quadraticRepresentation (P.unit - c) x := by
  let q := P.unit - c
  have hq : P.product q q = q := PositiveInstruments.complementary_idempotent P c hc
  have hzero : P.quadraticRepresentation c x = 0 := by
    apply (P.squareCone_unitPairing_zero_iff hinner _
      (P.quadraticRepresentation_preserves_squareCone hinner c x hx)).mp
    exact (PositiveInstruments.trace_quadratic_idempotent P hinner c x hc).trans hpair
  refine ⟨hzero, sub_eq_zero.mp ?_⟩
  apply PositiveInstruments.affine_line_in_squareCone_slope_zero P hinner
    (P.quadraticRepresentation q x)
  intro t
  have hline := P.quadraticRepresentation_preserves_squareCone hinner (q + t • (P.unit - q)) x hx
  rw [PositiveInstruments.quadratic_filter_interpolation P q x hq] at hline
  have hcomp : P.unit - q = c := sub_sub_cancel _ _
  simpa only [hcomp, hzero, sub_zero, smul_zero, add_zero] using hline

/-- In Lemma 3.1, zero pairing with an idempotent puts a positive element in its complementary corner. -/
theorem quadraticSupport_of_canonicalTrace_pairing_zero {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
    (c x : E) (hc : P.product c c = c) (hx : x ∈ P.squareCone)
    (hpair : P.canonicalTraceFormOfFormallyReal hfr x c = 0) :
    P.quadraticRepresentation c x = 0 ∧ x = P.quadraticRepresentation (P.unit - c) x := by
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
  have hc' : Q.product (e.symm c) (e.symm c) = e.symm c := by
    apply e.injective
    simpa only [Q, transportProduct_apply, e.apply_symm_apply] using hc
  have hx' : e.symm x ∈ Q.squareCone :=
    (P.transportProduct_squareCone_iff e (e.symm x)).mpr (by simpa only [e.apply_symm_apply] using hx)
  have hpair' : inner ℝ (e.symm x) (e.symm c) = 0 := by
    change form (e (e.symm x)) (e (e.symm c)) = 0
    simpa only [e.apply_symm_apply] using hpair
  obtain ⟨hzero, hfix⟩ := Q.quadraticSupport_of_pairing_zero hinner (e.symm c) (e.symm x) hc' hx' hpair'
  constructor
  · simpa only [Q, transportProduct_quadraticRepresentation, e.apply_symm_apply, map_zero] using
      congrArg e hzero
  · simpa only [Q, transportProduct_quadraticRepresentation, map_sub, transportProduct_unit,
      e.apply_symm_apply] using congrArg e hfix

end AlbertSequential.UnitalJordanProduct
