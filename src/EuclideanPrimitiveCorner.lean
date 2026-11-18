/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EuclideanJordanForm
public import JordanCubicCritical
public import JordanQuadraticSplit

/-! Primitive corners from a supplied positive associative inner product.
The proof is a cubic maximum and explicit quadratic split, with no spectral,
classification, or corner-idempotent-span premise. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem primitive_corner_eq_span
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q : E) (hq : P.IsPrimitive q) : P.peirceOne q=Submodule.span ℝ {q} := by
  have hqmem : q∈P.peirceOne q := (P.mem_peirceOne q q).mpr hq.1
  have hqqpos : 0 < inner ℝ q q := real_inner_self_pos.mpr hq.2.1
  have hqq : inner ℝ q q≠0 := ne_of_gt hqqpos
  let W : Submodule ℝ E := P.peirceOne q ⊓ (innerSL ℝ q).toLinearMap.ker
  apply le_antisymm
  · intro z hz
    let c := inner ℝ q z/inner ℝ q q
    let v := z-c • q
    have hvC : v∈P.peirceOne q := (P.peirceOne q).sub_mem hz
      ((P.peirceOne q).smul_mem c hqmem)
    have hvorth : inner ℝ q v=0 := by
      simp only [v, inner_sub_right, inner_smul_right]
      dsimp [c]
      field_simp [hqq]
      ring
    by_cases hv0 : v=0
    · have hzc : z=c • q := sub_eq_zero.mp hv0
      rw [hzc]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self q)
    · have hvW : v∈W := ⟨hvC,hvorth⟩
      haveI : Nontrivial W := nontrivial_of_ne (⟨v,hvW⟩ : W) 0
        (fun h => hv0 (congrArg Subtype.val h))
      obtain ⟨x, hxnorm, a, hcrit⟩ := P.exists_cubic_critical W hassoc
      have hxC : x.val∈P.peirceOne q := x.property.1
      have hxorth : inner ℝ q x.val=0 := x.property.2
      have hqx : P.product q x.val=x.val := (P.mem_peirceOne q x.val).mp hxC
      have hxxC : P.product x.val x.val∈P.peirceOne q :=
        P.peirceOne_product_mem q x.val x.val hq.1 hxC hxC
      have hxx : inner ℝ x.val x.val=1 := by
        rw [real_inner_self_eq_norm_sq]
        change ‖x‖^2=1
        rw [hxnorm]
        norm_num
      have hqxx : inner ℝ q (P.product x.val x.val)=1 := by
        rw [real_inner_comm (P.product x.val x.val) q, hassoc, P.commutative x.val q, hqx, hxx]
      let b := (inner ℝ q q)⁻¹
      have hb : 0<b := inv_pos.mpr hqqpos
      let u := P.product x.val x.val-a • x.val-b • q
      have huC : u∈P.peirceOne q := (P.peirceOne q).sub_mem
        ((P.peirceOne q).sub_mem hxxC ((P.peirceOne q).smul_mem a hxC))
        ((P.peirceOne q).smul_mem b hqmem)
      have huorth : inner ℝ q u=0 := by
        simp only [u, inner_sub_right, inner_smul_right, hqxx, hxorth, mul_zero, sub_zero]
        dsimp [b]
        rw [inv_mul_cancel₀ hqq, sub_self]
      have huW : u∈W := ⟨huC,huorth⟩
      have hcritU := hcrit ⟨u,huW⟩
      have huinner : inner ℝ u u=0 := by
        change inner ℝ (P.product x.val x.val-a • x.val-b • q) u=0
        rw [inner_sub_left, inner_sub_left, real_inner_smul_left,
          real_inner_smul_left, huorth, mul_zero, sub_zero]
        exact sub_eq_zero.mpr hcritU
      have hu0 : u=0 := inner_self_eq_zero.mp huinner
      have hquadratic : P.product x.val x.val=a • x.val+b • q := by
        apply sub_eq_zero.mp
        convert hu0 using 1
        dsimp [u]
        abel
      have houtside : x.val∉Submodule.span ℝ {q} := by
        intro hspan
        obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp hspan
        have hinner := congrArg (fun y => inner ℝ q y) hd
        simp only [inner_smul_right, hxorth] at hinner
        have hd0 : d=0 := (mul_eq_zero.mp hinner).resolve_right hqq
        have hx0 : x.val=0 := by rw [← hd, hd0, zero_smul]
        have hxnormE : ‖x.val‖=1 := hxnorm
        rw [hx0,norm_zero] at hxnormE
        norm_num at hxnormE
      obtain ⟨r,s,hr,hs,hrs,hrsum,hr0,hs0⟩ :=
        P.exists_split_of_quadratic_relation q x.val a b hq.1 hqx hquadratic hb houtside
      rcases hq.2.2 r s hr hs hrs hrsum with hzero | hzero
      · exact (hr0 hzero).elim
      · exact (hs0 hzero).elim
  · apply Submodule.span_le.mpr
    intro z hz
    have hzq := Set.mem_singleton_iff.mp hz
    rw [hzq]
    exact hqmem

/-- Compression with the exact denominator for the supplied associative form.
No primitive trace-one normalization is silently imposed. -/
theorem primitive_quadraticRepresentation_coefficient
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q x : E) (hq : P.IsPrimitive q) :
    P.quadraticRepresentation q x=(inner ℝ q x/inner ℝ q q) • q := by
  have hmem := P.quadraticRepresentation_mem_peirceOne q x hq.1
  rw [P.primitive_corner_eq_span hassoc q hq] at hmem
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
  have hqq : inner ℝ q q≠0 := ne_of_gt (real_inner_self_pos.mpr hq.2.1)
  have hcoeff : a * inner ℝ q q=inner ℝ q x := by
    calc
      _ = inner ℝ q (a • q) := (inner_smul_right q q a).symm
      _ = inner ℝ q (P.quadraticRepresentation q x) := by rw [ha]
      _ = inner ℝ (P.quadraticRepresentation q q) x :=
        (P.quadraticRepresentation_inner hassoc q q x).symm
      _ = inner ℝ q x := by rw [P.quadraticRepresentation_idempotent_self q hq.1]
  have ha' : a=inner ℝ q x/inner ℝ q q := (eq_div_iff hqq).mpr hcoeff
  rw [← ha,ha']

end AlbertSequential.UnitalJordanProduct
