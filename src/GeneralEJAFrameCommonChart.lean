/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAAssociativeCoordinates

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)
  {n : ℕ} (c : Fin n → E) {i j k l : Fin n}

local notation "W" => P.frameOffDiagonalSpace c
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

def frameOffDiagonal_scaledProduct (hc : ∀ r, P.product (c r) (c r) = c r)
    (hunit : ∑ r, c r = P.unit) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : W i j) (y : W j k) : W i k :=
  ⟨x.val ⋆ y.val,
    P.frameOffDiagonal_scaled_product_mem_of_shared c hc hunit hij hik hjk x.property y.property⟩

variable [FiniteDimensional ℝ E] (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

section NonzeroTransport

variable (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

include hfr hc hor hunit hij hik hjk in
theorem exists_frameOffDiagonal_scaledLeftEquiv (x : W i j) (hx : x.val ≠ 0) :
    ∃ e : W j k ≃ₗ[ℝ] W i k, ∀ y, (e y).val = x.val ⋆ y.val := by
  have hne : W i j ≠ ⊥ := (W i j).ne_bot_iff.mpr ⟨x.val, x.property, hx⟩
  obtain ⟨u, hu⟩ := P.exists_frameOffDiagonal_traceUnit hfr c hne
  have hd := (P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit hij hik hjk u hu).finrank_eq
  let f0 : W j k →ₗ[ℝ] E := (2 : ℝ) • (P.product x.val).comp (W j k).subtype
  let f := LinearMap.codRestrict (W i k) f0 (fun y =>
    P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1) hunit
      hij hik hjk x.property y.property)
  have hcancel := P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit hij hik hjk x.property hx
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext (hcancel y.property z.property (congrArg Subtype.val h))
  exact ⟨LinearMap.linearEquivOfInjective f hf hd, fun _ => rfl⟩

include hfr hc hor hunit hij hik hjk in
theorem exists_frameOffDiagonal_scaledRightEquiv (y : W j k) (hy : y.val ≠ 0) :
    ∃ e : W i j ≃ₗ[ℝ] W i k, ∀ x, (e x).val = x.val ⋆ y.val := by
  have hyRev : y.val ∈ W k j := by
    change y.val ∈ P.frameJointSpace c (frameOffDiagonalPattern k j)
    rw [frameOffDiagonalPattern_comm k j]
    exact y.property
  have hxRev (x : W i j) : x.val ∈ W j i := by
    change x.val ∈ P.frameJointSpace c (frameOffDiagonalPattern j i)
    rw [frameOffDiagonalPattern_comm j i]
    exact x.property
  obtain ⟨e, _⟩ := P.exists_frameOffDiagonal_scaledLeftEquiv c hfr hc hor hunit
    hjk.symm hik.symm hij.symm ⟨y.val, hyRev⟩ hy
  have hji : W j i = W i j := congrArg (P.frameJointSpace c) (frameOffDiagonalPattern_comm j i)
  have hki : W k i = W i k := congrArg (P.frameJointSpace c) (frameOffDiagonalPattern_comm k i)
  have hd := e.finrank_eq
  rw [hji, hki] at hd
  let f0 : W i j →ₗ[ℝ] E := (2 : ℝ) • (P.product.flip y.val).comp (W i j).subtype
  let f := LinearMap.codRestrict (W i k) f0 (fun x =>
    P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1) hunit
      hij hik hjk x.property y.property)
  have hcancel := P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit
    hjk.symm hik.symm hij.symm hyRev hy
  have hf : Function.Injective f := by
    intro x z h
    apply Subtype.ext
    apply hcancel (hxRev x) (hxRev z)
    change y.val ⋆ x.val = y.val ⋆ z.val
    rw [P.commutative y.val x.val, P.commutative y.val z.val]
    exact congrArg Subtype.val h
  exact ⟨LinearMap.linearEquivOfInjective f hf hd, fun _ => rfl⟩

end NonzeroTransport

section FourCharts

variable (C : P.PeirceTriangleCoordinates hfr c i j k)
  (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
  (hunit : ∑ r, c r = P.unit)
  (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)

local notation "scaledEdge" => P.frameOffDiagonal_scaledProduct c

/-- The three extra edges share the triangle's coefficient space, with all
four ordered chain products described by its same bilinear multiplication. -/
structure PeirceFourCharts where
  chartIL : W i l ≃ₗ[ℝ] W i k
  chartJL : W j l ≃ₗ[ℝ] W i k
  chartKL : W k l ≃ₗ[ℝ] W i k
  productIJK : ∀ (x : W i j) (y : W j k),
    scaledEdge (fun r => (hc r).1) hunit hij hik hjk x y = C.product (C.leftChart x) (C.rightChart y)
  productIJL : ∀ (x : W i j) (y : W j l),
    chartIL (scaledEdge (fun r => (hc r).1) hunit hij hil hjl x y) = C.product (C.leftChart x) (chartJL y)
  productIKL : ∀ (x : W i k) (y : W k l),
    chartIL (scaledEdge (fun r => (hc r).1) hunit hik hil hkl x y) = C.product x (chartKL y)
  productJKL : ∀ (x : W j k) (y : W k l),
    chartJL (scaledEdge (fun r => (hc r).1) hunit hjk hjl hkl x y) = C.product (C.rightChart x) (chartKL y)

include hor in
theorem exists_peirceFourCharts
    (t : W k l) (ht : τ (P.product t.val t.val) = 2) :
    Nonempty (P.PeirceFourCharts c hfr C hc hunit hij hik hil hjk hjl hkl) := by
  let a := C.leftChart.symm C.unit
  have hright (v : W j k) : (C.rightChart v).val = a.val ⋆ v.val := by
    have h := C.product_on_edges a v
    change (C.product (C.leftChart (C.leftChart.symm C.unit)) (C.rightChart v)).val = _ at h
    rwa [C.leftChart.apply_symm_apply, C.unit_left] at h
  have hunitTrace : τ (P.product C.unit.val C.unit.val) = 2 := by
    have h := C.unit_form
    rw [P.frameOffDiagonalTraceForm_apply] at h
    linarith only [h]
  have hnonzero {x : E} (hx : τ (P.product x x) = 2) : x ≠ 0 := by
    intro h
    rw [h, P.product.map_zero, LinearMap.zero_apply, map_zero] at hx
    exact (by norm_num : (0 : ℝ) ≠ 2) hx
  have ha : a.val ≠ 0 := by
    intro h
    have hval := hright (C.rightChart.symm C.unit)
    rw [C.rightChart.apply_symm_apply, h, P.product.map_zero, LinearMap.zero_apply, smul_zero] at hval
    exact hnonzero hunitTrace hval
  obtain ⟨F, hF⟩ := P.exists_frameOffDiagonal_scaledRightEquiv c hfr hc hor hunit hik hil hkl
    t (hnonzero ht)
  obtain ⟨G, hG⟩ := P.exists_frameOffDiagonal_scaledLeftEquiv c hfr hc hor hunit hij hil hjl a ha
  obtain ⟨T, hT⟩ := P.exists_frameOffDiagonal_scaledLeftEquiv c hfr hc hor hunit hik hil hkl
    C.unit (hnonzero hunitTrace)
  let α := F.symm
  let β := G.trans F.symm
  let γ := T.trans F.symm
  have hα (v : W i l) : (F (α v)).val = v.val := congrArg Subtype.val (F.apply_symm_apply v)
  have hβ (v : W j l) : (F (β v)).val = a.val ⋆ v.val := (hα (G v)).trans (hG v)
  have hγ (v : W k l) : (F (γ v)).val = C.unit.val ⋆ v.val := (hα (T v)).trans (hT v)
  have hchain {x y z : E} (hx : x ∈ W i j) (hy : y ∈ W j k) (hz : z ∈ W k l) :
      (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) :=
    P.frameOffDiagonal_scaled_product_associative_of_chain c (fun r => (hc r).1)
      hunit hij hik hil hjk hjl hkl hx hy hz
  have htranslate (w : W k l) (p : W i k) : (C.product p (γ w)).val ⋆ t.val = p.val ⋆ w.val :=
    P.peirceTriangle_translate_right_product hfr c C hc hor hunit hij hik hil hjk hjl hkl
      ((hγ w).symm.trans (hF (γ w))) p
  have hcancel : Set.InjOn (fun q : E => a.val ⋆ q) (W j l : Set E) :=
    P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit hij hil hjl a.property ha
  refine ⟨{
    chartIL := α
    chartJL := β
    chartKL := γ
    productIJK := fun x y => Subtype.ext (C.product_on_edges x y).symm
    productIJL := ?_
    productIKL := ?_
    productJKL := ?_ }⟩
  · intro x q
    let v := C.rightChart.symm (β q)
    have hv : (β q).val = a.val ⋆ v.val :=
      (congrArg Subtype.val (C.rightChart.apply_symm_apply (β q))).symm.trans (hright v)
    have hq : q.val = v.val ⋆ t.val := by
      apply hcancel q.property
        (P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1)
          hunit hjk hjl hkl v.property t.property)
      change a.val ⋆ q.val = a.val ⋆ (v.val ⋆ t.val)
      calc
        _ = (F (β q)).val := (hβ q).symm
        _ = (β q).val ⋆ t.val := hF (β q)
        _ = (a.val ⋆ v.val) ⋆ t.val := congrArg (fun z : E => z ⋆ t.val) hv
        _ = _ := hchain a.property v.property t.property
    have hp : (C.product (C.leftChart x) (β q)).val = x.val ⋆ v.val := by
      have hh := C.product_on_edges x v
      change (C.product (C.leftChart x) (C.rightChart (C.rightChart.symm (β q)))).val = _ at hh
      rwa [C.rightChart.apply_symm_apply] at hh
    apply F.injective
    apply Subtype.ext
    calc
      _ = x.val ⋆ q.val := hα (scaledEdge (fun r => (hc r).1) hunit hij hil hjl x q)
      _ = x.val ⋆ (v.val ⋆ t.val) := congrArg (fun z : E => x.val ⋆ z) hq
      _ = (x.val ⋆ v.val) ⋆ t.val := (hchain x.property v.property t.property).symm
      _ = (C.product (C.leftChart x) (β q)).val ⋆ t.val := congrArg (fun z : E => z ⋆ t.val) hp.symm
      _ = _ := (hF (C.product (C.leftChart x) (β q))).symm
  · intro x y
    apply F.injective
    apply Subtype.ext
    calc
      _ = x.val ⋆ y.val := hα (scaledEdge (fun r => (hc r).1) hunit hik hil hkl x y)
      _ = (C.product x (γ y)).val ⋆ t.val := (htranslate y x).symm
      _ = _ := (hF (C.product x (γ y))).symm
  · intro x y
    apply F.injective
    apply Subtype.ext
    calc
      _ = a.val ⋆ (x.val ⋆ y.val) := hβ (scaledEdge (fun r => (hc r).1) hunit hjk hjl hkl x y)
      _ = (a.val ⋆ x.val) ⋆ y.val := (hchain a.property x.property y.property).symm
      _ = (C.rightChart x).val ⋆ y.val := congrArg (fun z : E => z ⋆ y.val) (hright x).symm
      _ = (C.product (C.rightChart x) (γ y)).val ⋆ t.val := (htranslate y (C.rightChart x)).symm
      _ = _ := (hF (C.product (C.rightChart x) (γ y))).symm

end FourCharts

end AlbertSequential.UnitalJordanProduct
