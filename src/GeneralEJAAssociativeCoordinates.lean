/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameCoherence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {i j k l : Fin n}

local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "W" => P.frameOffDiagonalSpace c
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

variable (C : P.PeirceTriangleCoordinates hfr c i j k)

private theorem peirceTriangle_product_val (p q : W i k) :
    (C.product p q).val = (C.leftChart.symm p).val ⋆ (C.rightChart.symm q).val := by
  have h := C.product_on_edges (C.leftChart.symm p) (C.rightChart.symm q)
  rwa [C.leftChart.apply_symm_apply, C.rightChart.apply_symm_apply] at h

private theorem peirceTriangle_left_inv_val (p : W i k) :
    p.val = (C.leftChart.symm p).val ⋆ (C.rightChart.symm C.unit).val := by
  simpa only [C.unit_right] using P.peirceTriangle_product_val hfr c C p C.unit

private theorem peirceTriangle_right_inv_val (q : W i k) :
    q.val = (C.leftChart.symm C.unit).val ⋆ (C.rightChart.symm q).val := by
  simpa only [C.unit_left] using P.peirceTriangle_product_val hfr c C C.unit q

private theorem peirceTriangle_unit_trace_square : τ (P.product C.unit.val C.unit.val) = 2 := by
  have h := C.unit_form
  rw [P.frameOffDiagonalTraceForm_apply] at h
  linarith only [h]

private theorem nonzero_of_trace_square_eq_two {x : E} (hx : τ (P.product x x) = 2) : x ≠ 0 := by
  intro hz
  rw [hz, P.product.map_zero, LinearMap.zero_apply, map_zero] at hx
  exact (by norm_num : (0 : ℝ) ≠ 2) hx

private theorem peirceTriangle_left_anchor_ne_zero : (C.leftChart.symm C.unit).val ≠ 0 := by
  intro hz
  have h := P.peirceTriangle_right_inv_val hfr c C C.unit
  rw [hz, P.product.map_zero, LinearMap.zero_apply, smul_zero] at h
  exact P.nonzero_of_trace_square_eq_two hfr (P.peirceTriangle_unit_trace_square hfr c C) h

variable (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)

include hc hor hunit hij hik hil hjk hjl hkl in
/-- A mixed product into the fourth edge transports right multiplication in
the actual coordinate algebra, with the transports agreed on its unit. -/
theorem peirceTriangle_translate_right_product {t w : W k l} {q : W i k}
    (hcompat : C.unit.val ⋆ w.val = q.val ⋆ t.val) (p : W i k) :
    (C.product p q).val ⋆ t.val = p.val ⋆ w.val := by
  let a := C.leftChart.symm C.unit
  let b := C.rightChart.symm C.unit
  let u := C.leftChart.symm p
  let v := C.rightChart.symm q
  have ha0 : a.val ≠ 0 := P.peirceTriangle_left_anchor_ne_zero hfr c C
  have hcancel : Set.InjOn (fun q : E => a.val ⋆ q) (W j l : Set E) :=
    P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit hij hil hjl a.property ha0
  have hchain {x y z : E} (hx : x ∈ W i j) (hy : y ∈ W j k) (hz : z ∈ W k l) :
      (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) :=
    P.frameOffDiagonal_scaled_product_associative_of_chain c (fun r => (hc r).1)
      hunit hij hik hil hjk hjl hkl hx hy hz
  have hvw : v.val ⋆ t.val = b.val ⋆ w.val := by
    apply hcancel
    · exact P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1)
        hunit hjk hjl hkl v.property t.property
    · exact P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1)
        hunit hjk hjl hkl b.property w.property
    · change a.val ⋆ (v.val ⋆ t.val) = a.val ⋆ (b.val ⋆ w.val)
      calc
        _ = (a.val ⋆ v.val) ⋆ t.val := (hchain a.property v.property t.property).symm
        _ = q.val ⋆ t.val := congrArg (fun r : E => r ⋆ t.val) (P.peirceTriangle_right_inv_val hfr c C q).symm
        _ = C.unit.val ⋆ w.val := hcompat.symm
        _ = (a.val ⋆ b.val) ⋆ w.val :=
          congrArg (fun r : E => r ⋆ w.val) (P.peirceTriangle_right_inv_val hfr c C C.unit)
        _ = _ := hchain a.property b.property w.property
  calc
    _ = (u.val ⋆ v.val) ⋆ t.val :=
      congrArg (fun r : E => r ⋆ t.val) (P.peirceTriangle_product_val hfr c C p q)
    _ = u.val ⋆ (v.val ⋆ t.val) := hchain u.property v.property t.property
    _ = u.val ⋆ (b.val ⋆ w.val) := congrArg (fun r : E => u.val ⋆ r) hvw
    _ = (u.val ⋆ b.val) ⋆ w.val := (hchain u.property b.property w.property).symm
    _ = _ := congrArg (fun r : E => r ⋆ w.val) (P.peirceTriangle_left_inv_val hfr c C p).symm

include hc hor hunit hik hil hkl in
private theorem peirceTriangle_cancel_fourth_edge (t : W k l)
    (ht : τ (P.product t.val t.val) = 2) :
    Function.Injective (fun p : W i k => p.val ⋆ t.val) := by
  have ht0 := P.nonzero_of_trace_square_eq_two hfr ht
  have htRev : t.val ∈ W l k := by
    change t.val ∈ P.frameJointSpace c (frameOffDiagonalPattern l k)
    rw [frameOffDiagonalPattern_comm l k]
    exact t.property
  have hrev (p : W i k) : p.val ∈ W k i := by
    change p.val ∈ P.frameJointSpace c (frameOffDiagonalPattern k i)
    rw [frameOffDiagonalPattern_comm k i]
    exact p.property
  have hcancel := P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit
    hkl.symm hil.symm hik.symm htRev ht0
  intro p q hpq
  apply Subtype.ext
  apply hcancel (hrev p) (hrev q)
  change t.val ⋆ p.val = t.val ⋆ q.val
  rwa [P.commutative t.val p.val, P.commutative t.val q.val]

include hc hor hunit hij hik hil hjk hjl hkl in
/-- A fourth frame member with a nonzero connecting space makes the triangle's
coordinate product associative. -/
theorem peirceTriangle_product_associative_of_four
    (t : W k l) (ht : τ (P.product t.val t.val) = 2) (x y z : W i k) :
    C.product (C.product x y) z = C.product x (C.product y z) := by
  have hunitTrace := P.peirceTriangle_unit_trace_square hfr c C
  let T := P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit hik hil hkl C.unit hunitTrace
  have hT (w : W k l) : (T w).val = C.unit.val ⋆ w.val :=
    P.frameOffDiagonalLinearEquiv_of_traceUnit_apply hfr c hc hor hunit hik hil hkl C.unit hunitTrace w
  let fz : W i l := ⟨z.val ⋆ t.val, P.frameOffDiagonal_scaled_product_mem_of_shared c
    (fun r => (hc r).1) hunit hik hil hkl z.property t.property⟩
  obtain ⟨w, hw⟩ := T.surjective fz
  have hw' : C.unit.val ⋆ w.val = z.val ⋆ t.val :=
    (hT w).symm.trans (congrArg Subtype.val hw)
  have htranslate := P.peirceTriangle_translate_right_product hfr c C hc hor hunit hij hik hil
    hjk hjl hkl hw'
  let a := C.leftChart.symm C.unit
  let u := C.leftChart.symm x
  let v := C.rightChart.symm y
  let v' := C.rightChart.symm (C.product y z)
  have ha0 := P.peirceTriangle_left_anchor_ne_zero hfr c C
  have hcancel : Set.InjOn (fun q : E => a.val ⋆ q) (W j l : Set E) :=
    P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit hij hil hjl a.property ha0
  have hchain {x y z : E} (hx : x ∈ W i j) (hy : y ∈ W j k) (hz : z ∈ W k l) :
      (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) :=
    P.frameOffDiagonal_scaled_product_associative_of_chain c (fun r => (hc r).1)
      hunit hij hik hil hjk hjl hkl hx hy hz
  have hv : v'.val ⋆ t.val = v.val ⋆ w.val := by
    apply hcancel
    · exact P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1)
        hunit hjk hjl hkl v'.property t.property
    · exact P.frameOffDiagonal_scaled_product_mem_of_shared c (fun r => (hc r).1)
        hunit hjk hjl hkl v.property w.property
    · change a.val ⋆ (v'.val ⋆ t.val) = a.val ⋆ (v.val ⋆ w.val)
      calc
        _ = (a.val ⋆ v'.val) ⋆ t.val := (hchain a.property v'.property t.property).symm
        _ = (C.product y z).val ⋆ t.val := congrArg (fun r : E => r ⋆ t.val)
          (P.peirceTriangle_right_inv_val hfr c C (C.product y z)).symm
        _ = y.val ⋆ w.val := htranslate y
        _ = (a.val ⋆ v.val) ⋆ w.val :=
          congrArg (fun r : E => r ⋆ w.val) (P.peirceTriangle_right_inv_val hfr c C y)
        _ = _ := hchain a.property v.property w.property
  apply P.peirceTriangle_cancel_fourth_edge hfr c hc hor hunit hik hil hkl t ht
  change (C.product (C.product x y) z).val ⋆ t.val = (C.product x (C.product y z)).val ⋆ t.val
  calc
    _ = (C.product x y).val ⋆ w.val := htranslate (C.product x y)
    _ = (u.val ⋆ v.val) ⋆ w.val :=
      congrArg (fun r : E => r ⋆ w.val) (P.peirceTriangle_product_val hfr c C x y)
    _ = u.val ⋆ (v.val ⋆ w.val) := hchain u.property v.property w.property
    _ = u.val ⋆ (v'.val ⋆ t.val) := congrArg (fun r : E => u.val ⋆ r) hv.symm
    _ = (u.val ⋆ v'.val) ⋆ t.val := (hchain u.property v'.property t.property).symm
    _ = _ := congrArg (fun r : E => r ⋆ t.val) (P.peirceTriangle_product_val hfr c C x (C.product y z)).symm

section Simple

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (Q : UnitalJordanProduct F)

theorem exists_associative_peirceTriangleCoordinates_of_simple_four {m : ℕ} (d : Fin m → F)
    (hd : ∀ r, Q.IsPrimitive (d r)) (hor' : ∀ r s, r ≠ s → Q.product (d r) (d s) = 0)
    (hunit' : ∑ r, d r = Q.unit)
    (hinner : ∀ x y z, inner ℝ (Q.product x y) z = inner ℝ x (Q.product y z))
    (hsimple : Q.IsSimpleJordan) {r s t u : Fin m}
    (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ A : Q.PeirceTriangleCoordinates (Q.formallyReal_of_associative_inner hinner) d r s t,
      ∀ x y z, A.product (A.product x y) z = A.product x (A.product y z) := by
  let hfr' := Q.formallyReal_of_associative_inner hinner
  obtain ⟨A⟩ := Q.exists_peirceTriangleCoordinates_of_simple d hd hor' hunit' hinner hsimple hrs hrt hst
  obtain ⟨v, hv⟩ := Q.exists_frameOffDiagonal_traceUnit hfr' d
    (Q.frameOffDiagonal_ne_bot_of_simple d hd hor' hunit' hinner hsimple t u htu)
  exact ⟨A, Q.peirceTriangle_product_associative_of_four hfr' d A hd hor' hunit' hrs hrt hru hst hsu htu v hv⟩

end Simple

end AlbertSequential.UnitalJordanProduct
