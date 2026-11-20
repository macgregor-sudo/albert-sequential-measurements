/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameColumns

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

def halfTraceSquare (x : E) : ℝ := τ (P.product x x) / 2

local notation "N" => P.halfTraceSquare hfr

theorem halfTraceSquare_smul (a : ℝ) (x : E) : N (a • x) = a ^ 2 * N x := by
  unfold halfTraceSquare
  rw [P.product.map_smul, LinearMap.smul_apply, (P.product x).map_smul, smul_smul, map_smul,
    smul_eq_mul, pow_two]
  ring

variable {n : ℕ} (c : Fin n → E)

local notation "W" => P.frameOffDiagonalSpace c
local notation "Bedge" => P.frameOffDiagonalTraceForm hfr c

theorem halfTraceSquare_scaled_mixed
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit) {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (x : W i j) (y : W j k) :
    N (x.val ⋆ y.val) = N x.val * N y.val := by
  rw [P.halfTraceSquare_smul hfr]
  unfold halfTraceSquare
  rw [P.frameOffDiagonal_shared_trace_square hfr c hc hor hunit
    (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x.property y.property]
  ring

theorem frameOffDiagonalTraceForm_symm (i j : Fin n) (x y : W i j) :
    Bedge i j x y = Bedge i j y x := by
  rw [P.frameOffDiagonalTraceForm_apply, P.frameOffDiagonalTraceForm_apply, P.commutative x.val y.val]

theorem frameOffDiagonalTraceForm_eq_of_preserves_square {i j k l : Fin n}
    (f : W i j ≃ₗ[ℝ] W k l) (hf : ∀ x, N (f x).val = N x.val) (x y : W i j) :
    Bedge k l (f x) (f y) = Bedge i j x y := by
  have hdiag (z : W i j) : Bedge k l (f z) (f z) = Bedge i j z z := by
    simpa only [P.frameOffDiagonalTraceForm_apply, halfTraceSquare] using hf z
  have h := hdiag (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [P.frameOffDiagonalTraceForm_symm hfr c k l (f y) (f x),
    P.frameOffDiagonalTraceForm_symm hfr c i j y x, hdiag x, hdiag y] at h
  linear_combination (norm := ring) (1 / 2 : ℝ) * h

variable {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

theorem peirceTriangle_unit_halfTraceSquare : N C.unit.val = 1 := by
  simpa only [P.frameOffDiagonalTraceForm_apply, halfTraceSquare] using C.unit_form

theorem exists_peirceTriangle_normalized_left
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit) (hrs : r < s) (hst : s < t) :
    ∃ D : P.PeirceTriangleCoordinates hfr c r s t,
      D.product = C.product ∧ D.unit = C.unit ∧ ∀ x, N (D.leftChart x).val = N x.val := by
  let a := C.leftChart.symm C.unit
  let b := C.rightChart.symm C.unit
  have hL (x : W r s) : (C.leftChart x).val = x.val ⋆ b.val := by
    have h := C.product_on_edges x b
    change (C.product (C.leftChart x) (C.rightChart (C.rightChart.symm C.unit))).val = _ at h
    rwa [C.rightChart.apply_symm_apply, C.unit_right] at h
  have hu : C.unit.val = a.val ⋆ b.val :=
    (congrArg Subtype.val (C.leftChart.apply_symm_apply C.unit)).symm.trans (hL a)
  have hab : N a.val * N b.val = 1 := by
    rw [← P.halfTraceSquare_scaled_mixed hfr c hc hor hunit hrs hst a b, ← hu]
    exact P.peirceTriangle_unit_halfTraceSquare hfr c C
  have ha0 : a.val ≠ 0 := fun h => P.peirceTriangle_unit_ne_zero hfr c C
    (C.leftChart.symm.injective ((Subtype.ext h : a = 0).trans (map_zero C.leftChart.symm).symm))
  have ha : 0 < N a.val :=
    div_pos (P.canonicalTraceOfFormallyReal_square_positive hfr a.val ha0) (by norm_num)
  let l : ℝ := Real.sqrt (N a.val)
  have hl : l ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hl2 : l ^ 2 = N a.val := Real.sq_sqrt ha.le
  let left := C.leftChart.trans (LinearEquiv.smulOfNeZero ℝ (W r t) l hl)
  let right := C.rightChart.trans (LinearEquiv.smulOfNeZero ℝ (W r t) l⁻¹ (inv_ne_zero hl))
  have hproduct (x : W r s) (y : W s t) :
      C.product (left x) (right y) = C.product (C.leftChart x) (C.rightChart y) := by
    change C.product (l • C.leftChart x) (l⁻¹ • C.rightChart y) = _
    rw [C.product.map_smul, LinearMap.smul_apply, (C.product (C.leftChart x)).map_smul,
      smul_smul, mul_inv_cancel₀ hl, one_smul]
  have hleft (x : W r s) : N (left x).val = N x.val := by
    change N (l • (C.leftChart x).val) = _
    rw [P.halfTraceSquare_smul hfr, hl2, hL, P.halfTraceSquare_scaled_mixed hfr c hc hor hunit hrs hst x b]
    calc
      _ = N x.val * (N a.val * N b.val) := by ring
      _ = _ := by rw [hab, mul_one]
  let D : P.PeirceTriangleCoordinates hfr c r s t := {
    C with
    leftChart := left
    rightChart := right
    product_on_edges := fun x y =>
      (congrArg Subtype.val (hproduct x y)).trans (C.product_on_edges x y) }
  exact ⟨D, rfl, rfl, hleft⟩

end AlbertSequential.UnitalJordanProduct
