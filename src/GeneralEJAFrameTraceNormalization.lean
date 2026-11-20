/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJACoefficientNormalization
public import GeneralEJAFrameReverse

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "N" => P.halfTraceSquare hfr

def peirceTriangleLeftPreservesSquare : Prop :=
  ∀ x : W r s, N (C.leftChart x).val = N x.val

variable (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
  (hunit : ∑ j, c j = P.unit) (hrs : r < s) (hst : s < t)
  (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j)
  (hLeft : P.peirceTriangleLeftPreservesSquare hfr c C)

section ChosenColumns

variable (K : P.PeirceFrameColumns hfr c C)

include hc hor hunit hrs hst hfirst hLeft in
theorem peirceFrameColumn_preserves_square (j : Fin n) (hrj : r < j) (p : W r t) :
    N (K.column j hrj p).val = N p.val := by
  by_cases hjs : j = s
  · subst j
    rw [K.at_second]
    have h : N (C.leftChart (C.leftChart.symm p)).val = N (C.leftChart.symm p).val :=
      hLeft (C.leftChart.symm p)
    rw [C.leftChart.apply_symm_apply] at h
    exact h.symm
  by_cases hjt : j = t
  · subst j
    rw [K.at_third]
  have htj := hfirst j (ne_of_gt hrj) hjs hjt
  let v := K.tailVector j htj
  have hv : N v.val = 1 := by
    unfold halfTraceSquare
    rw [K.tail_trace j htj]
    norm_num
  rw [K.at_tail j hrj htj, P.halfTraceSquare_scaled_mixed hfr c hc hor hunit
    (lt_trans hrs hst) htj p v, hv, mul_one]

variable (L : P.PeirceFrameEdges hfr c C K)

include hc hor hunit hrs hst hfirst hLeft in
theorem peirceFrameEdge_preserves_square (i j : Fin n) (hij : i < j) (x : W i j) :
    N (L.chart i j hij x).val = N x.val := by
  have hcol := P.peirceFrameColumn_preserves_square hfr c C hc hor hunit hrs hst hfirst hLeft K
  by_cases hi : i = r
  · subst i
    rw [← hcol j hij (L.chart r j hij x), L.first]
  have hri : r < i := by
    by_cases his : i = s
    · exact his ▸ hrs
    by_cases hit : i = t
    · exact hit ▸ lt_trans hrs hst
    exact lt_trans (lt_trans hrs hst) (hfirst i hi his hit)
  let a := K.column i hri C.unit
  have ha : N a.val = 1 :=
    (hcol i hri C.unit).trans (P.peirceTriangle_unit_halfTraceSquare hfr c C)
  rw [← hcol j (lt_trans hri hij) (L.chart i j hij x), L.later i j hri hij,
    P.halfTraceSquare_scaled_mixed hfr c hc hor hunit hri hij a x, ha, one_mul]

end ChosenColumns

include hor hfirst hLeft in
theorem exists_tracePreserving_peirceIncreasingFrameChart
    (hconnected : ∀ i j, i < j → W i j ≠ ⊥) :
    ∃ D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst,
      P.peirceIncreasingChartPreservesTraceForm hfr c C hc hunit hrs hst D := by
  obtain ⟨K⟩ := P.exists_peirceFrameColumns hfr c C hc hor hunit hrs hst hfirst hconnected
  obtain ⟨L⟩ := P.exists_peirceFrameEdges hfr c C K hc hor hunit hrs hst hfirst
  have h01 (x : W r s) : L.chart r s hrs x = C.leftChart x := by
    have h := K.at_second hrs (L.chart r s hrs x)
    rw [L.first] at h
    apply C.leftChart.symm.injective
    rw [C.leftChart.symm_apply_apply]
    exact Subtype.ext h.symm
  have h02 (x : W r t) : L.chart r t (lt_trans hrs hst) x = x := by
    have h := K.at_third (lt_trans hrs hst) (L.chart r t (lt_trans hrs hst) x)
    rw [L.first] at h
    exact Subtype.ext h.symm
  have h12 (y : W s t) : L.chart s t hst y = C.rightChart y := by
    have h := L.later s t hrs hst y
    rw [K.at_third, K.at_second] at h
    have pos := C.product_on_edges (C.leftChart.symm C.unit) y
    rw [C.leftChart.apply_symm_apply, C.unit_left] at pos
    exact Subtype.ext (h.trans pos.symm)
  let D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst := {
    chart := L.chart
    initial_pair := h01
    coefficient_pair := h02
    second_pair := h12
    product := P.peirceFrameEdges_product_of_increasing hfr c C K L hrs hst hc hor hunit hfirst }
  refine ⟨D, ?_⟩
  intro i j hij x y
  exact P.frameOffDiagonalTraceForm_eq_of_preserves_square hfr c (L.chart i j hij)
    (P.peirceFrameEdge_preserves_square hfr c C hc hor hunit hrs hst hfirst hLeft K L i j hij) x y

include hor hfirst in
theorem exists_peirceIncreasingFrameChart_normalized
    (hconnected : ∀ i j, i < j → W i j ≠ ⊥) :
    ∃ C' : P.PeirceTriangleCoordinates hfr c r s t,
      C'.product = C.product ∧ C'.unit = C.unit ∧
      ∃ D : P.PeirceIncreasingFrameChart hfr c C' hc hunit hrs hst,
        P.peirceIncreasingChartPreservesTraceForm hfr c C' hc hunit hrs hst D := by
  obtain ⟨C', hp, hu, hL⟩ := P.exists_peirceTriangle_normalized_left hfr c C hc hor hunit hrs hst
  exact ⟨C', hp, hu, P.exists_tracePreserving_peirceIncreasingFrameChart hfr c C'
    hc hor hunit hrs hst hfirst hL hconnected⟩

end AlbertSequential.UnitalJordanProduct
