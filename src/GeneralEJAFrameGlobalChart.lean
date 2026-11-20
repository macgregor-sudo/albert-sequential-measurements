/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameColumns

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

private theorem rightChart_apply_val (y : W s t) :
    (C.rightChart y).val = (C.leftChart.symm C.unit).val ⋆ y.val := by
  have h := C.product_on_edges (C.leftChart.symm C.unit) y
  rwa [C.leftChart.apply_symm_apply, C.unit_left] at h

section ChosenColumns

variable (K : P.PeirceFrameColumns hfr c C) (L : P.PeirceFrameEdges hfr c C K)
  (hrs : r < s) (hst : s < t)

private theorem chart_initial_pair (x : W r s) :
    L.chart r s hrs x = C.leftChart x := by
  have h := K.at_second hrs (L.chart r s hrs x)
  rw [L.first] at h
  apply C.leftChart.symm.injective
  rw [C.leftChart.symm_apply_apply]
  exact Subtype.ext h.symm

private theorem chart_coefficient_pair (x : W r t) :
    L.chart r t (lt_trans hrs hst) x = x := by
  have h := K.at_third (lt_trans hrs hst) (L.chart r t (lt_trans hrs hst) x)
  rw [L.first] at h
  exact Subtype.ext h.symm

include hrs in
private theorem chart_second_pair (y : W s t) :
    L.chart s t hst y = C.rightChart y := by
  have h := L.later s t hrs hst y
  rw [K.at_third, K.at_second] at h
  exact Subtype.ext (h.trans (P.rightChart_apply_val hfr c C y).symm)

variable (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
  (hunit : ∑ j, c j = P.unit)

include hc hor hunit hst in
private theorem first_product_second_tail {k : Fin n} (htk : t < k)
    (x : W r s) (y : W s k) :
    (K.column k (lt_trans hrs (lt_trans hst htk))
      (C.product (L.chart r s hrs x) (L.chart s k (lt_trans hst htk) y))).val = x.val ⋆ y.val := by
  let q := L.chart s k (lt_trans hst htk) y
  let v := C.rightChart.symm q
  let a := C.leftChart.symm C.unit
  let w := K.tailVector k htk
  have ha0 : a.val ≠ 0 := fun ha =>
    P.peirceTriangle_unit_ne_zero hfr c C (C.leftChart.symm.injective
      ((Subtype.ext ha : a = 0).trans (map_zero C.leftChart.symm).symm))
  have hq : q.val = a.val ⋆ v.val :=
    (congrArg Subtype.val (C.rightChart.apply_symm_apply q)).symm.trans
      (P.rightChart_apply_val hfr c C v)
  have hlater := L.later s k hrs (lt_trans hst htk) y
  rw [K.at_tail k _ htk, K.at_second] at hlater
  have hchain {a' b' d' : E} (ha : a' ∈ W r s) (hb : b' ∈ W s t) (hd : d' ∈ W t k) :
      (a' ⋆ b') ⋆ d' = a' ⋆ (b' ⋆ d') :=
    P.frameOffDiagonal_scaled_product_associative_of_chain c (fun j => (hc j).1) hunit
      (ne_of_lt hrs) (ne_of_lt (lt_trans hrs hst)) (ne_of_lt (lt_trans hrs (lt_trans hst htk)))
      (ne_of_lt hst) (ne_of_lt (lt_trans hst htk)) (ne_of_lt htk) ha hb hd
  have hy : y.val = v.val ⋆ w.val := by
    apply P.frameOffDiagonal_scaled_left_injective c hfr hc hor hunit
      (ne_of_lt hrs) (ne_of_lt (lt_trans hrs (lt_trans hst htk))) (ne_of_lt (lt_trans hst htk))
      a.property ha0 y.property
    · exact P.frameOffDiagonal_scaled_product_mem_of_shared c (fun j => (hc j).1) hunit
        (ne_of_lt hst) (ne_of_lt (lt_trans hst htk)) (ne_of_lt htk) v.property w.property
    · change a.val ⋆ y.val = a.val ⋆ (v.val ⋆ w.val)
      calc
        _ = q.val ⋆ w.val := hlater.symm
        _ = (a.val ⋆ v.val) ⋆ w.val := congrArg (fun z : E => z ⋆ w.val) hq
        _ = _ := hchain a.property v.property w.property
  have hp : (C.product (L.chart r s hrs x) q).val = x.val ⋆ v.val := by
    rw [P.chart_initial_pair hfr c C K L hrs]
    simpa only [C.rightChart.apply_symm_apply, v] using C.product_on_edges x v
  calc
    _ = (C.product (L.chart r s hrs x) q).val ⋆ w.val := K.at_tail k _ htk _
    _ = (x.val ⋆ v.val) ⋆ w.val := congrArg (fun z : E => z ⋆ w.val) hp
    _ = x.val ⋆ (v.val ⋆ w.val) := hchain x.property v.property w.property
    _ = _ := congrArg (fun z : E => x.val ⋆ z) hy.symm

include hc hor hunit in
private theorem first_product_third_tail {k : Fin n} (htk : t < k)
    (x : W r t) (y : W t k) :
    (K.column k (lt_trans (lt_trans hrs hst) htk)
      (C.product (L.chart r t (lt_trans hrs hst) x) (L.chart t k htk y))).val = x.val ⋆ y.val := by
  have hcompat := L.later t k (lt_trans hrs hst) htk y
  rw [K.at_tail k _ htk, K.at_third] at hcompat
  rw [K.at_tail k _ htk, P.chart_coefficient_pair hfr c C K L hrs hst]
  exact P.peirceTriangle_translate_right_product hfr c C hc hor hunit
    (ne_of_lt hrs) (ne_of_lt (lt_trans hrs hst)) (ne_of_lt (lt_trans (lt_trans hrs hst) htk))
    (ne_of_lt hst) (ne_of_lt (lt_trans hst htk)) (ne_of_lt htk) hcompat.symm x

include hc hor hunit hst in
private theorem first_product_two_tail {j k : Fin n} (htj : t < j) (hjk : j < k)
    (x : W r j) (y : W j k) :
    (K.column k (lt_trans (lt_trans (lt_trans hrs hst) htj) hjk)
      (C.product (L.chart r j (lt_trans (lt_trans hrs hst) htj) x) (L.chart j k hjk y))).val =
      x.val ⋆ y.val := by
  have hrt := lt_trans hrs hst
  have hrj := lt_trans hrt htj
  have hrk := lt_trans hrj hjk
  have htk := lt_trans htj hjk
  let p := L.chart r j hrj x
  let q := L.chart j k hjk y
  let v := K.tailVector j htj
  let z := K.tailVector k htk
  let w := P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
    (ne_of_lt htj) (ne_of_lt htk) (ne_of_lt hjk) v y
  have hchain {a b d : E} (ha : a ∈ W r t) (hb : b ∈ W t j) (hd : d ∈ W j k) :
      (a ⋆ b) ⋆ d = a ⋆ (b ⋆ d) :=
    P.frameOffDiagonal_scaled_product_associative_of_chain c (fun a => (hc a).1) hunit
      (ne_of_lt hrt) (ne_of_lt hrj) (ne_of_lt hrk) (ne_of_lt htj) (ne_of_lt htk) (ne_of_lt hjk) ha hb hd
  have hcol := L.later j k hrj hjk y
  rw [K.at_tail k _ htk, K.at_tail j hrj htj] at hcol
  have hcompat : C.unit.val ⋆ w.val = q.val ⋆ z.val :=
    (hchain C.unit.property v.property y.property).symm.trans hcol.symm
  have hx := congrArg Subtype.val (L.first j hrj x)
  rw [K.at_tail j hrj htj] at hx
  calc
    _ = (C.product p q).val ⋆ z.val := K.at_tail k _ htk _
    _ = p.val ⋆ w.val := P.peirceTriangle_translate_right_product hfr c C hc hor hunit
      (ne_of_lt hrs) (ne_of_lt hrt) (ne_of_lt hrk) (ne_of_lt hst)
      (ne_of_lt (lt_trans hst htk)) (ne_of_lt htk) hcompat p
    _ = (p.val ⋆ v.val) ⋆ y.val := (hchain p.property v.property y.property).symm
    _ = _ := congrArg (fun u : E => u ⋆ y.val) hx

variable (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j)

include hc hor hunit hrs hst hfirst in
private theorem first_product_all {j k : Fin n} (hrj : r < j) (hjk : j < k)
    (x : W r j) (y : W j k) :
    (K.column k (lt_trans hrj hjk) (C.product (L.chart r j hrj x) (L.chart j k hjk y))).val =
      x.val ⋆ y.val := by
  by_cases hjs : j = s
  · subst j
    by_cases hkt : k = t
    · subst k
      rw [K.at_third, P.chart_initial_pair hfr c C K L hrs, P.chart_second_pair hfr c C K L hrs hst]
      exact C.product_on_edges x y
    have htk := hfirst k (ne_of_gt (lt_trans hrs hjk)) (ne_of_gt hjk) hkt
    exact P.first_product_second_tail hfr c C K L hrs hst hc hor hunit htk x y
  by_cases hjt : j = t
  · subst j
    exact P.first_product_third_tail hfr c C K L hrs hst hc hor hunit hjk x y
  have htj := hfirst j (ne_of_gt hrj) hjs hjt
  exact P.first_product_two_tail hfr c C K L hrs hst hc hor hunit htj hjk x y

include hc hor hunit hrs hst hfirst in
theorem peirceFrameEdges_product_of_increasing {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (x : W i j) (y : W j k) :
    L.chart i k (lt_trans hij hjk) (P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
      (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y) =
        C.product (L.chart i j hij x) (L.chart j k hjk y) := by
  let u := P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
    (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y
  change L.chart i k (lt_trans hij hjk) u = _
  by_cases hi : i = r
  · subst i
    apply (K.column k (lt_trans hij hjk)).injective
    apply Subtype.ext
    rw [L.first]
    exact (P.first_product_all hfr c C K L hrs hst hc hor hunit hfirst hij hjk x y).symm
  have hri : r < i := by
    by_cases his : i = s
    · exact his ▸ hrs
    by_cases hit : i = t
    · exact hit ▸ lt_trans hrs hst
    exact lt_trans (lt_trans hrs hst) (hfirst i hi his hit)
  have hrj := lt_trans hri hij
  have hrk := lt_trans hrj hjk
  let a := K.column i hri C.unit
  let p := K.column j hrj (L.chart i j hij x)
  have hp : L.chart r j hrj p = L.chart i j hij x :=
    (K.column j hrj).injective (L.first j hrj p)
  apply (K.column k hrk).injective
  apply Subtype.ext
  calc
    _ = a.val ⋆ (x.val ⋆ y.val) := L.later i k hri (lt_trans hij hjk) u
    _ = (a.val ⋆ x.val) ⋆ y.val := (P.frameOffDiagonal_scaled_product_associative_of_chain c
      (fun q => (hc q).1) hunit (ne_of_lt hri) (ne_of_lt hrj) (ne_of_lt hrk)
        (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) a.property x.property y.property).symm
    _ = p.val ⋆ y.val := congrArg (fun q : E => q ⋆ y.val) (L.later i j hri hij x).symm
    _ = (K.column k hrk (C.product (L.chart r j hrj p) (L.chart j k hjk y))).val :=
      (P.first_product_all hfr c C K L hrs hst hc hor hunit hfirst hrj hjk p y).symm
    _ = _ := congrArg (fun q : W r t => (K.column k hrk (C.product q (L.chart j k hjk y))).val) hp

end ChosenColumns

section FrameChart

variable (hc : ∀ j, P.IsPrimitive (c j)) (hunit : ∑ j, c j = P.unit) (hrs : r < s) (hst : s < t)

/-- One real-linear chart per increasing pair, with all increasing triple
products expressed by the same native coefficient algebra. -/
structure PeirceIncreasingFrameChart where
  chart (i j : Fin n) (_ : i < j) : W i j ≃ₗ[ℝ] W r t
  initial_pair (x : W r s) : chart r s hrs x = C.leftChart x
  coefficient_pair (x : W r t) : chart r t (lt_trans hrs hst) x = x
  second_pair (y : W s t) : chart s t hst y = C.rightChart y
  product {i j k : Fin n} (hij : i < j) (hjk : j < k) (x : W i j) (y : W j k) :
    chart i k (lt_trans hij hjk) (P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
      (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y) =
        C.product (chart i j hij x) (chart j k hjk y)

theorem exists_peirceIncreasingFrameChart
    (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j)
    (hconnected : ∀ i j, i < j → W i j ≠ ⊥) :
    Nonempty (P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst) := by
  obtain ⟨K⟩ := P.exists_peirceFrameColumns hfr c C hc hor hunit hrs hst hfirst hconnected
  obtain ⟨L⟩ := P.exists_peirceFrameEdges hfr c C K hc hor hunit hrs hst hfirst
  exact ⟨{
    chart := L.chart
    initial_pair := P.chart_initial_pair hfr c C K L hrs
    coefficient_pair := P.chart_coefficient_pair hfr c C K L hrs hst
    second_pair := P.chart_second_pair hfr c C K L hrs hst
    product := P.peirceFrameEdges_product_of_increasing hfr c C K L hrs hst hc hor hunit hfirst }⟩

end FrameChart

end AlbertSequential.UnitalJordanProduct
