/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameReverse

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "A" => W r t
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C

theorem peirceCoefficient_product_conjugate_self (x : A) :
    C.product x (bar x) = B x x • C.unit := by
  apply P.peirceCoefficient_form_ext hfr c C
  intro z
  have h := P.peirceCoefficient_right_adjoint hfr c C (bar x) x z
  rw [P.peirceCoefficientConjugate_involutive hfr c C x] at h
  calc
    _ = B x (C.product z x) := h
    _ = B (C.product C.unit x) (C.product z x) := by rw [C.unit_left]
    _ = B x x * B C.unit z := P.peirceCoefficient_right_pairing hfr c C x C.unit z
    _ = _ := by rw [(B).map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem peirceCoefficient_conjugate_product_self (x : A) :
    C.product (bar x) x = B x x • C.unit := by
  apply P.peirceCoefficient_form_ext hfr c C
  intro z
  have h := P.peirceCoefficient_left_adjoint hfr c C (bar x) x z
  rw [P.peirceCoefficientConjugate_involutive hfr c C x] at h
  calc
    _ = B x (C.product x z) := h
    _ = B (C.product x C.unit) (C.product x z) := by rw [C.unit_right]
    _ = B x x * B C.unit z := P.peirceCoefficient_left_pairing hfr c C x C.unit z
    _ = _ := by rw [(B).map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem peirceCoefficient_product_conjugate_polarized (x y : A) :
    C.product x (bar y) + C.product y (bar x) = (2 * B x y) • C.unit := by
  have h := P.peirceCoefficient_product_conjugate_self hfr c C (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [C.form_symmetric y x, P.peirceCoefficient_product_conjugate_self hfr c C x,
    P.peirceCoefficient_product_conjugate_self hfr c C y] at h
  linear_combination (norm := module) h

theorem peirceCoefficient_conjugate_product_polarized (x y : A) :
    C.product (bar x) y + C.product (bar y) x = (2 * B x y) • C.unit := by
  have h := P.peirceCoefficient_conjugate_product_self hfr c C (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [C.form_symmetric y x, P.peirceCoefficient_conjugate_product_self hfr c C x,
    P.peirceCoefficient_conjugate_product_self hfr c C y] at h
  linear_combination (norm := module) h

theorem peirceIncreasingChart_same_edge
    (hc : ∀ a, P.IsPrimitive (c a)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ a, c a = P.unit) (hrs : r < s) (hst : s < t)
    (D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst)
    (hform : P.peirceIncreasingChartPreservesTraceForm hfr c C hc hunit hrs hst D)
    {i j : Fin n} (hij : i < j) (x y : W i j) :
    P.product x.val y.val = B (D.chart i j hij x) (D.chart i j hij y) • (c i + c j) := by
  rw [hform i j hij x y, P.frameOffDiagonalTraceForm_apply]
  exact P.frameOffDiagonal_product_eq_trace_diag hfr c (hc i) (hc j) (hor i j (ne_of_lt hij))
    x.property y.property

end AlbertSequential.UnitalJordanProduct
