/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJACoefficientAdjoints
public import GeneralEJAFrameGlobalChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

theorem canonicalTrace_scaled_mixed_pairings (x y z : E) :
    τ (P.product (x ⋆ y) z) = τ (P.product y (x ⋆ z)) ∧
    τ (P.product (x ⋆ y) z) = τ (P.product x (z ⋆ y)) := by
  have h₁ := P.canonicalTraceOfFormallyReal_associative hfr y x z
  rw [P.commutative y x] at h₁
  have h₂ := P.canonicalTraceOfFormallyReal_associative hfr x y z
  rw [P.commutative y z] at h₂
  constructor
  · rw [P.product.map_smul, LinearMap.smul_apply, (P.product y).map_smul, map_smul, map_smul]
    exact congrArg (fun q : ℝ => (2 : ℝ) • q) h₁
  · rw [P.product.map_smul, LinearMap.smul_apply, (P.product x).map_smul, map_smul, map_smul]
    exact congrArg (fun q : ℝ => (2 : ℝ) • q) h₂

variable {n : ℕ} (c : Fin n → E)

local notation "W" => P.frameOffDiagonalSpace c
local notation "Bedge" => P.frameOffDiagonalTraceForm hfr c

section OffDiagonalProducts

variable (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
  {i j k : Fin n} (hij : i < j) (hjk : j < k)

def frameOffDiagonal_scaledLeftReverse (x : W i j) (z : W i k) : W j k :=
  P.frameOffDiagonal_scaledProduct c hc hunit (ne_of_gt hij) (ne_of_lt hjk) (ne_of_lt (lt_trans hij hjk))
    ⟨x.val, by
      change x.val ∈ P.frameJointSpace c (frameOffDiagonalPattern j i)
      rw [frameOffDiagonalPattern_comm j i]
      exact x.property⟩ z

def frameOffDiagonal_scaledRightReverse (z : W i k) (y : W j k) : W i j :=
  P.frameOffDiagonal_scaledProduct c hc hunit (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hij) (ne_of_gt hjk)
    z ⟨y.val, by
      change y.val ∈ P.frameJointSpace c (frameOffDiagonalPattern k j)
      rw [frameOffDiagonalPattern_comm k j]
      exact y.property⟩

theorem frameOffDiagonal_reverse_pairings (x : W i j) (y : W j k) (z : W i k) :
    let xy := P.frameOffDiagonal_scaledProduct c hc hunit (ne_of_lt hij)
      (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y
    Bedge j k (P.frameOffDiagonal_scaledLeftReverse c hc hunit hij hjk x z) y = Bedge i k xy z ∧
    Bedge i j (P.frameOffDiagonal_scaledRightReverse c hc hunit hij hjk z y) x = Bedge i k xy z := by
  have h := P.canonicalTrace_scaled_mixed_pairings hfr x.val y.val z.val
  constructor
  · simp only [P.frameOffDiagonalTraceForm_apply]
    change τ (P.product (x.val ⋆ z.val) y.val) / 2 = τ (P.product (x.val ⋆ y.val) z.val) / 2
    rw [P.commutative (x.val ⋆ z.val) y.val]
    exact congrArg (fun q : ℝ => q / 2) h.1.symm
  · simp only [P.frameOffDiagonalTraceForm_apply]
    change τ (P.product (z.val ⋆ y.val) x.val) / 2 = τ (P.product (x.val ⋆ y.val) z.val) / 2
    rw [P.commutative (z.val ⋆ y.val) x.val]
    exact congrArg (fun q : ℝ => q / 2) h.2.symm

end OffDiagonalProducts

section Chart

variable {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)
  (hc : ∀ a, P.IsPrimitive (c a)) (hunit : ∑ a, c a = P.unit) (hrs : r < s) (hst : s < t)
  (D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst)

local notation "B" => Bedge r t
local notation "A" => W r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C

def peirceIncreasingChartPreservesTraceForm : Prop :=
  ∀ (i j : Fin n) (hij : i < j) (x y : W i j),
    B (D.chart i j hij x) (D.chart i j hij y) = Bedge i j x y

variable (hform : P.peirceIncreasingChartPreservesTraceForm hfr c C hc hunit hrs hst D)
  {i j k : Fin n} (hij : i < j) (hjk : j < k)

include hform in
theorem peirceIncreasingChart_left_reverse (x : W i j) (z : W i k) :
    D.chart j k hjk (P.frameOffDiagonal_scaledLeftReverse c (fun a => (hc a).1) hunit hij hjk x z) =
      C.product (bar (D.chart i j hij x)) (D.chart i k (lt_trans hij hjk) z) := by
  apply P.peirceCoefficient_form_ext hfr c C
  intro b
  obtain ⟨y, rfl⟩ := (D.chart j k hjk).surjective b
  let xz := P.frameOffDiagonal_scaledLeftReverse c (fun a => (hc a).1) hunit hij hjk x z
  let xy := P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
    (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y
  calc
    _ = Bedge j k xz y := hform j k hjk xz y
    _ = Bedge i k xy z := (P.frameOffDiagonal_reverse_pairings hfr c
      (fun a => (hc a).1) hunit hij hjk x y z).1
    _ = B (D.chart i k (lt_trans hij hjk) xy) (D.chart i k (lt_trans hij hjk) z) :=
      (hform i k (lt_trans hij hjk) xy z).symm
    _ = B (C.product (D.chart i j hij x) (D.chart j k hjk y)) (D.chart i k (lt_trans hij hjk) z) :=
      congrArg (fun p : A => B p (D.chart i k (lt_trans hij hjk) z)) (D.product hij hjk x y)
    _ = B (D.chart j k hjk y) (C.product (bar (D.chart i j hij x)) (D.chart i k (lt_trans hij hjk) z)) :=
      P.peirceCoefficient_left_adjoint hfr c C _ _ _
    _ = _ := C.form_symmetric _ _

include hform in
theorem peirceIncreasingChart_right_reverse (z : W i k) (y : W j k) :
    D.chart i j hij (P.frameOffDiagonal_scaledRightReverse c (fun a => (hc a).1) hunit hij hjk z y) =
      C.product (D.chart i k (lt_trans hij hjk) z) (bar (D.chart j k hjk y)) := by
  apply P.peirceCoefficient_form_ext hfr c C
  intro b
  obtain ⟨x, rfl⟩ := (D.chart i j hij).surjective b
  let zy := P.frameOffDiagonal_scaledRightReverse c (fun a => (hc a).1) hunit hij hjk z y
  let xy := P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
    (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y
  calc
    _ = Bedge i j zy x := hform i j hij zy x
    _ = Bedge i k xy z := (P.frameOffDiagonal_reverse_pairings hfr c
      (fun a => (hc a).1) hunit hij hjk x y z).2
    _ = B (D.chart i k (lt_trans hij hjk) xy) (D.chart i k (lt_trans hij hjk) z) :=
      (hform i k (lt_trans hij hjk) xy z).symm
    _ = B (C.product (D.chart i j hij x) (D.chart j k hjk y)) (D.chart i k (lt_trans hij hjk) z) :=
      congrArg (fun p : A => B p (D.chart i k (lt_trans hij hjk) z)) (D.product hij hjk x y)
    _ = B (D.chart i j hij x) (C.product (D.chart i k (lt_trans hij hjk) z) (bar (D.chart j k hjk y))) :=
      P.peirceCoefficient_right_adjoint hfr c C _ _ _
    _ = _ := C.form_symmetric _ _

end Chart

end AlbertSequential.UnitalJordanProduct
