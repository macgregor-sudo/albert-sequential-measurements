/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameConnectivity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

abbrev frameOffDiagonalSpace {n : ℕ} (c : Fin n → E) (i j : Fin n) :=
  P.frameJointSpace c (frameOffDiagonalPattern i j)

section Triangle

variable [FiniteDimensional ℝ E] (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "W" => P.frameOffDiagonalSpace c

def frameOffDiagonalTraceForm (i j : Fin n) : W i j →ₗ[ℝ] W i j →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (P.canonicalTraceFormOfFormallyReal hfr).compl₁₂ (W i j).subtype (W i j).subtype

theorem frameOffDiagonalTraceForm_apply (i j : Fin n) (x y : W i j) :
    P.frameOffDiagonalTraceForm hfr c i j x y = τ (P.product x.val y.val) / 2 := by
  change (1 / 2 : ℝ) * P.canonicalTraceFormOfFormallyReal hfr x.val y.val = _
  rw [P.canonicalTraceFormOfFormallyReal_apply]
  ring

/-- An actual edge of a Peirce triangle carries a unital bilinear product with
positive multiplicative squared norm. The charts specify the native mixed-edge product. -/
structure PeirceTriangleCoordinates (i j k : Fin n) where
  leftChart : W i j ≃ₗ[ℝ] W i k
  rightChart : W j k ≃ₗ[ℝ] W i k
  product : W i k →ₗ[ℝ] W i k →ₗ[ℝ] W i k
  unit : W i k
  product_on_edges : ∀ (x : W i j) (y : W j k),
    (product (leftChart x) (rightChart y)).val = (2 : ℝ) • P.product x.val y.val
  unit_left : ∀ x, product unit x = x
  unit_right : ∀ x, product x unit = x
  form_symmetric : ∀ x y, P.frameOffDiagonalTraceForm hfr c i k x y =
    P.frameOffDiagonalTraceForm hfr c i k y x
  form_positive : ∀ x ≠ 0, 0 < P.frameOffDiagonalTraceForm hfr c i k x x
  unit_form : P.frameOffDiagonalTraceForm hfr c i k unit unit = 1
  form_composition : ∀ x y, P.frameOffDiagonalTraceForm hfr c i k (product x y) (product x y) =
    P.frameOffDiagonalTraceForm hfr c i k x x * P.frameOffDiagonalTraceForm hfr c i k y y

private def sharedEdgeProduct
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    W i j →ₗ[ℝ] W j k →ₗ[ℝ] W i k := by
  let f (x : W i j) (y : W j k) : W i k := ⟨(2 : ℝ) • P.product x.val y.val,
    Submodule.smul_mem _ _ (P.frameOffDiagonal_product_mem_of_shared c hc hunit
      hij hik hjk x.property y.property)⟩
  exact LinearMap.mk₂ ℝ f
    (fun x z y => Subtype.ext (by
      change (2 : ℝ) • P.product (x.val + z.val) y.val =
        (2 : ℝ) • P.product x.val y.val + (2 : ℝ) • P.product z.val y.val
      rw [P.product.map_add, LinearMap.add_apply, smul_add]))
    (fun r x y => Subtype.ext (by
      change (2 : ℝ) • P.product (r • x.val) y.val = r • ((2 : ℝ) • P.product x.val y.val)
      rw [P.product.map_smul, LinearMap.smul_apply, smul_comm (2 : ℝ) r]))
    (fun x y z => Subtype.ext (by
      change (2 : ℝ) • P.product x.val (y.val + z.val) =
        (2 : ℝ) • P.product x.val y.val + (2 : ℝ) • P.product x.val z.val
      rw [map_add, smul_add]))
    (fun r x y => Subtype.ext (by
      change (2 : ℝ) • P.product x.val (r • y.val) = r • ((2 : ℝ) • P.product x.val y.val)
      rw [map_smul, smul_comm (2 : ℝ) r]))

omit [FiniteDimensional ℝ E] in
private theorem sharedEdgeProduct_apply
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : W i j) (y : W j k) :
    (P.sharedEdgeProduct c hc hunit hij hik hjk x y).val = (2 : ℝ) • P.product x.val y.val := rfl

private theorem traceSquare_double_product
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : W i j) (y : W j k) :
    let z := (2 : ℝ) • P.product x.val y.val
    τ (P.product z z) / 2 = (τ (P.product x.val x.val) / 2) * (τ (P.product y.val y.val) / 2) := by
  change τ (P.product ((2 : ℝ) • P.product x.val y.val) ((2 : ℝ) • P.product x.val y.val)) / 2 = _
  rw [P.product.map_smul, LinearMap.smul_apply, (P.product (P.product x.val y.val)).map_smul,
    smul_smul, map_smul, smul_eq_mul,
    P.frameOffDiagonal_shared_trace_square hfr c hc hor hunit hij hik hjk x.property y.property]
  ring

private theorem exists_peirceTriangleCoordinates_of_charts
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : W i j) (b : W j k) (hb : τ (P.product b.val b.val) = 2)
    (left : W i j ≃ₗ[ℝ] W i k) (right : W j k ≃ₗ[ℝ] W i k)
    (hleft : ∀ x, (left x).val = (2 : ℝ) • P.product x.val b.val)
    (hright : ∀ y, (right y).val = (2 : ℝ) • P.product a.val y.val)
    (hleftForm : ∀ x, τ (P.product (left x).val (left x).val) = τ (P.product x.val x.val))
    (hrightForm : ∀ y, τ (P.product (right y).val (right y).val) = τ (P.product y.val y.val)) :
    Nonempty (P.PeirceTriangleCoordinates hfr c i j k) := by
  let m := P.sharedEdgeProduct c (fun r => (hc r).1) hunit hij hik hjk
  have hm (x : W i j) (y : W j k) : (m x y).val = (2 : ℝ) • P.product x.val y.val :=
    P.sharedEdgeProduct_apply c (fun r => (hc r).1) hunit hij hik hjk x y
  let μ := m.compl₁₂ left.symm.toLinearMap right.symm.toLinearMap
  let e := right b
  have he : left a = e := Subtype.ext ((hleft a).trans (hright b).symm)
  refine ⟨{
    leftChart := left
    rightChart := right
    product := μ
    unit := e
    product_on_edges := ?_
    unit_left := ?_
    unit_right := ?_
    form_symmetric := ?_
    form_positive := ?_
    unit_form := ?_
    form_composition := ?_ }⟩
  · intro x y
    change (m (left.symm (left x)) (right.symm (right y))).val = _
    rw [left.symm_apply_apply, right.symm_apply_apply, hm]
  · intro x
    change m (left.symm e) (right.symm x) = x
    rw [← he, left.symm_apply_apply]
    exact Subtype.ext ((hm a (right.symm x)).trans ((hright (right.symm x)).symm.trans
      (congrArg Subtype.val (right.apply_symm_apply x))))
  · intro x
    change m (left.symm x) (right.symm (right b)) = x
    rw [right.symm_apply_apply]
    exact Subtype.ext ((hm (left.symm x) b).trans ((hleft (left.symm x)).symm.trans
      (congrArg Subtype.val (left.apply_symm_apply x))))
  · intro x y
    rw [P.frameOffDiagonalTraceForm_apply, P.frameOffDiagonalTraceForm_apply, P.commutative x.val y.val]
  · intro x hx
    rw [P.frameOffDiagonalTraceForm_apply]
    exact div_pos (P.canonicalTraceOfFormallyReal_square_positive hfr x.val (fun h => hx (Subtype.ext h)))
      (by norm_num)
  · rw [P.frameOffDiagonalTraceForm_apply]
    change τ (P.product (right b).val (right b).val) / 2 = 1
    rw [hrightForm, hb]
    norm_num
  · intro x y
    let u := left.symm x
    let v := right.symm y
    have hu : τ (P.product u.val u.val) = τ (P.product x.val x.val) := by
      rw [← hleftForm u]
      change τ (P.product (left (left.symm x)).val (left (left.symm x)).val) = _
      rw [left.apply_symm_apply]
    have hv : τ (P.product v.val v.val) = τ (P.product y.val y.val) := by
      rw [← hrightForm v]
      change τ (P.product (right (right.symm y)).val (right (right.symm y)).val) = _
      rw [right.apply_symm_apply]
    simp only [P.frameOffDiagonalTraceForm_apply]
    change τ (P.product (m u v).val (m u v).val) / 2 = _
    rw [hm, P.traceSquare_double_product hfr c hc hor hunit hij hik hjk u v, hu, hv]

private theorem exists_leftEdgeChart
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (b : W j k) (hb : τ (P.product b.val b.val) = 2) :
    ∃ left : W i j ≃ₗ[ℝ] W i k,
      (∀ x, (left x).val = (2 : ℝ) • P.product x.val b.val) ∧
      (∀ x, τ (P.product (left x).val (left x).val) = τ (P.product x.val x.val)) := by
  have hbRev : b.val ∈ W k j := by
    change b.val ∈ P.frameJointSpace c (frameOffDiagonalPattern k j)
    rw [frameOffDiagonalPattern_comm k j]
    exact b.property
  have hxRev (x : W i j) : x.val ∈ W j i := by
    change x.val ∈ P.frameJointSpace c (frameOffDiagonalPattern j i)
    rw [frameOffDiagonalPattern_comm j i]
    exact x.property
  have hzRev (z : W i k) : z.val ∈ W k i := by
    change z.val ∈ P.frameJointSpace c (frameOffDiagonalPattern k i)
    rw [frameOffDiagonalPattern_comm k i]
    exact z.property
  let f (x : W i j) : W i k := ⟨(2 : ℝ) • P.product x.val b.val, Submodule.smul_mem _ _
    (P.frameOffDiagonal_product_mem_of_shared c (fun r => (hc r).1) hunit hij hik hjk x.property b.property)⟩
  let g (z : W i k) : W i j := ⟨(2 : ℝ) • P.product b.val z.val, Submodule.smul_mem _ _ (by
    change P.product b.val z.val ∈ P.frameJointSpace c (frameOffDiagonalPattern i j)
    rw [frameOffDiagonalPattern_comm i j]
    exact P.frameOffDiagonal_product_mem_of_shared c (fun r => (hc r).1) hunit hjk hij.symm hik.symm
      b.property (hzRev z))⟩
  have hleft (x : W i j) : g (f x) = x := by
    apply Subtype.ext
    change (2 : ℝ) • P.product b.val ((2 : ℝ) • P.product x.val b.val) = x.val
    rw [P.commutative x.val b.val, map_smul, smul_smul,
      P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hjk.symm hik.symm hij.symm hbRev (hxRev x),
      hb, smul_smul]
    norm_num
  have hright (z : W i k) : f (g z) = z := by
    apply Subtype.ext
    change (2 : ℝ) • P.product ((2 : ℝ) • P.product b.val z.val) b.val = z.val
    rw [P.commutative _ b.val, map_smul, smul_smul,
      P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hjk hij.symm hik.symm b.property (hzRev z),
      hb, smul_smul]
    norm_num
  let left : W i j ≃ₗ[ℝ] W i k := {
    toFun := f
    invFun := g
    left_inv := hleft
    right_inv := hright
    map_add' := fun x y => Subtype.ext (by
      change (2 : ℝ) • P.product (x.val + y.val) b.val =
        (2 : ℝ) • P.product x.val b.val + (2 : ℝ) • P.product y.val b.val
      rw [P.product.map_add, LinearMap.add_apply, smul_add])
    map_smul' := fun r x => Subtype.ext (by
      change (2 : ℝ) • P.product (r • x.val) b.val = r • ((2 : ℝ) • P.product x.val b.val)
      rw [P.product.map_smul, LinearMap.smul_apply, smul_comm (2 : ℝ) r]) }
  refine ⟨left, fun _ => rfl, ?_⟩
  intro x
  change τ (P.product ((2 : ℝ) • P.product x.val b.val) ((2 : ℝ) • P.product x.val b.val)) = _
  have h := P.traceSquare_double_product hfr c hc hor hunit hij hik hjk x b
  rw [hb] at h
  linarith only [h]

theorem exists_peirceTriangleCoordinates_of_traceUnits
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : W i j) (b : W j k) (ha : τ (P.product a.val a.val) = 2) (hb : τ (P.product b.val b.val) = 2) :
    Nonempty (P.PeirceTriangleCoordinates hfr c i j k) := by
  obtain ⟨left, hleft, hleftForm⟩ := P.exists_leftEdgeChart hfr c hc hor hunit hij hik hjk b hb
  let right := P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit hij hik hjk a ha
  exact P.exists_peirceTriangleCoordinates_of_charts hfr c hc hor hunit hij hik hjk a b hb left right
    hleft
    (P.frameOffDiagonalLinearEquiv_of_traceUnit_apply hfr c hc hor hunit hij hik hjk a ha)
    (hleftForm)
    (P.frameOffDiagonalLinearEquiv_of_traceUnit_preserves_trace_square hfr c hc hor hunit hij hik hjk a ha)

end Triangle

section SimpleTriangle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (Q : UnitalJordanProduct F)

theorem exists_peirceTriangleCoordinates_of_simple {n : ℕ} (c : Fin n → F)
    (hc : ∀ r, Q.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → Q.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = Q.unit)
    (hinner : ∀ x y z, inner ℝ (Q.product x y) z = inner ℝ x (Q.product y z))
    (hsimple : Q.IsSimpleJordan) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nonempty (Q.PeirceTriangleCoordinates (Q.formallyReal_of_associative_inner hinner) c i j k) := by
  let hfr := Q.formallyReal_of_associative_inner hinner
  obtain ⟨a, ha⟩ := Q.exists_frameOffDiagonal_traceUnit hfr c
    (Q.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j hij)
  obtain ⟨b, hb⟩ := Q.exists_frameOffDiagonal_traceUnit hfr c
    (Q.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple j k hjk)
  exact Q.exists_peirceTriangleCoordinates_of_traceUnits hfr c hc hor hunit hij hik hjk a b ha hb

end SimpleTriangle

end AlbertSequential.UnitalJordanProduct
