/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameProducts

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

theorem frameOffDiagonalPattern_comm {n : ℕ} (i j : Fin n) :
    frameOffDiagonalPattern i j = frameOffDiagonalPattern j i := by
  funext k
  simp only [frameOffDiagonalPattern, or_comm]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

private theorem trace_square_smul (a : ℝ) (x : E) :
    τ (P.product (a • x) (a • x)) = a ^ 2 * τ (P.product x x) := by
  rw [P.product.map_smul, LinearMap.smul_apply, (P.product x).map_smul, smul_smul, map_smul,
    smul_eq_mul, pow_two]

theorem exists_frameOffDiagonal_traceUnit {n : ℕ} (c : Fin n → E) {i j : Fin n}
    (h : P.frameJointSpace c (frameOffDiagonalPattern i j) ≠ ⊥) :
    ∃ x : P.frameJointSpace c (frameOffDiagonalPattern i j), τ (P.product x.val x.val) = 2 := by
  obtain ⟨x, hx, hx0⟩ := (P.frameJointSpace c (frameOffDiagonalPattern i j)).ne_bot_iff.mp h
  have hpos := P.canonicalTraceOfFormallyReal_square_positive hfr x hx0
  let a := Real.sqrt (2 / τ (P.product x x))
  refine ⟨⟨a • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  change τ (P.product (a • x) (a • x)) = 2
  rw [P.trace_square_smul hfr, Real.sq_sqrt (div_nonneg (by norm_num) hpos.le)]
  field_simp [hpos.ne']

variable {n : ℕ} (c : Fin n → E) (hc : ∀ r, P.IsPrimitive (c r))
  (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0) (hunit : ∑ r, c r = P.unit)
  {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

include hc hor hunit hij hik hjk in
theorem frameOffDiagonal_shared_trace_square {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern j k)) :
    τ (P.product (P.product x y) (P.product x y)) =
      τ (P.product x x) * τ (P.product y y) / 8 := by
  have h := P.canonicalTraceOfFormallyReal_associative hfr y x (P.product x y)
  rw [P.commutative y x, P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hij hik hjk hx hy,
    map_smul, map_smul, smul_eq_mul] at h
  linarith only [h]

/-- The actual edge transports defined by a canonical unit vector have the same formula
in both directions. -/
def frameOffDiagonalLinearEquiv_of_traceUnit
    (x : P.frameJointSpace c (frameOffDiagonalPattern i j)) (hxnorm : τ (P.product x.val x.val) = 2) :
    P.frameJointSpace c (frameOffDiagonalPattern j k) ≃ₗ[ℝ]
      P.frameJointSpace c (frameOffDiagonalPattern i k) := by
  let W := P.frameJointSpace c (frameOffDiagonalPattern j k)
  let V := P.frameJointSpace c (frameOffDiagonalPattern i k)
  have hx' : x.val ∈ P.frameJointSpace c (frameOffDiagonalPattern j i) := by
    rw [frameOffDiagonalPattern_comm j i]
    exact x.property
  let f (y : W) : V := ⟨(2 : ℝ) • P.product x.val y.val, Submodule.smul_mem _ _
    (P.frameOffDiagonal_product_mem_of_shared c (fun r => (hc r).1) hunit hij hik hjk x.property y.property)⟩
  let g (z : V) : W := ⟨(2 : ℝ) • P.product x.val z.val, Submodule.smul_mem _ _
    (P.frameOffDiagonal_product_mem_of_shared c (fun r => (hc r).1) hunit hij.symm hjk hik hx' z.property)⟩
  refine { toFun := f, invFun := g, map_add' := ?_, map_smul' := ?_, left_inv := ?_, right_inv := ?_ }
  · intro y z
    apply Subtype.ext
    change (2 : ℝ) • P.product x.val (y.val + z.val) =
      (2 : ℝ) • P.product x.val y.val + (2 : ℝ) • P.product x.val z.val
    rw [map_add, smul_add]
  · intro a y
    apply Subtype.ext
    change (2 : ℝ) • P.product x.val (a • y.val) = a • ((2 : ℝ) • P.product x.val y.val)
    rw [map_smul, smul_comm (2 : ℝ) a]
  · intro y
    apply Subtype.ext
    change (2 : ℝ) • P.product x.val ((2 : ℝ) • P.product x.val y.val) = y.val
    rw [map_smul, smul_smul, P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit
      hij hik hjk x.property y.property, hxnorm, smul_smul]
    norm_num
  · intro z
    apply Subtype.ext
    change (2 : ℝ) • P.product x.val ((2 : ℝ) • P.product x.val z.val) = z.val
    rw [map_smul, smul_smul, P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit
      hij.symm hjk hik hx' z.property, hxnorm, smul_smul]
    norm_num

theorem frameOffDiagonalLinearEquiv_of_traceUnit_apply
    (x : P.frameJointSpace c (frameOffDiagonalPattern i j)) (hxnorm : τ (P.product x.val x.val) = 2)
    (y : P.frameJointSpace c (frameOffDiagonalPattern j k)) :
    (P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit hij hik hjk x hxnorm y).val =
      (2 : ℝ) • P.product x.val y.val := rfl

theorem frameOffDiagonalLinearEquiv_of_traceUnit_preserves_trace_square
    (x : P.frameJointSpace c (frameOffDiagonalPattern i j)) (hxnorm : τ (P.product x.val x.val) = 2)
    (y : P.frameJointSpace c (frameOffDiagonalPattern j k)) :
    let z := (P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit hij hik hjk x hxnorm y).val
    τ (P.product z z) = τ (P.product y.val y.val) := by
  change τ (P.product ((2 : ℝ) • P.product x.val y.val) ((2 : ℝ) • P.product x.val y.val)) = _
  rw [P.trace_square_smul hfr, P.frameOffDiagonal_shared_trace_square hfr c hc hor hunit
    hij hik hjk x.property y.property, hxnorm]
  ring

end AlbertSequential.UnitalJordanProduct
