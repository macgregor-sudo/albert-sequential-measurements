/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FormalRealityCanonicalTrace
public import GeneralEJAFrameFusion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

/-- The product within one off-diagonal Peirce space is the canonical trace
coefficient on its two primitive diagonal idempotents. -/
theorem frameOffDiagonal_product_eq_trace_diag {n : ℕ} (c : Fin n → E)
    {i j : Fin n} (hci : P.IsPrimitive (c i)) (hcj : P.IsPrimitive (c j))
    (hor : P.product (c i) (c j) = 0) {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern i j)) :
    P.product x y = (τ (P.product x y) / 2) • (c i + c j) := by
  let z := P.product x y
  have hhalf (w : E) (hw : w ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
      (r : Fin n) (hr : r = i ∨ r = j) : P.product (c r) w = (1 / 2 : ℝ) • w := by
    simpa only [frameOffDiagonalPattern, ite_eq_left hr] using (P.mem_frameJointSpace c _).mp hw r
  have hi (w : E) (hw : w ∈ P.frameJointSpace c (frameOffDiagonalPattern i j)) :
      P.product (c i) w = (1 / 2 : ℝ) • w := hhalf w hw i (Or.inl rfl)
  have hj (w : E) (hw : w ∈ P.frameJointSpace c (frameOffDiagonalPattern i j)) :
      P.product (c j) w = (1 / 2 : ℝ) • w := hhalf w hw j (Or.inr rfl)
  have hsum : P.product (c i + c j) (c i + c j) = c i + c j := by
    have hji : P.product (c j) (c i) = 0 := (P.commutative (c j) (c i)).trans hor
    simp only [map_add, LinearMap.add_apply, hci.1, hcj.1, hor, hji, add_zero, zero_add]
  have hcorner (w : E) (hw : w ∈ P.frameJointSpace c (frameOffDiagonalPattern i j)) :
      w ∈ P.peirceOne (c i + c j) := by
    rw [P.mem_peirceOne, map_add, LinearMap.add_apply, hi w hw, hj w hw, ← add_smul]
    norm_num
  have hsumz : P.product (c i + c j) z = z :=
    (P.mem_peirceOne (c i + c j) z).mp
      (P.peirceOne_product_mem (c i + c j) x y hsum (hcorner x hx) (hcorner y hy))
  have hcompress (p : E) (hp : P.IsPrimitive p)
      (hx' : P.product p x = (1 / 2 : ℝ) • x) (hy' : P.product p y = (1 / 2 : ℝ) • y) :
      P.product p z = (τ z / 2) • p := by
    have hhalfz : P.peirceHalfProjection p z = 0 :=
      P.peirceHalfProjection_product_half_eigenvectors p x y hp.1 hx' hy'
    have hτ : τ (P.product p z) = τ z / 2 := by
      change τ (P.product p (P.product x y)) = τ z / 2
      rw [← P.canonicalTraceOfFormallyReal_associative hfr p x y, hx', map_smul,
        LinearMap.smul_apply, map_smul, smul_eq_mul]
      ring
    rw [P.leftMultiplication_projection_decomposition p z hp.1, hhalfz, smul_zero, add_zero,
      P.canonicalTraceOfFormallyReal_primitive_compression hfr p z hp, hτ]
  rw [map_add, LinearMap.add_apply, hcompress (c i) hci (hi x hx) (hi y hy),
    hcompress (c j) hcj (hj x hx) (hj y hy), ← smul_add] at hsumz
  exact hsumz.symm

/-- Multiplication across two shared edges is reciprocal up to the indicated
strictly positive scalar when the multiplying vector is nonzero. -/
theorem frameOffDiagonal_product_twice_of_shared {n : ℕ} (c : Fin n → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern j k)) :
    P.product x (P.product x y) = (τ (P.product x x) / 8) • y := by
  have hz := P.frameOffDiagonal_product_mem_of_shared c (fun r => (hc r).1) hunit hij hik hjk hx hy
  have hzK : P.product (P.product x y) (c k) = (1 / 2 : ℝ) • P.product x y := by
    rw [P.commutative (P.product x y) (c k)]
    simpa only [frameOffDiagonalPattern, or_true, ite_true] using (P.mem_frameJointSpace c _).mp hz k
  have hxK : P.product x (c k) = 0 := by
    rw [P.commutative x (c k)]
    simpa only [frameOffDiagonalPattern, hik.symm, hjk.symm, or_false, ite_false, zero_smul] using
      (P.mem_frameJointSpace c _).mp hx k
  have hyK : P.product y (c k) = (1 / 2 : ℝ) • y := by
    rw [P.commutative y (c k)]
    simpa only [frameOffDiagonalPattern, or_true, ite_true] using (P.mem_frameJointSpace c _).mp hy k
  have hyI : P.product (c i) y = 0 := by
    simpa only [frameOffDiagonalPattern, hij, hik, or_false, ite_false, zero_smul] using
      (P.mem_frameJointSpace c _).mp hy i
  have hyJ : P.product (c j) y = (1 / 2 : ℝ) • y := by
    simpa only [frameOffDiagonalPattern, true_or, ite_true] using (P.mem_frameJointSpace c _).mp hy j
  have hx2 := P.frameOffDiagonal_product_eq_trace_diag hfr c (hc i) (hc j) (hor i j hij) hx hx
  have hx2K : P.product (P.product x x) (c k) = 0 := by
    rw [hx2, P.commutative _ (c k), map_smul, map_add, hor k i hik.symm, hor k j hjk.symm,
      add_zero, smul_zero]
  have hx2y : P.product (P.product x x) y = (τ (P.product x x) / 4) • y := by
    conv_lhs => rw [hx2]
    rw [map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply, hyI, hyJ, zero_add, smul_smul]
    congr 1
    ring
  have h := P.cyclic_identity x x y (c k)
  simp only [P.commutative y x, hzK, hxK, hx2K, hyK, map_zero, map_smul, hx2y, smul_smul,
    sub_zero, zero_sub] at h
  linear_combination (norm := module) h

end AlbertSequential.UnitalJordanProduct
