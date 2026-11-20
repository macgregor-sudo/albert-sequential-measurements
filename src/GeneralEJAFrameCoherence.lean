/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameComposition

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)
  {n : ℕ} (c : Fin n → E)

local notation "W" => P.frameOffDiagonalSpace c

private theorem edge_product_frame_of_mem {i j r : Fin n} {x : E}
    (hx : x ∈ W i j) (hr : r = i ∨ r = j) :
    P.product x (c r) = (1 / 2 : ℝ) • x := by
  rw [P.commutative x (c r)]
  simpa only [frameOffDiagonalPattern, ite_eq_left hr] using (P.mem_frameJointSpace c _).mp hx r

private theorem edge_product_frame_of_notMem {i j r : Fin n} {x : E}
    (hx : x ∈ W i j) (hr : ¬ (r = i ∨ r = j)) :
    P.product x (c r) = 0 := by
  rw [P.commutative x (c r)]
  simpa only [frameOffDiagonalPattern, ite_eq_right hr, zero_smul] using
    (P.mem_frameJointSpace c _).mp hx r

section Chain

variable (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
  {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)

include hc hunit hij hik hil hjk hjl hkl in
/-- Consecutive off-diagonal Peirce blocks on four distinct frame indices
have associative products along the chain. -/
theorem frameOffDiagonal_product_associative_of_chain {x y z : E}
    (hx : x ∈ W i j) (hy : y ∈ W j k) (hz : z ∈ W k l) :
    P.product (P.product x y) z = P.product x (P.product y z) := by
  have hxy := P.frameOffDiagonal_product_mem_of_shared c hc hunit hij hik hjk hx hy
  have hyz := P.frameOffDiagonal_product_mem_of_shared c hc hunit hjk hjl hkl hy hz
  have hzx0 : P.product z x = 0 := by
    rw [P.commutative z x]
    apply P.frameOffDiagonal_product_eq_zero_of_disjoint c hc hunit hij hkl _ hx hz
    rintro r ⟨hr, hs⟩
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact hik (hr.symm.trans hs)
    · exact hil (hr.symm.trans hs)
    · exact hjk (hr.symm.trans hs)
    · exact hjl (hr.symm.trans hs)
  have hx0 := P.edge_product_frame_of_notMem c (r := l) hx (not_or_intro hil.symm hjl.symm)
  have hy0 := P.edge_product_frame_of_notMem c (r := l) hy (not_or_intro hjl.symm hkl.symm)
  have hzHalf := P.edge_product_frame_of_mem c (r := l) hz (Or.inr rfl)
  have hxy0 := P.edge_product_frame_of_notMem c (r := l) hxy (not_or_intro hil.symm hkl.symm)
  have hyzHalf := P.edge_product_frame_of_mem c (r := l) hyz (Or.inr rfl)
  have h := P.cyclic_identity x y z (c l)
  simp only [hx0, hy0, hzHalf, hxy0, hyzHalf, hzx0, map_zero, LinearMap.zero_apply, map_smul,
    sub_zero, zero_sub, add_zero] at h
  linear_combination (norm := module) (-2 : ℝ) • h

include hc hunit hij hik hil hjk hjl hkl in
theorem frameOffDiagonal_scaled_product_associative_of_chain {x y z : E}
    (hx : x ∈ W i j) (hy : y ∈ W j k) (hz : z ∈ W k l) :
    (2 : ℝ) • P.product ((2 : ℝ) • P.product x y) z =
      (2 : ℝ) • P.product x ((2 : ℝ) • P.product y z) := by
  rw [P.product.map_smul, LinearMap.smul_apply, (P.product x).map_smul,
    P.frameOffDiagonal_product_associative_of_chain c hc hunit hij hik hil hjk hjl hkl hx hy hz]

end Chain

theorem frameOffDiagonal_scaled_product_mem_of_shared
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y : E} (hx : x ∈ W i j) (hy : y ∈ W j k) :
    (2 : ℝ) • P.product x y ∈ W i k :=
  Submodule.smul_mem _ _ (P.frameOffDiagonal_product_mem_of_shared c hc hunit hij hik hjk hx hy)

variable [FiniteDimensional ℝ E]

theorem frameOffDiagonal_scaled_left_injective
    (hfr : P.FormallyReal) (hc : ∀ r, P.IsPrimitive (c r))
    (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0) (hunit : ∑ r, c r = P.unit)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : E} (hx : x ∈ W i j) (hx0 : x ≠ 0) :
    Set.InjOn (fun y : E => (2 : ℝ) • P.product x y) (W j k : Set E) := by
  intro y hy z hz he
  have hs := congrArg (P.product x) ((smul_right_injective (M := E) (by norm_num : (2 : ℝ) ≠ 0)) he)
  rw [P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hij hik hjk hx hy,
    P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hij hik hjk hx hz] at hs
  have hpos := P.canonicalTraceOfFormallyReal_square_positive hfr x hx0
  exact smul_right_injective (M := E) (ne_of_gt (div_pos hpos (by norm_num : (0 : ℝ) < 8))) hs

end AlbertSequential.UnitalJordanProduct
