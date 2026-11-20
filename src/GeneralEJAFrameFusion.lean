/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFramePeirce

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

theorem peirceZero_commute (q x y : E) (hq : P.product q q = q)
    (hx : P.product q x = 0) : P.product q (P.product x y) = P.product x (P.product q y) := by
  have hqc : P.product (P.unit - q) (P.unit - q) = P.unit - q := by
    simp only [map_sub, LinearMap.sub_apply, P.unit_left, P.commutative q P.unit, hq, sub_self, sub_zero]
  have hxc : P.product (P.unit - q) x = x := by
    simp only [map_sub, LinearMap.sub_apply, P.unit_left, hx, sub_zero]
  have h := P.peirceOne_commute (P.unit - q) x y hqc hxc
  simp only [map_sub, LinearMap.sub_apply, P.unit_left] at h
  exact sub_right_inj.mp h

private theorem sum_offDiagonalPattern {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ r, frameOffDiagonalPattern i j r = 1 := by
  have hpattern (r : Fin n) : frameOffDiagonalPattern i j r =
      (if r = i then (1 / 2 : ℝ) else 0) + (if r = j then (1 / 2 : ℝ) else 0) := by
    by_cases hi : r = i
    · subst r
      simp [frameOffDiagonalPattern, hij]
    · simp [frameOffDiagonalPattern, hi]
  simp only [hpattern, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num

private theorem product_eigenvalue_of_separated_index {n : ℕ} (c : Fin n → E)
    {i j k l r : Fin n} (hcr : P.product (c r) (c r) = c r) {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern k l))
    (hsep : ¬ ((r = i ∨ r = j) ∧ (r = k ∨ r = l))) :
    P.product (c r) (P.product x y) =
      (frameOffDiagonalPattern i j r + frameOffDiagonalPattern k l r) • P.product x y := by
  have hxr := (P.mem_frameJointSpace c _).mp hx r
  have hyr := (P.mem_frameJointSpace c _).mp hy r
  by_cases hi : r = i ∨ r = j
  · have hk : ¬ (r = k ∨ r = l) := fun hk => hsep ⟨hi, hk⟩
    have hb : frameOffDiagonalPattern k l r = 0 := ite_eq_right hk
    have hy0 : P.product (c r) y = 0 := by rw [hyr, hb, zero_smul]
    rw [P.commutative x y, P.peirceZero_commute (c r) y x hcr hy0, hxr, map_smul, hb, add_zero]
  · have ha : frameOffDiagonalPattern i j r = 0 := ite_eq_right hi
    have hx0 : P.product (c r) x = 0 := by rw [hxr, ha, zero_smul]
    rw [P.peirceZero_commute (c r) x y hcr hx0, hyr, map_smul, ha, zero_add]

/-- Off-diagonal Peirce spaces with disjoint pairs of indices multiply to zero. -/
theorem frameOffDiagonal_product_eq_zero_of_disjoint {n : ℕ} (c : Fin n → E)
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hsep : ∀ r, ¬ ((r = i ∨ r = j) ∧ (r = k ∨ r = l))) {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern k l)) : P.product x y = 0 := by
  by_contra hz
  have hspace : P.product x y ∈ P.frameJointSpace c
      (fun r => frameOffDiagonalPattern i j r + frameOffDiagonalPattern k l r) :=
    (P.mem_frameJointSpace c _).mpr fun r =>
      P.product_eigenvalue_of_separated_index c (hc r) hx hy (hsep r)
  have hsum := P.sum_frameEigenvalues c hunit _ hz hspace
  rw [Finset.sum_add_distrib, sum_offDiagonalPattern i j hij, sum_offDiagonalPattern k l hkl] at hsum
  norm_num at hsum

/-- Two off-diagonal Peirce spaces sharing one index multiply into the block
on their two other indices. -/
theorem frameOffDiagonal_product_mem_of_shared {n : ℕ} (c : Fin n → E)
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x y : E}
    (hx : x ∈ P.frameJointSpace c (frameOffDiagonalPattern i j))
    (hy : y ∈ P.frameJointSpace c (frameOffDiagonalPattern j k)) :
    P.product x y ∈ P.frameJointSpace c (frameOffDiagonalPattern i k) := by
  let z := P.product x y
  let a := frameOffDiagonalPattern i k
  have hother (r : Fin n) (hr : r ≠ j) : P.product (c r) z = a r • z := by
    have hsep : ¬ ((r = i ∨ r = j) ∧ (r = j ∨ r = k)) := by
      simp only [hr, or_false, false_or]
      exact fun h => hik (h.1.symm.trans h.2)
    have ha : frameOffDiagonalPattern i j r + frameOffDiagonalPattern j k r = a r := by
      by_cases hi : r = i
      · subst r
        simp [a, frameOffDiagonalPattern, hij, hik]
      · by_cases hk : r = k
        · subst r
          simp [a, frameOffDiagonalPattern, hi, hjk.symm]
        · simp [a, frameOffDiagonalPattern, hi, hr, hk]
    have h := P.product_eigenvalue_of_separated_index c (hc r) hx hy hsep
    rw [ha] at h
    exact h
  have hsum : ∑ r, (P.product (c r) z - a r • z) = 0 := by
    rw [Finset.sum_sub_distrib, ← LinearMap.sum_apply, ← map_sum, ← Finset.sum_smul,
      hunit, P.unit_left, sum_offDiagonalPattern i k hik, one_smul, sub_self]
  have hj : ∑ r, (P.product (c r) z - a r • z) = P.product (c j) z - a j • z :=
    Finset.sum_eq_single j (fun r _ hr => sub_eq_zero.mpr (hother r hr))
      (fun h => (h (Finset.mem_univ j)).elim)
  apply (P.mem_frameJointSpace c _).mpr
  intro r
  by_cases hr : r = j
  · subst r
    exact sub_eq_zero.mp (hj.symm.trans hsum)
  · exact hother r hr

end AlbertSequential.UnitalJordanProduct
