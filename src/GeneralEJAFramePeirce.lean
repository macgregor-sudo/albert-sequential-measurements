/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EuclideanPrimitiveCorner
public import JordanPeircePositiveMultiplication
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! The simultaneous eigenspaces of a Jordan frame give its Peirce
components. The cubic and the unit sum constrain their eigenvalues. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open Module.End
open scoped BigOperators InnerProductSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- Multiplication by orthogonal idempotents commutes. -/
theorem frameMultipliers_commute (q r : E) (hq : P.product q q = q)
    (hor : P.product q r = 0) : Commute (P.product q) (P.product r) := by
  have hqc : P.product (P.unit - q) (P.unit - q) = P.unit - q := by
    simp only [map_sub, LinearMap.sub_apply, P.unit_left, P.commutative q P.unit, hq, sub_self, sub_zero]
  have hpr : P.product (P.unit - q) r = r := by
    simp only [map_sub, LinearMap.sub_apply, P.unit_left, hor, sub_zero]
  ext z
  change P.product q (P.product r z) = P.product r (P.product q z)
  have h := P.peirceOne_commute (P.unit - q) r z hqc hpr
  simp only [map_sub, LinearMap.sub_apply, P.unit_left] at h
  exact (sub_right_inj.mp h)

/-- The eigenvalues of multiplication by an idempotent are the three Peirce values. -/
theorem peirce_eigenvalue (q x : E) (hq : P.product q q = q) (hx : x ≠ 0) (a : ℝ)
    (ha : P.product q x = a • x) : a = 0 ∨ a = 1 / 2 ∨ a = 1 := by
  have h₂ : P.product q (P.product q x) = (a * a) • x := by
    rw [ha, map_smul, ha, smul_smul]
  have h₃ : P.product q (P.product q (P.product q x)) = (a * (a * a)) • x := by
    rw [h₂, map_smul, ha, smul_smul, mul_assoc]
  have h := P.idempotent_leftMultiplication_cubic q x hq
  rw [h₃, h₂, ha, smul_smul, smul_smul, ← sub_smul, ← add_smul] at h
  have hp := (smul_eq_zero.mp h).resolve_right hx
  have hfact : a * (a - 1) * (2 * a - 1) = 0 := by nlinarith only [hp]
  rcases mul_eq_zero.mp hfact with h01 | hhalf
  · rcases mul_eq_zero.mp h01 with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inr (sub_eq_zero.mp hone))
  · exact Or.inr (Or.inl (by linarith))

/-- Joint eigenspace for the left multiplications of the indicated family. -/
def frameJointSpace {n : ℕ} (c : Fin n → E) (a : Fin n → ℝ) : Submodule ℝ E :=
  ⨅ i, eigenspace (P.product (c i)) (a i)

theorem mem_frameJointSpace {n : ℕ} (c : Fin n → E) (a : Fin n → ℝ) {x : E} :
    x ∈ P.frameJointSpace c a ↔ ∀ i, P.product (c i) x = (a i) • x := by
  simp only [frameJointSpace, Submodule.mem_iInf, mem_eigenspace_iff]

/-- On a nonzero joint eigenspace the Peirce eigenvalues sum to one. -/
theorem sum_frameEigenvalues {n : ℕ} (c : Fin n → E) (hunit : (∑ i, c i) = P.unit)
    (a : Fin n → ℝ) {x : E} (hx : x ≠ 0) (hspace : x ∈ P.frameJointSpace c a) :
    (∑ i, a i) = 1 := by
  have h := (P.mem_frameJointSpace c a).mp hspace
  apply (smul_left_injective ℝ hx)
  calc
    (∑ i, a i) • x = ∑ i, (a i) • x := Finset.sum_smul
    _ = ∑ i, P.product (c i) x := Finset.sum_congr rfl (fun i _ => (h i).symm)
    _ = P.product (∑ i, c i) x := by rw [map_sum, LinearMap.sum_apply]
    _ = (1 : ℝ) • x := by rw [hunit, P.unit_left, one_smul]

def frameDiagonalPattern {n : ℕ} (i : Fin n) (j : Fin n) : ℝ := if j = i then 1 else 0

def frameOffDiagonalPattern {n : ℕ} (i j : Fin n) (k : Fin n) : ℝ :=
  if k = i ∨ k = j then 1 / 2 else 0

/-- A nonzero joint component lies on a diagonal or a pair of half-eigenvalues. -/
theorem frameJointSpace_pattern {n : ℕ} (c : Fin n → E) (hc : ∀ i, P.product (c i) (c i) = c i)
    (hunit : (∑ i, c i) = P.unit) (a : Fin n → ℝ) {x : E}
    (hx : x ≠ 0) (hspace : x ∈ P.frameJointSpace c a) :
    (∃ i, a = frameDiagonalPattern i) ∨
    ∃ i j, i ≠ j ∧ a = frameOffDiagonalPattern i j := by
  classical
  have hroots (i : Fin n) : a i = 0 ∨ a i = 1 / 2 ∨ a i = 1 :=
    P.peirce_eigenvalue (c i) x (hc i) hx (a i) ((P.mem_frameJointSpace c a).mp hspace i)
  let w (i : Fin n) : ℕ := if a i = 0 then 0 else if a i = 1 / 2 then 1 else 2
  have hw (i : Fin n) : (w i : ℝ) = 2 * a i := by
    rcases hroots i with h | h | h <;> norm_num [w, h]
  have hsumReal : ∑ i, (w i : ℝ) = 2 := by
    simp_rw [hw, ← Finset.mul_sum, P.sum_frameEigenvalues c hunit a hx hspace, mul_one]
  have hsum : ∑ i, w i = 2 := by exact_mod_cast hsumReal
  by_cases hbig : ∃ i, w i = 2
  · obtain ⟨i, hi⟩ := hbig
    left
    refine ⟨i, funext fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      have h := hw i
      rw [hi] at h
      norm_num at h
      simp [frameDiagonalPattern]
      linarith only [h]
    · have hsumOther := Finset.sum_erase_add (s := Finset.univ) (f := w) (Finset.mem_univ i)
      rw [hi, hsum] at hsumOther
      have hbound : w j ≤ ∑ k ∈ Finset.univ.erase i, w k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le (w k)) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
      have hj : w j = 0 := by omega
      have h := hw j
      rw [hj] at h
      norm_num at h
      simp [frameDiagonalPattern, hji]
      linarith only [h]
  · let active := Finset.univ.filter (fun i => w i ≠ 0)
    have hcard : active.card = 2 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro i _
      rcases hroots i with h | h | h
      · simp [w, h]
      · norm_num [w, h]
      · exact (hbig ⟨i, by norm_num [w, h]⟩).elim
    obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp hcard
    right
    refine ⟨i, j, hij, funext fun k => ?_⟩
    have hmem : w k ≠ 0 ↔ k = i ∨ k = j := by
      calc
        w k ≠ 0 ↔ k ∈ active := by simp [active]
        _ ↔ k = i ∨ k = j := by rw [heq]; simp
    by_cases hk : k = i ∨ k = j
    · have hn0 := hmem.mpr hk
      have hw1 : w k = 1 := by
        rcases hroots k with h | h | h
        · exact (hn0 (by simp [w, h])).elim
        · norm_num [w, h]
        · exact (hbig ⟨k, by norm_num [w, h]⟩).elim
      have h := hw k
      rw [hw1] at h
      norm_num at h
      simp only [frameOffDiagonalPattern, ite_eq_left hk]
      linarith only [h]
    · have hw0 : w k = 0 := by
        by_contra h
        exact hk (hmem.mp h)
      have h := hw k
      rw [hw0] at h
      norm_num at h
      simp only [frameOffDiagonalPattern, ite_eq_right hk]
      linarith only [h]

/-- The product of two half-eigenvectors has zero half-eigenspace component. -/
theorem peirceHalfProjection_product_half_eigenvectors (q x y : E)
    (hq : P.product q q = q) (hx : P.product q x = (1 / 2 : ℝ) • x)
    (hy : P.product q y = (1 / 2 : ℝ) • y) :
    P.peirceHalfProjection q (P.product x y) = 0 := by
  have h := P.cyclic_identity q x y q
  simp only [P.commutative y q, P.commutative x q, P.commutative (P.product x y) q,
    hq, hx, hy, map_smul, LinearMap.smul_apply] at h
  rw [P.commutative y x] at h
  rw [P.peirceHalfProjection_apply]
  linear_combination (norm := module) (-4 : ℝ) • h

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct

open Module.End
open scoped BigOperators InnerProductSpace Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- The Peirce joint eigenspaces of the frame span the entire real Jordan algebra. -/
theorem iSup_frameJointSpace_eq_top {n : ℕ} (c : Fin n → E)
    (hc : ∀ i, P.product (c i) (c i) = c i)
    (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    (⨆ a, P.frameJointSpace c a) = ⊤ := by
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro i x y
    exact P.product_inner hinner (c i) x y
  · intro i j hij
    exact P.frameMultipliers_commute (c i) (c j) (hc i) (hor i j hij)

/-- A joint space with a coefficient 1 for a primitive frame member is
contained in that member's real line. -/
theorem frameJointSpace_le_primitive_line {n : ℕ} (c : Fin n → E) (a : Fin n → ℝ)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (i : Fin n) (hci : P.IsPrimitive (c i)) (hai : a i = 1) :
    P.frameJointSpace c a ≤ Submodule.span ℝ {c i} := by
  rw [← P.primitive_corner_eq_span hinner (c i) hci]
  intro x hx
  exact (P.mem_peirceOne (c i) x).mpr (by
    simpa only [hai, one_smul] using (P.mem_frameJointSpace c a).mp hx i)

/-- The diagonal joint space is exactly the line of a primitive frame member. -/
theorem frameJointSpace_diagonal_eq_line {n : ℕ} (c : Fin n → E)
    (hc : ∀ i, P.IsPrimitive (c i)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) (i : Fin n) :
    P.frameJointSpace c (frameDiagonalPattern i) = Submodule.span ℝ {c i} := by
  apply le_antisymm (P.frameJointSpace_le_primitive_line c _ hinner i (hc i) (by simp [frameDiagonalPattern]))
  refine Submodule.span_le.mpr ?_
  rintro _ rfl
  apply (P.mem_frameJointSpace c _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa [frameDiagonalPattern] using (hc i).1
  · simpa [frameDiagonalPattern, hji] using hor j i hji

/-- The real lines of a primitive frame and the pairwise half-eigenspaces
span the algebra. Only one copy of each unordered pair is needed. -/
theorem framePeirce_spanning {n : ℕ} (c : Fin n → E)
    (hc : ∀ i, P.IsPrimitive (c i)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ i, c i = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    (⨆ i, Submodule.span ℝ {c i}) ⊔
      (⨆ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
        P.frameJointSpace c (frameOffDiagonalPattern ij.val.1 ij.val.2)) = ⊤ := by
  apply top_unique
  rw [← P.iSup_frameJointSpace_eq_top c (fun i => (hc i).1) hor hinner]
  refine iSup_le fun a x hx => ?_
  by_cases hz : x = 0
  · exact hz ▸ Submodule.zero_mem _
  · rcases P.frameJointSpace_pattern c (fun i => (hc i).1) hunit a hz hx with
      ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · rw [P.frameJointSpace_diagonal_eq_line c hc hor hinner] at hx
      apply Submodule.mem_sup.mpr
      exact ⟨x, le_iSup (fun i => Submodule.span ℝ {c i}) i hx, 0, Submodule.zero_mem _, add_zero _⟩
    · rcases lt_or_gt_of_ne hij with hij' | hji'
      · apply Submodule.mem_sup.mpr
        refine ⟨0, Submodule.zero_mem _, x, ?_, zero_add _⟩
        exact le_iSup (fun ij : {ij : Fin n × Fin n // ij.1 < ij.2} =>
          P.frameJointSpace c (frameOffDiagonalPattern ij.val.1 ij.val.2)) ⟨(i, j), hij'⟩ hx
      · have hsymm : frameOffDiagonalPattern i j = frameOffDiagonalPattern j i := by
          funext k
          simp only [frameOffDiagonalPattern, or_comm]
        rw [hsymm] at hx
        apply Submodule.mem_sup.mpr
        refine ⟨0, Submodule.zero_mem _, x, ?_, zero_add _⟩
        exact le_iSup (fun ij : {ij : Fin n × Fin n // ij.1 < ij.2} =>
          P.frameJointSpace c (frameOffDiagonalPattern ij.val.1 ij.val.2)) ⟨(j, i), hji'⟩ hx

end AlbertSequential.UnitalJordanProduct
