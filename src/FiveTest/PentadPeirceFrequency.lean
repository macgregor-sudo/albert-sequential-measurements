/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.FiveTestClifford
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

namespace AlbertSequential.FiveTest

open MatchingModels
open Polynomial

noncomputable section

/-- The remaining occurrence cost at each column of the sparse Peirce table. -/
def occurrenceGrade (a : Fin 5) (k : Fin 27) : ℕ :=
  match a.val with
  | 0 => if [0,1,2,4,5,6,7,9,10,11,15,16,17,21,26].contains k.val then 0 else 1
  | 1 => if [0,1,2,3,5,6,7,8,10,11,13,14,17,20,25].contains k.val then 0 else 1
  | 2 => if k.val ≤ 6 then 0 else if k.val ≤ 22 then 1 else 2
  | 3 => if [0,1,2,3,4,6,7,8,9,11,12,14,16,19,24].contains k.val then 0 else 1
  | _ => if [0,1,2,3,4,5,7,8,9,10,12,13,15,18,23].contains k.val then 0 else 1

def occurrenceCost (a : Fin 5) : ℕ := if a = 2 then 2 else 1
def occurrenceStep (a r : Fin 5) : ℕ := if r = a then 1 else 0

private theorem grade_start :
    ∀ a : Fin 5, ∀ k : Fin 27, k.val = 0 ∨ k.val = 1 → occurrenceGrade a k = 0 := by
  decide +kernel

private theorem grade_m0 :
    ∀ a r : Fin 5, ∀ k : Fin 27, ∀ p ∈ m0RowZ12 r k,
      occurrenceGrade a p.1 ≤ occurrenceGrade a k + occurrenceStep a r := by
  decide +kernel

private theorem grade_m1 :
    ∀ a r : Fin 5, ∀ k : Fin 27, ∀ p ∈ m1RowZ12 r k,
      occurrenceGrade a p.1 + occurrenceCost a ≤ occurrenceGrade a k + occurrenceStep a r := by
  decide +kernel

private theorem exists_rowIndex_of_coeff_ne_zero (row : List (Fin 27 × ℤ)) (j : Fin 27)
    (h : listCoeffZ row j ≠ 0) : ∃ z, (j,z) ∈ row := by
  induction row with
  | nil => simp [listCoeffZ] at h
  | cons p t ih =>
    by_cases hp : p.1 = j
    · rcases p with ⟨k,z⟩
      change k = j at hp
      subst k
      exact ⟨z, List.mem_cons_self⟩
    · have ht : listCoeffZ t j ≠ 0 := by
        simpa [listCoeffZ, hp] using h
      obtain ⟨z,hz⟩ := ih ht
      exact ⟨z, List.mem_cons_of_mem _ hz⟩

private theorem grade_coeff0 (a r : Fin 5) (k j : Fin 27) (h : m0Coeff r k j ≠ 0) :
    occurrenceGrade a j ≤ occurrenceGrade a k + occurrenceStep a r := by
  have he : listCoeffZ (m0RowZ12 r k) j ≠ 0 := by
    intro hz; apply h; simp [m0Coeff, hz]
  obtain ⟨z,hz⟩ := exists_rowIndex_of_coeff_ne_zero _ _ he
  exact grade_m0 a r k (j,z) hz

private theorem grade_coeff1 (a r : Fin 5) (k j : Fin 27) (h : m1Coeff r k j ≠ 0) :
    occurrenceGrade a j + occurrenceCost a ≤ occurrenceGrade a k + occurrenceStep a r := by
  have he : listCoeffZ (m1RowZ12 r k) j ≠ 0 := by
    intro hz; apply h; simp [m1Coeff, hz]
  obtain ⟨z,hz⟩ := exists_rowIndex_of_coeff_ne_zero _ _ he
  exact grade_m1 a r k (j,z) hz

/-- Formal polynomial coordinates of left multiplication by the pentad chain. -/
def pentadChainPolynomial : List (Fin 5) → Fin 27 → Polynomial ℚ
  | [], j => C (unitVec j)
  | r :: L, j => ∑ k : Fin 27,
      (C (m0Coeff r k j) * pentadChainPolynomial L k +
        C (m1Coeff r k j) * (X * pentadChainPolynomial L k))

theorem pentadChainPolynomial_coeff_grade (L : List (Fin 5)) (a : Fin 5)
    {j : Fin 27} {n : ℕ} (h : (pentadChainPolynomial L j).coeff n ≠ 0) :
    occurrenceCost a * n + occurrenceGrade a j ≤ L.count a := by
  induction L generalizing j n with
  | nil =>
    simp only [pentadChainPolynomial, coeff_C] at h
    split at h
    case isTrue hn =>
      subst n
      have hj : j.val = 0 ∨ j.val = 1 := by
        unfold unitVec at h
        split at h
        · assumption
        · exact False.elim (h rfl)
      simp [grade_start a j hj]
    case isFalse => exact False.elim (h rfl)
  | cons r L ih =>
    have hc : (r :: L).count a = L.count a + occurrenceStep a r := by
      by_cases hr : r = a
      · subst r; simp [occurrenceStep]
      · simp [occurrenceStep, hr]
    cases n with
    | zero =>
      simp only [pentadChainPolynomial, finsetSum_coeff, coeff_add, coeff_C_mul,
        coeff_X_mul_zero, mul_zero, add_zero] at h
      obtain ⟨k,_,hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hstep := grade_coeff0 a r k j (left_ne_zero_of_mul hk)
      have hw := ih (right_ne_zero_of_mul hk)
      simp only [mul_zero, zero_add] at hw ⊢
      rw [hc]
      exact hstep.trans (Nat.add_le_add_right hw _)
    | succ n =>
      simp only [pentadChainPolynomial, finsetSum_coeff, coeff_add, coeff_C_mul,
        coeff_X_mul] at h
      obtain ⟨k,_,hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [hc]
      by_cases hh : m0Coeff r k j * (pentadChainPolynomial L k).coeff (n + 1) = 0
      · rw [hh, zero_add] at hk
        have hstep := grade_coeff1 a r k j (left_ne_zero_of_mul hk)
        have hw := ih (right_ne_zero_of_mul hk)
        rw [Nat.mul_succ]
        omega
      · have hstep := grade_coeff0 a r k j (left_ne_zero_of_mul hh)
        have hw := ih (right_ne_zero_of_mul hh)
        omega

def pentadConnectedTracePolynomial (L : List (Fin 5)) : Polynomial ℚ :=
  ∑ j : Fin 27, C ((trVecZ j : ℤ) : ℚ) * pentadChainPolynomial L j

theorem pentadConnectedTracePolynomial_coeff_frequency (L : List (Fin 5)) (a : Fin 5)
    {n : ℕ} (h : (pentadConnectedTracePolynomial L).coeff n ≠ 0) :
    occurrenceCost a * n ≤ L.count a := by
  simp only [pentadConnectedTracePolynomial, finsetSum_coeff, coeff_C_mul] at h
  obtain ⟨j,_,hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have he := pentadChainPolynomial_coeff_grade L a (right_ne_zero_of_mul hj)
  omega

private theorem counts_sum (L : List (Fin 5)) : ∑ a : Fin 5, L.count a = L.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have h (a : Fin 5) : (r :: L).count a = L.count a + occurrenceStep a r := by
      by_cases hr : r = a
      · subst r; simp [occurrenceStep]
      · simp [occurrenceStep, hr]
    simp only [h, Finset.sum_add_distrib, ih, List.length_cons]
    have hr : ∑ a : Fin 5, occurrenceStep a r = 1 := by
      simp [occurrenceStep]
    rw [hr]

theorem pentadConnectedTracePolynomial_coeff_length (L : List (Fin 5)) {n : ℕ}
    (h : (pentadConnectedTracePolynomial L).coeff n ≠ 0) :
    6 * n ≤ L.length := by
  have h0 := pentadConnectedTracePolynomial_coeff_frequency L 0 h
  have h1 := pentadConnectedTracePolynomial_coeff_frequency L 1 h
  have h2 := pentadConnectedTracePolynomial_coeff_frequency L 2 h
  have h3 := pentadConnectedTracePolynomial_coeff_frequency L 3 h
  have h4 := pentadConnectedTracePolynomial_coeff_frequency L 4 h
  have hsum := counts_sum L
  simp only [Fin.sum_univ_five] at hsum
  norm_num [occurrenceCost] at h0 h1 h2 h3 h4
  omega

end

end AlbertSequential.FiveTest
