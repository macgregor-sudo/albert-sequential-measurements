/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Order.Fin.Tuple
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Data.Fin.Parity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Ordinary cochains on the nonempty full ordered simplex with constant coefficients. -/
@[expose] public section
noncomputable section

open scoped BigOperators

namespace AlbertSequential

/-- A degree-`n` simplex on the `v+1` ordered vertices. -/
abbrev FullSimplex (v n : ℕ) := {s : Fin (n + 1) → Fin (v + 1) // StrictMono s}

def fullSimplexFace {v n : ℕ} (s : FullSimplex v (n + 1)) (i : Fin (n + 2)) : FullSimplex v n :=
  ⟨i.removeNth s.val, s.property.comp (Fin.strictMono_succAbove i)⟩

/-- The ordinary alternating simplicial coboundary with constant coefficients. -/
def fullSimplexCoboundary {v n : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v n → G) (s : FullSimplex v (n + 1)) : G :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • c (fullSimplexFace s i)

theorem fullSimplexCoboundary_squared {v n : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v n → G) (s : FullSimplex v (n + 2)) :
    fullSimplexCoboundary (fullSimplexCoboundary c) s = 0 := by
  simp only [fullSimplexCoboundary, Finset.smul_sum, smul_smul, ← pow_add]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  let swap (ij : Fin (n + 3) × Fin (n + 2)) : Fin (n + 3) × Fin (n + 2) :=
    (ij.1.succAbove ij.2, ij.2.predAbove ij.1)
  apply Finset.sum_ninvolution swap
  · rintro ⟨i, j⟩
    have hfaces : fullSimplexFace (fullSimplexFace s (i.succAbove j)) (j.predAbove i) =
        fullSimplexFace (fullSimplexFace s i) j :=
      Subtype.ext (funext (fun k => congrArg s.val (Fin.succAbove_succAbove_succAbove_predAbove i j k)))
    simp only [swap, hfaces, Fin.neg_one_pow_succAbove_add_predAbove, neg_zsmul, add_neg_cancel]
  · intro ij _
    exact fun h => Fin.succAbove_ne ij.1 ij.2 (congrArg Prod.fst h)
  · intro _
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j) (Fin.predAbove_predAbove_succAbove i j)

/-- Cone at the least vertex when that vertex is absent from a simplex. -/
def fullSimplexCone {v n : ℕ} (s : FullSimplex v n) (h : 0 < s.val 0) : FullSimplex v (n + 1) :=
  ⟨Fin.cons 0 s.val, Fin.strictMono_cons.mpr ⟨
    fun i => h.trans_le (s.property.monotone (Fin.zero_le i)), s.property⟩⟩

/-- The cochain homotopy given by the cone, extended by zero on a simplex that
already contains the least vertex. -/
def fullSimplexContract {v n : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v (n + 1) → G) (s : FullSimplex v n) : G :=
  if h : 0 < s.val 0 then c (fullSimplexCone s h) else 0

theorem fullSimplex_contraction {v n : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v (n + 1) → G) (s : FullSimplex v (n + 1)) :
    fullSimplexCoboundary (fullSimplexContract c) s +
      fullSimplexContract (fullSimplexCoboundary c) s = c s := by
  by_cases h : 0 < s.val 0
  · have hface (i : Fin (n + 2)) : 0 < (fullSimplexFace s i).val 0 :=
      h.trans_le (s.property.monotone (Fin.zero_le _))
    have htail : fullSimplexFace (fullSimplexCone s h) 0 = s :=
      Subtype.ext (funext (fun k => by simp [fullSimplexFace, fullSimplexCone]))
    have hstep (i : Fin (n + 2)) :
        fullSimplexFace (fullSimplexCone s h) i.succ =
          fullSimplexCone (fullSimplexFace s i) (hface i) :=
      Subtype.ext (Fin.cons_comp_succ_succAbove 0 s.val i)
    have hc : fullSimplexCoboundary c (fullSimplexCone s h) =
        c s - fullSimplexCoboundary (fullSimplexContract c) s := by
      rw [fullSimplexCoboundary, Fin.sum_univ_succ, htail]
      simp only [Fin.val_zero, pow_zero, one_zsmul]
      rw [sub_eq_add_neg, fullSimplexCoboundary, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hstep, fullSimplexContract, dite_eq_left (hface i), Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul]
    rw [fullSimplexContract, dite_eq_left h, hc]
    rw [add_comm]
    exact sub_add_cancel _ _
  · have h0 : s.val 0 = 0 := le_antisymm (not_lt.mp h) (Fin.zero_le _)
    have htail : 0 < (fullSimplexFace s 0).val 0 := by
      change 0 < s.val ((0 : Fin (n + 2)).succAbove (0 : Fin (n + 1)))
      rw [Fin.succAbove_zero, ← h0]
      exact s.property (show 0 < (0 : Fin (n + 1)).succ by simp)
    have hcone : fullSimplexCone (fullSimplexFace s 0) htail = s := by
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0.symm
      · simp [fullSimplexFace, fullSimplexCone, Fin.tail]
    have hother (i : Fin (n + 1)) : ¬ 0 < (fullSimplexFace s i.succ).val 0 := by
      change ¬ 0 < s.val (i.succ.succAbove 0)
      rw [Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i), h0]
      exact lt_irrefl _
    rw [fullSimplexContract, dite_eq_right h, add_zero, fullSimplexCoboundary, Fin.sum_univ_succ]
    simp [fullSimplexContract, htail, hcone, hother]

/-- Ordinary cohomology of a nonempty full simplex vanishes in each positive degree. -/
theorem fullSimplex_positiveCocycle_iff_coboundary {v n : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v (n + 1) → G) :
    (∀ s, fullSimplexCoboundary c s = 0) ↔
      ∃ b : FullSimplex v n → G, ∀ s, fullSimplexCoboundary b s = c s := by
  constructor
  · intro hc
    refine ⟨fullSimplexContract c, fun s => ?_⟩
    have h : fullSimplexContract (fullSimplexCoboundary c) s = 0 := by
      unfold fullSimplexContract
      split_ifs with h
      · exact hc _
      · rfl
    simpa only [h, add_zero] using fullSimplex_contraction c s
  · rintro ⟨b, hb⟩ s
    rw [← funext hb]
    exact fullSimplexCoboundary_squared b s

/-- The degree-zero cocycles are exactly the constant cochains. -/
theorem fullSimplex_zeroCocycle_iff_constant {v : ℕ} {G : Type*} [AddCommGroup G]
    (c : FullSimplex v 0 → G) :
    (∀ s, fullSimplexCoboundary c s = 0) ↔ ∃ a : G, ∀ s, c s = a := by
  let apex : FullSimplex v 0 := ⟨fun _ => 0, by
    intro i j hij
    rw [Fin.eq_zero i, Fin.eq_zero j] at hij
    exact ((lt_irrefl _) hij).elim⟩
  constructor
  · intro hc
    refine ⟨c apex, fun s => ?_⟩
    by_cases h : 0 < s.val 0
    · let edge := fullSimplexCone s h
      have htail : fullSimplexFace edge 0 = s :=
        Subtype.ext (funext (fun k => by simp [edge, fullSimplexCone, fullSimplexFace]))
      have hhead : fullSimplexFace edge 1 = apex := by
        apply Subtype.ext
        funext k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        rfl
      have he := hc edge
      change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • c (fullSimplexFace edge i)) = 0 at he
      rw [Fin.sum_univ_two, htail, hhead] at he
      apply sub_eq_zero.mp
      simpa [sub_eq_add_neg] using he
    · have h0 : s.val 0 = 0 := le_antisymm (not_lt.mp h) (Fin.zero_le _)
      exact congrArg c (Subtype.ext (funext (fun i => (Fin.eq_zero i).symm ▸ h0)))
  · rintro ⟨a, ha⟩ s
    simp [fullSimplexCoboundary, Fin.sum_univ_two, ha]

/-- The barycentric geometric realization of the full simplex is contractible. -/
theorem fullSimplex_realization_contractible (v : ℕ) :
    ContractibleSpace ({f : Fin (v + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} :
      Set (Fin (v + 1) → ℝ)) := by
  apply Convex.contractibleSpace
  · intro f hf g hg a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · change 0 ≤ a * f i + b * g i
      exact add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i))
    · change (∑ i, (a * f i + b * g i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2, mul_one, mul_one]
      exact hab
  · refine ⟨Pi.single 0 1, ⟨?_, ?_⟩⟩
    · intro i
      by_cases hi : i = 0 <;> simp [hi]
    · simp [Pi.single_apply]

end AlbertSequential
