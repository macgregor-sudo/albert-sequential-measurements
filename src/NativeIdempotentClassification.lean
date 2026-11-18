/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeDiagonalProduct
public import NativeWordPositivity

/-! Actual compact native idempotents have zero/one diagonal eigenvalues.
The raw trace is0,1,2 or3; no general EJA rank/classification is imported. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

@[simp] theorem albertTrace_unit : albertTrace albertUnit = 3 := by
  simp [albertTrace, albertUnit]

theorem native_idempotent_trace_card (q : Albert) (hq : jordanMul q q = q) :
    ∃ s : Finset (Fin 3), albertTrace q = (s.card : ℝ) := by
  classical
  obtain ⟨g,d,hg⟩ := nativeDiagonalization q
  have hid : jordanMul (diagonalElement d) (diagonalElement d) = diagonalElement d := by
    rw [← hg, ← g.preserves_product, hq]
  have hsq (i : Fin 3) : d i ^ 2 = d i := by
    have h := congrArg (fun x : Albert => x.1 i) hid
    rw [diagonal_square] at h
    exact h
  have hbits (i : Fin 3) : d i = 0 ∨ d i = 1 := by
    have h : d i * (d i - 1) = 0 := by nlinarith [hsq i]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  let s := Finset.univ.filter (fun i => d i = 1)
  refine ⟨s, ?_⟩
  have ht : albertTrace q = albertTrace (diagonalElement d) :=
    (g.preserves_trace q).symm.trans (congrArg albertTrace hg)
  rw [ht, diagonal_trace]
  calc
    (∑ i, d i) = ∑ i : Fin 3, if d i = 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hbits i with hi | hi <;> simp [hi]
    _ = ∑ _i ∈ s, (1 : ℝ) := by rw [Finset.sum_filter]
    _ = (s.card : ℝ) := by simp

theorem native_idempotent_trace_cases (q : Albert) (hq : jordanMul q q = q) :
    albertTrace q = 0 ∨ albertTrace q = 1 ∨ albertTrace q = 2 ∨ albertTrace q = 3 := by
  obtain ⟨s,hs⟩ := native_idempotent_trace_card q hq
  have hle : s.card ≤ 3 := by simpa using Finset.card_le_univ s
  have h : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases h with h | h | h | h <;> simp_all

theorem native_idempotent_classification (q : Albert) (hq : jordanMul q q = q) :
    q = 0 ∨ q = albertUnit ∨ IsAtom q ∨ IsAtom (albertUnit - q) := by
  rcases native_idempotent_trace_cases q hq with h0 | h1 | h2 | h3
  · exact Or.inl ((isPositive_trace_eq_zero q (isPositive_idempotent q hq)).mp h0)
  · exact Or.inr (Or.inr (Or.inl ⟨hq,h1⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨complementary_idempotent q hq, ?_⟩))
    rw [albertTrace_sub, albertTrace_unit, h2]
    norm_num
  · have hz : albertUnit - q = 0 := by
      apply (isPositive_trace_eq_zero _ (isPositive_idempotent _ (complementary_idempotent q hq))).mp
      rw [albertTrace_sub, albertTrace_unit, h3, sub_self]
    exact Or.inr (Or.inl (sub_eq_zero.mp hz).symm)

end AlbertSequential.NativeAnalysis
