/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.WordsAndCertificates
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Tactic.Tauto

/-! Exact reduced chronological grammar and the full finite horizon index set.
No word list is computed or replaced by an arbitrary sparse subset. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {ι : Type*}

theorem isReducedWord_tail (a : Outcome ι) (w : Word ι)
    (h : IsReducedWord (a :: w)) : IsReducedWord w := by
  cases w with
  | nil => trivial
  | cons b w => exact h.2

theorem isReducedWord_suffix (u v : Word ι)
    (h : IsReducedWord (u ++ v)) : IsReducedWord v := by
  induction u with
  | nil => exact h
  | cons a u ih =>
      exact ih (isReducedWord_tail a (u ++ v) h)

theorem isReducedWord_prefix (u v : Word ι)
    (h : IsReducedWord (u ++ v)) : IsReducedWord u := by
  induction u with
  | nil => trivial
  | cons a u ih =>
      cases u with
      | nil => trivial
      | cons b u =>
          exact ⟨h.1, ih h.2⟩

theorem isReducedWord_append_singleton_iff (w : Word ι) (a : Outcome ι) :
    IsReducedWord (w ++ [a]) ↔
      IsReducedWord w ∧ ∀ b, w.getLast? = some b → b.1 ≠ a.1 := by
  induction w with
  | nil => simp [IsReducedWord]
  | cons b w ih =>
      cases w with
      | nil => simp [IsReducedWord]
      | cons c w =>
          change (b.1 ≠ c.1 ∧ IsReducedWord ((c :: w) ++ [a])) ↔
            (b.1 ≠ c.1 ∧ IsReducedWord (c :: w)) ∧
              ∀ d, (b :: c :: w).getLast? = some d → d.1 ≠ a.1
          rw [ih]
          simp only [List.getLast?_cons_cons]
          tauto

theorem isReducedWord_append_outcome_iff (w : Word ι) (i : ι) (b c : Bool) :
    IsReducedWord (w ++ [(i, b)]) ↔ IsReducedWord (w ++ [(i, c)]) := by
  simp only [isReducedWord_append_singleton_iff]

theorem isReducedWord_last_ne (w : Word ι) (a b : Outcome ι)
    (h : IsReducedWord (w ++ [a])) (hlast : w.getLast? = some b) :
    b.1 ≠ a.1 :=
  (isReducedWord_append_singleton_iff w a).mp h |>.2 b hlast

theorem reducedWord_snoc_length (w : Word ι) (a : Outcome ι) (L : ℕ)
    (h : (w ++ [a]).length ≤ L) : w.length < L := by
  simp only [List.length_append, List.length_singleton] at h
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h

theorem finite_reducedWords_le [Finite ι] (L : ℕ) :
    {w : Word ι | w.length ≤ L ∧ IsReducedWord w}.Finite := by
  exact (List.finite_length_le (Outcome ι) L).subset (fun _ h => h.1)

/-- All and only reduced words through L, including the empty word. -/
def reducedWordsUpTo (ι : Type*) [Finite ι] (L : ℕ) : Finset (Word ι) :=
  (finite_reducedWords_le (ι := ι) L).toFinset

theorem mem_reducedWordsUpTo [Finite ι] (L : ℕ) (w : Word ι) :
    w ∈ reducedWordsUpTo ι L ↔ w.length ≤ L ∧ IsReducedWord w := by
  classical
  exact Set.Finite.mem_toFinset (finite_reducedWords_le (ι := ι) L)

theorem empty_mem_reducedWordsUpTo [Finite ι] (L : ℕ) :
    ([] : Word ι) ∈ reducedWordsUpTo ι L := by
  rw [mem_reducedWordsUpTo]
  exact ⟨Nat.zero_le L, trivial⟩

theorem append_mem_reducedWordsUpTo_iff [Finite ι] (L : ℕ)
    (w : Word ι) (a : Outcome ι) :
    w ++ [a] ∈ reducedWordsUpTo ι L ↔
      w.length + 1 ≤ L ∧ IsReducedWord w ∧
        ∀ b, w.getLast? = some b → b.1 ≠ a.1 := by
  rw [mem_reducedWordsUpTo, isReducedWord_append_singleton_iff]
  simp only [List.length_append, List.length_singleton]

end AlbertSequential
