/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.WordsAndCertificates
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.VecNotation
-- build order only: keeps large modules from compiling concurrently (memory)
import ComplexWindowDeterminantAndMax

/-! # thm:eleven, the count of the eleven-step list

The list `𝓕_A` is defined here by the disjoint-language description of the eleven-step list
(companion `app:cert:count`, `eq:cer:elevenlist` and the table `tab:cer:tails`). Base `j = A = 0`, `X = {k, l, m} = {B, C, D} = {1, 2, 3}`, cyclic orientation
`E = {(k,l), (l,m), (m,k)}`, `E^op` its reverse; `x̄` is the outcome "no" on `x`, plain letters are
"yes". Holonomy prefixes `H_d = {j x₁y₁ j ⋯ x_d y_d j : x_i ≠ y_i}`.

* scalar-part and unitarity tests: `T b` for `T ∈ H₀ ∪ H₁ ∪ H₂` and the forty tails `b ∈ B`
  (lengths 0..4: `∅`; `x`; `xj`, `xy` (x≠y), `x̄y` ((x,y)∈E); `xyx`, `xyj` (x≠y);
  `xyjy` (x≠y), `xyxj`, `x̄yx̄j` ((x,y)∈E));
* anticommutator tests: `T d` for `T ∈ H₀ ∪ H₁` and the 57 tails `d ∈ D` (`x̄y` ((x,y)∈E^op);
  `σx τy z` (distinct); `σx y σx j` ((x,y)∈E^op); `σx τy z τy σx j` (distinct));
* far-face tests: `jkmlj, jklmj, jklmlk, jk l̄ m l̄ k, jkmljl, jklmjm`.

Reading of the table: at lengths 2 and 4 the restriction "((x,y) ∈ E)" applies to the
`x̄`-items and, at length 4, also to `xyxj` (the row counts 12 force this; the appendix's
derivation "the scalar-part relations use E" says the same).

Proved: the union (duplicates removed) is an `ElevenWordList` (the structure of
`Interfaces.WordsAndCertificates`): 2,041 words, each reduced, beginning with "yes" on `A`, of length
≤ 11, with length histogram 1, 3, 15, 36, 32, 94, 240, 180, 432, 576, 432. Not proved in this file:
that the relation ledger of thm:eleven (a) generates this list (`BlockB.ElevenSupport`,
`elevenLedgerWords_eq_elevenBase`), and thm:eleven (a)–(c) (`BlockB.ElevenTheorem`). -/

@[expose] public section

namespace AlbertSequential.Ends.Eleven

open AlbertSequential

/-- "yes" and "no" outcomes. -/
abbrev yes (a : Fin 4) : Fin 4 × Bool := (a, true)
abbrev no (a : Fin 4) : Fin 4 × Bool := (a, false)

def letters : List (Fin 4) := [1, 2, 3]
def distinctPairs : List (Fin 4 × Fin 4) := [(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)]
def cyclicE : List (Fin 4 × Fin 4) := [(1, 2), (2, 3), (3, 1)]
def cyclicEop : List (Fin 4 × Fin 4) := [(2, 1), (3, 2), (1, 3)]
def distinctTriples : List (Fin 4 × Fin 4 × Fin 4) :=
  [(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)]
def signs : List Bool := [true, false]

/-- `H₀ ∪ H₁`. -/
def prefixes01 : List (Word (Fin 4)) :=
  [[yes 0]] ++ distinctPairs.map (fun p => [yes 0, yes p.1, yes p.2, yes 0])

/-- `H₀ ∪ H₁ ∪ H₂`. -/
def prefixes012 : List (Word (Fin 4)) :=
  prefixes01 ++ distinctPairs.flatMap (fun p => distinctPairs.map (fun q =>
    [yes 0, yes p.1, yes p.2, yes 0, yes q.1, yes q.2, yes 0]))

/-- The forty tails `B` of the scalar-part and unitarity tests. -/
def tailsB : List (Word (Fin 4)) :=
  [[]] ++ letters.map (fun x => [yes x]) ++
  letters.map (fun x => [yes x, yes 0]) ++ distinctPairs.map (fun p => [yes p.1, yes p.2]) ++
  cyclicE.map (fun p => [no p.1, yes p.2]) ++
  distinctPairs.map (fun p => [yes p.1, yes p.2, yes p.1]) ++
  distinctPairs.map (fun p => [yes p.1, yes p.2, yes 0]) ++
  distinctPairs.map (fun p => [yes p.1, yes p.2, yes 0, yes p.2]) ++
  cyclicE.map (fun p => [yes p.1, yes p.2, yes p.1, yes 0]) ++
  cyclicE.map (fun p => [no p.1, yes p.2, no p.1, yes 0])

/-- The 57 new tails `D` of the anticommutator tests. -/
def tailsD : List (Word (Fin 4)) :=
  cyclicEop.map (fun p => [no p.1, yes p.2]) ++
  distinctTriples.flatMap (fun t => signs.flatMap (fun s => signs.map (fun u =>
    [(t.1, s), (t.2.1, u), yes t.2.2]))) ++
  cyclicEop.flatMap (fun p => signs.map (fun s => [(p.1, s), yes p.2, (p.1, s), yes 0])) ++
  distinctTriples.flatMap (fun t => signs.flatMap (fun s => signs.map (fun u =>
    [(t.1, s), (t.2.1, u), yes t.2.2, (t.2.1, u), (t.1, s), yes 0])))

/-- The six far-face words. -/
def farFace : List (Word (Fin 4)) :=
  [[yes 0, yes 1, yes 3, yes 2, yes 0], [yes 0, yes 1, yes 2, yes 3, yes 0],
   [yes 0, yes 1, yes 2, yes 3, yes 2, yes 1], [yes 0, yes 1, no 2, yes 3, no 2, yes 1],
   [yes 0, yes 1, yes 3, yes 2, yes 0, yes 2], [yes 0, yes 1, yes 2, yes 3, yes 0, yes 3]]

/-- The ledger language with repetitions (2,125 entries). -/
def elevenList : List (Word (Fin 4)) :=
  prefixes012.flatMap (fun T => tailsB.map (T ++ ·)) ++
  prefixes01.flatMap (fun T => tailsD.map (T ++ ·)) ++ farFace

/-- The list `𝓕_A`. -/
def elevenBase : Finset (Word (Fin 4)) := elevenList.toFinset

/-! ## An injective numeric code (cheap kernel equality) -/

def digit (a : Fin 4 × Bool) : ℕ := 2 * a.1.val + a.2.toNat

theorem digit_lt (a : Fin 4 × Bool) : digit a < 8 := by
  obtain ⟨⟨x, hx⟩, s⟩ := a
  have := Bool.toNat_le s
  simp only [digit]
  omega

theorem digit_injective {a b : Fin 4 × Bool} (h : digit a = digit b) : a = b := by
  obtain ⟨⟨x, hx⟩, s⟩ := a
  obtain ⟨⟨y, hy⟩, t⟩ := b
  simp only [digit] at h
  cases s <;> cases t <;> simp only [Bool.toNat_false, Bool.toNat_true] at h
  · exact Prod.ext (Fin.ext (by simp only; omega)) rfl
  · omega
  · omega
  · exact Prod.ext (Fin.ext (by simp only; omega)) rfl

def code : Word (Fin 4) → ℕ
  | [] => 0
  | a :: w => 9 * code w + digit a + 1

theorem code_injective : Function.Injective code := by
  intro w
  induction w with
  | nil =>
    intro w' h
    cases w' with
    | nil => rfl
    | cons a w' => simp only [code] at h; omega
  | cons a w ih =>
    intro w' h
    cases w' with
    | nil => simp only [code] at h; omega
    | cons a' w' =>
      simp only [code] at h
      have h1 := digit_lt a
      have h2 := digit_lt a'
      have hc : code w = code w' := by omega
      have hd : digit a = digit a' := by omega
      rw [digit_injective hd, ih hc]

theorem toFinset_map_code (l : List (Word (Fin 4))) :
    (l.map code).toFinset = l.toFinset.image code := by
  ext x
  simp

theorem card_toFinset_eq_code (l : List (Word (Fin 4))) :
    l.toFinset.card = (l.map code).toFinset.card := by
  rw [toFinset_map_code, Finset.card_image_of_injective _ code_injective]

/-- Duplicate removal on codes by a plain structural recursion (predictable kernel cost). -/
def dedupB : List ℕ → List ℕ
  | [] => []
  | a :: l => if a ∈ l then dedupB l else a :: dedupB l

theorem mem_dedupB {x : ℕ} : ∀ {l : List ℕ}, x ∈ dedupB l ↔ x ∈ l
  | [] => by simp [dedupB]
  | a :: l => by
    by_cases h : a ∈ l
    · simp only [dedupB, h, ite_true, mem_dedupB, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact h
        · exact hx
    · simp only [dedupB, h, ite_false, List.mem_cons, mem_dedupB]

theorem nodup_dedupB : ∀ l : List ℕ, (dedupB l).Nodup
  | [] => by simp [dedupB]
  | a :: l => by
    by_cases h : a ∈ l
    · simp only [dedupB, h, ite_true]
      exact nodup_dedupB l
    · simp only [dedupB, h, ite_false]
      exact List.nodup_cons.mpr ⟨fun hm => h (mem_dedupB.mp hm), nodup_dedupB l⟩

theorem card_toFinset_eq_dedupB (l : List ℕ) : l.toFinset.card = (dedupB l).length := by
  have : l.toFinset = (dedupB l).toFinset := by
    ext x
    simp [mem_dedupB]
  rw [this, List.toFinset_card_of_nodup (nodup_dedupB l)]

theorem filter_elevenBase (q : Word (Fin 4) → Prop) [DecidablePred q] :
    elevenBase.filter q = (elevenList.filter (fun w => decide (q w))).toFinset := by
  ext w
  simp [elevenBase]

theorem card_filter_length (n : ℕ) :
    (elevenBase.filter (fun w => w.length = n)).card =
      (dedupB ((elevenList.filter (fun w => decide (w.length = n))).map code)).length := by
  rw [filter_elevenBase, card_toFinset_eq_code, card_toFinset_eq_dedupB]

/-! ## Reducedness as a Boolean check -/

def reducedB : Word (Fin 4) → Bool
  | [] => true
  | [_] => true
  | a :: b :: w => decide (a.1 ≠ b.1) && reducedB (b :: w)

theorem reducedB_sound : ∀ w : Word (Fin 4), reducedB w = true → IsReducedWord w
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: w, h => by
    simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, reducedB_sound (b :: w) h.2⟩

/-! ## The finite checks (kernel evaluation, no native code) -/

theorem elevenList_shape :
    elevenList.all (fun w => reducedB w && decide (w.head? = some (0, true)) &&
      decide (w.length ≤ 11)) = true := by
  decide +kernel

theorem hist_1 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 1))).map code)).length = 1 := by
  decide +kernel

theorem hist_2 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 2))).map code)).length = 3 := by
  decide +kernel

theorem hist_3 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 3))).map code)).length = 15 := by
  decide +kernel

theorem hist_4 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 4))).map code)).length = 36 := by
  decide +kernel

theorem hist_5 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 5))).map code)).length = 32 := by
  decide +kernel

theorem hist_6 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 6))).map code)).length = 94 := by
  decide +kernel

theorem hist_7 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 7))).map code)).length = 240 := by
  decide +kernel

theorem hist_8 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 8))).map code)).length = 180 := by
  decide +kernel

theorem hist_9 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 9))).map code)).length = 432 := by
  decide +kernel

theorem hist_10 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 10))).map code)).length = 576 := by
  decide +kernel

theorem hist_11 :
    (dedupB ((elevenList.filter (fun w => decide (w.length = 11))).map code)).length = 432 := by
  decide +kernel

theorem elevenBase_shape (w : Word (Fin 4)) (hw : w ∈ elevenBase) :
    IsReducedWord w ∧ w.head? = some (0, true) ∧ w.length ≤ 11 := by
  have hl : w ∈ elevenList := List.mem_toFinset.mp hw
  have h := List.all_eq_true.mp elevenList_shape w hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨reducedB_sound w h.1.1, h.1.2, h.2⟩

theorem card_length_1 : (elevenBase.filter (fun w => w.length = 1)).card = 1 := by
  rw [card_filter_length]
  exact hist_1

theorem card_length_2 : (elevenBase.filter (fun w => w.length = 2)).card = 3 := by
  rw [card_filter_length]
  exact hist_2

theorem card_length_3 : (elevenBase.filter (fun w => w.length = 3)).card = 15 := by
  rw [card_filter_length]
  exact hist_3

theorem card_length_4 : (elevenBase.filter (fun w => w.length = 4)).card = 36 := by
  rw [card_filter_length]
  exact hist_4

theorem card_length_5 : (elevenBase.filter (fun w => w.length = 5)).card = 32 := by
  rw [card_filter_length]
  exact hist_5

theorem card_length_6 : (elevenBase.filter (fun w => w.length = 6)).card = 94 := by
  rw [card_filter_length]
  exact hist_6

theorem card_length_7 : (elevenBase.filter (fun w => w.length = 7)).card = 240 := by
  rw [card_filter_length]
  exact hist_7

theorem card_length_8 : (elevenBase.filter (fun w => w.length = 8)).card = 180 := by
  rw [card_filter_length]
  exact hist_8

theorem card_length_9 : (elevenBase.filter (fun w => w.length = 9)).card = 432 := by
  rw [card_filter_length]
  exact hist_9

theorem card_length_10 : (elevenBase.filter (fun w => w.length = 10)).card = 576 := by
  rw [card_filter_length]
  exact hist_10

theorem card_length_11 : (elevenBase.filter (fun w => w.length = 11)).card = 432 := by
  rw [card_filter_length]
  exact hist_11

theorem elevenBase_hist (k : Fin 11) :
    (elevenBase.filter (fun w => w.length = k.val + 1)).card =
      (![1, 3, 15, 36, 32, 94, 240, 180, 432, 576, 432] : Fin 11 → ℕ) k := by
  match k with
  | ⟨0, _⟩ => exact card_length_1
  | ⟨1, _⟩ => exact card_length_2
  | ⟨2, _⟩ => exact card_length_3
  | ⟨3, _⟩ => exact card_length_4
  | ⟨4, _⟩ => exact card_length_5
  | ⟨5, _⟩ => exact card_length_6
  | ⟨6, _⟩ => exact card_length_7
  | ⟨7, _⟩ => exact card_length_8
  | ⟨8, _⟩ => exact card_length_9
  | ⟨9, _⟩ => exact card_length_10
  | ⟨10, _⟩ => exact card_length_11

theorem elevenBase_length_zero : (elevenBase.filter (fun w => w.length = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw h0
  have h := (elevenBase_shape w hw).2.1
  rw [List.length_eq_zero_iff.mp h0] at h
  simp at h

/-- Abstract counting step (the set is a variable, so the kernel never evaluates it here). -/
theorem card_of_counts (s : Finset (Word (Fin 4))) (hb : ∀ w ∈ s, w.length ≤ 11)
    (h0 : (s.filter (fun w => w.length = 0)).card = 0)
    (h1 : (s.filter (fun w => w.length = 1)).card = 1)
    (h2 : (s.filter (fun w => w.length = 2)).card = 3)
    (h3 : (s.filter (fun w => w.length = 3)).card = 15)
    (h4 : (s.filter (fun w => w.length = 4)).card = 36)
    (h5 : (s.filter (fun w => w.length = 5)).card = 32)
    (h6 : (s.filter (fun w => w.length = 6)).card = 94)
    (h7 : (s.filter (fun w => w.length = 7)).card = 240)
    (h8 : (s.filter (fun w => w.length = 8)).card = 180)
    (h9 : (s.filter (fun w => w.length = 9)).card = 432)
    (h10 : (s.filter (fun w => w.length = 10)).card = 576)
    (h11 : (s.filter (fun w => w.length = 11)).card = 432) :
    s.card = 2041 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := List.length) (t := Finset.range 12)
    (by intro w hw; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hb w hw)))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem elevenBase_card : elevenBase.card = 2041 :=
  card_of_counts elevenBase (fun w hw => (elevenBase_shape w hw).2.2) elevenBase_length_zero
    card_length_1 card_length_2 card_length_3 card_length_4 card_length_5 card_length_6
    card_length_7 card_length_8 card_length_9 card_length_10 card_length_11

/-- **thm:eleven, the count**: the ledger language of the counting appendix inhabits the
structure `ElevenWordList` (2,041 reduced words from "yes" on `A`, length ≤ 11, with the length
histogram of the paper). -/
def elevenWordList : ElevenWordList where
  baseWords := elevenBase
  cardinality := elevenBase_card
  starts_at_base w hw := (elevenBase_shape w hw).2.1
  reduced w hw := (elevenBase_shape w hw).1
  length_bound w hw := (elevenBase_shape w hw).2.2
  length_counts := elevenBase_hist

theorem elevenBase_eq : elevenWordList.baseWords = elevenBase := rfl

end AlbertSequential.Ends.Eleven

#print axioms AlbertSequential.Ends.Eleven.elevenBase_card
#print axioms AlbertSequential.Ends.Eleven.elevenBase_shape
#print axioms AlbertSequential.Ends.Eleven.elevenBase_hist
#print axioms AlbertSequential.Ends.Eleven.elevenWordList
