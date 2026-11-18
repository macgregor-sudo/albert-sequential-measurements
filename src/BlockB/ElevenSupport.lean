/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Ends.Eleven
public import ConstructedCornerTelescope
public import PurityOccurrenceRelabelling
public import FiniteCornerWitness
public import NativeWordPurity
public import NativeHalfSubspaces
public import RealWordFunctionals
public import ReducedWords
public import WordRelabelling
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Basic
-- build order only: keeps large modules from compiling concurrently (memory)
import RobustCert.RobustS

/-! # Combinatorics, Word Reduction, and Relation-Ledger Correspondence for `thm:eleven`

This module provides the word-level and ledger-level support for `thm:eleven`:
1. Canonical word reduction `reduceWord : Word ι → Option (Word ι)` and functional reduction
   `reduceFunctional : FiniteRealWordFunctional 4 → FiniteRealWordFunctional 4`, preserving
   both `AlgebraicProjectiveData.probability` and `nativeWordProbability` while reducing
   `coefficientNorm` and forcing every surviving word to be reduced.
2. Explicit relation-ledger application generator (`ledgerApplications`, 1,673 applications across
   `tab:cer:ledger` rows (i)–(iv)) and kernel-verified equivalence
   `elevenLedgerWords_eq_elevenBase : elevenLedgerWords = Ends.Eleven.elevenBase` (`2,041` words).
3. Four-base relabelled union `elevenUnion = ⋃ j, elevenFamily j` via `swapBase j := Equiv.swap 0 j`
   with cardinality `8,164` (`4 × 2,041`), pairwise disjointness, shape bounds, and relabelling transport.
4. Direct verification that every measured word (`shortWord`, `middleWord`, `longWord`) produced by
   `cornerResidualTelescopeOccurrences d C` is already reduced and lies inside
   `Ends.Eleven.elevenBase` (523 distinct words out of 2,041), hence its `swapBase`-relabelled
   four-base `combinedCornerWitness` is supported in `insert [] elevenUnion`.
-/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential.BlockB

open AlbertSequential AlbertSequential.Ends.Eleven

/-! ## 1. Fast Kernel Set Equality and Inclusion via Binary Word Trie (`BinTrie`) -/

def encodeOutcome (a : Outcome (Fin 4)) : Bool × Bool × Bool :=
  match a.1.1, a.2 with
  | 0, s => (false, false, s)
  | 1, s => (false, true, s)
  | 2, s => (true, false, s)
  | _, s => (true, true, s)

theorem encodeOutcome_injective : Function.Injective encodeOutcome := by
  intro a b
  revert a b
  decide

def encodeWord : Word (Fin 4) → List Bool
  | [] => []
  | a :: w =>
      let t := encodeOutcome a
      t.1 :: t.2.1 :: t.2.2 :: encodeWord w

theorem encodeWord_injective : Function.Injective encodeWord := by
  intro w₁ w₂ h
  induction w₁ generalizing w₂ with
  | nil =>
      cases w₂ with
      | nil => rfl
      | cons _ _ => simp [encodeWord] at h
  | cons a w₁ ih =>
      cases w₂ with
      | nil => simp [encodeWord] at h
      | cons b w₂' =>
          simp only [encodeWord, List.cons.injEq] at h
          rcases h with ⟨h1, h2, h3, hw⟩
          have hab : encodeOutcome a = encodeOutcome b := Prod.ext h1 (Prod.ext h2 h3)
          rw [encodeOutcome_injective hab, ih hw]

/-- Prefix binary trie over encoded `Word (Fin 4)` bitstrings (`Bool` steps, no `Nat` arithmetic). -/
inductive BinTrie where
  | empty : BinTrie
  | node (here : Bool) (f t : BinTrie) : BinTrie

namespace BinTrie

def mem : List Bool → BinTrie → Bool
  | _, .empty => false
  | [], .node h _ _ => h
  | false :: bs, .node _ f _ => mem bs f
  | true :: bs, .node _ _ t => mem bs t

def insert : List Bool → BinTrie → BinTrie
  | [], .empty => .node true .empty .empty
  | [], .node _ f t => .node true f t
  | false :: bs, .empty => .node false (insert bs .empty) .empty
  | false :: bs, .node h f t => .node h (insert bs f) t
  | true :: bs, .empty => .node false .empty (insert bs .empty)
  | true :: bs, .node h f t => .node h f (insert bs t)

theorem mem_empty (bs : List Bool) : mem bs .empty = false := by
  cases bs with
  | nil => rfl
  | cons b _ => cases b <;> rfl

theorem mem_insert_iff (bs cs : List Bool) (tr : BinTrie) :
    mem cs (insert bs tr) = true ↔ cs = bs ∨ mem cs tr = true := by
  induction bs generalizing cs tr with
  | nil =>
      cases tr with
      | empty =>
          cases cs with
          | nil => simp [insert, mem]
          | cons c cs => cases c <;> simp [insert, mem, mem_empty]
      | node h f t =>
          cases cs with
          | nil => simp [insert, mem]
          | cons c cs => cases c <;> simp [insert, mem]
  | cons b bs ih =>
      cases b <;> cases tr with
      | empty =>
          cases cs with
          | nil => simp [insert, mem]
          | cons c cs => cases c <;> simp [insert, mem, mem_empty, ih]
      | node h f t =>
          cases cs with
          | nil => simp [insert, mem]
          | cons c cs => cases c <;> simp [insert, mem, ih]

def union : BinTrie → BinTrie → BinTrie
  | .empty, t₂ => t₂
  | t₁, .empty => t₁
  | .node h1 f1 t1, .node h2 f2 t2 => .node (h1 || h2) (union f1 f2) (union t1 t2)

theorem mem_union (tr₁ tr₂ : BinTrie) (cs : List Bool) :
    mem cs (union tr₁ tr₂) = (mem cs tr₁ || mem cs tr₂) := by
  induction tr₁ generalizing tr₂ cs with
  | empty => simp [union, mem_empty]
  | node h1 f1 t1 ihf iht =>
      cases tr₂ with
      | empty => simp [union, mem_empty]
      | node h2 f2 t2 =>
          cases cs with
          | nil => rfl
          | cons c cs => cases c <;> simp [union, mem, ihf, iht]

def isEmpty : BinTrie → Bool
  | .empty => true
  | .node false f t => isEmpty f && isEmpty t
  | .node true _ _ => false

theorem isEmpty_sound (tr : BinTrie) (h : isEmpty tr = true) (cs : List Bool) :
    mem cs tr = false := by
  induction tr generalizing cs with
  | empty => exact mem_empty cs
  | node here f t ihf iht =>
      cases here with
      | true => simp [isEmpty] at h
      | false =>
          simp only [isEmpty, Bool.and_eq_true] at h
          cases cs with
          | nil => rfl
          | cons c cs =>
              cases c
              · exact ihf h.1 cs
              · exact iht h.2 cs

def eqBool : BinTrie → BinTrie → Bool
  | .empty, t₂ => isEmpty t₂
  | t₁, .empty => isEmpty t₁
  | .node h1 f1 t1, .node h2 f2 t2 => (h1 == h2) && eqBool f1 f2 && eqBool t1 t2

theorem eqBool_sound (tr₁ tr₂ : BinTrie) (h : eqBool tr₁ tr₂ = true) (cs : List Bool) :
    mem cs tr₁ = true ↔ mem cs tr₂ = true := by
  induction tr₁ generalizing tr₂ cs with
  | empty =>
      simp only [eqBool] at h
      simp [mem_empty, isEmpty_sound tr₂ h cs]
  | node h1 f1 t1 ihf iht =>
      cases tr₂ with
      | empty =>
          simp only [eqBool] at h
          simp [isEmpty_sound (.node h1 f1 t1) h cs, mem_empty]
      | node h2 f2 t2 =>
          simp only [eqBool, Bool.and_eq_true] at h
          cases cs with
          | nil =>
              have hh := h.1.1
              cases h1 <;> cases h2 <;> simp_all [mem]
          | cons c cs =>
              cases c
              · exact ihf f2 h.1.2 cs
              · exact iht t2 h.2 cs

def subBool : BinTrie → BinTrie → Bool
  | .empty, _ => true
  | t₁, .empty => isEmpty t₁
  | .node h1 f1 t1, .node h2 f2 t2 => (!h1 || h2) && subBool f1 f2 && subBool t1 t2

theorem subBool_sound (tr₁ tr₂ : BinTrie) (h : subBool tr₁ tr₂ = true) (cs : List Bool)
    (hmem : mem cs tr₁ = true) : mem cs tr₂ = true := by
  induction tr₁ generalizing tr₂ cs with
  | empty => simp [mem_empty] at hmem
  | node h1 f1 t1 ihf iht =>
      cases tr₂ with
      | empty =>
          simp only [subBool] at h
          rw [isEmpty_sound (.node h1 f1 t1) h cs] at hmem
          simp at hmem
      | node h2 f2 t2 =>
          simp only [subBool, Bool.and_eq_true] at h
          cases cs with
          | nil =>
              have hh := h.1.1
              cases h1 <;> cases h2 <;> simp_all [mem]
          | cons c cs =>
              cases c
              · exact ihf f2 h.1.2 cs hmem
              · exact iht t2 h.2 cs hmem

def ofWordList (L : List (Word (Fin 4))) : BinTrie :=
  L.foldl (fun tr w => tr.insert (encodeWord w)) .empty

theorem mem_ofWordList (L : List (Word (Fin 4))) (w : Word (Fin 4)) :
    mem (encodeWord w) (ofWordList L) = true ↔ w ∈ L := by
  have hgen : ∀ (init : BinTrie),
      mem (encodeWord w) (L.foldl (fun tr u => tr.insert (encodeWord u)) init) = true ↔
        mem (encodeWord w) init = true ∨ w ∈ L := by
    induction L with
    | nil =>
        intro init
        simp
    | cons u L ih =>
        intro init
        simp only [List.foldl_cons, ih, mem_insert_iff, List.mem_cons]
        constructor
        · rintro ((heq | hinit) | hw)
          · exact Or.inr (Or.inl (encodeWord_injective heq))
          · exact Or.inl hinit
          · exact Or.inr (Or.inr hw)
        · rintro (hinit | rfl | hw)
          · exact Or.inl (Or.inr hinit)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hw
  simpa only [ofWordList, mem_empty, Bool.false_eq_true, false_or] using hgen .empty

def unionMap {α : Type*} (f : α → BinTrie) (xs : List α) : BinTrie :=
  xs.foldl (fun tr a => union tr (f a)) .empty

theorem mem_unionMap {α : Type*} (f : α → BinTrie) (xs : List α) (cs : List Bool) :
    mem cs (unionMap f xs) = true ↔ ∃ a ∈ xs, mem cs (f a) = true := by
  have hgen : ∀ (init : BinTrie),
      mem cs (xs.foldl (fun tr a => union tr (f a)) init) = true ↔
        mem cs init = true ∨ ∃ a ∈ xs, mem cs (f a) = true := by
    induction xs with
    | nil =>
        intro init
        simp
    | cons x xs ih =>
        intro init
        simp only [List.foldl_cons, ih, mem_union, Bool.or_eq_true, List.mem_cons]
        constructor
        · rintro ((hinit | hx) | ⟨a, ha, hfa⟩)
          · exact Or.inl hinit
          · exact Or.inr ⟨x, Or.inl rfl, hx⟩
          · exact Or.inr ⟨a, Or.inr ha, hfa⟩
        · rintro (hinit | ⟨a, rfl | ha, hfa⟩)
          · exact Or.inl (Or.inl hinit)
          · exact Or.inl (Or.inr hfa)
          · exact Or.inr ⟨a, ha, hfa⟩
  simpa only [unionMap, mem_empty, Bool.false_eq_true, false_or] using hgen .empty

def batchAux {α : Type*} (limit : ℕ) :
    List α → ℕ → List α → List (List α) → List (List α)
  | [], _, cur, acc => if cur.isEmpty then acc else cur :: acc
  | x :: xs, k, cur, acc =>
      match k with
      | 0 => batchAux limit xs limit [x] (cur :: acc)
      | k + 1 => batchAux limit xs k (x :: cur) acc

theorem exists_mem_batchAux {α : Type*} (P : α → Prop) (limit : ℕ)
    (xs : List α) (k : ℕ) (cur : List α) (acc : List (List α)) :
    (∃ c ∈ batchAux limit xs k cur acc, ∃ a ∈ c, P a) ↔
      (∃ a ∈ cur, P a) ∨ (∃ c ∈ acc, ∃ a ∈ c, P a) ∨ (∃ a ∈ xs, P a) := by
  induction xs generalizing k cur acc with
  | nil =>
      cases cur <;> simp [batchAux]
  | cons x xs ih =>
      cases k with
      | zero =>
          simp only [batchAux, ih, List.mem_cons, exists_eq_or_imp, or_assoc]
          constructor
          · rintro (hx | hnil | hcur | hacc | hxs)
            · exact Or.inr (Or.inr (Or.inl hx))
            · rcases hnil with ⟨_, hmem, _⟩
              cases hmem
            · exact Or.inl hcur
            · exact Or.inr (Or.inl hacc)
            · exact Or.inr (Or.inr (Or.inr hxs))
          · rintro (hcur | hacc | hx | hxs)
            · exact Or.inr (Or.inr (Or.inl hcur))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hacc)))
            · exact Or.inl hx
            · exact Or.inr (Or.inr (Or.inr (Or.inr hxs)))
      | succ k =>
          simp only [batchAux, ih, List.mem_cons, exists_eq_or_imp, or_assoc]
          constructor
          · rintro (hx | hcur | hacc | hxs)
            · exact Or.inr (Or.inr (Or.inl hx))
            · exact Or.inl hcur
            · exact Or.inr (Or.inl hacc)
            · exact Or.inr (Or.inr (Or.inr hxs))
          · rintro (hcur | hacc | hx | hxs)
            · exact Or.inr (Or.inl hcur)
            · exact Or.inr (Or.inr (Or.inl hacc))
            · exact Or.inl hx
            · exact Or.inr (Or.inr (Or.inr hxs))

def unionList (ts : List BinTrie) : BinTrie :=
  ts.foldl union .empty

theorem mem_unionList (ts : List BinTrie) (cs : List Bool) :
    mem cs (unionList ts) = true ↔ ∃ t ∈ ts, mem cs t = true :=
  mem_unionMap id ts cs

def ofWordListBatched (L : List (Word (Fin 4))) : BinTrie :=
  let trees := (batchAux 15 L 15 [] []).map ofWordList
  let groups := batchAux 15 trees 15 [] []
  unionMap unionList groups

theorem mem_ofWordListBatched (L : List (Word (Fin 4))) (w : Word (Fin 4)) :
    mem (encodeWord w) (ofWordListBatched L) = true ↔ w ∈ L := by
  unfold ofWordListBatched
  rw [mem_unionMap]
  simp only [mem_unionList]
  rw [exists_mem_batchAux (fun t : BinTrie => mem (encodeWord w) t = true)]
  simp only [List.not_mem_nil, false_and, exists_false, false_or,
    List.mem_map, exists_exists_and_eq_and, mem_ofWordList]
  have hL : (∃ c ∈ batchAux 15 L 15 [] [], w ∈ c) ↔
      (∃ c ∈ batchAux 15 L 15 [] [], ∃ v ∈ c, w = v) := by
    simp only [exists_eq_right']
  rw [hL, exists_mem_batchAux (fun v => w = v)]
  simp

theorem toFinset_eq_of_eqBool {L₁ L₂ : List (Word (Fin 4))} {tr₁ tr₂ : BinTrie}
    (h₁ : ∀ w, mem (encodeWord w) tr₁ = true ↔ w ∈ L₁)
    (h₂ : ∀ w, mem (encodeWord w) tr₂ = true ↔ w ∈ L₂)
    (heq : eqBool tr₁ tr₂ = true) :
    L₁.toFinset = L₂.toFinset := by
  ext w
  simp only [List.mem_toFinset, ← h₁ w, ← h₂ w]
  exact eqBool_sound tr₁ tr₂ heq (encodeWord w)

theorem mem_toFinset_of_subBool {L₁ L₂ : List (Word (Fin 4))} {tr₁ tr₂ : BinTrie}
    (h₁ : ∀ w, mem (encodeWord w) tr₁ = true ↔ w ∈ L₁)
    (h₂ : ∀ w, mem (encodeWord w) tr₂ = true ↔ w ∈ L₂)
    (hsub : subBool tr₁ tr₂ = true) {w : Word (Fin 4)} (hw : w ∈ L₁) :
    w ∈ L₂.toFinset := by
  rw [List.mem_toFinset, ← h₂ w]
  exact subBool_sound tr₁ tr₂ hsub (encodeWord w) ((h₁ w).mpr hw)

end BinTrie

/-! ## 2. Canonical Word Reduction -/

/-- Prepend an outcome onto an already reduced optional word, merging adjacent equal
outcomes and collapsing adjacent complementary outcomes to `none`. -/
def consReduced {ι : Type*} [DecidableEq ι] (a : Outcome ι) :
    Option (Word ι) → Option (Word ι)
  | none => none
  | some [] => some [a]
  | some (b :: w) =>
      if a.1 = b.1 then
        if a.2 = b.2 then some (b :: w) else none
      else
        some (a :: b :: w)

/-- Canonical reduction of a chronological word `Word ι`: merges adjacent identical
`(i, s), (i, s)` and returns `none` if any adjacent contradictory pair `(i, s), (i, !s)`
occurs. -/
def reduceWord {ι : Type*} [DecidableEq ι] : Word ι → Option (Word ι)
  | [] => some []
  | a :: w => consReduced a (reduceWord w)

theorem consReduced_isReduced {ι : Type*} [DecidableEq ι] {a : Outcome ι}
    {o : Option (Word ι)} {v : Word ι}
    (ho : ∀ u, o = some u → IsReducedWord u)
    (h : consReduced a o = some v) : IsReducedWord v := by
  cases o with
  | none => simp [consReduced] at h
  | some u =>
      have hu := ho u rfl
      cases u with
      | nil =>
          simp only [consReduced, Option.some.injEq] at h
          subst h
          trivial
      | cons b w =>
          simp only [consReduced] at h
          by_cases h1 : a.1 = b.1
          · simp only [h1, ↓reduceIte] at h
            by_cases h2 : a.2 = b.2
            · simp only [h2, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact hu
            · simp [h2] at h
          · simp only [h1, ↓reduceIte, Option.some.injEq] at h
            subst h
            exact ⟨h1, hu⟩

theorem reduceWord_isReduced {ι : Type*} [DecidableEq ι] :
    ∀ {w v : Word ι}, reduceWord w = some v → IsReducedWord v
  | [], v, h => by
      simp only [reduceWord, Option.some.injEq] at h
      subst h
      trivial
  | a :: w, v, h =>
      consReduced_isReduced (fun _ hu => reduceWord_isReduced hu) h

theorem reduceWord_of_isReduced {ι : Type*} [DecidableEq ι] :
    ∀ {w : Word ι}, IsReducedWord w → reduceWord w = some w
  | [], _ => rfl
  | [a], _ => rfl
  | a :: b :: w, h => by
      have ih := reduceWord_of_isReduced h.2
      change consReduced a (reduceWord (b :: w)) = some (a :: b :: w)
      rw [ih]
      simp [consReduced, h.1]

theorem reduceWord_idempotent {ι : Type*} [DecidableEq ι] {w v : Word ι}
    (h : reduceWord w = some v) : reduceWord v = some v :=
  reduceWord_of_isReduced (reduceWord_isReduced h)

theorem reduceWord_head? {ι : Type*} [DecidableEq ι] {a : Outcome ι} {w v : Word ι}
    (h : reduceWord (a :: w) = some v) : v.head? = some a := by
  simp only [reduceWord] at h
  cases ho : reduceWord w with
  | none => simp [ho, consReduced] at h
  | some u =>
      rw [ho] at h
      cases u with
      | nil =>
          simp only [consReduced, Option.some.injEq] at h
          subst h
          rfl
      | cons b u' =>
          simp only [consReduced] at h
          by_cases h1 : a.1 = b.1
          · simp only [h1, ↓reduceIte] at h
            by_cases h2 : a.2 = b.2
            · simp only [h2, ↓reduceIte, Option.some.injEq] at h
              subst h
              have hab : b = a := Prod.ext h1.symm h2.symm
              simp [hab]
            · simp [h2] at h
          · simp only [h1, ↓reduceIte, Option.some.injEq] at h
            subst h
            rfl

theorem reduceWord_length_le {ι : Type*} [DecidableEq ι] :
    ∀ {w v : Word ι}, reduceWord w = some v → v.length ≤ w.length
  | [], v, h => by
      simp only [reduceWord, Option.some.injEq] at h
      subst h
      exact le_refl _
  | a :: w, v, h => by
      simp only [reduceWord] at h
      cases ho : reduceWord w with
      | none => simp [ho, consReduced] at h
      | some u =>
          have ih := reduceWord_length_le ho
          rw [ho] at h
          cases u with
          | nil =>
              simp only [consReduced, Option.some.injEq] at h
              subst h
              simp only [List.length_cons]
              omega
          | cons b u' =>
              simp only [consReduced] at h
              by_cases h1 : a.1 = b.1
              · simp only [h1, ↓reduceIte] at h
                by_cases h2 : a.2 = b.2
                · simp only [h2, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  simp only [List.length_cons] at ih ⊢
                  omega
                · simp [h2] at h
              · simp only [h1, ↓reduceIte, Option.some.injEq] at h
                subst h
                simp only [List.length_cons] at ih ⊢
                omega

theorem consReduced_relabel {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {f : ι → κ} (hf : Function.Injective f) (a : Outcome ι) (o : Option (Word ι)) :
    consReduced (relabelOutcome f a) (o.map (relabelWord f)) =
      (consReduced a o).map (relabelWord f) := by
  cases o with
  | none => rfl
  | some u =>
      cases u with
      | nil => rfl
      | cons b u' =>
          simp only [Option.map_some, relabelWord_cons, consReduced, relabelOutcome]
          by_cases h1 : a.1 = b.1
          · have hf1 : f a.1 = f b.1 := congrArg f h1
            simp only [h1, ↓reduceIte]
            by_cases h2 : a.2 = b.2 <;> simp [h2, relabelWord_cons, relabelOutcome]
          · have hf1 : f a.1 ≠ f b.1 := fun heq => h1 (hf heq)
            simp [h1, hf1, relabelWord_cons, relabelOutcome]

theorem reduceWord_relabel {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {f : ι → κ} (hf : Function.Injective f) (w : Word ι) :
    reduceWord (relabelWord f w) = (reduceWord w).map (relabelWord f) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [relabelWord_cons]
      change consReduced (relabelOutcome f a) (reduceWord (relabelWord f w)) =
        Option.map (relabelWord f) (consReduced a (reduceWord w))
      rw [ih, consReduced_relabel hf]

/-! ## 3. Relation-Ledger Application Generator (`tab:cer:ledger` & `app:cert:count`) -/

/-- A single purity relation application `(t, q, v)` at vector word `t`, base outcome `q`,
and suffix word `v`, requiring the three measured words `(t, q)`, `(t, q, v)`, and
`(t, q, v, purityMirror v, q)` (reduced by `reduceWord`). -/
abbrev PurityApplication := Word (Fin 4) × Outcome (Fin 4) × Word (Fin 4)

namespace PurityApplication

def words (app : PurityApplication) : List (Word (Fin 4)) :=
  let (t, q, v) := app
  let shortW := t ++ [q]
  let midW := shortW ++ v
  let longW := match v with
    | [] => shortW
    | _ :: _ => midW ++ purityMirror v ++ [q]
  [shortW, midW, longW]

end PurityApplication

def r1App (t : Word (Fin 4)) (q b : Fin 4) : PurityApplication :=
  (t, (q, true), [(b, true)])

def r2Apps (t : Word (Fin 4)) (q x y : Fin 4) : List PurityApplication :=
  [(t, (q, true), [(y, true)]),
   (t, (q, true), [(x, true), (y, true)]),
   (t, (q, true), [(x, false), (y, true)])]

def accessSuffixList (i : Fin 4) (w : Word (Fin 4)) : List (Word (Fin 4)) :=
  [w, (i, true) :: w, (i, false) :: w]

def doubleAccessSuffixList (k l m : Fin 4) : List (Word (Fin 4)) :=
  (accessSuffixList l [(m, true)]).flatMap (accessSuffixList k)

def dedupWordList : List (Word (Fin 4)) → List (Word (Fin 4))
  | [] => []
  | w :: ws => if w ∈ ws then dedupWordList ws else w :: dedupWordList ws

def r3SuffixList (k l m : Fin 4) : List (Word (Fin 4)) :=
  dedupWordList
    (doubleAccessSuffixList k l m ++ doubleAccessSuffixList m k l ++ doubleAccessSuffixList l k m)

def r3Apps (t : Word (Fin 4)) (q k l m : Fin 4) : List PurityApplication :=
  (r3SuffixList k l m).map (fun v => (t, (q, true), v))

def cyclicTriples : List (Fin 4 × Fin 4 × Fin 4) :=
  [(1, 2, 3), (2, 3, 1), (3, 1, 2)]

/-- Rows (i) and (ii) of `tab:cer:ledger`: scalar-part `(R2)` at `0` using cyclic `E`
and three `(R1)` unitarity contractions for each ordered distinct pair, over `H₀ ∪ H₁ ∪ H₂`.
Counts: `43 × (3 × 3 + 6 × 3) = 43 × 27 = 1,161` applications. -/
def ledgerRow12Apps : List PurityApplication :=
  prefixes012.flatMap (fun T =>
    cyclicE.flatMap (fun p => r2Apps T 0 p.1 p.2) ++
    distinctPairs.flatMap (fun p =>
      [r1App (T ++ [(p.2, true)]) p.1 0, r1App T p.2 p.1, r1App T 0 p.2]))

/-- Row (iii) of `tab:cer:ledger`: anticommutator contractions `(R1)` and `(R3)` at `0` over
`H₀ ∪ H₁` and all 3 cyclic triples (`2 + 22 = 24` applications per `(T, (k, l, m))`).
Counts: `7 × 3 × 24 = 504` applications. -/
def ledgerRow3Apps : List PurityApplication :=
  prefixes01.flatMap (fun T =>
    cyclicTriples.flatMap (fun c =>
      [r1App (T ++ [(c.1, true)]) c.2.1 0, r1App (T ++ [(c.2.2, true)]) c.2.1 0] ++
      r3Apps T 0 c.1 c.2.1 c.2.2))

/-- Row (iv) of `tab:cer:ledger`: fourth-face contractions (`(R1)` and `(R2)` at `k=1`).
Counts: `4 + 3 + 1 = 8` applications. -/
def ledgerRow4Apps : List PurityApplication :=
  [r1App [(0, true), (1, true)] 3 0,
   r1App [(0, true), (1, true), (3, true)] 2 0,
   r1App [(0, true), (1, true)] 2 0,
   r1App [(0, true), (1, true), (2, true)] 3 0] ++
  r2Apps [(0, true), (1, true)] 1 2 3 ++
  [r1App [(0, true)] 0 1]

/-- Complete relation-ledger application list matching `tab:cer:ledger` and companion `app:cert:count`. -/
def ledgerApplications : List PurityApplication :=
  ledgerRow12Apps ++ ledgerRow3Apps ++ ledgerRow4Apps

/-- Uncompressed `(R3)` variant without intra-triple suffix deduplication (`27` instead of `22`
terms per `(R3)` call, `7 × 3 × 29 = 609` row-(iii) applications, `1,778` total). -/
def ledgerRow3UncompressedApps : List PurityApplication :=
  prefixes01.flatMap (fun T =>
    cyclicTriples.flatMap (fun c =>
      [r1App (T ++ [(c.1, true)]) c.2.1 0, r1App (T ++ [(c.2.2, true)]) c.2.1 0] ++
      (doubleAccessSuffixList c.1 c.2.1 c.2.2 ++ doubleAccessSuffixList c.2.2 c.1 c.2.1 ++
        doubleAccessSuffixList c.2.1 c.1 c.2.2).map (fun v => (T, (0, true), v))))

def ledgerApplicationsUncompressed : List PurityApplication :=
  ledgerRow12Apps ++ ledgerRow3UncompressedApps ++ ledgerRow4Apps

def elevenLedgerRawWords : List (Word (Fin 4)) :=
  (ledgerApplications.flatMap PurityApplication.words).filterMap reduceWord

def elevenLedgerWords : Finset (Word (Fin 4)) :=
  elevenLedgerRawWords.toFinset

theorem ledgerRow12Apps_length : ledgerRow12Apps.length = 1161 := by decide +kernel
theorem ledgerRow3Apps_length : ledgerRow3Apps.length = 504 := by decide +kernel
theorem ledgerRow4Apps_length : ledgerRow4Apps.length = 8 := by decide +kernel
theorem ledgerApplications_length : ledgerApplications.length = 1673 := by decide +kernel
theorem ledgerApplicationsUncompressed_length :
    ledgerApplicationsUncompressed.length = 1778 := by decide +kernel

theorem ledgerApplications_no_contradiction :
    (ledgerApplications.flatMap PurityApplication.words).all
      (fun w => (reduceWord w).isSome) = true := by
  decide +kernel

theorem mem_dedupWordList (w : Word (Fin 4)) (ws : List (Word (Fin 4))) :
    w ∈ dedupWordList ws ↔ w ∈ ws := by
  induction ws with
  | nil => simp [dedupWordList]
  | cons a ws ih =>
      simp only [dedupWordList]
      split_ifs with ha
      · simp only [ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | hw)
          · exact ha
          · exact hw
      · simp only [List.mem_cons, ih]

def ledgerTrie : BinTrie :=
  BinTrie.union
    (BinTrie.union
      (BinTrie.unionMap
        (fun T => BinTrie.ofWordList
          (((cyclicE.flatMap (fun p => r2Apps T 0 p.1 p.2) ++
             distinctPairs.flatMap (fun p =>
               [r1App (T ++ [(p.2, true)]) p.1 0, r1App T p.2 p.1, r1App T 0 p.2])).flatMap
            PurityApplication.words).filterMap reduceWord))
        prefixes012)
      (BinTrie.unionMap
        (fun T => BinTrie.unionMap
          (fun c => BinTrie.ofWordList
            ((([r1App (T ++ [(c.1, true)]) c.2.1 0, r1App (T ++ [(c.2.2, true)]) c.2.1 0] ++
               r3Apps T 0 c.1 c.2.1 c.2.2).flatMap PurityApplication.words).filterMap reduceWord))
          cyclicTriples)
        prefixes01))
    (BinTrie.ofWordList ((ledgerRow4Apps.flatMap PurityApplication.words).filterMap reduceWord))

theorem mem_ledgerTrie (w : Word (Fin 4)) :
    BinTrie.mem (encodeWord w) ledgerTrie = true ↔ w ∈ elevenLedgerRawWords := by
  unfold ledgerTrie elevenLedgerRawWords ledgerApplications
    ledgerRow12Apps ledgerRow3Apps
  simp only [BinTrie.mem_union, Bool.or_eq_true, BinTrie.mem_unionMap,
    BinTrie.mem_ofWordList, List.mem_filterMap, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ((⟨T, hT, u, ⟨app, happ, hu⟩, hred⟩ |
        ⟨T, hT, c, hc, u, ⟨app, happ, hu⟩, hred⟩) |
      ⟨u, ⟨app, happ, hu⟩, hred⟩)
    · exact ⟨u, ⟨app, Or.inl (Or.inl ⟨T, hT, happ⟩), hu⟩, hred⟩
    · exact ⟨u, ⟨app, Or.inl (Or.inr ⟨T, hT, c, hc, happ⟩), hu⟩, hred⟩
    · exact ⟨u, ⟨app, Or.inr happ, hu⟩, hred⟩
  · rintro ⟨u, ⟨app, (⟨T, hT, happ⟩ | ⟨T, hT, c, hc, happ⟩) | happ, hu⟩, hred⟩
    · exact Or.inl (Or.inl ⟨T, hT, u, ⟨app, happ, hu⟩, hred⟩)
    · exact Or.inl (Or.inr ⟨T, hT, c, hc, u, ⟨app, happ, hu⟩, hred⟩)
    · exact Or.inr ⟨u, ⟨app, happ, hu⟩, hred⟩

def elevenListTrie : BinTrie :=
  BinTrie.ofWordListBatched elevenList

theorem mem_elevenListTrie (w : Word (Fin 4)) :
    BinTrie.mem (encodeWord w) elevenListTrie = true ↔ w ∈ elevenList :=
  BinTrie.mem_ofWordListBatched elevenList w

set_option maxRecDepth 8192 in
theorem ledger_binTrie_eq :
    BinTrie.eqBool ledgerTrie elevenListTrie = true := by
  decide +kernel

/-- Exact ledger-language correspondence (`thm:eleven(a)` / `app:cert:count`): the reduced
non-contradictory word set generated by the `1,673` relation-ledger applications equals
`Ends.Eleven.elevenBase` (`2,041` words). -/
theorem elevenLedgerWords_eq_elevenBase : elevenLedgerWords = elevenBase :=
  BinTrie.toFinset_eq_of_eqBool mem_ledgerTrie mem_elevenListTrie
    ledger_binTrie_eq

theorem elevenLedgerUncompressed_eq_elevenBase :
    ((ledgerApplicationsUncompressed.flatMap PurityApplication.words).filterMap
      reduceWord).toFinset = elevenBase := by
  rw [← elevenLedgerWords_eq_elevenBase]
  unfold elevenLedgerWords elevenLedgerRawWords
  ext w
  simp only [List.mem_toFinset, List.mem_filterMap, List.mem_flatMap]
  have happ : ∀ app : PurityApplication,
      app ∈ ledgerApplicationsUncompressed ↔ app ∈ ledgerApplications := by
    intro app
    simp only [ledgerApplicationsUncompressed, ledgerApplications, List.mem_append,
      ledgerRow3UncompressedApps, ledgerRow3Apps, List.mem_flatMap]
    constructor
    · rintro ((h | ⟨T, hT, c, hc, hmem⟩) | h)
      · exact Or.inl (Or.inl h)
      · refine Or.inl (Or.inr ⟨T, hT, c, hc, ?_⟩)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          r3Apps, r3SuffixList, List.mem_map] at hmem ⊢
        rcases hmem with h1 | ⟨v, hv, rfl⟩
        · exact Or.inl h1
        · refine Or.inr ⟨v, (mem_dedupWordList v _).mpr ?_, rfl⟩
          simpa only [List.mem_append] using hv
      · exact Or.inr h
    · rintro ((h | ⟨T, hT, c, hc, hmem⟩) | h)
      · exact Or.inl (Or.inl h)
      · refine Or.inl (Or.inr ⟨T, hT, c, hc, ?_⟩)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          r3Apps, r3SuffixList, List.mem_map] at hmem ⊢
        rcases hmem with h1 | ⟨v, hv, rfl⟩
        · exact Or.inl h1
        · refine Or.inr ⟨v, ?_, rfl⟩
          simpa only [List.mem_append] using (mem_dedupWordList v _).mp hv
      · exact Or.inr h
  constructor
  · rintro ⟨u, ⟨app, hap, hu⟩, hred⟩
    exact ⟨u, ⟨app, (happ app).mp hap, hu⟩, hred⟩
  · rintro ⟨u, ⟨app, hap, hu⟩, hred⟩
    exact ⟨u, ⟨app, (happ app).mpr hap, hu⟩, hred⟩

theorem yes0_mem_elevenBase : [(0, true)] ∈ elevenBase := by
  refine List.mem_toFinset.mpr ?_
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_flatMap.mpr ⟨[yes 0], List.mem_append_left _ (List.mem_cons_self),
    List.mem_map.mpr ⟨[], List.mem_cons_self, rfl⟩⟩

theorem norm_xi_mem_elevenLedgerWords : [(0, true)] ∈ elevenLedgerWords := by
  rw [elevenLedgerWords_eq_elevenBase]
  exact yes0_mem_elevenBase

/-! ## 4. Computable Inclusion Check for `cornerResidualTelescopeOccurrences` -/

def leafTemplateWords (hp : Word (Fin 4)) (o : Outcome (Fin 4)) (suf : Word (Fin 4)) :
    List (Word (Fin 4)) :=
  let hist := hp ++ [o]
  let mid := hist ++ suf
  let long := match suf with
    | [] => hist
    | _ :: _ => mid ++ purityMirror suf ++ [o]
  [hist, mid, long]

def leafTemplateWordsFromHist (hist : Word (Fin 4)) (o : Outcome (Fin 4)) (suf : Word (Fin 4)) :
    List (Word (Fin 4)) :=
  let mid := hist ++ suf
  let long := match suf with
    | [] => hist
    | _ :: _ => mid ++ purityMirror suf ++ [o]
  [hist, mid, long]

def faceFirstFin : Fin 3 → Fin 4 := ![1, 2, 3]
def faceSecondFin : Fin 3 → Fin 4 := ![2, 3, 1]
def faceThirdFin : Fin 3 → Fin 4 := ![3, 1, 2]

def hermitianTemplateWords : List (Word (Fin 4)) :=
  prefixes012.flatMap (fun T =>
    ([0, 1, 2] : List (Fin 3)).flatMap (fun i =>
      (accessSuffixList (faceFirstFin i) [(faceSecondFin i, true)]).flatMap
        (leafTemplateWordsFromHist T (0, true))))

def reverseProductTemplateWords : List (Word (Fin 4)) :=
  prefixes012.flatMap (fun T =>
    distinctPairs.flatMap (fun p =>
      leafTemplateWords (T ++ [(p.2, true)]) (p.1, true) [(0, true)] ++
      leafTemplateWords T (p.2, true) [(p.1, true)] ++
      leafTemplateWordsFromHist T (0, true) [(p.2, true)]))

def mixedTemplateWords : List (Word (Fin 4)) :=
  prefixes01.flatMap (fun T =>
    ([0, 1, 2] : List (Fin 3)).flatMap (fun i =>
      leafTemplateWords (T ++ [(faceThirdFin i, true)]) (faceSecondFin i, true) [(0, true)] ++
      leafTemplateWords (T ++ [(faceFirstFin i, true)]) (faceSecondFin i, true) [(0, true)] ++
      (doubleAccessSuffixList (faceFirstFin i) (faceSecondFin i) (faceThirdFin i) ++
        doubleAccessSuffixList (faceThirdFin i) (faceFirstFin i) (faceSecondFin i) ++
        doubleAccessSuffixList (faceSecondFin i) (faceFirstFin i) (faceThirdFin i)).flatMap
        (leafTemplateWordsFromHist T (0, true))))

def cubicTemplateWords : List (Word (Fin 4)) :=
  leafTemplateWords [(0, true), (1, true)] (3, true) [(0, true)] ++
  leafTemplateWords [(0, true), (1, true), (3, true)] (2, true) [(0, true)] ++
  leafTemplateWords [(0, true), (1, true)] (2, true) [(0, true)] ++
  leafTemplateWords [(0, true), (1, true), (2, true)] (3, true) [(0, true)] ++
  (accessSuffixList 2 [(3, true)]).flatMap (leafTemplateWords [(0, true)] (1, true)) ++
  leafTemplateWordsFromHist [(0, true)] (0, true) [(1, true)]

def telescopeTemplateWords : List (Word (Fin 4)) :=
  hermitianTemplateWords ++ reverseProductTemplateWords ++ mixedTemplateWords ++ cubicTemplateWords

def telescopeTrie : BinTrie :=
  BinTrie.union
    (BinTrie.union
      (BinTrie.unionMap
        (fun T => BinTrie.ofWordList
          (([0, 1, 2] : List (Fin 3)).flatMap (fun i =>
            (accessSuffixList (faceFirstFin i) [(faceSecondFin i, true)]).flatMap
              (leafTemplateWordsFromHist T (0, true)))))
        prefixes012)
      (BinTrie.unionMap
        (fun T => BinTrie.ofWordList
          (distinctPairs.flatMap (fun p =>
            leafTemplateWords (T ++ [(p.2, true)]) (p.1, true) [(0, true)] ++
            leafTemplateWords T (p.2, true) [(p.1, true)] ++
            leafTemplateWordsFromHist T (0, true) [(p.2, true)])))
        prefixes012))
    (BinTrie.union
      (BinTrie.unionMap
        (fun T => BinTrie.ofWordList
          (([0, 1, 2] : List (Fin 3)).flatMap (fun i =>
            leafTemplateWords (T ++ [(faceThirdFin i, true)]) (faceSecondFin i, true) [(0, true)] ++
            leafTemplateWords (T ++ [(faceFirstFin i, true)]) (faceSecondFin i, true) [(0, true)] ++
            (doubleAccessSuffixList (faceFirstFin i) (faceSecondFin i) (faceThirdFin i) ++
              doubleAccessSuffixList (faceThirdFin i) (faceFirstFin i) (faceSecondFin i) ++
              doubleAccessSuffixList (faceSecondFin i) (faceFirstFin i) (faceThirdFin i)).flatMap
              (leafTemplateWordsFromHist T (0, true)))))
        prefixes01)
      (BinTrie.ofWordList cubicTemplateWords))

theorem mem_telescopeTrie (w : Word (Fin 4)) :
    BinTrie.mem (encodeWord w) telescopeTrie = true ↔ w ∈ telescopeTemplateWords := by
  unfold telescopeTrie telescopeTemplateWords
    hermitianTemplateWords reverseProductTemplateWords mixedTemplateWords
  simp only [BinTrie.mem_union, Bool.or_eq_true, BinTrie.mem_unionMap,
    BinTrie.mem_ofWordList, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ((⟨T, hT, hw⟩ | ⟨T, hT, hw⟩) | (⟨T, hT, hw⟩ | hw))
    · exact Or.inl (Or.inl (Or.inl ⟨T, hT, hw⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨T, hT, hw⟩))
    · exact Or.inl (Or.inr ⟨T, hT, hw⟩)
    · exact Or.inr hw
  · rintro (((⟨T, hT, hw⟩ | ⟨T, hT, hw⟩) | ⟨T, hT, hw⟩) | hw)
    · exact Or.inl (Or.inl ⟨T, hT, hw⟩)
    · exact Or.inl (Or.inr ⟨T, hT, hw⟩)
    · exact Or.inr (Or.inl ⟨T, hT, hw⟩)
    · exact Or.inr (Or.inr hw)

set_option maxRecDepth 8192 in
theorem telescopeTemplateWords_sub_binTrie :
    BinTrie.subBool telescopeTrie elevenListTrie = true := by
  decide +kernel

theorem telescopeTemplateWords_mem_elevenBase {w : Word (Fin 4)}
    (hw : w ∈ telescopeTemplateWords) : w ∈ elevenBase :=
  BinTrie.mem_toFinset_of_subBool mem_telescopeTrie mem_elevenListTrie
    telescopeTemplateWords_sub_binTrie hw

/-! ## 5. Preservation of Algebraic and Native Probabilities & Functional Reduction -/

noncomputable section

theorem reduceWord_wordAmplitude {ι A : Type*} [DecidableEq ι] [Ring A]
    (P : ι → A) (hp : ∀ i, P i * P i = P i) (w : Word ι) :
    wordAmplitude P w =
      match reduceWord w with
      | none => 0
      | some v => wordAmplitude P v := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [wordAmplitude_cons, ih, reduceWord]
      cases ho : reduceWord w with
      | none =>
          simp only [consReduced, zero_mul]
      | some u =>
          cases u with
          | nil =>
              simp only [consReduced, wordAmplitude_nil, one_mul, wordAmplitude_singleton]
          | cons b u' =>
              simp only [consReduced]
              by_cases h1 : a.1 = b.1
              · simp only [h1, ↓reduceIte]
                by_cases h2 : a.2 = b.2
                · simp only [h2, ↓reduceIte]
                  have hab : a = b := Prod.ext h1 h2
                  rw [hab, wordAmplitude_cons, mul_assoc, algebraicOutcome_idempotent P hp b]
                · simp only [h2, ↓reduceIte]
                  rcases a with ⟨ia, sa⟩
                  rcases b with ⟨ib, sb⟩
                  dsimp only at h1 h2
                  subst h1
                  have hneg : sa = !sb := by cases sa <;> cases sb <;> simp_all
                  subst hneg
                  have hopp : algebraicOutcome P (ia, sb) * algebraicOutcome P (ia, !sb) = 0 := by
                    simpa only [Bool.not_not] using algebraicOutcome_opposite_mul P hp ia (!sb)
                  rw [wordAmplitude_cons, mul_assoc, hopp, mul_zero]
              · simp only [h1, ↓reduceIte, wordAmplitude_cons]

theorem reduceWord_wordOperator {ι A : Type*} [DecidableEq ι] [Ring A] [StarRing A]
    (P : ι → A) (hp : ∀ i, P i * P i = P i) (w : Word ι) :
    wordOperator P w =
      match reduceWord w with
      | none => 0
      | some v => wordOperator P v := by
  simp only [wordOperator, reduceWord_wordAmplitude P hp w]
  cases reduceWord w with
  | none => simp
  | some v => rfl

theorem reduceWord_probability {ι A : Type*} [DecidableEq ι]
    [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    M.probability w =
      match reduceWord w with
      | none => 0
      | some v => M.probability v := by
  unfold AlgebraicProjectiveData.probability
  rw [reduceWord_wordOperator M.projection M.idempotent w]
  cases reduceWord w with
  | none => exact map_zero M.state
  | some v => rfl

open NativeAnalysis in
theorem quadraticMap_complement_comp_idem (q x : Albert) (hq : jordanMul q q = q) :
    quadraticMap (albertUnit - q) (quadraticMap q x) = 0 := by
  have h1 : jordanMul q (quadraticMap q x) = quadraticMap q x :=
    native_idempotent_quadratic_mem_one q x hq
  have h2 : quadraticMap q (quadraticMap q x) = quadraticMap q x :=
    quadraticMap_idempotent_comp q x hq
  rw [quadraticMap_complement, h1, h2, two_smul]
  abel

open NativeAnalysis in
theorem quadraticMap_idem_comp_complement (q x : Albert) (hq : jordanMul q q = q) :
    quadraticMap q (quadraticMap (albertUnit - q) x) = 0 := by
  have hq' := complementary_idempotent q hq
  have h := quadraticMap_complement_comp_idem (albertUnit - q) x hq'
  have heq : albertUnit - (albertUnit - q) = q := by abel
  rwa [heq] at h

open NativeAnalysis in
theorem quadraticMap_nativeOutcome_opposite {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (i : ι) (s t : Bool) (hst : s ≠ t) (x : Albert) :
    quadraticMap (nativeOutcome p (i, s)) (quadraticMap (nativeOutcome p (i, t)) x) = 0 := by
  cases s <;> cases t
  · exact absurd rfl hst
  · simpa only [nativeOutcome, Bool.false_eq_true, ↓reduceIte] using
      quadraticMap_complement_comp_idem (p i) x (hp i)
  · simpa only [nativeOutcome, Bool.false_eq_true, ↓reduceIte] using
      quadraticMap_idem_comp_complement (p i) x (hp i)
  · exact absurd rfl hst

open NativeAnalysis in
theorem reduceWord_nativeWordEffect {ι : Type*} [DecidableEq ι] (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (w : Word ι) :
    nativeWordEffect p w =
      match reduceWord w with
      | none => 0
      | some v => nativeWordEffect p v := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change quadraticMap (nativeOutcome p a) (nativeWordEffect p w) = _
      rw [ih, reduceWord]
      cases ho : reduceWord w with
      | none =>
          simp only [consReduced, quadraticMap_zero_right]
      | some u =>
          cases u with
          | nil => rfl
          | cons b u' =>
              simp only [consReduced]
              by_cases h1 : a.1 = b.1
              · simp only [h1, ↓reduceIte]
                by_cases h2 : a.2 = b.2
                · simp only [h2, ↓reduceIte]
                  have hab : a = b := Prod.ext h1 h2
                  rw [hab]
                  exact quadraticMap_idempotent_comp _ _ (nativeOutcome_idempotent p hp b)
                · simp only [h2, ↓reduceIte]
                  rcases a with ⟨ia, sa⟩
                  rcases b with ⟨ib, sb⟩
                  dsimp only at h1 h2
                  subst h1
                  exact quadraticMap_nativeOutcome_opposite p hp ia sa sb h2 _
              · simp only [h1, ↓reduceIte]
                rfl

open NativeAnalysis in
theorem reduceWord_nativeWordProbability {ι : Type*} [DecidableEq ι] (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (ρ : Albert) (w : Word ι) :
    nativeWordProbability p ρ w =
      match reduceWord w with
      | none => 0
      | some v => nativeWordProbability p ρ v := by
  rw [nativeWordProbability_eq_pairing, reduceWord_nativeWordEffect p hp w]
  cases reduceWord w with
  | none =>
      unfold tracePairing
      rw [jordanMul_zero_right, albertTrace_zero]
  | some v =>
      exact (nativeWordProbability_eq_pairing p ρ v).symm

theorem reduceWord_nativeWordProbability_atoms {ι : Type*} [DecidableEq ι] (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (w : Word ι) :
    nativeWordProbability p ρ w =
      match reduceWord w with
      | none => 0
      | some v => nativeWordProbability p ρ v :=
  reduceWord_nativeWordProbability p (fun i => (hp i).1) ρ w

/-! ### Canonical Functional Reduction -/

open Classical in
/-- Insert `(r, v)` into an already deduplicated list of reduced-word terms, combining
coefficients on matching words and dropping exact zeros. -/
def addReducedTerm (r : ℝ) (v : Word (Fin 4)) :
    List (ℝ × Word (Fin 4)) → List (ℝ × Word (Fin 4))
  | [] => if r = 0 then [] else [(r, v)]
  | (s, u) :: ts =>
      if u = v then
        if r + s = 0 then ts else (r + s, u) :: ts
      else
        (s, u) :: addReducedTerm r v ts

/-- Canonical reduced-word list obtained by reducing each term via `reduceWord`, dropping
contradictory (`none`) terms, and merging duplicate reduced words. -/
def mergeReducedTerms : List (ℝ × Word (Fin 4)) → List (ℝ × Word (Fin 4))
  | [] => []
  | (r, w) :: ts =>
      match reduceWord w with
      | none => mergeReducedTerms ts
      | some v => addReducedTerm r v (mergeReducedTerms ts)

/-- Canonical reduction of `Λ : FiniteRealWordFunctional 4` onto reduced non-contradictory
words with merged duplicate words and zero-coefficient elimination. -/
def reduceFunctional (Λ : FiniteRealWordFunctional 4) : FiniteRealWordFunctional 4 where
  terms := mergeReducedTerms Λ.terms

open Classical in
def coeffReduce (f : Word (Fin 4) →₀ ℝ) : Word (Fin 4) →₀ ℝ :=
  f.sum (fun w c => match reduceWord w with | none => 0 | some v => Finsupp.single v c)

theorem coeffReduce_add (f g : Word (Fin 4) →₀ ℝ) :
    coeffReduce (f + g) = coeffReduce f + coeffReduce g := by
  classical
  unfold coeffReduce
  refine Finsupp.sum_add_index' ?_ ?_
  · intro w
    cases reduceWord w <;> simp
  · intro w a b
    cases reduceWord w with
    | none => simp
    | some v => simp [Finsupp.single_add]

theorem coeffReduce_single (w : Word (Fin 4)) (r : ℝ) :
    coeffReduce (Finsupp.single w r) =
      match reduceWord w with | none => 0 | some v => Finsupp.single v r := by
  classical
  unfold coeffReduce
  refine Finsupp.sum_single_index ?_
  cases reduceWord w <;> simp

theorem coefficientsOfTerms_addReducedTerm (r : ℝ) (v : Word (Fin 4))
    (ts : List (ℝ × Word (Fin 4))) :
    FiniteRealWordFunctional.coefficientsOfTerms (addReducedTerm r v ts) =
      Finsupp.single v r + FiniteRealWordFunctional.coefficientsOfTerms ts := by
  classical
  induction ts with
  | nil =>
      simp only [addReducedTerm]
      by_cases hr : r = 0
      · subst hr
        simp [FiniteRealWordFunctional.coefficientsOfTerms_nil]
      · simp [hr, FiniteRealWordFunctional.coefficientsOfTerms_cons,
          FiniteRealWordFunctional.coefficientsOfTerms_nil]
  | cons t ts ih =>
      rcases t with ⟨s, u⟩
      simp only [addReducedTerm]
      by_cases huv : u = v
      · subst huv
        simp only [↓reduceIte]
        by_cases hrs : r + s = 0
        · simp only [hrs, ↓reduceIte, FiniteRealWordFunctional.coefficientsOfTerms_cons]
          rw [← add_assoc, ← Finsupp.single_add, hrs, Finsupp.single_zero, zero_add]
        · simp only [hrs, ↓reduceIte, FiniteRealWordFunctional.coefficientsOfTerms_cons]
          rw [← add_assoc, ← Finsupp.single_add]
      · simp only [huv, ↓reduceIte, FiniteRealWordFunctional.coefficientsOfTerms_cons, ih]
        abel

theorem coefficientsOfTerms_mergeReducedTerms (ts : List (ℝ × Word (Fin 4))) :
    FiniteRealWordFunctional.coefficientsOfTerms (mergeReducedTerms ts) =
      coeffReduce (FiniteRealWordFunctional.coefficientsOfTerms ts) := by
  induction ts with
  | nil =>
      simp [mergeReducedTerms, FiniteRealWordFunctional.coefficientsOfTerms_nil, coeffReduce]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      simp only [mergeReducedTerms, FiniteRealWordFunctional.coefficientsOfTerms_cons,
        coeffReduce_add, coeffReduce_single]
      cases hw : reduceWord w with
      | none => simp [ih]
      | some v => simp [coefficientsOfTerms_addReducedTerm, ih]

theorem reduceFunctional_coefficients (Λ : FiniteRealWordFunctional 4) :
    (reduceFunctional Λ).coefficients = coeffReduce Λ.coefficients :=
  coefficientsOfTerms_mergeReducedTerms Λ.terms

theorem evaluateTerms_addReducedTerm (r : ℝ) (v : Word (Fin 4))
    (ts : List (ℝ × Word (Fin 4))) (g : Word (Fin 4) → ℝ) :
    ((addReducedTerm r v ts).map (fun t => t.1 * g t.2)).sum =
      r * g v + (ts.map (fun t => t.1 * g t.2)).sum := by
  classical
  induction ts with
  | nil =>
      simp only [addReducedTerm]
      by_cases hr : r = 0
      · subst hr; simp
      · simp [hr]
  | cons t ts ih =>
      rcases t with ⟨s, u⟩
      simp only [addReducedTerm]
      by_cases huv : u = v
      · subst huv
        simp only [↓reduceIte]
        by_cases hrs : r + s = 0
        · simp only [hrs, ↓reduceIte, List.map_cons, List.sum_cons]
          linear_combination -hrs * g u
        · simp only [hrs, ↓reduceIte, List.map_cons, List.sum_cons]
          ring
      · simp only [huv, ↓reduceIte, List.map_cons, List.sum_cons, ih]
        ring

theorem reduceFunctional_evaluate_of_invariant (Λ : FiniteRealWordFunctional 4)
    (g : Word (Fin 4) → ℝ)
    (hg : ∀ w, g w = Option.elim (reduceWord w) 0 g) :
    (reduceFunctional Λ).evaluate g = Λ.evaluate g := by
  change ((mergeReducedTerms Λ.terms).map (fun t => t.1 * g t.2)).sum =
    (Λ.terms.map (fun t => t.1 * g t.2)).sum
  induction Λ.terms with
  | nil => rfl
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      simp only [mergeReducedTerms, List.map_cons, List.sum_cons]
      have hgw := hg w
      cases hw : reduceWord w with
      | none =>
          rw [hw] at hgw
          simp only [Option.elim_none] at hgw
          simp only [hgw, mul_zero, zero_add, ih]
      | some v =>
          rw [hw] at hgw
          simp only [Option.elim_some] at hgw
          simp only [evaluateTerms_addReducedTerm, ih, hgw]

theorem reduceFunctional_evaluate_probability
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (Λ : FiniteRealWordFunctional 4) (M : AlgebraicProjectiveData (Fin 4) A) :
    (reduceFunctional Λ).evaluate M.probability = Λ.evaluate M.probability := by
  apply reduceFunctional_evaluate_of_invariant
  intro w
  have h := reduceWord_probability M w
  cases hred : reduceWord w with
  | none => simpa [hred] using h
  | some v => simpa [hred] using h

theorem reduceFunctional_evaluate_native (Λ : FiniteRealWordFunctional 4)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) :
    (reduceFunctional Λ).evaluate (nativeWordProbability p ρ) =
      Λ.evaluate (nativeWordProbability p ρ) := by
  apply reduceFunctional_evaluate_of_invariant
  intro w
  have h := reduceWord_nativeWordProbability_atoms p hp ρ w
  cases hred : reduceWord w with
  | none => simpa [hred] using h
  | some v => simpa [hred] using h

theorem coefficientAbsSum_finset_sum_le {ι : Type*} (s : Finset ι)
    (h : ι → Word (Fin 4) →₀ ℝ) :
    FiniteRealWordFunctional.coefficientAbsSum (∑ i ∈ s, h i) ≤
      ∑ i ∈ s, FiniteRealWordFunctional.coefficientAbsSum (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FiniteRealWordFunctional.coefficientAbsSum]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (FiniteRealWordFunctional.coefficientAbsSum_add_le _ _).trans
        (add_le_add le_rfl ih)

theorem reduceFunctional_coefficientNorm_le (Λ : FiniteRealWordFunctional 4) :
    (reduceFunctional Λ).coefficientNorm ≤ Λ.coefficientNorm := by
  classical
  unfold FiniteRealWordFunctional.coefficientNorm
  rw [reduceFunctional_coefficients]
  unfold coeffReduce Finsupp.sum
  calc
    FiniteRealWordFunctional.coefficientAbsSum
        (∑ w ∈ Λ.coefficients.support,
          match reduceWord w with | none => 0 | some v => Finsupp.single v (Λ.coefficients w))
      ≤ ∑ w ∈ Λ.coefficients.support,
          FiniteRealWordFunctional.coefficientAbsSum
            (match reduceWord w with | none => 0 | some v => Finsupp.single v (Λ.coefficients w)) :=
        coefficientAbsSum_finset_sum_le _ _
    _ ≤ ∑ w ∈ Λ.coefficients.support, |Λ.coefficients w| := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        cases reduceWord w with
        | none =>
            simp [FiniteRealWordFunctional.coefficientAbsSum]
        | some v =>
            rw [FiniteRealWordFunctional.coefficientAbsSum_single]
    _ = FiniteRealWordFunctional.coefficientAbsSum Λ.coefficients := rfl

private def WellFormedReducedTerms (ts : List (ℝ × Word (Fin 4))) : Prop :=
  (∀ t ∈ ts, IsReducedWord t.2 ∧ t.1 ≠ 0) ∧ (ts.map Prod.snd).Nodup

private theorem addReducedTerm_word_mem (r : ℝ) (v : Word (Fin 4))
    (ts : List (ℝ × Word (Fin 4))) {x : Word (Fin 4)}
    (hx : x ∈ (addReducedTerm r v ts).map Prod.snd) :
    x = v ∨ x ∈ ts.map Prod.snd := by
  classical
  induction ts with
  | nil =>
      simp only [addReducedTerm] at hx
      by_cases hr : r = 0
      · simp [hr] at hx
      · simp only [hr, ↓reduceIte, List.map_cons, List.map_nil, List.mem_singleton] at hx
        exact Or.inl hx
  | cons t ts ih =>
      rcases t with ⟨s, u⟩
      simp only [addReducedTerm] at hx
      by_cases huv : u = v
      · subst huv
        simp only [↓reduceIte] at hx
        by_cases hrs : r + s = 0
        · simp only [hrs, ↓reduceIte, List.mem_map, Prod.exists] at hx
          rcases hx with ⟨c, w, hw, rfl⟩
          exact Or.inr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(c, w), hw, rfl⟩))
        · simp only [hrs, ↓reduceIte, List.map_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hx)
      · simp only [huv, ↓reduceIte, List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr (List.mem_cons_self)
        · rcases ih hx with rfl | hx'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hx')

private theorem wellFormed_addReducedTerm (r : ℝ) (v : Word (Fin 4)) (hv : IsReducedWord v)
    (ts : List (ℝ × Word (Fin 4))) (hts : WellFormedReducedTerms ts) :
    WellFormedReducedTerms (addReducedTerm r v ts) := by
  classical
  induction ts with
  | nil =>
      simp only [addReducedTerm]
      by_cases hr : r = 0
      · simp [hr, WellFormedReducedTerms]
      · simp [hr, WellFormedReducedTerms, hv]
  | cons t ts ih =>
      rcases t with ⟨s, u⟩
      rcases hts with ⟨hall, hnodup⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hts' : WellFormedReducedTerms ts :=
        ⟨fun x hx => hall x (List.mem_cons_of_mem _ hx), hnodup.2⟩
      have hu := hall (s, u) List.mem_cons_self
      simp only [addReducedTerm]
      by_cases huv : u = v
      · subst huv
        simp only [↓reduceIte]
        by_cases hrs : r + s = 0
        · simp only [hrs, ↓reduceIte]
          exact hts'
        · simp only [hrs, ↓reduceIte]
          refine ⟨fun x hx => ?_, ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨hu.1, hrs⟩
            · exact hts'.1 x hx
          · simp only [List.map_cons, List.nodup_cons]
            exact hnodup
      · simp only [huv, ↓reduceIte]
        have ih' := ih hts'
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hu
          · exact ih'.1 x hx
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨fun hum => ?_, ih'.2⟩
          rcases addReducedTerm_word_mem r v ts hum with rfl | hum'
          · exact huv rfl
          · exact hnodup.1 hum'

private theorem wellFormed_mergeReducedTerms (ts : List (ℝ × Word (Fin 4))) :
    WellFormedReducedTerms (mergeReducedTerms ts) := by
  induction ts with
  | nil => simp [mergeReducedTerms, WellFormedReducedTerms]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      simp only [mergeReducedTerms]
      cases hw : reduceWord w with
      | none => exact ih
      | some v => exact wellFormed_addReducedTerm r v (reduceWord_isReduced hw) _ ih

private theorem coeff_eq_of_wellFormed {ts : List (ℝ × Word (Fin 4))}
    (hts : WellFormedReducedTerms ts) {t : ℝ × Word (Fin 4)} (ht : t ∈ ts) :
    FiniteRealWordFunctional.coefficientsOfTerms ts t.2 = t.1 := by
  classical
  induction ts with
  | nil => cases ht
  | cons a ts ih =>
      rcases a with ⟨s, u⟩
      rcases hts with ⟨hall, hnodup⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hts' : WellFormedReducedTerms ts :=
        ⟨fun x hx => hall x (List.mem_cons_of_mem _ hx), hnodup.2⟩
      rw [FiniteRealWordFunctional.coefficientsOfTerms_cons, Finsupp.add_apply]
      rcases List.mem_cons.mp ht with hhead | ht'
      · rw [hhead]
        have habsent : FiniteRealWordFunctional.coefficientsOfTerms ts u = 0 := by
          apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
          intro x hx hxw
          exact hnodup.1 (hxw ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
        rw [habsent, add_zero, Finsupp.single_eq_same]
      · have hne : u ≠ t.2 := by
          intro heq
          apply hnodup.1
          exact heq ▸ List.mem_map.mpr ⟨t, ht', rfl⟩
        rw [Finsupp.single_eq_of_ne (Ne.symm hne), zero_add]
        exact ih hts' ht'

theorem reduceFunctional_terms_reduced (Λ : FiniteRealWordFunctional 4) :
    ∀ t ∈ (reduceFunctional Λ).terms, IsReducedWord t.2 :=
  fun t ht => ((wellFormed_mergeReducedTerms Λ.terms).1 t ht).1

theorem reduceFunctional_terms_nonzero (Λ : FiniteRealWordFunctional 4) :
    ∀ t ∈ (reduceFunctional Λ).terms, t.1 ≠ 0 :=
  fun t ht => ((wellFormed_mergeReducedTerms Λ.terms).1 t ht).2

theorem reduceFunctional_terms_nodup (Λ : FiniteRealWordFunctional 4) :
    ((reduceFunctional Λ).terms.map Prod.snd).Nodup :=
  (wellFormed_mergeReducedTerms Λ.terms).2

theorem reduceFunctional_terms_mem_support (Λ : FiniteRealWordFunctional 4) :
    ∀ t ∈ (reduceFunctional Λ).terms, t.2 ∈ (reduceFunctional Λ).coefficients.support := by
  intro t ht
  rw [Finsupp.mem_support_iff, FiniteRealWordFunctional.coefficients]
  change FiniteRealWordFunctional.coefficientsOfTerms (mergeReducedTerms Λ.terms) t.2 ≠ 0
  rw [coeff_eq_of_wellFormed (wellFormed_mergeReducedTerms Λ.terms) ht]
  exact reduceFunctional_terms_nonzero Λ t ht

theorem reduceFunctional_support_subset (Λ : FiniteRealWordFunctional 4) :
    ∀ v ∈ (reduceFunctional Λ).coefficients.support,
      IsReducedWord v ∧ ∃ w ∈ Λ.coefficients.support, reduceWord w = some v := by
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, reduceFunctional_coefficients] at hv
  unfold coeffReduce Finsupp.sum at hv
  have hex : ∃ w ∈ Λ.coefficients.support,
      (match reduceWord w with | none => (0 : Word (Fin 4) →₀ ℝ) | some u => Finsupp.single u (Λ.coefficients w)) v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero hall
  rcases hex with ⟨w, hw, hne⟩
  cases hred : reduceWord w with
  | none =>
      simp [hred] at hne
  | some u =>
      rw [hred] at hne
      have huv : u = v := by
        by_contra hne_uv
        exact hne (Finsupp.single_eq_of_ne (Ne.symm hne_uv))
      subst huv
      exact ⟨reduceWord_isReduced hred, w, hw, hred⟩

theorem reduceFunctional_terms_in_reduced_image (Λ : FiniteRealWordFunctional 4) :
    ∀ t ∈ (reduceFunctional Λ).terms,
      IsReducedWord t.2 ∧ ∃ w ∈ Λ.coefficients.support, reduceWord w = some t.2 :=
  fun t ht => reduceFunctional_support_subset Λ t.2 (reduceFunctional_terms_mem_support Λ t ht)

theorem reduceFunctional_rawCoefficientBound_eq (Λ : FiniteRealWordFunctional 4) :
    (reduceFunctional Λ).rawCoefficientBound = (reduceFunctional Λ).coefficientNorm := by
  classical
  have hwf := wellFormed_mergeReducedTerms Λ.terms
  have hsum : ∀ (ts : List (ℝ × Word (Fin 4))),
      WellFormedReducedTerms ts →
      wordAmplitudeCoefficientBound ts =
        FiniteRealWordFunctional.coefficientAbsSum (FiniteRealWordFunctional.coefficientsOfTerms ts) := by
    intro ts hts
    induction ts with
    | nil =>
        simp [wordAmplitudeCoefficientBound, FiniteRealWordFunctional.coefficientAbsSum,
          FiniteRealWordFunctional.coefficientsOfTerms_nil]
    | cons a ts ih =>
        rcases a with ⟨s, u⟩
        rcases hts with ⟨hall, hnodup⟩
        simp only [List.map_cons, List.nodup_cons] at hnodup
        have hts' : WellFormedReducedTerms ts :=
          ⟨fun x hx => hall x (List.mem_cons_of_mem _ hx), hnodup.2⟩
        rw [wordAmplitudeCoefficientBound_cons, ih hts',
          FiniteRealWordFunctional.coefficientsOfTerms_cons]
        have hu_abs : FiniteRealWordFunctional.coefficientsOfTerms ts u = 0 := by
          apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
          intro x hx hxu
          exact hnodup.1 (hxu ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
        have hdisj : Disjoint (Finsupp.single u s).support
            (FiniteRealWordFunctional.coefficientsOfTerms ts).support := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          have hwu : w = u := Finsupp.support_single_subset hw1 |> Finset.mem_singleton.mp
          rw [hwu, Finsupp.mem_support_iff] at hw2
          exact hw2 hu_abs
        unfold FiniteRealWordFunctional.coefficientAbsSum
        rw [Finsupp.sum_add_index_of_disjoint hdisj,
          Finsupp.sum_single_index (h := fun _ r => |r|) abs_zero]
  exact hsum (reduceFunctional Λ).terms hwf

/-! ## 6. Four-Base Relabelled Union `elevenUnion` (`8,164` words) -/

/-- Label permutation exchanging base `0` (`A`) with `j : Fin 4`. -/
def swapBase (j : Fin 4) : Equiv.Perm (Fin 4) := Equiv.swap 0 j

/-- The 2,041-word family `𝓕_j` obtained by swapping labels `0` and `j` in `elevenBase`. -/
def elevenFamily (j : Fin 4) : Finset (Word (Fin 4)) :=
  elevenBase.image (relabelWord (swapBase j))

/-- The 8,164-word four-base union `𝓕 = 𝓕_A ∪ 𝓕_B ∪ 𝓕_C ∪ 𝓕_D`. -/
def elevenUnion : Finset (Word (Fin 4)) :=
  Finset.univ.biUnion elevenFamily

theorem relabelOutcome_injective {ι κ : Type*} {f : ι → κ} (hf : Function.Injective f) :
    Function.Injective (relabelOutcome f) := by
  intro a b hab
  rcases a with ⟨ia, ba⟩
  rcases b with ⟨ib, bb⟩
  simp only [relabelOutcome, Prod.mk.injEq] at hab
  exact Prod.ext (hf hab.1) hab.2

theorem relabelWord_injective {ι κ : Type*} {f : ι → κ} (hf : Function.Injective f) :
    Function.Injective (relabelWord f) :=
  List.map_injective_iff.mpr (relabelOutcome_injective hf)

theorem isReducedWord_relabel {ι κ : Type*} {f : ι → κ} (hf : Function.Injective f) :
    ∀ {w : Word ι}, IsReducedWord w → IsReducedWord (relabelWord f w)
  | [], _ => trivial
  | [_], _ => trivial
  | _a :: _b :: _w, h =>
      ⟨fun heq => h.1 (hf heq), isReducedWord_relabel hf h.2⟩

theorem relabelWord_id {ι : Type*} (w : Word ι) : relabelWord id w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [relabelWord_cons, ih]
      rfl

theorem elevenFamily_zero : elevenFamily 0 = elevenBase := by
  unfold elevenFamily swapBase
  rw [Equiv.swap_self]
  ext w
  simp [relabelWord_id]

theorem elevenFamily_card (j : Fin 4) : (elevenFamily j).card = 2041 := by
  unfold elevenFamily
  rw [Finset.card_image_of_injective _ (relabelWord_injective (swapBase j).injective)]
  exact elevenBase_card

theorem elevenFamily_shape (j : Fin 4) {w : Word (Fin 4)} (hw : w ∈ elevenFamily j) :
    IsReducedWord w ∧ w.head? = some (j, true) ∧ w.length ≤ 11 := by
  rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
  obtain ⟨hred, hhead, hlen⟩ := elevenBase_shape u hu
  refine ⟨isReducedWord_relabel (swapBase j).injective hred, ?_, ?_⟩
  · cases u with
    | nil => simp at hhead
    | cons _ _ =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        rw [hhead, relabelWord_cons, relabelOutcome]
        simp [swapBase]
  · simpa only [relabelWord_length] using hlen

theorem elevenFamily_disjoint {j₁ j₂ : Fin 4} (h : j₁ ≠ j₂) :
    Disjoint (elevenFamily j₁) (elevenFamily j₂) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  have h1 := (elevenFamily_shape j₁ hw1).2.1
  have h2 := (elevenFamily_shape j₂ hw2).2.1
  rw [h1, Option.some.injEq, Prod.mk.injEq] at h2
  exact h h2.1

theorem elevenUnion_card : elevenUnion.card = 8164 := by
  unfold elevenUnion
  rw [Finset.card_biUnion (fun j₁ _ j₂ _ hij => elevenFamily_disjoint hij)]
  simp only [elevenFamily_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem relabelWord_mem_elevenFamily (j : Fin 4) {w : Word (Fin 4)} (hw : w ∈ elevenBase) :
    relabelWord (swapBase j) w ∈ elevenFamily j :=
  Finset.mem_image_of_mem _ hw

theorem elevenFamily_subset_elevenUnion (j : Fin 4) : elevenFamily j ⊆ elevenUnion :=
  Finset.subset_biUnion_of_mem elevenFamily (Finset.mem_univ j)

theorem relabelWord_mem_elevenUnion (j : Fin 4) {w : Word (Fin 4)} (hw : w ∈ elevenBase) :
    relabelWord (swapBase j) w ∈ elevenUnion :=
  elevenFamily_subset_elevenUnion j (relabelWord_mem_elevenFamily j hw)

theorem reduceWord_relabel_swapBase_mem (j : Fin 4) {w v : Word (Fin 4)}
    (hred : reduceWord w = some v) (hv : v ∈ elevenBase) :
    ∃ u, reduceWord (relabelWord (swapBase j) w) = some u ∧ u ∈ elevenFamily j ∧ u ∈ elevenUnion := by
  refine ⟨relabelWord (swapBase j) v, ?_, relabelWord_mem_elevenFamily j hv,
    relabelWord_mem_elevenUnion j hv⟩
  rw [reduceWord_relabel (swapBase j).injective, hred, Option.map_some]

/-! ## 7. Inclusion of `cornerResidualTelescopeOccurrences` in `elevenBase` -/

/-- Every measured word (`shortWord`, `middleWord`, `longWord`) of leaf `l` lies in `S`. -/
def LeafWordsIn (S : Finset (Word (Fin 4))) (l : SupportedPurityLeaf (Fin 4)) : Prop :=
  l.shortWord ∈ S ∧ l.middleWord ∈ S ∧ l.longWord ∈ S

theorem leafWordsIn_mono {S T : Finset (Word (Fin 4))} (hST : S ⊆ T)
    {l : SupportedPurityLeaf (Fin 4)} (hl : LeafWordsIn S l) : LeafWordsIn T l :=
  ⟨hST hl.1, hST hl.2.1, hST hl.2.2⟩

theorem leafWordsIn_relabel (f : Fin 4 → Fin 4) {S T : Finset (Word (Fin 4))}
    (hST : ∀ w ∈ S, relabelWord f w ∈ T) {l : SupportedPurityLeaf (Fin 4)}
    (hl : LeafWordsIn S l) : LeafWordsIn T (SupportedPurityLeaf.relabel f l) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SupportedPurityLeaf.shortWord_relabel]; exact hST _ hl.1
  · rw [SupportedPurityLeaf.middleWord_relabel]; exact hST _ hl.2.1
  · rw [SupportedPurityLeaf.longWord_relabel]; exact hST _ hl.2.2

theorem leafWordsIn_wordFunctional_terms {S : Finset (Word (Fin 4))}
    {l : SupportedPurityLeaf (Fin 4)} (hl : LeafWordsIn S l) :
    ∀ t ∈ l.wordFunctional.terms, t.2 ∈ S := by
  intro t ht
  simp only [SupportedPurityLeaf.wordFunctional, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact hl.2.2
  · exact hl.2.1
  · exact hl.1

theorem leafWordsIn_evaluate_eq {S : Finset (Word (Fin 4))}
    {l : SupportedPurityLeaf (Fin 4)} (hl : LeafWordsIn S l)
    {f g : Word (Fin 4) → ℝ} (hfg : ∀ w ∈ S, f w = g w) :
    l.wordFunctional.evaluate f = l.wordFunctional.evaluate g := by
  rw [SupportedPurityLeaf.wordFunctional_evaluate, SupportedPurityLeaf.wordFunctional_evaluate,
    hfg _ hl.2.2, hfg _ hl.2.1, hfg _ hl.1]

private theorem leafWordsIn_of_template {hp : Word (Fin 4)} {o : Outcome (Fin 4)}
    {suf : Word (Fin 4)} {c : ℝ}
    (h : ∀ w ∈ leafTemplateWords hp o suf, w ∈ elevenBase) :
    LeafWordsIn elevenBase ⟨hp, o, suf, c⟩ := by
  cases suf with
  | nil =>
      refine ⟨h _ ?_, h _ ?_, h _ ?_⟩ <;>
        simp [SupportedPurityLeaf.shortWord, SupportedPurityLeaf.middleWord,
          SupportedPurityLeaf.longWord, SupportedPurityLeaf.history, leafTemplateWords]
  | cons a suf' =>
      refine ⟨h _ ?_, h _ ?_, h _ ?_⟩ <;>
        simp [SupportedPurityLeaf.shortWord, SupportedPurityLeaf.middleWord,
          SupportedPurityLeaf.longWord, SupportedPurityLeaf.history, leafTemplateWords]

private theorem leafWordsIn_of_templateFromHist {hp : Word (Fin 4)} {o : Outcome (Fin 4)}
    {suf : Word (Fin 4)} {c : ℝ} {hist : Word (Fin 4)} (hhist : hp ++ [o] = hist)
    (h : ∀ w ∈ leafTemplateWordsFromHist hist o suf, w ∈ elevenBase) :
    LeafWordsIn elevenBase ⟨hp, o, suf, c⟩ := by
  cases suf with
  | nil =>
      have h1 : hist ∈ leafTemplateWordsFromHist hist o [] := by simp [leafTemplateWordsFromHist]
      refine ⟨?_, ?_, ?_⟩
      · change hp ++ [o] ∈ elevenBase
        rw [hhist]
        exact h _ h1
      · change (hp ++ [o]) ++ [] ∈ elevenBase
        rw [hhist, List.append_nil]
        exact h _ h1
      · change hp ++ [o] ∈ elevenBase
        rw [hhist]
        exact h _ h1
  | cons a suf' =>
      have h1 : hist ∈ leafTemplateWordsFromHist hist o (a :: suf') := by
        simp [leafTemplateWordsFromHist]
      have h2 : hist ++ (a :: suf') ∈ leafTemplateWordsFromHist hist o (a :: suf') := by
        simp [leafTemplateWordsFromHist]
      have h3 : hist ++ (a :: suf') ++ purityMirror (a :: suf') ++ [o] ∈
          leafTemplateWordsFromHist hist o (a :: suf') := by
        simp [leafTemplateWordsFromHist]
      refine ⟨?_, ?_, ?_⟩
      · change hp ++ [o] ∈ elevenBase
        rw [hhist]
        exact h _ h1
      · change (hp ++ [o]) ++ (a :: suf') ∈ elevenBase
        rw [hhist]
        exact h _ h2
      · change ((hp ++ [o]) ++ (a :: suf')) ++ purityMirror (a :: suf') ++ [o] ∈ elevenBase
        rw [hhist]
        exact h _ h3

private theorem holonomyPair_mem_distinctPairs (a : Fin 6) :
    (HolonomyPath.secondLabel a, HolonomyPath.firstLabel a) ∈ distinctPairs := by
  fin_cases a <;> decide

private theorem holonomyWord_mem_prefixes01 {p : List (Fin 6)} (hp : p.length ≤ 1) :
    HolonomyPath.word p ∈ prefixes01 := by
  cases p with
  | nil => decide
  | cons a p =>
      cases p with
      | nil =>
          have hmem := holonomyPair_mem_distinctPairs a
          simp only [HolonomyPath.word, prefixes01, List.mem_append, List.mem_singleton,
            List.mem_map]
          exact Or.inr ⟨(_, _), hmem, rfl⟩
      | cons _ _ =>
          simp only [List.length_cons] at hp
          omega

private theorem holonomyWord_mem_prefixes012 {p : List (Fin 6)} (hp : p.length ≤ 2) :
    HolonomyPath.word p ∈ prefixes012 := by
  cases p with
  | nil => exact List.mem_append_left _ (holonomyWord_mem_prefixes01 (by simp))
  | cons a p =>
      cases p with
      | nil => exact List.mem_append_left _ (holonomyWord_mem_prefixes01 (by simp))
      | cons b p =>
          cases p with
          | nil =>
              have ha := holonomyPair_mem_distinctPairs a
              have hb := holonomyPair_mem_distinctPairs b
              simp only [HolonomyPath.word, prefixes012, List.mem_append, List.mem_flatMap,
                List.mem_map]
              refine Or.inr ⟨(_, _), hb, (_, _), ha, ?_⟩
              rfl
          | cons _ _ =>
              simp only [List.length_cons] at hp
              omega

private theorem accessWordTerms_mem_suffixList (i : Fin 4) (w : Word (Fin 4))
    (t : ℝ × Word (Fin 4)) (ht : t ∈ accessWordTerms i w) :
    t.2 ∈ accessSuffixList i w := by
  simp only [accessWordTerms, signedAccessChoices, List.map_cons, List.map_nil,
    accessPrefix, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [accessSuffixList]

private theorem doubleAccessWordTerms_mem_suffixList (k l m : Fin 4)
    (t : ℝ × Word (Fin 4)) (ht : t ∈ doubleAccessWordTerms k l m) :
    t.2 ∈ doubleAccessSuffixList k l m := by
  rcases List.mem_flatMap.mp ht with ⟨u, hu, htu⟩
  rcases List.mem_map.mp htu with ⟨s, hs, rfl⟩
  have h1 := accessWordTerms_mem_suffixList l [(m, true)] u hu
  have h2 := accessWordTerms_mem_suffixList k u.2 s hs
  exact List.mem_flatMap.mpr ⟨u.2, h1, h2⟩

private theorem polarizedTripleWordTerms_mem_suffixList (k l m : Fin 4)
    (t : ℝ × Word (Fin 4)) (ht : t ∈ polarizedTripleWordTerms k l m) :
    t.2 ∈ doubleAccessSuffixList k l m ++ doubleAccessSuffixList m k l ++
      doubleAccessSuffixList l k m := by
  have hmem : t ∈ doubleAccessWordTerms k l m ∨ t ∈ doubleAccessWordTerms m k l ∨
      t ∈ scaleWordTerms (-1) (doubleAccessWordTerms l k m) := by
    simpa only [polarizedTripleWordTerms, List.mem_append, or_assoc] using ht
  rcases hmem with h | h | h
  · exact List.mem_append_left _ (List.mem_append_left _ (doubleAccessWordTerms_mem_suffixList k l m t h))
  · exact List.mem_append_left _ (List.mem_append_right _ (doubleAccessWordTerms_mem_suffixList m k l t h))
  · rcases List.mem_map.mp h with ⟨u, hu, rfl⟩
    exact List.mem_append_right _ (doubleAccessWordTerms_mem_suffixList l k m u hu)

private theorem vector_leafWordsIn_append {e f : PurityVectorExpression 4}
    (he : ∀ t ∈ e, LeafWordsIn elevenBase t.leaf)
    (hf : ∀ t ∈ f, LeafWordsIn elevenBase t.leaf) :
    ∀ t ∈ e ++ f, LeafWordsIn elevenBase t.leaf := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact he t h
  · exact hf t h

private theorem vector_leafWordsIn_scale {r : ℝ} {e : PurityVectorExpression 4}
    (he : ∀ t ∈ e, LeafWordsIn elevenBase t.leaf) :
    ∀ t ∈ PurityVectorExpression.scale r e, LeafWordsIn elevenBase t.leaf := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact he u hu

private theorem vector_leafWordsIn_leftMultiply {U : FiniteRealWordFunctional 4}
    {e : PurityVectorExpression 4} (he : ∀ t ∈ e, LeafWordsIn elevenBase t.leaf) :
    ∀ t ∈ PurityVectorExpression.leftMultiply U e, LeafWordsIn elevenBase t.leaf := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact he u hu

private theorem occ_leafWordsIn_pairAgainst {U : FiniteRealWordFunctional 4}
    {e : PurityVectorExpression 4} (he : ∀ t ∈ e, LeafWordsIn elevenBase t.leaf) :
    ∀ o ∈ PurityVectorExpression.pairAgainst U e, LeafWordsIn elevenBase o.leaf := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨t, ht, rfl⟩
  exact he t ht

private theorem occ_leafWordsIn_scale {r : ℝ} {es : List (ResidualTelescopeOccurrence 4)}
    (he : ∀ o ∈ es, LeafWordsIn elevenBase o.leaf) :
    ∀ o ∈ ResidualOccurrenceExpression.scale r es, LeafWordsIn elevenBase o.leaf := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  exact he u hu

private theorem occ_leafWordsIn_combine {ess : List (List (ResidualTelescopeOccurrence 4))}
    (he : ∀ es ∈ ess, ∀ o ∈ es, LeafWordsIn elevenBase o.leaf) :
    ∀ o ∈ ResidualOccurrenceExpression.combine ess, LeafWordsIn elevenBase o.leaf := by
  intro o ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho'⟩
  exact he es hes o ho'

private theorem extendPaths_leafWordsIn (d : CornerNumericalData)
    (f : List (Fin 6) → PurityVectorExpression 4) (e : HolonomyPath.Combination)
    (depth : ℕ) (hd : HolonomyPath.HasDepth e depth)
    (hf : ∀ p, p.length ≤ depth → ∀ t ∈ f p, LeafWordsIn elevenBase t.leaf) :
    ∀ t ∈ CornerResidualBuilder.extendPaths d f e, LeafWordsIn elevenBase t.leaf := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨x, hx, htx⟩
  exact vector_leafWordsIn_scale (hf x.2 (hd x hx)) t htx

private theorem faceFirst_eq (i : Fin 3) :
    CornerResidualBuilder.faceFirst i = faceFirstFin i := by fin_cases i <;> rfl
private theorem faceSecond_eq (i : Fin 3) :
    CornerResidualBuilder.faceSecond i = faceSecondFin i := by fin_cases i <;> rfl
private theorem faceThird_eq (i : Fin 3) :
    CornerResidualBuilder.faceThird i = faceThirdFin i := by fin_cases i <;> rfl

private theorem hermitianOnPath_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) (p : List (Fin 6)) (hp : p.length ≤ 2) :
    ∀ t ∈ CornerResidualBuilder.hermitianOnPath d C i p, LeafWordsIn elevenBase t.leaf := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  have hT := holonomyWord_mem_prefixes012 hp
  have hs := accessWordTerms_mem_suffixList
    (CornerResidualBuilder.faceFirst i) [(CornerResidualBuilder.faceSecond i, true)] u hu
  rw [faceFirst_eq, faceSecond_eq] at hs
  refine leafWordsIn_of_templateFromHist (HolonomyPath.word_eq_prefix p).symm (fun w hw => ?_)
  apply telescopeTemplateWords_mem_elevenBase
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  simp only [hermitianTemplateWords, List.mem_flatMap]
  exact ⟨HolonomyPath.word p, hT, i, by fin_cases i <;> simp, u.2, hs, hw⟩

private theorem reverseProduct_face_mem (i : Fin 3) :
    (CornerResidualBuilder.faceFirst i, CornerResidualBuilder.faceSecond i) ∈ distinctPairs ∧
    (CornerResidualBuilder.faceSecond i, CornerResidualBuilder.faceFirst i) ∈ distinctPairs := by
  fin_cases i <;> decide

private theorem reverseProductOnPath_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) {k l : Fin 4} (hkl : (k, l) ∈ distinctPairs)
    (p : List (Fin 6)) (hp : p.length ≤ 2) :
    ∀ t ∈ CornerResidualBuilder.reverseProductOnPath d C k l p, LeafWordsIn elevenBase t.leaf := by
  have hT := holonomyWord_mem_prefixes012 hp
  intro t ht
  simp only [CornerResidualBuilder.reverseProductOnPath, List.mem_append] at ht
  rcases ht with (ht | ht) | ht
  · rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu
    subst hu'
    refine leafWordsIn_of_template (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    simp only [reverseProductTemplateWords, List.mem_flatMap, List.mem_append]
    exact ⟨HolonomyPath.word p, hT, (k, l), hkl, Or.inl (Or.inl hw)⟩
  · rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu
    subst hu'
    refine leafWordsIn_of_template (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    simp only [reverseProductTemplateWords, List.mem_flatMap, List.mem_append]
    exact ⟨HolonomyPath.word p, hT, (k, l), hkl, Or.inl (Or.inr hw)⟩
  · rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu
    subst hu'
    refine leafWordsIn_of_templateFromHist (HolonomyPath.word_eq_prefix p).symm (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    simp only [reverseProductTemplateWords, List.mem_flatMap, List.mem_append]
    exact ⟨HolonomyPath.word p, hT, (k, l), hkl, Or.inr hw⟩

private theorem squareOnPath_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) (p : List (Fin 6)) (hp : p.length ≤ 2) :
    ∀ t ∈ CornerResidualBuilder.squareOnPath d C i p, LeafWordsIn elevenBase t.leaf := by
  refine vector_leafWordsIn_append
    (vector_leafWordsIn_leftMultiply (hermitianOnPath_leafWordsIn d C i p hp))
    (vector_leafWordsIn_scale (vector_leafWordsIn_append
      (vector_leafWordsIn_scale (reverseProductOnPath_leafWordsIn d C
        (reverseProduct_face_mem i).2 p hp))
      (vector_leafWordsIn_scale (reverseProductOnPath_leafWordsIn d C
        (reverseProduct_face_mem i).1 p hp))))

private theorem mixedOnPath_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) (p : List (Fin 6)) (hp : p.length ≤ 1) :
    ∀ t ∈ CornerResidualBuilder.mixedOnPath d C i p, LeafWordsIn elevenBase t.leaf := by
  have hT := holonomyWord_mem_prefixes01 hp
  apply vector_leafWordsIn_scale
  refine vector_leafWordsIn_append (vector_leafWordsIn_append ?_ ?_) ?_
  · intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu
    subst hu'
    refine leafWordsIn_of_template (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [mixedTemplateWords, List.mem_flatMap, List.mem_append]
    refine ⟨HolonomyPath.word p, hT, i, by fin_cases i <;> simp, Or.inl (Or.inl ?_)⟩
    simpa only [faceSecond_eq, faceThird_eq] using hw
  · intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu
    subst hu'
    refine leafWordsIn_of_template (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [mixedTemplateWords, List.mem_flatMap, List.mem_append]
    refine ⟨HolonomyPath.word p, hT, i, by fin_cases i <;> simp, Or.inl (Or.inr ?_)⟩
    simpa only [faceSecond_eq, faceFirst_eq] using hw
  · intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hs := polarizedTripleWordTerms_mem_suffixList
      (CornerResidualBuilder.faceFirst i)
      (CornerResidualBuilder.faceSecond i)
      (CornerResidualBuilder.faceThird i) u hu
    rw [faceFirst_eq, faceSecond_eq, faceThird_eq] at hs
    simp only [List.mem_append] at hs
    refine leafWordsIn_of_templateFromHist (HolonomyPath.word_eq_prefix p).symm (fun w hw => ?_)
    apply telescopeTemplateWords_mem_elevenBase
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [mixedTemplateWords, List.mem_flatMap, List.mem_append]
    exact ⟨HolonomyPath.word p, hT, i, by fin_cases i <;> simp, Or.inr ⟨u.2, hs, hw⟩⟩

private theorem pairOnPath_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) (p : List (Fin 6)) (hp : p.length ≤ 1) :
    ∀ t ∈ CornerResidualBuilder.pairOnPath d C i p, LeafWordsIn elevenBase t.leaf := by
  have hp2 : p.length ≤ 2 := Nat.le_trans hp (by decide)
  have hpc : ∀ a : Fin 6, (a :: p).length ≤ 2 := fun _ => by simp only [List.length_cons]; omega
  refine vector_leafWordsIn_append
    (vector_leafWordsIn_scale (mixedOnPath_leafWordsIn d C i p hp))
    (vector_leafWordsIn_scale (vector_leafWordsIn_append (vector_leafWordsIn_append
      (vector_leafWordsIn_append
        (vector_leafWordsIn_scale (hermitianOnPath_leafWordsIn d C i _ (hpc _)))
        (vector_leafWordsIn_leftMultiply (hermitianOnPath_leafWordsIn d C _ p hp2)))
      (vector_leafWordsIn_scale (hermitianOnPath_leafWordsIn d C _ _ (hpc _))))
      (vector_leafWordsIn_leftMultiply (hermitianOnPath_leafWordsIn d C i p hp2))))

private theorem allPairs_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (e : HolonomyPath.Combination) (depth : ℕ)
    (hd : HolonomyPath.HasDepth e depth) (hdepth : depth ≤ 1) (i j : Fin 3) :
    ∀ t ∈ CornerResidualBuilder.allPairs d C e i j, LeafWordsIn elevenBase t.leaf := by
  have hdepth2 : depth ≤ 2 := Nat.le_trans hdepth (by decide)
  fin_cases i <;> fin_cases j <;>
    simp only [CornerResidualBuilder.allPairs, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
    | exact extendPaths_leafWordsIn d _ e depth hd
        (fun p hp => pairOnPath_leafWordsIn d C _ p (Nat.le_trans hp hdepth))
    | exact vector_leafWordsIn_scale (extendPaths_leafWordsIn d _ e depth hd
        (fun p hp => squareOnPath_leafWordsIn d C _ p (Nat.le_trans hp hdepth2)))

private theorem cubicAtBase_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ t ∈ CornerResidualBuilder.cubicAtBase d C, LeafWordsIn elevenBase t.leaf := by
  apply vector_leafWordsIn_scale
  refine vector_leafWordsIn_append (vector_leafWordsIn_append (vector_leafWordsIn_append
    (vector_leafWordsIn_append (vector_leafWordsIn_append ?_ ?_) ?_) ?_) ?_) ?_
  · intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu; subst hu'
    refine leafWordsIn_of_template (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)))))
  · apply vector_leafWordsIn_scale
    intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu; subst hu'
    refine leafWordsIn_of_template (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))))
  · intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu; subst hu'
    refine leafWordsIn_of_template (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hw))))
  · apply vector_leafWordsIn_scale
    intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu; subst hu'
    refine leafWordsIn_of_template (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hw)))
  · apply vector_leafWordsIn_scale
    intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hs := accessWordTerms_mem_suffixList 2 [(3, true)] u hu
    refine leafWordsIn_of_template (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    exact List.mem_flatMap.mpr ⟨u.2, hs, hw⟩
  · apply vector_leafWordsIn_scale
    intro t ht
    rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
    rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
    have hu' := List.mem_singleton.mp hu; subst hu'
    refine leafWordsIn_of_templateFromHist rfl (fun w hw => telescopeTemplateWords_mem_elevenBase ?_)
    exact List.mem_append_right _ (List.mem_append_right _ hw)

private theorem hermitianProductAtBase_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ t ∈ CornerResidualBuilder.hermitianProductAtBase d C, LeafWordsIn elevenBase t.leaf := by
  apply vector_leafWordsIn_scale
  refine vector_leafWordsIn_append (vector_leafWordsIn_append (vector_leafWordsIn_append
    (vector_leafWordsIn_append (vector_leafWordsIn_append ?_ ?_) ?_) ?_) ?_) ?_
  · exact extendPaths_leafWordsIn d _ _ 2 (HolonomyPath.twoGenerator_base_hasDepth _ _)
      (hermitianOnPath_leafWordsIn d C 0)
  · exact vector_leafWordsIn_leftMultiply (extendPaths_leafWordsIn d _ _ 1
      (HolonomyPath.hasDepth_generatorAction _ _ _ HolonomyPath.baseCombination_hasDepth)
      (fun p hp => hermitianOnPath_leafWordsIn d C 1 p (Nat.le_trans hp (by decide))))
  · exact vector_leafWordsIn_leftMultiply (extendPaths_leafWordsIn d _ _ 0
      HolonomyPath.baseCombination_hasDepth
      (fun p hp => hermitianOnPath_leafWordsIn d C 2 p (Nat.le_trans hp (by decide))))
  · exact extendPaths_leafWordsIn d _ _ 2 (HolonomyPath.twoGenerator_base_hasDepth _ _)
      (hermitianOnPath_leafWordsIn d C 2)
  · exact vector_leafWordsIn_leftMultiply (extendPaths_leafWordsIn d _ _ 1
      (HolonomyPath.hasDepth_generatorAction _ _ _ HolonomyPath.baseCombination_hasDepth)
      (fun p hp => hermitianOnPath_leafWordsIn d C 1 p (Nat.le_trans hp (by decide))))
  · exact vector_leafWordsIn_leftMultiply (extendPaths_leafWordsIn d _ _ 0
      HolonomyPath.baseCombination_hasDepth
      (fun p hp => hermitianOnPath_leafWordsIn d C 0 p (Nat.le_trans hp (by decide))))

private theorem dataAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ t ∈ CornerResidualBuilder.dataAtBase d C, LeafWordsIn elevenBase t.leaf := by
  refine vector_leafWordsIn_append (vector_leafWordsIn_append
    (cubicAtBase_leafWordsIn d C)
    (vector_leafWordsIn_scale (hermitianProductAtBase_leafWordsIn d C)))
    (vector_leafWordsIn_scale (vector_leafWordsIn_append (vector_leafWordsIn_append
      (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) 1 2))
      (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) 0 2)))
      (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) 0 1))))

private theorem volumeAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ t ∈ CornerResidualBuilder.volumeAtBase d C, LeafWordsIn elevenBase t.leaf := by
  refine vector_leafWordsIn_append (vector_leafWordsIn_append
    (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 1
      (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) (by decide) 1 2))
    (vector_leafWordsIn_scale (vector_leafWordsIn_leftMultiply
      (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) 0 2))))
    (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 1
      (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) (by decide) 0 1))

private theorem gramAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i j : Fin 3) :
    ∀ o ∈ CornerResidualBuilder.gramAtBase d C i j, LeafWordsIn elevenBase o.leaf :=
  occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
    (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) i j))

private theorem crossAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) :
    ∀ o ∈ CornerResidualBuilder.crossAtBase d C i, LeafWordsIn elevenBase o.leaf := by
  fin_cases i
  · apply occ_leafWordsIn_combine
    intro es hes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
    rcases hes with rfl | rfl
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 1 2)
    · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
        (extendPaths_leafWordsIn d _ _ 0 HolonomyPath.baseCombination_hasDepth
          (fun p hp => squareOnPath_leafWordsIn d C 0 p (Nat.le_trans hp (by decide)))))
  · apply occ_leafWordsIn_combine
    intro es hes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
    rcases hes with rfl | rfl | rfl | rfl
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 0 2)
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 1 2)
    · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
        (extendPaths_leafWordsIn d _ _ 1
          (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth)
          (fun p hp => squareOnPath_leafWordsIn d C 1 p (Nat.le_trans hp (by decide)))))
    · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
        (allPairs_leafWordsIn d C _ 0 HolonomyPath.baseCombination_hasDepth (by decide) 0 1))
  · apply occ_leafWordsIn_combine
    intro es hes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
    rcases hes with rfl | rfl | rfl | rfl | rfl
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 0 1)
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 1 2)
    · exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C 0 2)
    · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
        (extendPaths_leafWordsIn d _ _ 0 HolonomyPath.baseCombination_hasDepth
          (fun p hp => squareOnPath_leafWordsIn d C 2 p (Nat.le_trans hp (by decide)))))
    · apply occ_leafWordsIn_pairAgainst
      refine vector_leafWordsIn_append
        (vector_leafWordsIn_leftMultiply (allPairs_leafWordsIn d C _ 0
          HolonomyPath.baseCombination_hasDepth (by decide) 1 2))
        (vector_leafWordsIn_scale (allPairs_leafWordsIn d C _ 1
          (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) (by decide) 0 2))

private theorem normAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ o ∈ CornerResidualBuilder.normAtBase d C, LeafWordsIn elevenBase o.leaf := by
  apply occ_leafWordsIn_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl
  · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
      (extendPaths_leafWordsIn d _ _ 2 (HolonomyPath.twoSkew_base_hasDepth _ _)
        (squareOnPath_leafWordsIn d C 0)))
  · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
      (extendPaths_leafWordsIn d _ _ 1
        (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth)
        (fun p hp => squareOnPath_leafWordsIn d C 1 p (Nat.le_trans hp (by decide)))))
  · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst
      (extendPaths_leafWordsIn d _ _ 0 HolonomyPath.baseCombination_hasDepth
        (fun p hp => squareOnPath_leafWordsIn d C 2 p (Nat.le_trans hp (by decide)))))

private theorem gramRowAtBase_leafWordsIn (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) :
    ∀ o ∈ CornerResidualBuilder.gramRowAtBase d C i, LeafWordsIn elevenBase o.leaf := by
  apply occ_leafWordsIn_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl <;> exact occ_leafWordsIn_scale (gramAtBase_leafWordsIn d C i _)

/-- Every leaf word generated by `cornerResidualTelescopeOccurrences d C` already
belongs to `Ends.Eleven.elevenBase` (no pruning needed). -/
theorem cornerResidualTelescope_leafWordsIn (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ o ∈ cornerResidualTelescopeOccurrences d C, LeafWordsIn elevenBase o.leaf := by
  apply occ_leafWordsIn_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact occ_leafWordsIn_pairAgainst (dataAtBase_leafWordsIn d C)
  · exact occ_leafWordsIn_scale (occ_leafWordsIn_pairAgainst (volumeAtBase_leafWordsIn d C))
  · exact occ_leafWordsIn_scale (normAtBase_leafWordsIn d C)
  · exact occ_leafWordsIn_scale (crossAtBase_leafWordsIn d C 0)
  · exact occ_leafWordsIn_scale (crossAtBase_leafWordsIn d C 1)
  · exact occ_leafWordsIn_scale (crossAtBase_leafWordsIn d C 2)
  · exact gramRowAtBase_leafWordsIn d C 0
  · exact gramRowAtBase_leafWordsIn d C 1
  · exact gramRowAtBase_leafWordsIn d C 2

theorem cornerResidualTelescope_words_mem_elevenBase (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ o ∈ cornerResidualTelescopeOccurrences d C,
      ∀ t ∈ o.leaf.wordFunctional.terms, t.2 ∈ elevenBase ∧ IsReducedWord t.2 := by
  intro o ho t ht
  have hmem := leafWordsIn_wordFunctional_terms
    (cornerResidualTelescope_leafWordsIn d C o ho) t ht
  exact ⟨hmem, (elevenBase_shape t.2 hmem).1⟩

theorem cornerResidualTelescope_eq_of_eqOn_elevenBase (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) {f g : Word (Fin 4) → ℝ}
    (hfg : ∀ w ∈ elevenBase, f w = g w) :
    ∀ o ∈ cornerResidualTelescopeOccurrences d C,
      o.leaf.wordFunctional.evaluate f = o.leaf.wordFunctional.evaluate g :=
  fun o ho => leafWordsIn_evaluate_eq (cornerResidualTelescope_leafWordsIn d C o ho) hfg

theorem cornerBaseFunctional_words_mem_elevenBase (d : CornerNumericalData) :
    ∀ t ∈ (cornerBaseFunctional d).terms, t.2 ∈ elevenBase ∧ IsReducedWord t.2 := by
  intro t ht
  simp only [cornerBaseFunctional, List.mem_singleton] at ht
  subst ht
  exact ⟨yes0_mem_elevenBase, (elevenBase_shape _ yes0_mem_elevenBase).1⟩

theorem cornerBaseFunctional_eq_of_eqOn_elevenBase (d : CornerNumericalData)
    {f g : Word (Fin 4) → ℝ} (hfg : ∀ w ∈ elevenBase, f w = g w) :
    (cornerBaseFunctional d).evaluate f = (cornerBaseFunctional d).evaluate g := by
  simp only [cornerBaseFunctional_evaluate, hfg [(0, true)] yes0_mem_elevenBase]

private theorem terms_mem_scale {r : ℝ} {Λ : FiniteRealWordFunctional 4} {P : Word (Fin 4) → Prop}
    (h : ∀ t ∈ Λ.terms, P t.2) :
    ∀ t ∈ (FiniteRealWordFunctional.scale r Λ).terms, P t.2 := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact h u hu

private theorem terms_mem_append {Λ₁ Λ₂ : FiniteRealWordFunctional 4} {P : Word (Fin 4) → Prop}
    (h1 : ∀ t ∈ Λ₁.terms, P t.2) (h2 : ∀ t ∈ Λ₂.terms, P t.2) :
    ∀ t ∈ (FiniteRealWordFunctional.append Λ₁ Λ₂).terms, P t.2 := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact h1 t h
  · exact h2 t h

private theorem terms_mem_combine {cs : List (FiniteRealWordFunctional 4)} {P : Word (Fin 4) → Prop}
    (h : ∀ c ∈ cs, ∀ t ∈ c.terms, P t.2) :
    ∀ t ∈ (FiniteRealWordFunctional.combine cs).terms, P t.2 := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨c, hc, htc⟩
  exact h c hc t htc

private theorem combinedCornerBase_swapBase_terms (d : Fin 4 → CornerNumericalData)
    (weight : Fin 4 → ℝ) :
    ∀ t ∈ (combinedCornerBase d (fun j a => swapBase j a) weight).terms,
      t.2 ∈ elevenUnion ∧ IsReducedWord t.2 := by
  unfold combinedCornerBase
  apply terms_mem_combine (P := fun w => w ∈ elevenUnion ∧ IsReducedWord w)
  intro c hc
  rcases List.mem_ofFn.mp hc with ⟨j, rfl⟩
  apply terms_mem_scale (P := fun w => w ∈ elevenUnion ∧ IsReducedWord w)
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  have hmem := (cornerBaseFunctional_words_mem_elevenBase (d j) u hu).1
  exact ⟨relabelWord_mem_elevenUnion j hmem,
    isReducedWord_relabel (swapBase j).injective (elevenBase_shape u.2 hmem).1⟩

private theorem combinedCornerOccurrences_swapBase_terms (d : Fin 4 → CornerNumericalData)
    (C : Fin 4 → Fin 4 → Word (Fin 4) → ℝ) (weight : Fin 4 → ℝ) :
    ∀ o ∈ combinedCornerOccurrences d C (fun j a => swapBase j a) weight,
      ∀ t ∈ o.leaf.wordFunctional.terms, t.2 ∈ elevenUnion ∧ IsReducedWord t.2 := by
  intro o ho
  unfold combinedCornerOccurrences ResidualOccurrenceExpression.combine
    ResidualOccurrenceExpression.scale ResidualOccurrenceExpression.relabel at ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho'⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho' with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  intro t ht
  change t ∈ (SupportedPurityLeaf.relabel (fun a => swapBase j a) v.leaf).wordFunctional.terms at ht
  rw [SupportedPurityLeaf.wordFunctional_relabel] at ht
  rcases List.mem_map.mp ht with ⟨x, hx, rfl⟩
  have hmem := (cornerResidualTelescope_words_mem_elevenBase (d j) (C j) v hv x hx).1
  exact ⟨relabelWord_mem_elevenUnion j hmem,
    isReducedWord_relabel (swapBase j).injective (elevenBase_shape x.2 hmem).1⟩

theorem constructiveResidualSeparator_terms_mem {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n)) (m : ℝ)
    {P : Word (Fin n) → Prop} (hempty : P [])
    (hbase : ∀ t ∈ base.terms, P t.2)
    (hocc : ∀ o ∈ occ, ∀ t ∈ o.leaf.wordFunctional.terms, P t.2) :
    ∀ t ∈ (constructiveResidualSeparator base occ m).terms, P t.2 := by
  unfold constructiveResidualSeparator
  intro t ht
  rcases List.mem_append.mp ht with h1 | h2
  · rcases List.mem_append.mp h1 with h11 | h12
    · rcases List.mem_map.mp h11 with ⟨u, hu, rfl⟩
      rcases List.mem_flatMap.mp hu with ⟨c, hc, huc⟩
      rcases List.mem_map.mp hc with ⟨o, ho, rfl⟩
      exact hocc o ho u huc
    · rcases List.mem_map.mp h12 with ⟨u, hu, rfl⟩
      exact hbase u hu
  · have hsing : t = (m / 2, []) := List.mem_singleton.mp h2
    rw [hsing]
    exact hempty

theorem constructiveResidualSeparator_support_mem {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n)) (m : ℝ)
    {P : Word (Fin n) → Prop} (hempty : P [])
    (hbase : ∀ t ∈ base.terms, P t.2)
    (hocc : ∀ o ∈ occ, ∀ t ∈ o.leaf.wordFunctional.terms, P t.2) :
    (∀ t ∈ (constructiveResidualSeparator base occ m).terms, P t.2) ∧
    (∀ w ∈ (constructiveResidualSeparator base occ m).coefficients.support, P w) := by
  have hterms := constructiveResidualSeparator_terms_mem base occ m hempty hbase hocc
  refine ⟨hterms, fun w hw => ?_⟩
  by_contra hbad
  apply Finsupp.mem_support_iff.mp hw
  apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
  intro t ht heq
  exact hbad (heq ▸ hterms t ht)

/-- Support and reducedness of the `swapBase`-relabelled four-base `combinedCornerWitness`:
every term and every coefficient-support word is either `[]` or lies in `elevenUnion`, and
is reduced (`IsReducedWord`). -/
theorem combinedCornerWitness_swapBase_support (d : Fin 4 → CornerNumericalData)
    (C : Fin 4 → Fin 4 → Word (Fin 4) → ℝ) (weight : Fin 4 → ℝ) (m : ℝ) :
    (∀ t ∈ (combinedCornerWitness d C (fun j a => swapBase j a) weight m).terms,
      (t.2 = [] ∨ t.2 ∈ elevenUnion) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ (combinedCornerWitness d C (fun j a => swapBase j a) weight m).coefficients.support,
      (w = [] ∨ w ∈ elevenUnion) ∧ IsReducedWord w) := by
  have hbase := combinedCornerBase_swapBase_terms d weight
  have hocc := combinedCornerOccurrences_swapBase_terms d C weight
  unfold combinedCornerWitness
  exact constructiveResidualSeparator_support_mem
    (combinedCornerBase d (fun j a => swapBase j a) weight)
    (combinedCornerOccurrences d C (fun j a => swapBase j a) weight)
    m
    (P := fun w => (w = [] ∨ w ∈ elevenUnion) ∧ IsReducedWord w)
    ⟨Or.inl rfl, trivial⟩
    (fun t ht => ⟨Or.inr (hbase t ht).1, (hbase t ht).2⟩)
    (fun o ho t ht => ⟨Or.inr (hocc o ho t ht).1, (hocc o ho t ht).2⟩)

end

end AlbertSequential.BlockB

#print axioms AlbertSequential.BlockB.elevenLedgerWords_eq_elevenBase
#print axioms AlbertSequential.BlockB.ledgerApplications_length
#print axioms AlbertSequential.BlockB.reduceWord_probability
#print axioms AlbertSequential.BlockB.reduceWord_nativeWordProbability_atoms
#print axioms AlbertSequential.BlockB.reduceFunctional_evaluate_probability
#print axioms AlbertSequential.BlockB.reduceFunctional_evaluate_native
#print axioms AlbertSequential.BlockB.reduceFunctional_coefficientNorm_le
#print axioms AlbertSequential.BlockB.elevenFamily_card
#print axioms AlbertSequential.BlockB.elevenUnion_card
#print axioms AlbertSequential.BlockB.cornerResidualTelescope_words_mem_elevenBase
#print axioms AlbertSequential.BlockB.combinedCornerWitness_swapBase_support
