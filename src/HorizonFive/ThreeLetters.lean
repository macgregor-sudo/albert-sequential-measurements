/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.WordFacts
public import HorizonFive.Window

/-! # Step 2 of lem:cer:h5:seven without Cohn's theorem

Paper (Step 2): components using at most three letters are handled by Cohn's theorem (lifting
the lower-order words of `σ̂(F_T)`) and prop:three.  Lean route (same statement, different and
cheaper route): if `G j` is free of `x_j` for each `j` and `Σ_j σ̂(G j) = 0`, then the reduced words
of `σ̂(G j)` that use all three letters other than `j` cancel against nothing, so `σ̂(G j)` lives
on words with at most two letters.  Reversal classes of such words have explicit lifts
(`liftRW`: odd alternating words are `U_x U_y ⋯ x`, even ones `x ∘ (odd)`), one canonical lift per
reduced word.  Then `transfer_free_letter` (prop:three) applies to `G j − Σ_g c_{j,g} D_g`, and the
coefficients `Σ_j c_{j,g} = coef_g(Σ_j σ̂(G j))` vanish.  No Cohn theorem and no descent through
letter sets is needed.

Headline: `three_letter_transfer`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Finite sums of Jordan expressions -/

/-- The zero expression. -/
def zeroP : JPoly Test := .smul 0 .one

/-- `Σ_{i ∈ l} c_i P_i` as a Jordan expression. -/
def jsumL {ι : Type} (c : ι → ℝ) (P : ι → JPoly Test) : List ι → JPoly Test
  | [] => zeroP
  | i :: l => .add (.smul (c i) (P i)) (jsumL c P l)

theorem eval_jsumL {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
    {ι : Type} (c : ι → ℝ) (P : ι → JPoly Test) (l : List ι) :
    T.eval v (jsumL c P l) = (l.map fun i => c i • T.eval v (P i)).sum := by
  induction l with
  | nil => simp [jsumL, zeroP, JTarget.eval]
  | cons i l ih => simp only [jsumL, JTarget.eval, ih, List.map_cons, List.sum_cons]

/-- `Σ_{i ∈ s} c_i P_i` as a Jordan expression. -/
def jsum {ι : Type} (s : Finset ι) (c : ι → ℝ) (P : ι → JPoly Test) : JPoly Test :=
  jsumL c P s.toList

theorem eval_jsum {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (P : ι → JPoly Test) :
    T.eval v (jsum s c P) = ∑ i ∈ s, c i • T.eval v (P i) := by
  rw [jsum, eval_jsumL, Finset.sum_map_toList]

theorem freeOf_jsumL {ι : Type} (c : ι → ℝ) (P : ι → JPoly Test) (z : Test) (l : List ι)
    (h : ∀ i ∈ l, (P i).FreeOf z) : (jsumL c P l).FreeOf z := by
  induction l with
  | nil => exact .smul _ _ .one
  | cons i l ih =>
    exact .add _ _ (.smul _ _ (h i (by simp))) (ih fun k hk => h k (by simp [hk]))

theorem freeOf_jsum {ι : Type} (s : Finset ι) (c : ι → ℝ) (P : ι → JPoly Test) (z : Test)
    (h : ∀ i ∈ s, (P i).FreeOf z) : (jsum s c P).FreeOf z :=
  freeOf_jsumL c P z s.toList fun i hi => h i (Finset.mem_toList.1 hi)

theorem deg_jsumL {ι : Type} (c : ι → ℝ) (P : ι → JPoly Test) (n : ℕ) (l : List ι)
    (h : ∀ i ∈ l, (P i).deg ≤ n) : (jsumL c P l).deg ≤ n := by
  induction l with
  | nil => simp [jsumL, zeroP, JPoly.deg]
  | cons i l ih =>
    simp only [jsumL, JPoly.deg, max_le_iff]
    exact ⟨h i (by simp), ih fun k hk => h k (by simp [hk])⟩

theorem deg_jsum {ι : Type} (s : Finset ι) (c : ι → ℝ) (P : ι → JPoly Test) (n : ℕ)
    (h : ∀ i ∈ s, (P i).deg ≤ n) : (jsum s c P).deg ≤ n :=
  deg_jsumL c P n s.toList fun i hi => h i (Finset.mem_toList.1 hi)

/-- `F - G`. -/
def jsub (F G : JPoly Test) : JPoly Test := .add F (.smul (-1) G)

theorem eval_jsub {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
    (F G : JPoly Test) : T.eval v (jsub F G) = T.eval v F - T.eval v G := by
  simp only [jsub, JTarget.eval, neg_one_smul, sub_eq_add_neg]

/-! ## Alternating words and their lifts -/

/-- The alternating word `x y x y ⋯` of length `n`. -/
def alt (x y : Test) : ℕ → List Test
  | 0 => []
  | n + 1 => x :: alt y x n

theorem alt_succ_right (x y : Test) (n : ℕ) :
    alt x y (n + 1) = alt x y n ++ [if n % 2 = 0 then x else y] := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rw [alt, ih y x, alt, List.cons_append]
    congr 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (n + 1) % 2 = 0 := by omega
      simp [h, this]

theorem alt_odd_succ (x y : Test) (k : ℕ) :
    alt x y (2 * k + 3) = x :: alt y x (2 * k + 1) ++ [x] := by
  rw [alt, alt_succ_right y x (2 * k + 1)]
  have : (2 * k + 1) % 2 = 1 := by omega
  simp [this]

theorem alt_reverse (k : ℕ) : ∀ x y : Test,
    (alt x y (2 * k + 1)).reverse = alt x y (2 * k + 1) ∧
      (alt x y (2 * k + 2)).reverse = alt y x (2 * k + 2) := by
  induction k with
  | zero => intro x y; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro x y
    have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    have e2 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    rw [e1, e2]
    constructor
    · rw [alt_odd_succ]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons_append, (ih y x).1]
    · rw [show alt x y (2 * k + 4) = x :: y :: alt x y (2 * k + 2) from rfl,
        alt_succ_right y x (2 * k + 3), alt_succ_right y x (2 * k + 2)]
      have h3 : (2 * k + 3) % 2 = 1 := by omega
      have h2 : (2 * k + 2) % 2 = 0 := by omega
      simp only [h3, h2, ite_true, ite_false, one_ne_zero, List.reverse_cons, (ih x y).2,
        List.append_assoc, List.singleton_append]

/-- Odd alternating palindromes `U_x U_y ⋯ x`. -/
def palP (x y : Test) : ℕ → JPoly Test
  | 0 => .var x
  | k + 1 => .U (.var x) (palP y x k)

theorem specialEval_palP (k : ℕ) : ∀ x y : Test,
    specialEval (palP x y k) = groupElt (alt x y (2 * k + 1)) := by
  induction k with
  | zero => intro x y; simp [palP, specialEval, JTarget.eval, groupElt, alt]
  | succ k ih =>
    intro x y
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, alt_odd_succ]
    change (specialTarget _).eval specialSymmetry (JPoly.U _ _) = _
    rw [JTarget.eval_U, specialTarget_Uop]
    change specialSymmetry x * specialEval (palP y x k) * specialSymmetry x = _
    rw [ih, groupElt_append, groupElt_cons]
    simp [groupElt]

theorem freeOf_palP (z : Test) (k : ℕ) : ∀ x y : Test, x ≠ z → y ≠ z → (palP x y k).FreeOf z := by
  induction k with
  | zero => intro x y hx _; exact .var x hx
  | succ k ih =>
    intro x y hx hy
    have hv : (JPoly.var x : JPoly Test).FreeOf z := .var x hx
    have hp := ih y x hy hx
    exact .add _ _ (.smul _ _ (.mul _ _ hv (.mul _ _ hv hp)))
      (.smul _ _ (.mul _ _ (.mul _ _ hv hv) hp))

/-- Lift of the reversal class of `alt x y n`. -/
def liftAlt (x y : Test) (n : ℕ) : JPoly Test :=
  if n = 0 then .one
  else if n % 2 = 1 then palP x y (n / 2)
  else .mul (.var x) (palP y x ((n - 2) / 2))

theorem specialEval_liftAlt (x y : Test) (n : ℕ) :
    specialEval (liftAlt x y n) = classElt (alt x y n) := by
  unfold liftAlt
  split_ifs with h0 h1
  · subst h0
    simp only [classElt, alt, List.reverse_nil]
    change (1 : UniversalProjectionAlgebra 4) = _
    simp [groupElt]
    module
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hk : (2 * k + 1) / 2 = k := by omega
    rw [hk, specialEval_palP, classElt, (alt_reverse k x y).1]
    module
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨(n - 2) / 2, by omega⟩
    have hk : (2 * k + 2 - 2) / 2 = k := by omega
    rw [hk, classElt, (alt_reverse k x y).2]
    change (specialTarget _).mul (specialSymmetry x) (specialEval (palP y x k)) = _
    rw [specialTarget_mul, specialEval_palP]
    congr 1
    rw [show alt x y (2 * k + 2) = x :: alt y x (2 * k + 1) from rfl, groupElt_cons,
      alt_succ_right y x (2 * k + 1)]
    have : (2 * k + 1) % 2 = 1 := by omega
    simp only [this, one_ne_zero, ite_false, groupElt_append]
    simp [groupElt]

theorem freeOf_liftAlt (x y z : Test) (n : ℕ) (hx : x ≠ z) (hy : y ≠ z) :
    (liftAlt x y n).FreeOf z := by
  unfold liftAlt
  split_ifs
  · exact .one
  · exact freeOf_palP z _ x y hx hy
  · exact .mul _ _ (.var x hx) (freeOf_palP z _ y x hy hx)

theorem reduced_alt (l : List Test) : ∀ x y : Test, reducedB l = true →
    (∀ z ∈ l, z = x ∨ z = y) → l.head? = some x → l = alt x y l.length := by
  induction l with
  | nil => intro x y _ _ h; simp at h
  | cons a t ih =>
    intro x y hr hl hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil => rfl
    | cons b t' =>
      have hab : a ≠ b := by
        simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hr
        exact hr.1
      have hb : b = y := by
        rcases hl b (by simp) with h | h
        · exact absurd h.symm hab
        · exact h
      have := ih y a (reducedB_tail a _ hr)
        (fun z hz => (hl z (List.mem_cons_of_mem _ hz)).symm) (by simp [hb])
      rw [List.length_cons, alt, ← this]

/-- The second letter of a word (or its first, if it has only one). -/
def secondLetter : List Test → Test
  | _ :: b :: _ => b
  | [a] => a
  | [] => 0

/-- The canonical lift of a reduced word on at most two letters. -/
def liftRW (g : RW) : JPoly Test :=
  match g.1 with
  | [] => .one
  | a :: t => liftAlt a (secondLetter (a :: t)) (t.length + 1)

theorem secondLetter_mem (a : Test) (t : List Test) : secondLetter (a :: t) ∈ a :: t := by
  cases t with
  | nil => simp [secondLetter]
  | cons b t => simp [secondLetter]

theorem freeOf_liftRW (g : RW) (z : Test) (hz : z ∉ g.1) : (liftRW g).FreeOf z := by
  obtain ⟨l, hl⟩ := g
  unfold liftRW
  cases l with
  | nil => exact .one
  | cons a t =>
    simp only at hz ⊢
    refine freeOf_liftAlt _ _ _ _ (fun h => hz (h ▸ by simp)) (fun h => hz (h ▸ ?_))
    exact secondLetter_mem a t

/-- A reduced word on at most two letters (every letter is its first or second letter) has
its reversal class lifted by `liftRW`. -/
theorem specialEval_liftRW (g : RW) (h2 : ∀ z ∈ g.1, z = g.1.headD 0 ∨ z = secondLetter g.1) :
    specialEval (liftRW g) = classElt g.1 := by
  obtain ⟨l, hl⟩ := g
  unfold liftRW
  cases l with
  | nil =>
    simp only
    rw [show ([] : List Test) = alt 0 0 0 from rfl, ← specialEval_liftAlt]
    rfl
  | cons a t =>
    simp only at h2 ⊢
    have e := reduced_alt (a :: t) a (secondLetter (a :: t)) hl h2 rfl
    conv_rhs => rw [e]
    exact specialEval_liftAlt _ _ _

/-! ## Step 2 -/

theorem fin4_two_left (z x y j k : Test) (hzj : z ≠ j) (hzk : z ≠ k) (hxj : x ≠ j) (hxk : x ≠ k)
    (hyj : y ≠ j) (hyk : y ≠ k) (hxy : x ≠ y) (hjk : j ≠ k) : z = x ∨ z = y := by
  revert z x y j k
  decide

theorem two_letters_of_avoid (g : RW) (j k : Test) (hjk : j ≠ k) (hj : j ∉ g.1) (hk : k ∉ g.1) :
    ∀ z ∈ g.1, z = g.1.headD 0 ∨ z = secondLetter g.1 := by
  obtain ⟨l, hl⟩ := g
  intro z hz
  simp only at hj hk hz ⊢
  cases l with
  | nil => simp at hz
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hz
      left; simpa using hz
    | cons b t' =>
      have hab : a ≠ b := by
        simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hl
        exact hl.1
      simp only [List.headD_cons, secondLetter]
      exact fin4_two_left z a b j k (fun h => hj (h ▸ hz)) (fun h => hk (h ▸ hz))
        (fun h => hj (h ▸ by simp)) (fun h => hk (h ▸ by simp))
        (fun h => hj (h ▸ by simp)) (fun h => hk (h ▸ by simp)) hab hjk

theorem coef_specialEval_free (j : Test) (F : JPoly Test) (hF : F.FreeOf j) (g : RW)
    (hg : j ∈ g.1) : coef g (specialEval F) = 0 := by
  refine coef_eq_zero_of_letterSpan (fun z => z ≠ j) g j hg (fun h => h rfl) ?_
  refine specialEval_mem_letterSpan _ F fun z hz => ?_
  push Not at hz
  rw [hz]; exact hF

/-- **Step 2 of lem:cer:h5:seven (proved, Cohn-free).** For any four atoms: if each `G j` is free
of `x_j` and `Σ_j σ̂(G j) = 0`, then `Σ_j ν̂(G j) = 0`. -/
theorem three_letter_transfer (p : Test → Albert) (hp : ∀ i, IsAtom (p i))
    (G : Test → JPoly Test) (hG : ∀ j, (G j).FreeOf j)
    (h0 : ∑ j, specialEval (G j) = 0) : ∑ j, albertEval p (G j) = 0 := by
  classical
  set y : Test → UniversalProjectionAlgebra 4 := fun j => specialEval (G j) with hy
  -- support of the coefficients of `σ̂(G j)`
  have hsupp : ∀ j, ∀ g ∈ (coefVec (y j)).support, j ∉ g.1 ∧ ∃ k, k ≠ j ∧ k ∉ g.1 := by
    intro j g hg
    rw [mem_coefVec_support] at hg
    have hj : j ∉ g.1 := fun h => hg (coef_specialEval_free j _ (hG j) g h)
    refine ⟨hj, ?_⟩
    by_contra hall
    push Not at hall
    apply hg
    have hsum := congrArg (coef g) h0
    rw [map_sum, map_zero, Finset.sum_eq_single j] at hsum
    · exact hsum
    · intro k _ hkj
      exact coef_specialEval_free k _ (hG k) g (hall k hkj)
    · intro h; exact absurd (Finset.mem_univ j) h
  -- the lifts
  let L : Test → JPoly Test := fun j => jsum (coefVec (y j)).support (fun g => coef g (y j)) liftRW
  have hLspec : ∀ j, specialEval (L j) = y j := by
    intro j
    simp only [L, specialEval, eval_jsum]
    conv_rhs => rw [expand_class (y j) (star_specialEval _)]
    refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨hj, k, hkj, hk⟩ := hsupp j g hg
    rw [← specialEval, specialEval_liftRW g (two_letters_of_avoid g j k (Ne.symm hkj) hj hk)]
  have hLfree : ∀ j, (L j).FreeOf j := fun j =>
    freeOf_jsum _ _ _ j fun g hg => freeOf_liftRW g j (hsupp j g hg).1
  have hLalb : ∀ j, albertEval p (G j) = albertEval p (L j) := by
    intro j
    have hd : (jsub (G j) (L j)).FreeOf j := .add _ _ (hG j) (.smul _ _ (hLfree j))
    have hs : specialEval (jsub (G j) (L j)) = 0 := by
      rw [specialEval, eval_jsub, ← specialEval, ← specialEval, hLspec, sub_self]
    have := transfer_free_letter p hp j _ hd hs
    rw [albertEval, eval_jsub] at this
    exact sub_eq_zero.1 this
  -- regroup by reduced words
  set S : Finset RW := Finset.univ.biUnion fun j => (coefVec (y j)).support
  have hext : ∀ j, albertEval p (L j) = ∑ g ∈ S, coef g (y j) • albertEval p (liftRW g) := by
    intro j
    simp only [L, albertEval, eval_jsum]
    refine Finset.sum_subset (fun g hg => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hg⟩) ?_
    intro g _ hg
    rw [mem_coefVec_support, not_not] at hg
    rw [hg, zero_smul]
  simp only [hLalb, hext]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [← Finset.sum_smul, ← map_sum]
  change coef g (∑ j, specialEval (G j)) • _ = 0
  rw [h0, map_zero, zero_smul]

end AlbertSequential.HorizonFive
