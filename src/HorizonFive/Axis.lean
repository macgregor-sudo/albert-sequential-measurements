/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Contraction

/-! # The axis of a cyclically reduced element of `G = ℤ₂^{*4}`, by reduced words

Group-theoretic core of lem:cer:h5:refl(a), proved by a direct combinatorial argument on reduced
words (no trees, no imported axis theorem).

* A bi-infinite sequence `a : ℤ → Test` with `a (n+1) ≠ a n` gives the group elements
  `P_a(n) = a_0 a_1 ⋯ a_{n-1}` (`n ≥ 0`) and `P_a(-n) = a_{-1} ⋯ a_{-n}` (`seqP a n`), all
  reduced words with `|P_a(x)⁻¹ P_a(y)| = |y - x|` (`rlen_seqP_diff`).
* For a cyclically reduced `k` of length `L ≥ 2` and `a` the periodic sequence of its letters,
  `P_a(L) = k` and, for every reduced `g`, `|g⁻¹ k g| = L` iff `g = P_a(n)` for some `n`
  (`axis_lemma`, `rlen_conj_seqP`): the vertices of least displacement are the `P_a(n)`.
* A reflection `s` with `s k s = k⁻¹` acts on this line as `P_a(m) ↦ P_a(c - m)`
  (`refl_on_axis`).

Group equalities are equalities of `groupElt` in the universal projection algebra, and
`rlen l` is the length of the reduced form of `l`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Basic facts on `G` -/

theorem groupElt_nil : groupElt ([] : List Test) = 1 := by simp [groupElt]

theorem groupElt_singleton (a : Test) : groupElt [a] = specialSymmetry a := by simp [groupElt]

/-- The reduced length `|l|` of the group element of a word. -/
def rlen (l : List Test) : ℕ := (reduceRW l).1.length

theorem rlen_congr {l m : List Test} (h : groupElt l = groupElt m) : rlen l = rlen m := by
  unfold rlen; rw [reduceRW_eq_of_groupElt_eq h]

theorem rlen_of_reduced {l : List Test} (h : reducedB l = true) : rlen l = l.length := by
  unfold rlen; rw [reduceRW_of_reduced l h]

theorem rlen_reverse (l : List Test) : rlen l.reverse = rlen l := reduceRW_reverse_length l

theorem groupElt_eq_one_of_rlen {l : List Test} (h : rlen l = 0) : groupElt l = 1 := by
  rw [← groupElt_reduceRW]
  unfold rlen at h
  rw [List.eq_nil_of_length_eq_zero h]
  exact groupElt_nil

theorem rlen_parity (l : List Test) : rlen l % 2 = l.length % 2 := by
  unfold rlen
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [reduceRW, List.length_cons]
    rcases flipWord_length_cases a (reduceRW l) with h | ⟨h, -⟩
    · omega
    · rw [h, List.length_cons]; omega

theorem groupElt_mul_reverse_cancel (w : List Test) (x : UniversalProjectionAlgebra 4) :
    groupElt w * (groupElt w.reverse * x) = x := by
  rw [← mul_assoc, groupElt_mul_reverse, one_mul]

theorem groupElt_reverse_of_sq {s : List Test} (h : groupElt s * groupElt s = 1) :
    groupElt s.reverse = groupElt s := by
  calc groupElt s.reverse = groupElt s.reverse * (groupElt s * groupElt s) := by rw [h, mul_one]
    _ = groupElt s := by rw [← mul_assoc, groupElt_reverse_mul, one_mul]

/-! ## Alternating sequences and their partial products -/

/-- Adjacent letters differ. -/
def Alt (a : ℤ → Test) : Prop := ∀ n, a (n + 1) ≠ a n

/-- Shift: `(sh x a) k = a (k + x)`. -/
def sh (x : ℤ) (a : ℤ → Test) : ℤ → Test := fun k => a (k + x)

theorem alt_sh {a : ℤ → Test} (ha : Alt a) (x : ℤ) : Alt (sh x a) := by
  intro n
  simp only [sh]
  have := ha (n + x)
  rwa [show n + 1 + x = n + x + 1 by ring]

theorem sh_zero (a : ℤ → Test) : sh 0 a = a := by
  funext k; simp [sh]

theorem sh_sh (x y : ℤ) (a : ℤ → Test) : sh x (sh y a) = sh (x + y) a := by
  funext k; simp only [sh]; congr 1; ring

theorem sh_apply (x : ℤ) (a : ℤ → Test) (k : ℤ) : sh x a k = a (k + x) := rfl

/-- `P_a(n)`: the word `a_0 ⋯ a_{n-1}` for `n ≥ 0`, `a_{-1} ⋯ a_{n}` for `n < 0`. -/
def seqP (a : ℤ → Test) : ℤ → List Test
  | Int.ofNat n => (List.range n).map (fun i : ℕ => a (i : ℤ))
  | Int.negSucc n => (List.range (n + 1)).map (fun i : ℕ => a (-1 - (i : ℤ)))

theorem seqP_zero (a : ℤ → Test) : seqP a 0 = [] := rfl

theorem seqP_one (a : ℤ → Test) : seqP a 1 = [a 0] := by
  simp [seqP]

theorem seqP_neg_one (a : ℤ → Test) : seqP a (-1) = [a (-1)] := by
  show (List.range 1).map (fun i : ℕ => a (-1 - (i : ℤ))) = _
  simp

theorem seqP_ofNat (a : ℤ → Test) (n : ℕ) :
    seqP a (n : ℤ) = (List.range n).map (fun i : ℕ => a (i : ℤ)) := rfl

theorem seqP_length (a : ℤ → Test) (n : ℤ) : (seqP a n).length = n.natAbs := by
  cases n with
  | ofNat n => simp [seqP]
  | negSucc n => simp [seqP]

theorem reducedB_map_range (f : ℕ → Test) (hf : ∀ i, f (i + 1) ≠ f i) (n : ℕ) :
    reducedB ((List.range n).map f) = true := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine reducedB_cons _ _ (ih (f ∘ Nat.succ) (fun i => hf (i + 1))) ?_
    cases n with
    | zero => simp
    | succ n =>
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.head?_cons, Function.comp, ne_eq, Option.some.injEq]
      exact hf 0

theorem seqP_reduced {a : ℤ → Test} (ha : Alt a) (n : ℤ) : reducedB (seqP a n) = true := by
  cases n with
  | ofNat n =>
    show reducedB ((List.range n).map (fun i : ℕ => a (i : ℤ))) = true
    refine reducedB_map_range _ (fun i => ?_) n
    have := ha i
    simpa using this
  | negSucc n =>
    show reducedB ((List.range (n + 1)).map (fun i : ℕ => a (-1 - (i : ℤ)))) = true
    refine reducedB_map_range _ (fun i => ?_) (n + 1)
    have := ha (-2 - (i : ℤ))
    intro h
    apply this
    rw [show (-2 - (i : ℤ)) + 1 = -1 - (i : ℤ) by ring]
    rw [show -1 - ((i + 1 : ℕ) : ℤ) = -2 - (i : ℤ) by push_cast; ring] at h
    exact h.symm

theorem rlen_seqP {a : ℤ → Test} (ha : Alt a) (n : ℤ) : rlen (seqP a n) = n.natAbs := by
  rw [rlen_of_reduced (seqP_reduced ha n), seqP_length]

/-- One step: `P_a(n+1) = a_0 · P_{sh 1 a}(n)`. -/
theorem seqP_succ (a : ℤ → Test) (n : ℤ) :
    groupElt (seqP a (n + 1)) = specialSymmetry (a 0) * groupElt (seqP (sh 1 a) n) := by
  cases n with
  | ofNat m =>
    have e : (Int.ofNat m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [e, seqP_ofNat, List.range_succ_eq_map, List.map_cons, List.map_map, groupElt_cons]
    congr 2
  | negSucc m =>
    cases m with
    | zero =>
      rw [show Int.negSucc 0 + 1 = 0 by rfl, seqP_zero, groupElt_nil,
        show Int.negSucc 0 = -1 by rfl, seqP_neg_one, groupElt_singleton]
      simp only [sh]
      rw [show (-1 : ℤ) + 1 = 0 by ring, specialSymmetry_mul_self]
    | succ m =>
      rw [show Int.negSucc (m + 1) + 1 = Int.negSucc m by rfl]
      have e : seqP (sh 1 a) (Int.negSucc (m + 1)) = a 0 :: seqP a (Int.negSucc m) := by
        show (List.range (m + 1 + 1)).map (fun i : ℕ => sh 1 a (-1 - (i : ℤ))) =
          a 0 :: (List.range (m + 1)).map (fun i : ℕ => a (-1 - (i : ℤ)))
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        refine congrArg₂ List.cons (by simp [sh]) (List.map_congr_left (fun i _ => ?_))
        simp only [Function.comp, sh]
        congr 1
        push_cast; ring
      rw [e, groupElt_cons, specialSymmetry_mul_self']

/-- `P_a(x + n) = P_a(x) · P_{sh x a}(n)`. -/
theorem seqP_add (a : ℤ → Test) (x : ℤ) : ∀ n : ℤ,
    groupElt (seqP a (x + n)) = groupElt (seqP a x) * groupElt (seqP (sh x a) n) := by
  induction x using Int.induction_on with
  | zero => intro n; rw [zero_add, seqP_zero, groupElt_nil, one_mul, sh_zero]
  | succ i ih =>
    intro n
    have h1 := ih (1 + n)
    have h2 := ih 1
    rw [show (i : ℤ) + 1 + n = i + (1 + n) by ring, h1, h2, add_comm 1 n, seqP_succ, seqP_one,
      groupElt_singleton, sh_sh, sh_apply, zero_add, mul_assoc]
    congr 3
    ring
  | pred i ih =>
    intro n
    have h1 : groupElt (seqP a (-(i : ℤ) - 1 + n)) =
        groupElt (seqP a (-(i : ℤ))) * groupElt (seqP (sh (-(i : ℤ)) a) (n - 1)) := by
      rw [show -(i : ℤ) - 1 + n = -i + (n - 1) by ring]; exact ih _
    have h2 : groupElt (seqP a (-(i : ℤ) - 1)) =
        groupElt (seqP a (-(i : ℤ))) * specialSymmetry (a (-(i : ℤ) - 1)) := by
      have := ih (-1)
      rw [show -(i : ℤ) + -1 = -i - 1 by ring, seqP_neg_one, groupElt_singleton, sh_apply,
        show (-1 : ℤ) + -i = -i - 1 by ring] at this
      exact this
    have h3 := seqP_succ (sh (-(i : ℤ) - 1) a) (n - 1)
    rw [sub_add_cancel, sh_sh, sh_apply, zero_add,
      show (1 : ℤ) + (-(i : ℤ) - 1) = -i by ring] at h3
    rw [h1, h2, h3, mul_assoc, specialSymmetry_mul_self']

theorem seqP_succ_right (a : ℤ → Test) (n : ℤ) :
    groupElt (seqP a (n + 1)) = groupElt (seqP a n) * specialSymmetry (a n) := by
  rw [seqP_add, seqP_one, groupElt_singleton, sh_apply, zero_add]

/-- `|P_a(x)⁻¹ P_a(y)| = |y - x|`. -/
theorem groupElt_seqP_diff (a : ℤ → Test) (x y : ℤ) :
    groupElt ((seqP a x).reverse ++ seqP a y) = groupElt (seqP (sh x a) (y - x)) := by
  rw [groupElt_append, show y = x + (y - x) by ring, seqP_add, groupElt_reverse_mul_cancel]
  congr 3; ring

theorem rlen_seqP_diff {a : ℤ → Test} (ha : Alt a) (x y : ℤ) :
    rlen ((seqP a x).reverse ++ seqP a y) = (y - x).natAbs := by
  rw [rlen_congr (groupElt_seqP_diff a x y), rlen_seqP (alt_sh ha x)]

theorem seqP_inj {a : ℤ → Test} (ha : Alt a) {x y : ℤ}
    (h : groupElt (seqP a x) = groupElt (seqP a y)) : x = y := by
  have h1 := rlen_seqP_diff ha x y
  have h2 : groupElt ((seqP a x).reverse ++ seqP a y) = groupElt [] := by
    rw [groupElt_append, ← h, groupElt_reverse_mul, groupElt_nil]
  rw [rlen_congr h2] at h1
  have : (y - x).natAbs = 0 := by rw [← h1]; rfl
  omega

end AlbertSequential.HorizonFive
