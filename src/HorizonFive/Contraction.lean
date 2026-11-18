/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Assembly

/-! # lem:cer:h5:refl(b), proved: `reflectionContraction : ReflectionContraction`

Paper (companion `app:cert:h5`, proof of lem:cer:h5:refl(b)): for reflections `t, u` of `G = ℤ₂^{*4}` there is
a Jordan polynomial `K` of degree `|tu|` with `σ̂(K) = [tu]` and `ν̂(K) = ς(t) ∘ ς(u)`.

The Lean route follows the paper's descent.

* Canonical forms (`exists_canon`): every presentation `(v, i)` of a reflection can be replaced
  by one whose word `v i v^R` is reduced, with the same group element and the same `ς`
  (`U_{s_a}² = id` and `U_{s_i} s_i = s_i`).  This is the paper's well-definedness of `ς`, in
  the computational form needed here.
* Common segment (`exists_lcp`): `v = w x`, `v' = w y` with `x, y` empty or with different
  first letters.
* First case (`contr_good`): the word `w (x i x^R)(y j y^R) w^R` is reduced and
  `K = U_{x_{w_1}} ⋯ U_{x_{w_m}} (R_{t_0} ∘ R_{u_0})`.
* `t = u` (`contr_equal`): `K = 1`.
* Remaining case (`contr_bad`): `t = w i w^R`, `u = w i z j z^R i w^R`; replace `(t,u)` by
  `(tut, t)`, with `tut = w z j z^R w^R` (two letters shorter) and the contraction
  `L_s U_s = L_s` (`native_reflection_contraction`).  The symmetric case uses `contr_symm`.
* The degree is first bounded by `|tu|` and then padded to equality by adding `0 · x_1^n`
  (`pad`); `deg` is the syntactic degree of `JPoly`.

Facts about `G` are read in the universal projection algebra: `reduceRW l = g` iff
`groupElt l = groupElt g` (`reduceRW_eq_iff`, from linear independence of reduced words). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## The group `G` inside the universal projection algebra -/

theorem reduceRW_eq_iff (l : List Test) (g : RW) :
    reduceRW l = g ↔ groupElt l = groupElt g.1 := by
  constructor
  · rintro rfl; exact (groupElt_reduceRW l).symm
  · intro h
    have h1 := coef_groupElt g l
    rw [h, coef_groupElt, reduceRW_val, ite_eq_left rfl] at h1
    by_contra hne
    rw [ite_eq_right hne] at h1
    exact one_ne_zero h1

theorem reduceRW_eq_of_groupElt_eq {l m : List Test} (h : groupElt l = groupElt m) :
    reduceRW l = reduceRW m :=
  (reduceRW_eq_iff l (reduceRW m)).2 (by rw [groupElt_reduceRW]; exact h)

theorem groupElt_mul_reverse (l : List Test) : groupElt l * groupElt l.reverse = 1 := by
  have := groupElt_reverse_mul l.reverse
  rwa [List.reverse_reverse] at this

theorem groupElt_reverse_eq {l m : List Test} (h : groupElt l = groupElt m) :
    groupElt l.reverse = groupElt m.reverse := by
  calc groupElt l.reverse = groupElt l.reverse * (groupElt m * groupElt m.reverse) := by
        rw [groupElt_mul_reverse, mul_one]
    _ = (groupElt l.reverse * groupElt l) * groupElt m.reverse := by rw [h, mul_assoc]
    _ = groupElt m.reverse := by rw [groupElt_reverse_mul, one_mul]

theorem classElt_eq_of_groupElt_eq {l m : List Test} (h : groupElt l = groupElt m) :
    classElt l = classElt m := by
  unfold classElt
  rw [h, groupElt_reverse_eq h]

theorem groupElt_reverse_mul_cancel (w : List Test) (x : UniversalProjectionAlgebra 4) :
    groupElt w.reverse * (groupElt w * x) = x := by
  rw [← mul_assoc, groupElt_reverse_mul, one_mul]

theorem reduceRW_reverse_length (l : List Test) :
    (reduceRW l.reverse).1.length = (reduceRW l).1.length := by
  have h : reduceRW l.reverse = ⟨(reduceRW l).1.reverse, reducedB_reverse _ (reduceRW l).2⟩ :=
    (reduceRW_eq_iff _ _).2 (groupElt_reverse_eq (groupElt_reduceRW l).symm)
  rw [h, List.length_reverse]

/-! ## Reduced words -/

theorem reducedB_left {A B : List Test} (h : reducedB (A ++ B) = true) : reducedB A = true :=
  ((reducedB_append A B).1 h).1

theorem reducedB_right {A B : List Test} (h : reducedB (A ++ B) = true) : reducedB B = true :=
  ((reducedB_append A B).1 h).2.1

theorem reducedB_append3 (A B C : List Test) (hAB : reducedB (A ++ B) = true)
    (hBC : reducedB (B ++ C) = true) (hB : B ≠ []) : reducedB (A ++ B ++ C) = true := by
  rw [List.append_assoc, reducedB_append]
  refine ⟨reducedB_left hAB, hBC, ?_⟩
  intro a b ha hb
  obtain ⟨c, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  have hcb : c = b := by simpa using hb
  have hac := ((reducedB_append A (c :: B')).1 hAB).2.2 a c ha rfl
  rw [← hcb]
  exact hac

theorem reducedB_conj (a b : Test) (l : List Test) (hl : reducedB l = true)
    (hh : l.head? = some b) (hlast : l.getLast? = some b) (hab : a ≠ b) :
    reducedB (a :: (l ++ [a])) = true := by
  have h1 : reducedB (l ++ [a]) = true := by
    rw [reducedB_append]
    refine ⟨hl, rfl, fun x y hx hy => ?_⟩
    rw [hlast] at hx
    have hx' : b = x := by simpa using hx
    have hy' : a = y := by simpa using hy
    intro e
    exact hab (hy'.trans (e.symm.trans hx'.symm))
  refine reducedB_cons a _ h1 ?_
  cases l with
  | nil => simp at hh
  | cons c l =>
    have hc : c = b := by simpa using hh
    intro e
    have : c = a := by simpa using e
    exact hab (this.symm.trans hc)

theorem reducedB_of_conj (a : Test) (l : List Test) (h : reducedB (a :: (l ++ [a])) = true) :
    reducedB l = true :=
  reducedB_left (reducedB_tail a _ h)

/-! ## Reflection words -/

/-- The first letter of the word of a presentation. -/
def Refl.lead (t : Refl) : Test := t.v.head?.getD t.i

theorem Refl.word_reverse (t : Refl) : t.word.reverse = t.word := by
  simp [Refl.word]

theorem Refl.word_head (t : Refl) : t.word.head? = some t.lead := by
  rcases t with ⟨v, i⟩
  cases v <;> simp [Refl.word, Refl.lead]

theorem Refl.word_getLast (t : Refl) : t.word.getLast? = some t.lead := by
  rw [← List.head?_reverse, Refl.word_reverse, Refl.word_head]

theorem Refl.word_ne_nil (t : Refl) : t.word ≠ [] := by
  simp [Refl.word]

theorem Refl.word_length (t : Refl) : t.word.length = 2 * t.v.length + 1 := by
  simp only [Refl.word, List.length_append, List.length_singleton, List.length_reverse]
  omega

theorem word_cons_eq (a : Test) (v : List Test) (i : Test) :
    Refl.word ⟨a :: v, i⟩ = a :: (Refl.word ⟨v, i⟩ ++ [a]) := by
  simp [Refl.word]

theorem word_split (w x : List Test) (i : Test) :
    Refl.word ⟨w ++ x, i⟩ = w ++ Refl.word ⟨x, i⟩ ++ w.reverse := by
  simp [Refl.word, List.reverse_append]

theorem groupElt_word_cons (a : Test) (v : List Test) (i : Test) :
    groupElt (Refl.word ⟨a :: v, i⟩) =
      specialSymmetry a * groupElt (Refl.word ⟨v, i⟩) * specialSymmetry a := by
  rw [word_cons_eq, groupElt_cons, groupElt_append, mul_assoc]
  congr 2
  simp [groupElt]

theorem varsigma_cons (p : Test → Albert) (a : Test) (v : List Test) (i : Test) :
    varsigma p ⟨a :: v, i⟩ = quadraticMap (nativeSymmetry p a) (varsigma p ⟨v, i⟩) := rfl

theorem varsigma_append (p : Test → Albert) (w x : List Test) (i : Test) :
    varsigma p ⟨w ++ x, i⟩ = nativeRho p w (varsigma p ⟨x, i⟩) :=
  nativeRho_append p w x (nativeSymmetry p i)

/-! ## Native facts for symmetries -/

theorem quadraticMap_sym_sym (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) : quadraticMap (nativeSymmetry p i) (nativeSymmetry p i) = nativeSymmetry p i := by
  unfold quadraticMap
  rw [nativeSymmetry_sq p hp, jordanMul_albertUnit_right, jordanMul_albertUnit_left]
  abel

theorem quadraticMap_sym_invol (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) (y : Albert) :
    quadraticMap (nativeSymmetry p i) (quadraticMap (nativeSymmetry p i) y) = y := by
  have h := (native_canonRelations p hp).CC i y
  rwa [albertTarget_Uop, albertTarget_Uop] at h

theorem quadraticMap_sym_unit (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) : quadraticMap (nativeSymmetry p i) albertUnit = albertUnit := by
  have h := (native_canonRelations p hp).Cone i
  rw [albertTarget_Uop] at h
  exact h

theorem nativeRho_unit (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (w : List Test) : nativeRho p w albertUnit = albertUnit := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show quadraticMap (nativeSymmetry p a) (nativeRho p w albertUnit) = albertUnit
    rw [ih, quadraticMap_sym_unit p hp]

/-! ## Reflection polynomials and padding -/

/-- `U_{x_{w_1}} ⋯ U_{x_{w_m}} Y`. -/
def uFold (w : List Test) (Y : JPoly Test) : JPoly Test :=
  w.foldr (fun a y => JPoly.U (.var a) y) Y

/-- The reflection polynomial `R_t = U_{x_{v_1}} ⋯ U_{x_{v_k}} x_i` of a presentation. -/
def rpoly (t : Refl) : JPoly Test := uFold t.v (.var t.i)

theorem deg_U_var (a : Test) (Y : JPoly Test) : (JPoly.U (.var a) Y).deg = Y.deg + 2 := by
  simp only [JPoly.U, JPoly.deg]
  omega

theorem deg_uFold (w : List Test) (Y : JPoly Test) :
    (uFold w Y).deg = 2 * w.length + Y.deg := by
  induction w with
  | nil => simp [uFold]
  | cons a w ih =>
    simp only [uFold, List.foldr_cons] at ih ⊢
    rw [deg_U_var, ih, List.length_cons]
    omega

theorem specialEval_uFold (w : List Test) (Y : JPoly Test) :
    specialEval (uFold w Y) = groupElt w * specialEval Y * groupElt w.reverse := by
  induction w with
  | nil => simp [uFold, groupElt]
  | cons a w ih =>
    change (specialTarget _).eval specialSymmetry (JPoly.U _ _) = _
    rw [JTarget.eval_U, specialTarget_Uop]
    change specialSymmetry a * specialEval (uFold w Y) * specialSymmetry a = _
    rw [ih, List.reverse_cons, groupElt_append, groupElt_cons]
    simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      _root_.mul_one, mul_assoc]

theorem albertEval_uFold (p : Test → Albert) (w : List Test) (Y : JPoly Test) :
    albertEval p (uFold w Y) = nativeRho p w (albertEval p Y) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change albertTarget.eval (nativeSymmetry p) (JPoly.U _ _) = _
    rw [JTarget.eval_U, albertTarget_Uop]
    change quadraticMap (nativeSymmetry p a) (albertEval p (uFold w Y)) = _
    rw [ih]
    rfl

theorem deg_rpoly (t : Refl) : (rpoly t).deg = t.word.length := by
  rw [rpoly, deg_uFold, Refl.word_length]
  rfl

theorem specialEval_rpoly (t : Refl) : specialEval (rpoly t) = groupElt t.word := by
  rw [rpoly, specialEval_uFold, Refl.word, groupElt_append, groupElt_append]
  congr 2
  simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, _root_.mul_one]
  rfl

theorem albertEval_rpoly (p : Test → Albert) (t : Refl) : albertEval p (rpoly t) = varsigma p t := by
  rw [rpoly, albertEval_uFold]
  rfl

/-- `x_1^n` (right-nested), of syntactic degree `n`. -/
def powX : ℕ → JPoly Test
  | 0 => .one
  | n + 1 => .mul (.var 0) (powX n)

theorem deg_powX (n : ℕ) : (powX n).deg = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powX, JPoly.deg, ih]
    omega

/-- Padding `K + 0 · x_1^n`: same values, degree `max (deg K) n`. -/
def pad (K : JPoly Test) (n : ℕ) : JPoly Test := .add K (.smul 0 (powX n))

theorem deg_pad (K : JPoly Test) (n : ℕ) (h : K.deg ≤ n) : (pad K n).deg = n := by
  simp only [pad, JPoly.deg, deg_powX]
  omega

theorem specialEval_pad (K : JPoly Test) (n : ℕ) : specialEval (pad K n) = specialEval K := by
  change specialEval K + (0 : ℝ) • specialEval (powX n) = _
  rw [zero_smul, add_zero]

theorem albertEval_pad (p : Test → Albert) (K : JPoly Test) (n : ℕ) :
    albertEval p (pad K n) = albertEval p K := by
  change albertEval p K + (0 : ℝ) • albertEval p (powX n) = _
  rw [zero_smul, add_zero]

/-! ## Canonical presentations -/

theorem exists_canon_v (i : Test) (v : List Test) :
    ∃ w : List Test, reducedB (Refl.word ⟨w, i⟩) = true ∧
      groupElt (Refl.word ⟨w, i⟩) = groupElt (Refl.word ⟨v, i⟩) ∧
      w.length ≤ v.length ∧
      ∀ p : Test → Albert, (∀ k, IsAtom (p k)) → varsigma p ⟨w, i⟩ = varsigma p ⟨v, i⟩ := by
  induction v with
  | nil => exact ⟨[], rfl, rfl, le_rfl, fun _ _ => rfl⟩
  | cons a v ih =>
    obtain ⟨w, hred, hg, hlen, hς⟩ := ih
    rcases w with _ | ⟨b, w'⟩
    · by_cases hia : i = a
      · subst hia
        refine ⟨[], rfl, ?_, Nat.zero_le _, ?_⟩
        · rw [groupElt_word_cons _ v, ← hg]
          simp [Refl.word, groupElt, mul_assoc, specialSymmetry_mul_self]
        · intro p hp
          rw [varsigma_cons, ← hς p hp]
          exact (quadraticMap_sym_sym p (fun k => (hp k).1) _).symm
      · refine ⟨[a], ?_, ?_, by simp, ?_⟩
        · rw [word_cons_eq]
          exact reducedB_conj a i _ rfl rfl rfl (Ne.symm hia)
        · rw [groupElt_word_cons a [], groupElt_word_cons a v, hg]
        · intro p hp
          show quadraticMap (nativeSymmetry p a) (varsigma p ⟨[], i⟩) =
            quadraticMap (nativeSymmetry p a) (varsigma p ⟨v, i⟩)
          rw [hς p hp]
    · by_cases hba : b = a
      · subst hba
        refine ⟨w', ?_, ?_, ?_, ?_⟩
        · rw [word_cons_eq] at hred
          exact reducedB_of_conj _ _ hred
        · rw [groupElt_word_cons _ v, ← hg, groupElt_word_cons _ w']
          simp only [mul_assoc, specialSymmetry_mul_self', specialSymmetry_mul_self, _root_.mul_one]
        · simp only [List.length_cons] at hlen ⊢
          omega
        · intro p hp
          rw [varsigma_cons _ _ v, ← hς p hp, varsigma_cons _ _ w',
            quadraticMap_sym_invol p (fun k => (hp k).1)]
      · refine ⟨a :: b :: w', ?_, ?_, ?_, ?_⟩
        · rw [word_cons_eq]
          exact reducedB_conj a b _ hred (Refl.word_head _) (Refl.word_getLast _) (Ne.symm hba)
        · rw [groupElt_word_cons a (b :: w'), groupElt_word_cons a v, hg]
        · simp only [List.length_cons] at hlen ⊢
          omega
        · intro p hp
          show quadraticMap (nativeSymmetry p a) (varsigma p ⟨b :: w', i⟩) =
            quadraticMap (nativeSymmetry p a) (varsigma p ⟨v, i⟩)
          rw [hς p hp]

/-- Every presentation has a canonical (reduced-word) presentation with the same group element
and the same `ς` (the paper's well-definedness of `ς`, computational form). -/
theorem exists_canon (t : Refl) : ∃ t' : Refl, reducedB t'.word = true ∧
    groupElt t'.word = groupElt t.word ∧ t'.word.length ≤ t.word.length ∧
    ∀ p : Test → Albert, (∀ k, IsAtom (p k)) → varsigma p t' = varsigma p t := by
  obtain ⟨v, i⟩ := t
  obtain ⟨w, h1, h2, h3, h4⟩ := exists_canon_v i v
  refine ⟨⟨w, i⟩, h1, h2, ?_, h4⟩
  rw [Refl.word_length, Refl.word_length]
  show 2 * w.length + 1 ≤ 2 * v.length + 1
  omega

/-- Longest common initial segment. -/
theorem exists_lcp (v v' : List Test) : ∃ w x y : List Test, v = w ++ x ∧ v' = w ++ y ∧
    (x = [] ∨ y = [] ∨ ∃ c d x' y', c ≠ d ∧ x = c :: x' ∧ y = d :: y') := by
  induction v generalizing v' with
  | nil => exact ⟨[], [], v', rfl, rfl, Or.inl rfl⟩
  | cons a v ih =>
    cases v' with
    | nil => exact ⟨[], a :: v, [], rfl, rfl, Or.inr (Or.inl rfl)⟩
    | cons b v' =>
      by_cases hab : a = b
      · cases hab
        obtain ⟨w, x, y, h1, h2, h3⟩ := ih v'
        exact ⟨a :: w, x, y, by simp [h1], by simp [h2], h3⟩
      · exact ⟨[], a :: v, b :: v', rfl, rfl, Or.inr (Or.inr ⟨a, b, v, v', hab, rfl, rfl⟩)⟩

/-! ## The descent -/

/-- The conclusion of lem:cer:h5:refl(b) with `deg K ≤ |tu|`. -/
def ContrConcl (t u : Refl) : Prop :=
  ∃ K : JPoly Test, K.deg ≤ (reduceRW (t.word ++ u.word)).1.length ∧
    specialEval K = classElt (t.word ++ u.word) ∧
    ∀ p : Test → Albert, (∀ k, IsAtom (p k)) →
      albertEval p K = jordanMul (varsigma p t) (varsigma p u)

theorem contr_symm {t u : Refl} (h : ContrConcl t u) : ContrConcl u t := by
  obtain ⟨K, hdeg, hspec, halb⟩ := h
  have hrev : (t.word ++ u.word).reverse = u.word ++ t.word := by
    rw [List.reverse_append, Refl.word_reverse, Refl.word_reverse]
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← hrev, reduceRW_reverse_length]; exact hdeg
  · rw [← hrev, classElt_reverse]; exact hspec
  · intro p hp; rw [halb p hp, jordanMul_comm]

/-- `t = u`: `K = 1`. -/
theorem contr_equal (t : Refl) : ContrConcl t t := by
  refine ⟨.one, Nat.zero_le _, ?_, ?_⟩
  · have h1 := groupElt_reverse_mul t.word
    rw [Refl.word_reverse] at h1
    unfold classElt
    rw [List.reverse_append, Refl.word_reverse, groupElt_append, h1]
    show (1 : UniversalProjectionAlgebra 4) = _
    module
  · intro p hp
    have hp' : ∀ k, jordanMul (p k) (p k) = p k := fun k => (hp k).1
    show albertUnit = _
    rw [varsigma_eq, ← nativeRho_jordanMul p hp, nativeSymmetry_sq p hp', nativeRho_unit p hp']

/-- First case of the paper: the word `w t_0 u_0 w^R` is reduced. -/
theorem contr_good (w x y : List Test) (i j : Test)
    (ht : reducedB (Refl.word ⟨w ++ x, i⟩) = true) (hu : reducedB (Refl.word ⟨w ++ y, j⟩) = true)
    (hj : (⟨x, i⟩ : Refl).lead ≠ (⟨y, j⟩ : Refl).lead) :
    ContrConcl ⟨w ++ x, i⟩ ⟨w ++ y, j⟩ := by
  rw [word_split] at ht hu
  have hT : reducedB (w ++ Refl.word ⟨x, i⟩) = true := reducedB_left ht
  have hU : reducedB (Refl.word ⟨y, j⟩ ++ w.reverse) = true := by
    rw [List.append_assoc] at hu
    exact reducedB_right hu
  have hT0 : reducedB (Refl.word ⟨x, i⟩) = true := reducedB_right hT
  have hU0 : reducedB (Refl.word ⟨y, j⟩) = true := reducedB_left hU
  have hTU : reducedB (Refl.word ⟨x, i⟩ ++ Refl.word ⟨y, j⟩) = true := by
    rw [reducedB_append]
    refine ⟨hT0, hU0, fun a b ha hb => ?_⟩
    rw [Refl.word_getLast] at ha
    rw [Refl.word_head] at hb
    have ha' : (⟨x, i⟩ : Refl).lead = a := by simpa using ha
    have hb' : (⟨y, j⟩ : Refl).lead = b := by simpa using hb
    rw [← ha', ← hb']
    exact hj
  have hL : reducedB (w ++ Refl.word ⟨x, i⟩ ++ Refl.word ⟨y, j⟩ ++ w.reverse) = true :=
    reducedB_append3 _ _ _ (reducedB_append3 _ _ _ hT hTU (Refl.word_ne_nil _)) hU
      (Refl.word_ne_nil _)
  have hG : groupElt (w ++ Refl.word ⟨x, i⟩ ++ Refl.word ⟨y, j⟩ ++ w.reverse) =
      groupElt (Refl.word ⟨w ++ x, i⟩ ++ Refl.word ⟨w ++ y, j⟩) := by
    rw [word_split w x, word_split w y]
    simp only [groupElt_append, mul_assoc, groupElt_reverse_mul_cancel]
  have hR : reduceRW (Refl.word ⟨w ++ x, i⟩ ++ Refl.word ⟨w ++ y, j⟩) = ⟨_, hL⟩ :=
    (reduceRW_eq_iff _ _).2 hG.symm
  refine ⟨uFold w (.mul (rpoly ⟨x, i⟩) (rpoly ⟨y, j⟩)), ?_, ?_, ?_⟩
  · rw [hR, deg_uFold]
    simp only [JPoly.deg, deg_rpoly, List.length_append, List.length_reverse]
    omega
  · rw [specialEval_uFold]
    change groupElt w * (specialTarget _).mul (specialEval (rpoly ⟨x, i⟩))
      (specialEval (rpoly ⟨y, j⟩)) * groupElt w.reverse = _
    rw [specialTarget_mul, specialEval_rpoly, specialEval_rpoly]
    unfold classElt
    rw [List.reverse_append, Refl.word_reverse, Refl.word_reverse, word_split w x, word_split w y]
    simp only [groupElt_append, _root_.mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
      groupElt_reverse_mul_cancel, smul_add]
  · intro p hp
    rw [albertEval_uFold]
    change nativeRho p w (jordanMul (albertEval p (rpoly ⟨x, i⟩)) (albertEval p (rpoly ⟨y, j⟩))) = _
    rw [albertEval_rpoly, albertEval_rpoly, nativeRho_jordanMul p hp, varsigma_append,
      varsigma_append]

theorem bad_groupElt (w z : List Test) (i j : Test) :
    groupElt (Refl.word ⟨w ++ z, j⟩ ++ Refl.word ⟨w, i⟩) =
      groupElt (Refl.word ⟨w, i⟩ ++ Refl.word ⟨w ++ i :: z, j⟩) := by
  simp only [Refl.word, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.cons_append, List.singleton_append, groupElt_append, groupElt_cons,
    mul_assoc, groupElt_reverse_mul_cancel, specialSymmetry_mul_self']

theorem bad_varsigma (p : Test → Albert) (hp : ∀ k, IsAtom (p k)) (w z : List Test) (i j : Test) :
    jordanMul (varsigma p ⟨w ++ z, j⟩) (varsigma p ⟨w, i⟩) =
      jordanMul (varsigma p ⟨w, i⟩) (varsigma p ⟨w ++ i :: z, j⟩) := by
  have hp' : ∀ k, jordanMul (p k) (p k) = p k := fun k => (hp k).1
  rw [varsigma_append p w z, varsigma_append p w (i :: z), varsigma_cons]
  have e : varsigma p ⟨w, i⟩ = nativeRho p w (nativeSymmetry p i) := rfl
  rw [e, ← nativeRho_jordanMul p hp, ← nativeRho_jordanMul p hp]
  congr 1
  rw [jordanMul_comm (nativeSymmetry p i), native_reflection_contraction p hp' i]

/-- Remaining case of the paper: `t = w i w^R`, `u = w i z j z^R i w^R`; pass to `(tut, t)`. -/
theorem contr_bad (w z : List Test) (i j : Test)
    (IH : ∀ t'' : Refl, reducedB t''.word = true →
      t''.word.length + 2 ≤ (Refl.word ⟨w ++ i :: z, j⟩).length → ContrConcl t'' ⟨w, i⟩) :
    ContrConcl ⟨w, i⟩ ⟨w ++ i :: z, j⟩ := by
  obtain ⟨t'', hr, hg, hl, hς⟩ := exists_canon ⟨w ++ z, j⟩
  have hlen : (Refl.word ⟨w ++ z, j⟩).length + 2 = (Refl.word ⟨w ++ i :: z, j⟩).length := by
    rw [Refl.word_length, Refl.word_length]
    show 2 * (w ++ z).length + 1 + 2 = 2 * (w ++ i :: z).length + 1
    simp only [List.length_append, List.length_cons]
    omega
  obtain ⟨K, hdeg, hspec, halb⟩ := IH t'' hr (by omega)
  have hG : groupElt (t''.word ++ Refl.word ⟨w, i⟩) =
      groupElt (Refl.word ⟨w, i⟩ ++ Refl.word ⟨w ++ i :: z, j⟩) := by
    rw [groupElt_append, hg, ← groupElt_append]
    exact bad_groupElt w z i j
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← reduceRW_eq_of_groupElt_eq hG]; exact hdeg
  · rw [hspec, classElt_eq_of_groupElt_eq hG]
  · intro p hp
    rw [halb p hp, hς p hp]
    exact bad_varsigma p hp w z i j

theorem contraction_core (n : ℕ) : ∀ t u : Refl, reducedB t.word = true →
    reducedB u.word = true → t.word.length + u.word.length ≤ n → ContrConcl t u := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t u ht hu hn
  obtain ⟨v, i⟩ := t
  obtain ⟨v', j⟩ := u
  obtain ⟨w, x, y, rfl, rfl, h3⟩ := exists_lcp v v'
  rcases h3 with rfl | rfl | ⟨c, d, x', y', hcd, rfl, rfl⟩
  · rcases y with _ | ⟨d, z⟩
    · by_cases hij : i = j
      · subst hij; exact contr_equal _
      · exact contr_good w [] [] i j ht hu (by simpa [Refl.lead] using hij)
    · by_cases hdi : d = i
      · subst hdi
        simp only [List.append_nil] at ht hn ⊢
        exact contr_bad w z _ _ (fun t'' hr hl => ih _ (by omega) t'' _ hr ht le_rfl)
      · exact contr_good w [] (d :: z) i j ht hu (by simpa [Refl.lead] using Ne.symm hdi)
  · rcases x with _ | ⟨c, z⟩
    · by_cases hij : i = j
      · subst hij; exact contr_equal _
      · exact contr_good w [] [] i j ht hu (by simpa [Refl.lead] using hij)
    · by_cases hcj : c = j
      · subst hcj
        simp only [List.append_nil] at hu hn ⊢
        exact contr_symm (contr_bad w z _ _ (fun t'' hr hl => ih _ (by omega) t'' _ hr hu le_rfl))
      · exact contr_good w (c :: z) [] i j ht hu (by simpa [Refl.lead] using hcj)
  · exact contr_good w (c :: x') (d :: y') i j ht hu (by simpa [Refl.lead] using hcd)

/-- **lem:cer:h5:refl(b), proved** (no hypotheses). -/
theorem reflectionContraction : ReflectionContraction := by
  intro t u
  obtain ⟨t', ht', hgt, -, hςt⟩ := exists_canon t
  obtain ⟨u', hu', hgu, -, hςu⟩ := exists_canon u
  obtain ⟨K, hdeg, hspec, halb⟩ := contraction_core _ t' u' ht' hu' le_rfl
  have hg : groupElt (t'.word ++ u'.word) = groupElt (t.word ++ u.word) := by
    rw [groupElt_append, groupElt_append, hgt, hgu]
  refine ⟨pad K (reduceRW (t.word ++ u.word)).1.length, ?_, ?_, ?_⟩
  · exact deg_pad _ _ (by rw [← reduceRW_eq_of_groupElt_eq hg]; exact hdeg)
  · rw [specialEval_pad, hspec, classElt_eq_of_groupElt_eq hg]
  · intro p hp
    rw [albertEval_pad, halb p hp, hςt p hp, hςu p hp]

/-- The horizon-five clause with lem:cer:h5:refl(b) discharged. -/
theorem horizonFive_of_refl_a_and_seven (hA : ReflectionClassConsistency)
    (h7 : TransferThroughSeven) : HorizonFiveClause :=
  horizonFive_of_lemmas hA reflectionContraction h7

end AlbertSequential.HorizonFive
