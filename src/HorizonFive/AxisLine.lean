/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Axis

/-! # Reflections inverting a cyclically reduced element: dihedral coordinates

Continuation of `Axis.lean` (group-theoretic core of lem:cer:h5:refl(a), word-combinatorial route).

* `axis_lemma`: for an alternating sequence `a` of period `L ≥ 2` with `k = P_a(L)`, a reduced word
  `g` with `|g⁻¹ k g| = L` is one of the `P_a(n)`.
* `refl_on_axis`: an involution `s` of odd length with `s k s = k⁻¹` acts on the line by
  `P_a(m) ↦ P_a(c - m)`.
* `dihedral_coords`: the reflection centres `c` form an arithmetic progression `b + δℤ`; for two
  factorizations `k = tu = t'u'` into such reflections the four centres are `b + nδ` with
  `n_t - n_u = n_{t'} - n_{u'}`.
* `cyc_reduce`, `cycSeq`: every reduced word is `g k g⁻¹` with `k` cyclically reduced, and a
  cyclically reduced `k` is `P_a(|k|)` for its periodic letter sequence. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- Period `L`. -/
def Per (a : ℤ → Test) (L : ℕ) : Prop := ∀ n, a (n + L) = a n

theorem per_sh {a : ℤ → Test} {L : ℕ} (h : Per a L) (x : ℤ) : Per (sh x a) L := by
  intro n
  simp only [sh]
  rw [show n + L + x = n + x + L by ring]
  exact h _

theorem sh_per {a : ℤ → Test} {L : ℕ} (h : Per a L) : sh (L : ℤ) a = a := by
  funext n; exact h n

theorem seqP_cons_form (a : ℤ → Test) (L : ℕ) (hL : 1 ≤ L) :
    ∃ K', seqP a L = a 0 :: K' := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  refine ⟨(List.range n).map (fun i : ℕ => a ((i + 1 : ℕ) : ℤ)), ?_⟩
  rw [seqP_ofNat, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem seqP_snoc_form (a : ℤ → Test) (L : ℕ) (hL : 1 ≤ L) :
    ∃ K', seqP a L = K' ++ [a ((L : ℤ) - 1)] := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  refine ⟨(List.range n).map (fun i : ℕ => a (i : ℤ)), ?_⟩
  rw [seqP_ofNat, List.range_succ, List.map_append, List.map_singleton]
  congr 3
  push_cast; ring

/-- Rotation: `P_a(m)⁻¹ P_a(L) P_a(m) = P_{sh m a}(L)`. -/
theorem groupElt_conj_seqP {a : ℤ → Test} {L : ℕ} (hper : Per a L) (m : ℤ) :
    groupElt ((seqP a m).reverse ++ seqP a L ++ seqP a m) = groupElt (seqP (sh m a) L) := by
  rw [List.append_assoc, groupElt_append, groupElt_append]
  have h1 : groupElt (seqP a L) * groupElt (seqP a m) = groupElt (seqP a (L + m)) := by
    rw [seqP_add, sh_per hper]
  rw [h1, add_comm, seqP_add, groupElt_reverse_mul_cancel]

theorem rlen_conj_seqP {a : ℤ → Test} (ha : Alt a) {L : ℕ} (hper : Per a L) (m : ℤ) :
    rlen ((seqP a m).reverse ++ seqP a L ++ seqP a m) = L := by
  rw [rlen_congr (groupElt_conj_seqP hper m), rlen_seqP (alt_sh ha m)]
  rfl

theorem shift_key_one {a : ℤ → Test} {L : ℕ} (hL : 1 ≤ L) (hper : Per a L) :
    groupElt ([a 0] ++ seqP a L ++ [a 0]) = groupElt (seqP (sh 1 a) L) := by
  have h1 := seqP_succ a ((L : ℤ) - 1)
  have h2 := seqP_succ_right (sh 1 a) ((L : ℤ) - 1)
  rw [sub_add_cancel] at h1 h2
  rw [h2, groupElt_append, groupElt_append, h1, groupElt_singleton, sh_apply,
    show (L : ℤ) - 1 + 1 = 0 + L by ring, hper 0, ← mul_assoc, specialSymmetry_mul_self, one_mul]

theorem shift_key_neg {a : ℤ → Test} {L : ℕ} (hL : 1 ≤ L) (hper : Per a L) :
    groupElt ([a (-1)] ++ seqP a L ++ [a (-1)]) = groupElt (seqP (sh (-1) a) L) := by
  have h1 := seqP_succ (sh (-1) a) ((L : ℤ) - 1)
  have h2 := seqP_succ_right a ((L : ℤ) - 1)
  rw [sub_add_cancel] at h1 h2
  rw [sh_sh, show (1 : ℤ) + -1 = 0 by ring, sh_zero, sh_apply, zero_add] at h1
  rw [h1, groupElt_append, groupElt_append, h2, groupElt_singleton,
    show (L : ℤ) - 1 = -1 + L by ring, hper (-1), mul_assoc, mul_assoc,
    specialSymmetry_mul_self, mul_one]

/-! ## The axis lemma -/

theorem axis_lemma (L : ℕ) (hL : 2 ≤ L) (g : List Test) (hg : reducedB g = true) :
    ∀ a : ℤ → Test, Alt a → Per a L →
      rlen (g.reverse ++ seqP a L ++ g) = L → ∃ n : ℤ, groupElt g = groupElt (seqP a n) := by
  induction g with
  | nil => intro a _ _ _; exact ⟨0, rfl⟩
  | cons r g ih =>
    intro a ha hper hlen
    have hg' : reducedB g = true := reducedB_tail r g hg
    have hconj : ∀ M : List Test, groupElt ([r] ++ seqP a L ++ [r]) = groupElt M →
        groupElt ((r :: g).reverse ++ seqP a L ++ (r :: g)) = groupElt (g.reverse ++ M ++ g) := by
      intro M hM
      have e : (r :: g).reverse ++ seqP a L ++ (r :: g) =
          g.reverse ++ ([r] ++ seqP a L ++ [r]) ++ g := by simp
      rw [e, groupElt_append, groupElt_append, hM, ← groupElt_append, ← groupElt_append]
    by_cases h0 : r = a 0
    · have key := shift_key_one (by omega) hper
      rw [← h0] at key
      obtain ⟨n, hn⟩ := ih hg' (sh 1 a) (alt_sh ha 1) (per_sh hper 1)
        (by rw [← rlen_congr (hconj _ key)]; exact hlen)
      refine ⟨n + 1, ?_⟩
      rw [groupElt_cons, hn, seqP_succ, h0]
    · by_cases h1 : r = a (-1)
      · have key := shift_key_neg (by omega) hper
        rw [← h1] at key
        obtain ⟨n, hn⟩ := ih hg' (sh (-1) a) (alt_sh ha (-1)) (per_sh hper (-1))
          (by rw [← rlen_congr (hconj _ key)]; exact hlen)
        refine ⟨n - 1, ?_⟩
        have h3 := seqP_succ (sh (-1) a) (n - 1)
        rw [sub_add_cancel, sh_sh, show (1 : ℤ) + -1 = 0 by ring, sh_zero, sh_apply, zero_add,
          ← h1] at h3
        rw [groupElt_cons, hn, h3, specialSymmetry_mul_self']
      · exfalso
        obtain ⟨K1, hK1⟩ := seqP_cons_form a L (by omega)
        obtain ⟨K2, hK2⟩ := seqP_snoc_form a L (by omega)
        have hK := seqP_reduced ha (L : ℤ)
        have hlast : a ((L : ℤ) - 1) = a (-1) := by
          rw [show (L : ℤ) - 1 = -1 + L by ring]; exact hper (-1)
        have hhead : g.head? ≠ some r := by
          cases g with
          | nil => simp
          | cons b g =>
            simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hg
            simp only [List.head?_cons, ne_eq, Option.some.injEq]
            exact fun e => hg.1 e.symm
        -- `seqP a L ++ (r :: g)` is reduced
        have hB : reducedB (seqP a L ++ (r :: g)) = true := by
          rw [reducedB_append]
          refine ⟨hK, hg, fun x y hx hy => ?_⟩
          rw [hK2] at hx
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.some.injEq] at hx
          simp only [List.head?_cons, Option.some.injEq] at hy
          rw [← hx, ← hy, hlast]
          exact fun e => h1 e.symm
        have hA : reducedB (r :: g).reverse = true := reducedB_reverse _ hg
        have hAB : reducedB ((r :: g).reverse ++ (seqP a L ++ (r :: g))) = true := by
          rw [reducedB_append]
          refine ⟨hA, hB, fun x y hx hy => ?_⟩
          rw [List.getLast?_reverse] at hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          rw [hK1] at hy
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hy
          rw [← hx, ← hy]
          exact h0
        rw [List.append_assoc, rlen_of_reduced hAB] at hlen
        simp only [List.length_append, List.length_reverse, List.length_cons, seqP_length] at hlen
        omega

/-! ## Reflections inverting `k` act as reflections of the line -/

theorem refl_on_axis (L : ℕ) (hL : 2 ≤ L) {a : ℤ → Test} (ha : Alt a) (hper : Per a L)
    (s : List Test) (hss : groupElt s * groupElt s = 1) (hodd : rlen s % 2 = 1)
    (hk : groupElt s * groupElt (seqP a L) * groupElt s = groupElt (seqP a L).reverse) :
    ∃ c : ℤ, ∀ m, groupElt s * groupElt (seqP a m) = groupElt (seqP a (c - m)) := by
  have hsr := groupElt_reverse_of_sq hss
  have hf : ∀ m : ℤ, ∃ n : ℤ, groupElt s * groupElt (seqP a m) = groupElt (seqP a n) := by
    intro m
    have hy1 : groupElt (reduceRW (s ++ seqP a m)).1 = groupElt s * groupElt (seqP a m) := by
      rw [groupElt_reduceRW, groupElt_append]
    set y := (reduceRW (s ++ seqP a m)).1 with hy
    have hyr : reducedB y = true := (reduceRW (s ++ seqP a m)).2
    have hy2 : groupElt y.reverse = groupElt (seqP a m).reverse * groupElt s := by
      rw [groupElt_reverse_eq (show groupElt y = groupElt (s ++ seqP a m) by
        rw [hy1, groupElt_append]), List.reverse_append, groupElt_append, hsr]
    have hlen : rlen (y.reverse ++ seqP a L ++ y) = L := by
      have e : groupElt (y.reverse ++ seqP a L ++ y) =
          groupElt ((seqP a m).reverse ++ seqP a L ++ seqP a m).reverse := by
        rw [groupElt_append, groupElt_append, hy1, hy2]
        simp only [List.reverse_append, List.reverse_reverse, groupElt_append]
        rw [← hk]
        simp only [mul_assoc]
      rw [rlen_congr e, rlen_reverse, rlen_conj_seqP ha hper]
    obtain ⟨n, hn⟩ := axis_lemma L hL y hyr a ha hper hlen
    exact ⟨n, by rw [← hy1, hn]⟩
  choose f hf using hf
  have hrev : ∀ m, groupElt (seqP a (f m)).reverse = groupElt (seqP a m).reverse * groupElt s := by
    intro m
    have := groupElt_reverse_eq (show groupElt (s ++ seqP a m) = groupElt (seqP a (f m)) by
      rw [groupElt_append, hf m])
    rw [← this, List.reverse_append, groupElt_append, hsr]
  have hdist : ∀ m m', (f m' - f m).natAbs = (m' - m).natAbs := by
    intro m m'
    rw [← rlen_seqP_diff ha, ← rlen_seqP_diff ha]
    apply rlen_congr
    rw [groupElt_append, groupElt_append, hrev, ← hf m', mul_assoc, ← mul_assoc (groupElt s), hss,
      one_mul]
  obtain ⟨c, hc⟩ : ∃ c, c = f 0 := ⟨_, rfl⟩
  have hs0 : groupElt s = groupElt (seqP a c) := by
    have := hf 0
    rwa [seqP_zero, groupElt_nil, mul_one, ← hc] at this
  have h1 := hdist 0 1
  have hneg : f 1 ≠ c + 1 := by
    intro hpos
    have hall : ∀ m, f m = c + m := by
      intro m; have := hdist 0 m; have := hdist 1 m; omega
    have e1 : groupElt (seqP a (2 * c)) = groupElt (seqP a 0) := by
      rw [show 2 * c = c + c by ring, ← hall c, ← hf c, ← hs0, hss, seqP_zero, groupElt_nil]
    have hc0 : c = 0 := by have := seqP_inj ha e1; omega
    have : rlen s = 0 := by rw [rlen_congr hs0, hc0, rlen_seqP ha]; rfl
    omega
  refine ⟨c, fun m => ?_⟩
  have hfm : f m = c - m := by have := hdist 0 m; have := hdist 1 m; omega
  rw [hf m, hfm]

/-! ## The progression of reflection centres -/

/-- `P_a(c)` acts on the line as `P_a(m) ↦ P_a(c - m)`. -/
def Act (a : ℤ → Test) (c : ℤ) : Prop :=
  ∀ m, groupElt (seqP a c) * groupElt (seqP a m) = groupElt (seqP a (c - m))

theorem act_of_refl (L : ℕ) (hL : 2 ≤ L) {a : ℤ → Test} (ha : Alt a) (hper : Per a L)
    (s : List Test) (hss : groupElt s * groupElt s = 1) (hodd : rlen s % 2 = 1)
    (hk : groupElt s * groupElt (seqP a L) * groupElt s = groupElt (seqP a L).reverse) :
    ∃ c, groupElt s = groupElt (seqP a c) ∧ Act a c := by
  obtain ⟨c, hc⟩ := refl_on_axis L hL ha hper s hss hodd hk
  have hs : groupElt s = groupElt (seqP a c) := by
    have := hc 0
    rwa [seqP_zero, groupElt_nil, mul_one, sub_zero] at this
  exact ⟨c, hs, fun m => by rw [← hs]; exact hc m⟩

theorem act_reflect {a : ℤ → Test} {c d : ℤ} (hc : Act a c) (hd : Act a d) :
    Act a (2 * d - c) := by
  have e : groupElt (seqP a (2 * d - c)) =
      groupElt (seqP a d) * groupElt (seqP a c) * groupElt (seqP a d) := by
    rw [mul_assoc, hc d, hd, show d - (c - d) = 2 * d - c by ring]
  intro m
  rw [e, mul_assoc, mul_assoc, hd m, hc, hd, show d - (c - (d - m)) = 2 * d - c - m by ring]

theorem act_odd {a : ℤ → Test} (ha : Alt a) {c : ℤ} (hc : Act a c) : ∃ m, c = 2 * m + 1 := by
  rcases Int.emod_two_eq c with h | h
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m, c = 2 * m := ⟨c / 2, by omega⟩
    have h1 := hc m
    rw [show c - m = m by omega] at h1
    have h2 : groupElt (seqP a c) = groupElt (seqP a 0) := by
      calc groupElt (seqP a c) =
            groupElt (seqP a c) * groupElt (seqP a m) * groupElt (seqP a m).reverse := by
              rw [mul_assoc, groupElt_mul_reverse, mul_one]
        _ = groupElt (seqP a 0) := by rw [h1, groupElt_mul_reverse, seqP_zero, groupElt_nil]
    have hc0 := seqP_inj ha h2
    have h3 := hc 1
    rw [hc0, seqP_zero, groupElt_nil, one_mul] at h3
    have := seqP_inj ha h3
    omega
  · exact ⟨c / 2, by omega⟩

/-- A reflection centre `c = 2m + 1` gives the presentation `P_a(m) a_m P_a(m)⁻¹`. -/
theorem act_palin {a : ℤ → Test} {c m : ℤ} (hc : Act a c) (hm : c = 2 * m + 1) :
    groupElt (seqP a c) = groupElt (Refl.word ⟨seqP a m, a m⟩) := by
  have h1 := hc m
  rw [show c - m = m + 1 by omega, seqP_succ_right] at h1
  calc groupElt (seqP a c) =
        groupElt (seqP a c) * groupElt (seqP a m) * groupElt (seqP a m).reverse := by
          rw [mul_assoc, groupElt_mul_reverse, mul_one]
    _ = _ := by rw [h1, Refl.word, groupElt_append, groupElt_append, groupElt_singleton]

/-- **Dihedral coordinates.** For two factorizations `k = tu = t'u'` into involutions of odd
length inverting `k`, the four reflection centres lie on one progression `b + δℕ` whose first
two terms are reflection centres, with `n_t - n_u = n_{t'} - n_{u'}`. -/
theorem dihedral_coords (L : ℕ) (hL : 2 ≤ L) {a : ℤ → Test} (ha : Alt a) (hper : Per a L)
    (t u t' u' : List Test)
    (hgood : ∀ s ∈ [t, u, t', u'], groupElt s * groupElt s = 1 ∧ rlen s % 2 = 1 ∧
      groupElt s * groupElt (seqP a L) * groupElt s = groupElt (seqP a L).reverse)
    (htu : groupElt t * groupElt u = groupElt (seqP a L))
    (htu' : groupElt t' * groupElt u' = groupElt (seqP a L)) :
    ∃ (b : ℤ) (δ : ℕ) (nt nu nt' nu' : ℕ), Act a b ∧ Act a (b + δ) ∧
      groupElt t = groupElt (seqP a (b + nt * δ)) ∧ groupElt u = groupElt (seqP a (b + nu * δ)) ∧
      groupElt t' = groupElt (seqP a (b + nt' * δ)) ∧
      groupElt u' = groupElt (seqP a (b + nu' * δ)) ∧ nt + nu' = nt' + nu := by
  have get : ∀ s ∈ [t, u, t', u'], ∃ c, groupElt s = groupElt (seqP a c) ∧ Act a c := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hgood s hs
    exact act_of_refl L hL ha hper s h1 h2 h3
  obtain ⟨ct, hct, act⟩ := get t (by simp)
  obtain ⟨cu, hcu, acu⟩ := get u (by simp)
  obtain ⟨ct', hct', act'⟩ := get t' (by simp)
  obtain ⟨cu', hcu', acu'⟩ := get u' (by simp)
  have hdiff : ∀ {x y : ℤ} {v w : List Test}, Act a x → groupElt v = groupElt (seqP a x) →
      groupElt w = groupElt (seqP a y) → groupElt v * groupElt w = groupElt (seqP a L) →
      x - y = L := by
    intro x y v w hx hv hw h
    rw [hv, hw, hx y] at h
    exact seqP_inj ha h
  have d1 := hdiff act hct hcu htu
  have d2 := hdiff act' hct' hcu' htu'
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ x, Act a x ∧ Act a (x + d) :=
    ⟨L, by omega, cu, acu, by rw [show cu + L = ct by omega]; exact act⟩
  classical
  obtain ⟨δ, ⟨hδpos, x0, hx0, hx0δ⟩, hmin⟩ : ∃ δ : ℕ, (0 < δ ∧ ∃ x, Act a x ∧ Act a (x + δ)) ∧
      ∀ d < δ, ¬ (0 < d ∧ ∃ x, Act a x ∧ Act a (x + d)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d hd => Nat.find_min hex hd⟩
  have hAP : ∀ j : ℤ, Act a (x0 + j * δ) ∧ Act a (x0 + (j + 1) * δ) := by
    intro j
    induction j using Int.induction_on with
    | zero =>
      rw [zero_mul, add_zero, zero_add, one_mul]
      exact ⟨hx0, hx0δ⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      have := act_reflect ih.1 ih.2
      rwa [show 2 * (x0 + ((i : ℤ) + 1) * δ) - (x0 + (i : ℤ) * δ) = x0 + ((i : ℤ) + 1 + 1) * δ by
        ring] at this
    | pred i ih =>
      refine ⟨?_, by rw [show -(i : ℤ) - 1 + 1 = -i by ring]; exact ih.1⟩
      have := act_reflect ih.2 ih.1
      rwa [show 2 * (x0 + -(i : ℤ) * δ) - (x0 + (-(i : ℤ) + 1) * δ) = x0 + (-(i : ℤ) - 1) * δ by
        ring] at this
  have hδ : (0 : ℤ) < δ := by exact_mod_cast hδpos
  have hmem : ∀ c, Act a c → ∃ j : ℤ, c = x0 + j * δ := by
    intro c hc
    refine ⟨(c - x0) / δ, ?_⟩
    have h1 := Int.emod_add_ediv_mul (c - x0) δ
    have h2 := Int.emod_nonneg (c - x0) (ne_of_gt hδ)
    have h3 := Int.emod_lt_of_pos (c - x0) hδ
    set q := (c - x0) / (δ : ℤ)
    set r := (c - x0) % (δ : ℤ)
    by_contra hne
    have hr : 0 < r := by
      rcases h2.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [← h] at h1; linarith
    obtain ⟨r', hr'⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
    apply hmin r' (by omega) ⟨by omega, x0 + q * δ, (hAP q).1, ?_⟩
    rw [show x0 + q * (δ : ℤ) + (r' : ℤ) = c by rw [← hr']; linarith]
    exact hc
  obtain ⟨jt, rfl⟩ := hmem ct act
  obtain ⟨ju, rfl⟩ := hmem cu acu
  obtain ⟨jt', rfl⟩ := hmem ct' act'
  obtain ⟨ju', rfl⟩ := hmem cu' acu'
  have hj : jt - ju = jt' - ju' := by
    have : (jt - ju) * (δ : ℤ) = (jt' - ju') * δ := by linarith
    exact mul_right_cancel₀ (ne_of_gt hδ) this
  obtain ⟨jm, hjm1, hjm2, hjm3, hjm4⟩ : ∃ jm : ℤ, jm ≤ jt ∧ jm ≤ ju ∧ jm ≤ jt' ∧ jm ≤ ju' :=
    ⟨min (min jt ju) (min jt' ju'), by omega, by omega, by omega, by omega⟩
  obtain ⟨nt, hnt⟩ : ∃ n : ℕ, jt - jm = n := ⟨(jt - jm).toNat, by omega⟩
  obtain ⟨nu, hnu⟩ : ∃ n : ℕ, ju - jm = n := ⟨(ju - jm).toNat, by omega⟩
  obtain ⟨nt', hnt'⟩ : ∃ n : ℕ, jt' - jm = n := ⟨(jt' - jm).toNat, by omega⟩
  obtain ⟨nu', hnu'⟩ : ∃ n : ℕ, ju' - jm = n := ⟨(ju' - jm).toNat, by omega⟩
  refine ⟨x0 + jm * δ, δ, nt, nu, nt', nu', (hAP jm).1, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · have := (hAP jm).2
    rwa [show x0 + (jm + 1) * (δ : ℤ) = x0 + jm * δ + δ by ring] at this
  · rw [hct, show x0 + jm * (δ : ℤ) + (nt : ℤ) * δ = x0 + jt * δ by rw [← hnt]; ring]
  · rw [hcu, show x0 + jm * (δ : ℤ) + (nu : ℤ) * δ = x0 + ju * δ by rw [← hnu]; ring]
  · rw [hct', show x0 + jm * (δ : ℤ) + (nt' : ℤ) * δ = x0 + jt' * δ by rw [← hnt']; ring]
  · rw [hcu', show x0 + jm * (δ : ℤ) + (nu' : ℤ) * δ = x0 + ju' * δ by rw [← hnu']; ring]

/-! ## Cyclic reduction and the periodic letter sequence -/

theorem cyc_reduce : ∀ (n : ℕ) (h : List Test), h.length ≤ n → reducedB h = true →
    ∃ g k : List Test, h = g ++ k ++ g.reverse ∧ reducedB k = true ∧
      (k.length ≤ 1 ∨ k.head? ≠ k.getLast?) := by
  intro n
  induction n with
  | zero => intro h hn hr; exact ⟨[], h, by simp, hr, Or.inl (by omega)⟩
  | succ n ih =>
    intro h hn hr
    rcases h with _ | ⟨x, _ | ⟨y, l⟩⟩
    · exact ⟨[], [], rfl, hr, Or.inl (by simp)⟩
    · exact ⟨[], [x], rfl, hr, Or.inl (by simp)⟩
    · obtain ⟨m, z, hmz⟩ : ∃ m z, y :: l = m ++ [z] :=
        ⟨(y :: l).dropLast, (y :: l).getLast (by simp), (List.dropLast_append_getLast _).symm⟩
      by_cases hxz : x = z
      · subst hxz
        have hm : reducedB m = true := by
          rw [hmz] at hr; exact reducedB_of_conj x m hr
        have hlen := congrArg List.length hmz
        simp only [List.length_cons, List.length_append] at hlen hn
        obtain ⟨g, k, hgk, hk, hc⟩ := ih m (by omega) hm
        exact ⟨x :: g, k, by rw [hmz, hgk]; simp, hk, hc⟩
      · refine ⟨[], x :: y :: l, by simp, hr, Or.inr ?_⟩
        rw [hmz, show x :: (m ++ [z]) = (x :: m) ++ [z] from rfl]
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq]
        intro e
        apply hxz
        simpa using e

theorem getD_eq_get (k : List Test) (i : ℕ) (h : i < k.length) : k.getD i 0 = k[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The periodic letter sequence of a word. -/
def cycSeq (k : List Test) (n : ℤ) : Test := k.getD (n % (k.length : ℤ)).toNat 0

theorem cycSeq_per (k : List Test) : Per (cycSeq k) k.length := by
  intro n
  simp only [cycSeq, Int.add_emod_right]

theorem seqP_cycSeq (k : List Test) : seqP (cycSeq k) k.length = k := by
  rw [seqP_ofNat]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, cycSeq]
    have : ((i : ℤ) % (k.length : ℤ)).toNat = i := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
    rw [this, getD_eq_get _ _ h2]

theorem reducedB_getElem {k : List Test} (hk : reducedB k = true) (i : ℕ)
    (h : i + 1 < k.length) : k[i + 1] ≠ k[i] := by
  induction k generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h
    | cons b l =>
      simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hk
      cases i with
      | zero => simp only [List.getElem_cons_succ, List.getElem_cons_zero]; exact fun e => hk.1 e.symm
      | succ i =>
        simp only [List.getElem_cons_succ]
        exact ih hk.2 i (by simp only [List.length_cons] at h ⊢; omega)

theorem cycSeq_alt (k : List Test) (hk : reducedB k = true) (hL : 2 ≤ k.length)
    (hcyc : k.head? ≠ k.getLast?) : Alt (cycSeq k) := by
  intro n
  have hL' : (0 : ℤ) < k.length := by omega
  have hs : (n + 1) % (k.length : ℤ) = (n % k.length + 1) % k.length :=
    (Int.emod_add_emod n k.length 1).symm
  have h0 : 0 ≤ n % (k.length : ℤ) := Int.emod_nonneg _ (by omega)
  have hlt : n % (k.length : ℤ) < k.length := Int.emod_lt_of_pos _ hL'
  show k.getD ((n + 1) % (k.length : ℤ)).toNat 0 ≠ k.getD (n % (k.length : ℤ)).toNat 0
  rw [hs]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, n % (k.length : ℤ) = r := ⟨(n % (k.length : ℤ)).toNat, by omega⟩
  rw [hr]
  rw [hr] at hlt
  by_cases hc : r + 1 < k.length
  · rw [Int.emod_eq_of_lt (by omega) (by omega),
      show ((r : ℤ) + 1).toNat = r + 1 by omega, show ((r : ℤ)).toNat = r by omega,
      getD_eq_get _ _ hc, getD_eq_get _ _ (by omega)]
    exact reducedB_getElem hk r hc
  · have hr1 : (r : ℤ) + 1 = k.length := by omega
    rw [hr1, Int.emod_self, show ((r : ℤ)).toNat = r by omega,
      getD_eq_get _ _ (by omega), getD_eq_get _ _ (by omega)]
    intro e
    apply hcyc
    rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega)]
    simp only [Int.toNat_zero] at e
    simp only [Option.some.injEq, e]
    congr 1
    omega

end AlbertSequential.HorizonFive
