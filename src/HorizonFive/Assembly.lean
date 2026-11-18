/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.ShapeFacts

/-! # Final assembly of companion `app:cert:h5`: (eq:cer:h5:goal) from the paper lemmas

"Proof of (eq:cer:h5:goal)", hence of core `rem:cer:fivestep`, formalized:

* degree nine: each `C_{u_1}⋯C_{u_4}A_x 1` has special value `2·(u x u^R)`, a reduced palindrome of
  length nine determining the symbol; lower symbols reach only words of length at most eight;
  reading the coefficient (`coef`, from `HorizonFive.Groups`) kills every such coefficient;
* degree eight: `C_U A_x C_V A_y 1` has special value `4[g]`, `g = U x V y V^R U^R`, and Albert
  value `4 ς(t) ∘ ς(t')`.  If `g` is reduced (`|g| = 8`), the coefficients in each reversal class
  sum to zero and lem:cer:h5:refl(a) makes the class contribute zero natively; otherwise
  `|g| ≤ 7` and lem:cer:h5:refl(b) contracts the symbol;
* what remains has degree at most seven and lem:cer:h5:seven applies.

`symbolTransfer_of_lemmas` is fully proved from the three paper-lemma hypotheses;
`horizonFive_of_lemmas` composes it with the proved reductions to the horizon-five clause. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Degree-eight shape extraction -/

/-- The degree-eight symbol with data `(U, x, V, y)`. -/
def mk8 (q : List Test × Test × List Test × Test) : List Op :=
  q.1.map Op.C ++ Op.A q.2.1 :: (q.2.2.1.map Op.C ++ [Op.A q.2.2.2])

theorem cPrefix_mk (U : List Test) (x : Test) (l : List Op) :
    cPrefix (U.map Op.C ++ Op.A x :: l) = U := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [List.map_cons, List.cons_append, cPrefix, ih]

theorem afterC_mk (U : List Test) (x : Test) (l : List Op) :
    afterC (U.map Op.C ++ Op.A x :: l) = Op.A x :: l := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [List.map_cons, List.cons_append, afterC, ih]

/-- Read `(U, x, V, y)` off a degree-eight symbol. -/
def shapeOf (s : List Op) : List Test × Test × List Test × Test :=
  match afterC s with
  | .A x :: r =>
    match afterC r with
    | .A y :: _ => (cPrefix s, x, cPrefix r, y)
    | _ => ([], 0, [], 0)
  | _ => ([], 0, [], 0)

theorem shapeOf_mk8 (q : List Test × Test × List Test × Test) : shapeOf (mk8 q) = q := by
  obtain ⟨U, x, V, y⟩ := q
  simp only [shapeOf, mk8, afterC_mk, cPrefix_mk]

theorem eq_mk8 (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5) (h8 : opDeg s = 8) :
    s = mk8 (shapeOf s) := by
  obtain ⟨U, x, V, y, rfl, -⟩ := symbol_deg_eight s hs hl h8
  change mk8 (U, x, V, y) = mk8 (shapeOf (mk8 (U, x, V, y)))
  rw [shapeOf_mk8]

theorem mk8_len (q : List Test × Test × List Test × Test) (s : List Op) (hs : s = mk8 q)
    (hl : s.length ≤ 5) (h8 : opDeg s = 8) : q.1.length + q.2.2.1.length = 3 := by
  subst hs
  simp only [mk8, opDeg_append, opDeg_mapC, opDeg] at h8
  omega

/-- The word `g` of a symbol (meaningful in degree eight). -/
def gW (s : List Op) : List Test :=
  gWord (shapeOf s).1 (shapeOf s).2.1 (shapeOf s).2.2.1 (shapeOf s).2.2.2

/-- The two reflections of a symbol (meaningful in degree eight). -/
def trW (s : List Op) : Refl × Refl :=
  topRefls (shapeOf s).1 (shapeOf s).2.1 (shapeOf s).2.2.1 (shapeOf s).2.2.2

/-- The reversal class of `g`, as a set of two words. -/
def keyW (s : List Op) : Finset (List Test) := {gW s, (gW s).reverse}

theorem classElt_reverse (l : List Test) : classElt l.reverse = classElt l := by
  simp only [classElt, List.reverse_reverse, add_comm]

theorem gW_length (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5) (h8 : opDeg s = 8) :
    (gW s).length = 8 := by
  have h := mk8_len (shapeOf s) s (eq_mk8 s hs hl h8) hl h8
  simp only [gW, gWord, List.length_append, List.length_singleton, List.length_reverse]
  omega

theorem deg8_special (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5)
    (h8 : opDeg s = 8) : specialEval (opPoly s) = (4 : ℝ) • classElt (gW s) := by
  conv_lhs => rw [eq_mk8 s hs hl h8]
  exact specialEval_deg_eight _ _ _ _

theorem deg8_albert (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (s : List Op)
    (hs : isSymbol s = true) (hl : s.length ≤ 5) (h8 : opDeg s = 8) :
    albertEval p (opPoly s) =
      (4 : ℝ) • jordanMul (varsigma p (trW s).1) (varsigma p (trW s).2) := by
  conv_lhs => rw [eq_mk8 s hs hl h8]
  exact albertEval_deg_eight p hp _ _ _ _

/-! ## Degree of operator words -/

theorem deg_opPoly (l : List Op) : (opPoly l).deg = opDeg l := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | A i => simp only [opPoly, JPoly.A, JPoly.deg, opDeg, ih]; omega
    | C i => simp only [opPoly, JPoly.U, JPoly.deg, opDeg, ih]; omega

theorem specialEvalC_eq (F : JComb) :
    specialEvalC F = Finsupp.linearCombination ℝ specialEval F := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem albertEvalC_eq (p : Test → Albert) (F : JComb) :
    albertEvalC p F = Finsupp.linearCombination ℝ (albertEval p) F := by
  rw [Finsupp.linearCombination_apply]; rfl

/-! ## The assembly -/

/-- **Final assembly of companion `app:cert:h5` (proved, conditional on the three paper lemmas).** -/
theorem symbolTransfer_of_lemmas (hA : ReflectionClassConsistency) (hB : ReflectionContraction)
    (h7 : TransferThroughSeven) : SymbolTransfer5 := by
  classical
  intro p hp F hF h0
  set S := F.support with hSdef
  have hsym : ∀ s ∈ S, isSymbol s = true ∧ s.length ≤ 5 := fun s hs =>
    (Finsupp.mem_supported ℝ F).1 hF hs
  have hspec : opSpecial F = ∑ s ∈ S, F s • specialEval (opPoly s) := by
    unfold opSpecial JTarget.evalOps
    rw [Finsupp.linearCombination_apply]; rfl
  have halb : opAlbert p F = ∑ s ∈ S, F s • albertEval p (opPoly s) := by
    unfold opAlbert JTarget.evalOps
    rw [Finsupp.linearCombination_apply]; rfl
  have hdeg9 : ∀ s ∈ S, opDeg s ≤ 9 := fun s hs =>
    symbol_opDeg_le_nine s (hsym s hs).1 (hsym s hs).2
  -- Degree nine: coefficients vanish.
  have h9 : ∀ s ∈ S, opDeg s = 9 → F s = 0 := by
    intro s0 hs0 hd0
    obtain ⟨U0, x0, hs0eq, hU0, hred0⟩ := symbol_deg_nine s0 (hsym _ hs0).1 (hsym _ hs0).2 hd0
    have hpal0 := palWord_reduced U0 x0 hred0
    set g0 : RW := ⟨palWord U0 x0, hpal0⟩ with hg0
    have hlen0 : g0.1.length = 9 := by simp [g0, palWord, hU0]
    have hc := congrArg (coef g0) h0
    rw [hspec, map_sum, map_zero] at hc
    rw [Finset.sum_eq_single s0] at hc
    · rw [map_smul, hs0eq, specialEval_deg_nine, map_smul, coef_groupElt,
        reduceRW_of_reduced _ hpal0, ite_eq_left rfl, smul_eq_mul, smul_eq_mul] at hc
      rw [hs0eq]
      linarith
    · intro s hs hne
      rw [map_smul]
      rcases Nat.lt_or_ge (opDeg s) 9 with hlt | hge
      · rw [coef_eq_zero_of_mem_wordSpan g0 (by omega) (specialEval_opPoly_mem_wordSpan s),
          smul_zero]
      · have hd9 : opDeg s = 9 := le_antisymm (hdeg9 s hs) hge
        obtain ⟨U, x, hseq, hU, hred⟩ := symbol_deg_nine s (hsym s hs).1 (hsym s hs).2 hd9
        rw [hseq, specialEval_deg_nine, map_smul, coef_groupElt,
          reduceRW_of_reduced _ (palWord_reduced U x hred), ite_eq_right, smul_zero, smul_zero]
        intro heq
        have := congrArg Subtype.val heq
        obtain ⟨rfl, rfl⟩ := palWord_injective U U0 x x0 hU hU0 this
        exact hne (hseq.trans hs0eq.symm)
    · intro hnot; exact absurd hs0 hnot
  -- Degree eight, reduced classes.
  set T := S.filter (fun s => opDeg s = 8 ∧ reducedB (gW s) = true) with hTdef
  have hTmem : ∀ s ∈ T, s ∈ S ∧ opDeg s = 8 ∧ reducedB (gW s) = true := fun s hs => by
    simpa [hTdef] using hs
  have hne_rev : ∀ s ∈ T, (gW s).reverse ≠ gW s := fun s hs => by
    obtain ⟨hsS, h8, hr⟩ := hTmem s hs
    exact reduced_length_eight_ne_reverse _ hr (gW_length s (hsym s hsS).1 (hsym s hsS).2 h8)
  have hkey : ∀ s ∈ T, ∀ s0 ∈ T, keyW s = keyW s0 ↔ (gW s = gW s0 ∨ gW s = (gW s0).reverse) := by
    intro s hs s0 hs0
    constructor
    · intro hk
      have : gW s ∈ keyW s0 := hk ▸ (by simp [keyW])
      simpa [keyW] using this
    · rintro (h | h)
      · simp [keyW, h]
      · simp only [keyW, h, List.reverse_reverse]
        exact Finset.pair_comm _ _
  -- Claim A: class sums vanish.
  have hclass : ∀ s0 ∈ T, ∑ s ∈ T.filter (fun s => keyW s = keyW s0), F s = 0 := by
    intro s0 hs0
    obtain ⟨hs0S, h80, hr0⟩ := hTmem s0 hs0
    set g0 : RW := ⟨gW s0, hr0⟩ with hg0
    have hlen0 : g0.1.length = 8 := gW_length s0 (hsym _ hs0S).1 (hsym _ hs0S).2 h80
    have hc := congrArg (coef g0) h0
    rw [hspec, map_sum, map_zero] at hc
    have hterm : ∀ s ∈ S, coef g0 (F s • specialEval (opPoly s)) =
        if s ∈ T ∧ keyW s = keyW s0 then 2 * F s else 0 := by
      intro s hs
      rw [map_smul, smul_eq_mul]
      rcases Nat.lt_or_ge (opDeg s) 8 with hlt | hge
      · rw [coef_eq_zero_of_mem_wordSpan g0 (by omega) (specialEval_opPoly_mem_wordSpan s),
          mul_zero, ite_eq_right]
        rintro ⟨hT, -⟩
        have := (hTmem s hT).2.1; omega
      · rcases Nat.eq_or_lt_of_le (hdeg9 s hs) with h9' | hlt9
        · rw [h9 s hs h9', zero_mul]; split_ifs <;> simp
        · have h8 : opDeg s = 8 := by omega
          rw [deg8_special s (hsym s hs).1 (hsym s hs).2 h8, map_smul, classElt, map_smul,
            map_add, coef_groupElt, coef_groupElt]
          by_cases hr : reducedB (gW s) = true
          · have hsT : s ∈ T := by simp [hTdef, hs, h8, hr]
            have hrr := reducedB_reverse _ hr
            rw [reduceRW_of_reduced _ hr, reduceRW_of_reduced _ hrr]
            have hns := hne_rev s hsT
            have hns0 := hne_rev s0 hs0
            by_cases e1 : gW s = gW s0
            · have hk : keyW s = keyW s0 := (hkey s hsT s0 hs0).2 (Or.inl e1)
              have e2 : ¬ (gW s).reverse = gW s0 := fun e => hns (e.trans e1.symm)
              rw [ite_eq_left (Subtype.ext e1), ite_eq_right (fun e => e2 (congrArg Subtype.val e)),
                ite_eq_left ⟨hsT, hk⟩]
              norm_num; ring
            · by_cases e2 : (gW s).reverse = gW s0
              · have hk : keyW s = keyW s0 :=
                  (hkey s hsT s0 hs0).2 (Or.inr (by rw [← e2, List.reverse_reverse]))
                rw [ite_eq_right (fun e => e1 (congrArg Subtype.val e)), ite_eq_left (Subtype.ext e2),
                  ite_eq_left ⟨hsT, hk⟩]
                norm_num; ring
              · have hk : keyW s ≠ keyW s0 := by
                  intro hk
                  rcases (hkey s hsT s0 hs0).1 hk with h | h
                  · exact e1 h
                  · exact e2 (by rw [h, List.reverse_reverse])
                rw [ite_eq_right (fun e => e1 (congrArg Subtype.val e)),
                  ite_eq_right (fun e => e2 (congrArg Subtype.val e)), ite_eq_right (fun h => hk h.2)]
                norm_num
          · have hsT : s ∉ T := fun h => hr (hTmem s h).2.2
            have hlen8 := gW_length s (hsym s hs).1 (hsym s hs).2 h8
            have hshort : ∀ l : List Test, l.length = 8 → reducedB l ≠ true →
                reduceRW l ≠ g0 := by
              intro l hl hnr heq
              have h1 := reduceRW_length l
              have h2 : (reduceRW l).1.length ≠ l.length := fun e =>
                hnr (reducedB_of_reduceRW_length l e)
              rw [heq] at h1 h2
              omega
            have hnr' : reducedB (gW s).reverse ≠ true := fun h =>
              hr ((reducedB_reverse_iff _).1 h)
            rw [ite_eq_right (hshort _ hlen8 hr), ite_eq_right (hshort _ (by simp [hlen8]) hnr'),
              ite_eq_right (fun h => hsT h.1)]
            norm_num
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter] at hc
    have hfilt : S.filter (fun s => s ∈ T ∧ keyW s = keyW s0) =
        T.filter (fun s => keyW s = keyW s0) := by
      ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨-, hT, hk⟩; exact ⟨hT, hk⟩
      · rintro ⟨hT, hk⟩; exact ⟨(hTmem s hT).1, hT, hk⟩
    rw [hfilt, ← Finset.mul_sum] at hc
    linarith
  -- Fibre sums over the classes.
  have hfibre : ∀ (M : Type) [AddCommGroup M] [Module ℝ M] (X : List Op → M),
      (∀ s ∈ T, ∀ s0 ∈ T, keyW s = keyW s0 → X s = X s0) →
      ∑ s ∈ T, F s • X s = 0 := by
    intro M _ _ X hX
    rw [← Finset.sum_fiberwise_of_maps_to (g := keyW) (t := T.image keyW)
      (fun s hs => Finset.mem_image_of_mem keyW hs)]
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.1 hk
    have : ∀ s ∈ T.filter (fun s => keyW s = keyW s0), F s • X s = F s • X s0 := by
      intro s hs
      rw [Finset.mem_filter] at hs
      rw [hX s hs.1 s0 hs0 hs.2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul, hclass s0 hs0, zero_smul]
  have hTspec : ∑ s ∈ T, F s • specialEval (opPoly s) = 0 := by
    have : ∀ s ∈ T, F s • specialEval (opPoly s) = F s • ((4 : ℝ) • classElt (gW s)) := by
      intro s hs
      obtain ⟨hsS, h8, -⟩ := hTmem s hs
      rw [deg8_special s (hsym s hsS).1 (hsym s hsS).2 h8]
    rw [Finset.sum_congr rfl this]
    refine hfibre _ (fun s => (4 : ℝ) • classElt (gW s)) ?_
    intro s hs s0 hs0 hk
    rcases (hkey s hs s0 hs0).1 hk with h | h
    · simp only [h]
    · simp only [h, classElt_reverse]
  have hTalb : ∑ s ∈ T, F s • albertEval p (opPoly s) = 0 := by
    have : ∀ s ∈ T, F s • albertEval p (opPoly s) =
        F s • ((4 : ℝ) • jordanMul (varsigma p (trW s).1) (varsigma p (trW s).2)) := by
      intro s hs
      obtain ⟨hsS, h8, -⟩ := hTmem s hs
      rw [deg8_albert p hp s (hsym s hsS).1 (hsym s hsS).2 h8]
    rw [Finset.sum_congr rfl this]
    refine hfibre _ (fun s => (4 : ℝ) • jordanMul (varsigma p (trW s).1) (varsigma p (trW s).2)) ?_
    intro s hs s0 hs0 hk
    congr 1
    have hw := topRefls_word (shapeOf s).1 (shapeOf s).2.1 (shapeOf s).2.2.1 (shapeOf s).2.2.2
    have hw0 := topRefls_word (shapeOf s0).1 (shapeOf s0).2.1 (shapeOf s0).2.2.1
      (shapeOf s0).2.2.2
    refine (hA p hp (trW s0).1 (trW s0).2 (trW s).1 (trW s).2 ?_).symm
    change reduceRW ((trW s).1.word ++ (trW s).2.word) = reduceRW ((trW s0).1.word ++ (trW s0).2.word) ∨
      reduceRW ((trW s).1.word ++ (trW s).2.word) = reduceRW ((trW s0).1.word ++ (trW s0).2.word).reverse
    unfold trW
    rw [hw.1, hw0.1, hw0.2]
    rcases (hkey s hs s0 hs0).1 hk with h | h
    · left; exact congrArg reduceRW h
    · right; exact congrArg reduceRW h
  -- Degree eight, non-reduced: contraction polynomials.
  set L8 := S.filter (fun s => opDeg s = 8 ∧ ¬ reducedB (gW s) = true) with hL8def
  have hL8mem : ∀ s ∈ L8, s ∈ S ∧ opDeg s = 8 ∧ ¬ reducedB (gW s) = true := fun s hs => by
    simpa [hL8def] using hs
  let K : List Op → JPoly Test := fun s => Classical.choose (hB (trW s).1 (trW s).2)
  have hK : ∀ s, (K s).deg = (reduceRW ((trW s).1.word ++ (trW s).2.word)).1.length ∧
      specialEval (K s) = classElt ((trW s).1.word ++ (trW s).2.word) ∧
      ∀ p : Test → Albert, (∀ i, IsAtom (p i)) →
        albertEval p (K s) = jordanMul (varsigma p (trW s).1) (varsigma p (trW s).2) :=
    fun s => Classical.choose_spec (hB (trW s).1 (trW s).2)
  have hKdeg : ∀ s ∈ L8, (K s).deg ≤ 7 := by
    intro s hs
    obtain ⟨hsS, h8, hr⟩ := hL8mem s hs
    rw [(hK s).1]
    have hw := topRefls_word (shapeOf s).1 (shapeOf s).2.1 (shapeOf s).2.2.1 (shapeOf s).2.2.2
    change (reduceRW (_ ++ _)).1.length ≤ 7
    unfold trW
    rw [hw.1]
    have h1 := reduceRW_length (gW s)
    have h2 : (reduceRW (gW s)).1.length ≠ (gW s).length := fun e =>
      hr (reducedB_of_reduceRW_length _ e)
    have h3 := gW_length s (hsym s hsS).1 (hsym s hsS).2 h8
    change (reduceRW (gW s)).1.length ≤ 7
    omega
  have hKspec : ∀ s ∈ L8, specialEval (K s) = classElt (gW s) := by
    intro s hs
    rw [(hK s).2.1]
    exact classElt_topRefls _ _ _ _
  -- The remaining combination of degree at most seven.
  set Low := S.filter (fun s => opDeg s ≤ 7) with hLowdef
  let F' : JComb := (∑ s ∈ Low, Finsupp.single (opPoly s) (F s)) +
    ∑ s ∈ L8, Finsupp.single (K s) ((4 : ℝ) * F s)
  have hF'deg : ∀ G ∈ F'.support, G.deg ≤ 7 := by
    have hmem : F' ∈ Finsupp.supported ℝ ℝ {G : JPoly Test | G.deg ≤ 7} := by
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun s hs => ?_)
        (Submodule.sum_mem _ fun s hs => ?_)
      · refine Finsupp.single_mem_supported ℝ _ ?_
        show (opPoly s).deg ≤ 7
        rw [deg_opPoly]
        exact (Finset.mem_filter.1 hs).2
      · exact Finsupp.single_mem_supported ℝ _ (hKdeg s hs)
    exact fun G hG => (Finsupp.mem_supported ℝ F').1 hmem hG
  -- Splitting the support by degree.
  have hsplit : ∀ (M : Type) [AddCommGroup M] [Module ℝ M] (f : List Op → M),
      ∑ s ∈ S, f s = ∑ s ∈ Low, f s + ∑ s ∈ T, f s + ∑ s ∈ L8, f s +
        ∑ s ∈ S.filter (fun s => opDeg s = 9), f s := by
    intro M _ _ f
    simp only [hLowdef, hTdef, hL8def, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hdeg9 s hs
    by_cases h7' : opDeg s ≤ 7
    · simp [h7', show ¬ opDeg s = 8 by omega, show ¬ opDeg s = 9 by omega]
    · by_cases h8 : opDeg s = 8
      · by_cases hr : reducedB (gW s) = true <;> simp [h7', h8, hr]
      · have h9' : opDeg s = 9 := by omega
        simp [h7', h8, h9']
  have hN9spec : ∑ s ∈ S.filter (fun s => opDeg s = 9), F s • specialEval (opPoly s) = 0 :=
    Finset.sum_eq_zero fun s hs => by
      rw [Finset.mem_filter] at hs; rw [h9 s hs.1 hs.2, zero_smul]
  have hN9alb : ∑ s ∈ S.filter (fun s => opDeg s = 9), F s • albertEval p (opPoly s) = 0 :=
    Finset.sum_eq_zero fun s hs => by
      rw [Finset.mem_filter] at hs; rw [h9 s hs.1 hs.2, zero_smul]
  -- Values of the remaining combination.
  have hF'spec : specialEvalC F' = opSpecial F := by
    rw [specialEvalC_eq, map_add, map_sum, map_sum, hspec, hsplit _ _, hTspec, hN9spec]
    simp only [Finsupp.linearCombination_single, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsS, h8, -⟩ := hL8mem s hs
    rw [hKspec s hs, deg8_special s (hsym s hsS).1 (hsym s hsS).2 h8, smul_smul, mul_comm]
  have hF'alb : albertEvalC p F' = opAlbert p F := by
    rw [albertEvalC_eq, map_add, map_sum, map_sum, halb, hsplit _ _, hTalb, hN9alb]
    simp only [Finsupp.linearCombination_single, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsS, h8, -⟩ := hL8mem s hs
    rw [(hK s).2.2 p hp, deg8_albert p hp s (hsym s hsS).1 (hsym s hsS).2 h8, smul_smul, mul_comm]
  rw [← hF'alb]
  exact h7 p hp F' hF'deg (by rw [hF'spec]; exact h0)

/-- **Main conditional theorem.** The horizon-five clause (core `rem:cer:fivestep`,
every four atoms, any state) follows from the three paper lemmas
lem:cer:h5:refl(a), lem:cer:h5:refl(b) and lem:cer:h5:seven.  Everything between them and the
clause (words → operator words → canonical symbols → degree nine/eight elimination) is proved. -/
theorem horizonFive_of_lemmas (hA : ReflectionClassConsistency) (hB : ReflectionContraction)
    (h7 : TransferThroughSeven) : HorizonFiveClause :=
  horizonFive_of_symbolTransfer (symbolTransfer_of_lemmas hA hB h7)

end AlbertSequential.HorizonFive
