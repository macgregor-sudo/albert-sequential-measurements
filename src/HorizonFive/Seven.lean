/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Passive
public import HorizonFive.Volume
public import HorizonFive.RecogBase

/-! # lem:cer:h5:seven from lem:cer:h5:lift

Step 3 of the paper's proof (descent on the largest four-letter multidegree), with Step 1
(`passive_transfer`), Step 2 (`three_letter_transfer`, Cohn-free) and lem:cer:h5:lift
(`RecognitionThroughFivePos`, i.e. `RecognitionThroughFive` for `1 ≤ n`, an explicit
hypothesis here, proved in `Recognition.lean`).

Headlines:

* `transferThroughSeven_of_lift (hL : RecognitionThroughFivePos) : TransferThroughSeven`;
* `horizonFive_of_refl_a_and_lift (hA : ReflectionClassConsistency) (hL : RecognitionThroughFivePos) :
  HorizonFiveClause`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Coefficients and reversal -/

/-- Reversal of a reduced word. -/
def revRW (g : RW) : RW := ⟨g.1.reverse, reducedB_reverse _ g.2⟩

theorem coef_star (g : RW) (x : UniversalProjectionAlgebra 4) :
    coef g (star x) = coef (revRW g) x := by
  classical
  have h1 := expand_eq x
  have h2 : star x = ∑ h ∈ (coefVec x).support, coef h x • groupElt h.1.reverse := by
    conv_lhs => rw [h1]
    rw [star_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [star_smul, star_trivial, star_groupElt]
  rw [h2, map_sum]
  have e : ∀ h : RW, coef g (coef h x • groupElt h.1.reverse) =
      if h = revRW g then coef h x else 0 := by
    intro h
    rw [map_smul, coef_groupElt, reduceRW_of_reduced _ (reducedB_reverse _ h.2)]
    by_cases hh : h = revRW g
    · subst hh
      rw [ite_eq_left, ite_eq_left rfl, smul_eq_mul, mul_one]
      apply Subtype.ext
      simp [revRW]
    · rw [ite_eq_right, ite_eq_right hh, smul_zero]
      intro e
      apply hh
      apply Subtype.ext
      have := congrArg Subtype.val e
      simp only at this
      simp [revRW, ← this]
  simp only [e]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [mem_coefVec_support, not_not] at hm
    exact hm.symm

theorem length_eq_sum_count (l : List Test) : l.length = ∑ i, l.count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib, ih, beq_iff_eq]
    simp

/-! ## Using lem:cer:h5:lift -/

theorem lift_of_hyp (hL : RecognitionThroughFivePos) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 5) (j : Test)
    (x : UniversalProjectionAlgebra 4) (hx : star x = x)
    (hsupp : ∀ g : RW, coef g x ≠ 0 → g.1.length ≤ n ∧ g.1.count j = 1)
    (hvol : volFun x = 0) :
    ∃ K : JPoly Test, K.deg ≤ n ∧ K.LinearIn j ∧ specialEval K = x := by
  classical
  let y : List Test →₀ ℝ := Finsupp.mapDomain Subtype.val (coefVec x)
  have hinj : Function.Injective (Subtype.val : RW → List Test) := Subtype.val_injective
  have hy_red : ∀ g : RW, y g.1 = coef g x := fun g => Finsupp.mapDomain_apply_of_injective hinj _ g
  have hy_not : ∀ l, reducedB l = false → y l = 0 := by
    intro l hl
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨g, rfl⟩
    rw [g.2] at hl
    exact Bool.noConfusion hl
  have hsumV : (y.sum fun l a => a • groupElt l) = x := by
    show ((Finsupp.mapDomain Subtype.val (coefVec x)).sum fun l (a : ℝ) => a • groupElt l) = x
    rw [Finsupp.sum_mapDomain_index (h := fun l (a : ℝ) => a • groupElt l)
      (fun _ => zero_smul ℝ _) (fun _ _ _ => add_smul _ _ _)]
    conv_rhs => rw [expand_eq x]
    rfl
  have hsumL : (y.sum fun l a => a * (cliffVol l : ℝ)) = 0 := by
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    rw [← hvol]
    conv_rhs => rw [expand_eq x, map_sum]
    simp only [Finsupp.sum, map_smul, volFun_groupElt, smul_eq_mul]
    try rfl
  have hS : ∀ l ∈ y.support, reducedB l = true ∧ l.length ≤ n ∧ l.count j = 1 := by
    intro l hl
    rw [Finsupp.mem_support_iff] at hl
    cases hr : reducedB l with
    | false => exact absurd (hy_not l hr) hl
    | true =>
      have e1 : y l = coef ⟨l, hr⟩ x := hy_red ⟨l, hr⟩
      have h := hsupp ⟨l, hr⟩ (by rw [← e1]; exact hl)
      exact ⟨rfl, h.1, h.2⟩
  have hR : ∀ l, y l.reverse = y l := by
    intro l
    cases hr : reducedB l with
    | false =>
      have hr' : reducedB l.reverse = false := Bool.eq_false_iff.2 fun h => by
        rw [(reducedB_reverse_iff l).1 h] at hr; exact Bool.noConfusion hr
      rw [hy_not l hr, hy_not _ hr']
    | true =>
      have e1 : y l = coef ⟨l, hr⟩ x := hy_red ⟨l, hr⟩
      have e2 : y l.reverse = coef (revRW ⟨l, hr⟩) x := hy_red (revRW ⟨l, hr⟩)
      rw [e2, e1, ← coef_star, hx]
  obtain ⟨K, hK1, hK2, hK3⟩ := hL n hn1 hn j y hS hR hsumL
  exact ⟨K, hK1, hK2, hK3.trans hsumV⟩

/-! ## The descent -/

section Descent
variable (p : Test → Albert)

/-- All letters occur. -/
def isFour (μ : MD) : Prop := ∀ i, 0 < μ i

instance (μ : MD) : Decidable (isFour μ) := by unfold isFour; infer_instance

theorem mdSize_ge_four {μ : MD} (h : isFour μ) : 4 ≤ mdSize μ := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [mdSize, Fin.sum_univ_four]
  omega

/-- Four-letter components above `N` have vanishing values. -/
def GoodAbove (N : ℕ) (F : JPoly Test) : Prop :=
  ∀ μ, isFour μ → N < mdSize μ →
    specialEval (compAll F μ) = 0 ∧ albertEval p (compAll F μ) = 0

/-- The statement proved by descent. -/
def ClaimAt (N : ℕ) : Prop :=
  ∀ F : JPoly Test, F.deg ≤ 7 → GoodAbove p N F → specialEval F = 0 → albertEval p F = 0

theorem specialEval_eq_eval (F : JPoly Test) :
    specialEval F = (specialTarget (UniversalProjectionAlgebra 4)).eval specialSymmetry F := rfl

/-- A letter missing from `μ` (if any). -/
def zeroLetter (μ : MD) : Test :=
  if h : ∃ i, μ i = 0 then Classical.choose h else 0

theorem zeroLetter_spec {μ : MD} (h : ¬ isFour μ) : μ (zeroLetter μ) = 0 := by
  have h' : ∃ i, μ i = 0 := by
    unfold isFour at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by omega⟩
  simp only [zeroLetter, dite_eq_left h']
  exact Classical.choose_spec h'

theorem sum_fiber {E : Type*} [AddCommMonoid E] (s : Finset MD) (f : MD → E) :
    ∑ j : Test, ∑ μ ∈ s.filter (fun μ => zeroLetter μ = j), f μ = ∑ μ ∈ s, f μ :=
  Finset.sum_fiberwise s zeroLetter f

/-- **Base of the descent (Step 2).** -/
theorem claim_three (hp : ∀ i, IsAtom (p i)) : ClaimAt p 3 := by
  classical
  intro F hdeg hgood h0
  let S := (boxMD 7).filter fun μ => ¬ isFour μ
  let G : Test → JPoly Test := fun j =>
    jsum (S.filter fun μ => zeroLetter μ = j) (fun _ => 1) (compAll F)
  have hG : ∀ j, (G j).FreeOf j := by
    intro j
    refine freeOf_jsum _ _ _ j fun μ hμ => ?_
    obtain ⟨hμS, hμj⟩ := Finset.mem_filter.1 hμ
    have hnf := (Finset.mem_filter.1 hμS).2
    have hz := zeroLetter_spec hnf
    rw [hμj] at hz
    exact (homog_letters j (homog_compAll F μ)).1 hz
  have hsplit : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E),
      T.eval v F = ∑ μ ∈ (boxMD 7).filter isFour, T.eval v (compAll F μ) +
        ∑ j, T.eval v (G j) := by
    intro E _ _ T v
    rw [eval_decomp T v F 7 hdeg, ← Finset.sum_filter_add_sum_filter_not (boxMD 7) isFour]
    congr 1
    simp only [G, eval_jsum, one_smul]
    exact (sum_fiber S _).symm
  have hfour : ∀ μ ∈ (boxMD 7).filter isFour,
      specialEval (compAll F μ) = 0 ∧ albertEval p (compAll F μ) = 0 := by
    intro μ hμ
    have h4 := (Finset.mem_filter.1 hμ).2
    exact hgood μ h4 (by have := mdSize_ge_four h4; omega)
  have hs := hsplit (specialTarget (UniversalProjectionAlgebra 4)) specialSymmetry
  rw [← specialEval_eq_eval, h0] at hs
  simp only [← specialEval_eq_eval] at hs
  rw [Finset.sum_eq_zero fun μ hμ => (hfour μ hμ).1, zero_add] at hs
  have h3 := three_letter_transfer p hp G hG hs.symm
  have ha := hsplit albertTarget (nativeSymmetry p)
  change albertEval p F = ∑ μ ∈ _, albertEval p (compAll F μ) + ∑ j, albertEval p (G j) at ha
  rw [ha, h3, Finset.sum_eq_zero fun μ hμ => (hfour μ hμ).2, add_zero]

theorem eval_compAll_jsumL {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)
    (v : Test → E) {ι : Type} (c : ι → ℝ) (P : ι → JPoly Test) (l : List ι) (ν : MD) :
    T.eval v (compAll (jsumL c P l) ν) = (l.map fun i => c i • T.eval v (compAll (P i) ν)).sum := by
  induction l with
  | nil =>
    show T.eval v (compAll (.smul 0 .one) ν) = _
    simp [compAll, JTarget.eval]
  | cons i l ih =>
    show T.eval v (compAll (.add (.smul (c i) (P i)) (jsumL c P l)) ν) = _
    simp only [compAll, JTarget.eval] at ih ⊢
    rw [ih, List.map_cons, List.sum_cons]

theorem eval_compAll_jsum {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)
    (v : Test → E) {ι : Type} (s : Finset ι) (c : ι → ℝ) (P : ι → JPoly Test) (ν : MD) :
    T.eval v (compAll (jsum s c P) ν) = ∑ i ∈ s, c i • T.eval v (compAll (P i) ν) := by
  rw [jsum, eval_compAll_jsumL, Finset.sum_map_toList]

theorem eval_compAll_jsub {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)
    (v : Test → E) (F G : JPoly Test) (ν : MD) :
    T.eval v (compAll (jsub F G) ν) = T.eval v (compAll F ν) - T.eval v (compAll G ν) := by
  show T.eval v (compAll (.add F (.smul (-1) G)) ν) = _
  simp only [compAll, JTarget.eval, neg_one_smul, sub_eq_add_neg]

theorem lt_mdSize_of_le {μ ν : MD} (hle : μ ≤ ν) (hne : ν ≠ μ) : mdSize μ < mdSize ν := by
  have : ∃ i, μ i < ν i := by
    by_contra h
    push Not at h
    exact hne (funext fun i => le_antisymm (h i) (hle i))
  obtain ⟨i, hi⟩ := this
  exact Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ _, hi⟩

/-- **Descent step (Step 3).** -/
theorem claim_step (hp : ∀ i, IsAtom (p i)) (hL : RecognitionThroughFivePos) (N : ℕ) (hN3 : 3 ≤ N) (hN7 : N + 1 ≤ 7)
    (hc : ClaimAt p N) : ClaimAt p (N + 1) := by
  classical
  intro F hdeg hgood h0
  let Top := (boxMD 7).filter fun μ => isFour μ ∧ mdSize μ = N + 1
  -- lifts of the top components
  have hK : ∀ μ, ∃ K : JPoly Test, μ ∈ Top → (K.deg ≤ N - 1 ∧
      specialEval K = specialEval (compAll F μ) ∧ albertEval p K = albertEval p (compAll F μ)) := by
    intro μ
    by_cases hμ : μ ∈ Top
    swap
    · exact ⟨zeroP, fun h => absurd h hμ⟩
    obtain ⟨hμbox, hμ4, hμN⟩ := Finset.mem_filter.1 hμ
    obtain ⟨j, hj⟩ := four_positive_le_seven_has_one μ hμ4 (by
      have : mdSize μ ≤ 7 := by omega
      simpa [mdSize, Fin.sum_univ_four] using this)
    set x := specialEval (compAll F μ) with hxdef
    have hmd := specialEval_mem_mdSpan (homog_compAll F μ)
    have hsupp : ∀ g : RW, coef g x ≠ 0 → g.1.length ≤ N - 1 ∧ g.1.count j = 1 := by
      intro g hg
      have ha := coef_mdSpan g hmd hg
      have hb : ¬ ∀ i, g.1.count i = μ i := by
        intro hall
        apply hg
        have hsum := congrArg (coef g) h0
        rw [specialEval_eq_eval, eval_decomp _ _ F 7 hdeg, map_sum, map_zero] at hsum
        rw [Finset.sum_eq_single μ] at hsum
        · exact hsum
        · intro ν hν hne
          by_contra hcν
          have haν := coef_mdSpan g (specialEval_mem_mdSpan (homog_compAll F ν)) hcν
          have hle : μ ≤ ν := by
            intro i
            obtain ⟨k, hk⟩ := haν i
            have e := hall i
            show μ i ≤ ν i
            omega
          have h4 : isFour ν := fun i => lt_of_lt_of_le (hμ4 i) (hle i)
          have hlt := lt_mdSize_of_le hle hne
          exact hcν (by
            show coef g (specialEval (compAll F ν)) = 0
            rw [(hgood ν h4 (by omega)).1, map_zero])
        · intro h; exact absurd hμbox h
      constructor
      · rw [length_eq_sum_count]
        push Not at hb
        obtain ⟨i0, hi0⟩ := hb
        choose k hk using ha
        have hk0 : 1 ≤ k i0 := by
          rcases Nat.eq_zero_or_pos (k i0) with h | h
          · exact absurd (by rw [hk i0, h]; ring) hi0
          · exact h
        have : ∑ i, μ i = ∑ i, g.1.count i + 2 * ∑ i, k i := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => hk i
        have hks : k i0 ≤ ∑ i, k i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le (k i)) (Finset.mem_univ i0)
        simp only [mdSize] at hμN
        omega
      · obtain ⟨k, hk⟩ := ha j
        omega
    obtain ⟨K, hKdeg, hKlin, hKval⟩ := lift_of_hyp hL (N - 1) (by omega) (by omega) j x
      (star_specialEval _) hsupp (volFun_specialEval _)
    refine ⟨K, fun _ => ⟨hKdeg, hKval, ?_⟩⟩
    have hlin : (jsub (compAll F μ) K).LinearIn j :=
      .add _ _ ((homog_letters j (homog_compAll F μ)).2 hj) (.smul _ _ hKlin)
    have hs : specialEval (jsub (compAll F μ) K) = 0 := by
      rw [specialEval_eq_eval, eval_jsub, ← specialEval_eq_eval, ← specialEval_eq_eval, hKval,
        sub_self]
    have := passive_transfer p hp j _ hlin hs
    rw [albertEval, eval_jsub] at this
    exact (sub_eq_zero.1 this).symm
  choose K hKs using hK
  let F' : JPoly Test := .add (jsub F (jsum Top (fun _ => 1) (compAll F))) (jsum Top (fun _ => 1) K)
  have hval : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E),
      T.eval v F' = T.eval v F - ∑ μ ∈ Top, T.eval v (compAll F μ) +
        ∑ μ ∈ Top, T.eval v (K μ) := by
    intro E _ _ T v
    change T.eval v (jsub F _) + T.eval v (jsum _ _ _) = _
    rw [eval_jsub, eval_jsum, eval_jsum]
    simp only [one_smul]
  have hspec : specialEval F' = 0 := by
    rw [specialEval_eq_eval, hval, ← specialEval_eq_eval, h0, zero_sub]
    simp only [← specialEval_eq_eval]
    rw [Finset.sum_congr rfl fun μ hμ => (hKs μ hμ).2.1]
    simp
  have halb : albertEval p F' = albertEval p F := by
    change albertTarget.eval _ F' = _
    rw [hval]
    change albertEval p F - ∑ μ ∈ Top, albertEval p (compAll F μ) +
      ∑ μ ∈ Top, albertEval p (K μ) = _
    rw [Finset.sum_congr rfl fun μ hμ => (hKs μ hμ).2.2]
    simp
  have hdeg' : F'.deg ≤ 7 := by
    simp only [F', jsub, JPoly.deg, max_le_iff]
    refine ⟨⟨hdeg, deg_jsum _ _ _ _ fun μ hμ => ?_⟩, deg_jsum _ _ _ _ fun μ hμ => ?_⟩
    · rw [homog_deg (homog_compAll F μ)]
      have := (Finset.mem_filter.1 hμ).2.2
      omega
    · have := (hKs μ hμ).1; omega
  have hcomp : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
      (ν : MD), N < mdSize ν →
      T.eval v (compAll F' ν) = T.eval v (compAll F ν) -
        (if ν ∈ Top then T.eval v (compAll F ν) else 0) := by
    intro E _ _ T v ν hν
    change T.eval v (compAll (jsub F _) ν) + T.eval v (compAll (jsum _ _ _) ν) = _
    rw [eval_compAll_jsub, eval_compAll_jsum, eval_compAll_jsum]
    simp only [one_smul]
    rw [Finset.sum_eq_zero fun μ hμ =>
      eval_compAll_big T v (K μ) ν (by have := (hKs μ hμ).1; omega), add_zero]
    simp only [eval_compAll_homog T v (homog_compAll F _) ν]
    rw [Finset.sum_ite_eq]
  have hgood' : GoodAbove p N F' := by
    intro ν h4 hν
    have hcs := hcomp (specialTarget (UniversalProjectionAlgebra 4)) specialSymmetry ν hν
    have hca := hcomp albertTarget (nativeSymmetry p) ν hν
    simp only [← specialEval_eq_eval] at hcs
    change albertEval p (compAll F' ν) = albertEval p (compAll F ν) -
      (if ν ∈ Top then albertEval p (compAll F ν) else 0) at hca
    by_cases hbig : N + 1 < mdSize ν
    · obtain ⟨h1, h2⟩ := hgood ν h4 hbig
      rw [hcs, hca, h1, h2]
      simp
    · have hmem : ν ∈ Top := by
        refine Finset.mem_filter.2 ⟨mem_boxMD.2 fun i => le_of_mdSize_le (by omega) i, h4, by omega⟩
      rw [hcs, hca, ite_eq_left hmem, ite_eq_left hmem, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
  rw [← halb]
  exact hc F' hdeg' hgood' hspec

theorem claim_seven (hp : ∀ i, IsAtom (p i)) (hL : RecognitionThroughFivePos) : ClaimAt p 7 :=
  claim_step p hp hL 6 (by norm_num) (by norm_num)
    (claim_step p hp hL 5 (by norm_num) (by norm_num)
      (claim_step p hp hL 4 (by norm_num) (by norm_num)
        (claim_step p hp hL 3 (by norm_num) (by norm_num) (claim_three p hp))))

end Descent

/-- **lem:cer:h5:seven from lem:cer:h5:lift (proved).** `TransferThroughSeven` holds whenever
`RecognitionThroughFivePos` does. -/
theorem transferThroughSeven_of_lift (hL : RecognitionThroughFivePos) : TransferThroughSeven := by
  classical
  intro p hp F hdeg h0
  let F₀ : JPoly Test := jsum F.support (fun G => F G) id
  have hval : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E),
      T.eval v F₀ = ∑ G ∈ F.support, F G • T.eval v G := by
    intro E _ _ T v
    exact eval_jsum T v _ _ _
  have hdeg₀ : F₀.deg ≤ 7 := deg_jsum _ _ _ _ fun G hG => hdeg G hG
  have hs : specialEval F₀ = 0 := by
    rw [specialEval_eq_eval, hval]
    exact h0
  have hgood : GoodAbove p 7 F₀ := by
    intro μ _ hμ
    exact ⟨eval_compAll_big _ _ F₀ μ (by omega), eval_compAll_big _ _ F₀ μ (by omega)⟩
  have := claim_seven p hp hL F₀ hdeg₀ hgood hs
  change albertTarget.eval _ F₀ = 0 at this
  rw [hval] at this
  exact this

/-- **Horizon five from lem:cer:h5:refl(a) and lem:cer:h5:lift.** -/
theorem horizonFive_of_refl_a_and_lift (hA : ReflectionClassConsistency)
    (hL : RecognitionThroughFivePos) : HorizonFiveClause :=
  horizonFive_of_refl_a_and_seven hA (transferThroughSeven_of_lift hL)

end AlbertSequential.HorizonFive
