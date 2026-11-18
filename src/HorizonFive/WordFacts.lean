/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Contraction

/-! # Facts about reduced words in `ℝ[G]` used by lem:cer:h5:seven

* `groupElt_reduceRW`: a word and its reduced form have the same group element;
* `count_reduceRW`: reduction deletes letters in equal pairs (counts drop by an even number);
* `groupElt_span_top`, `expand_eq`: the reduced words span `ℝ[G]`, and every element is the sum of
  its coefficients times reduced words;
* `star_groupElt`, `star_specialEval`: reversal is `star`, and special values are reversal-fixed;
  `expand_class`: a reversal-fixed element is the sum of its coefficients times reversal classes;
* `letterSpan`, `specialEval_mem_letterSpan`, `coef_eq_zero_of_letterSpan`: special values of
  expressions avoiding some letters only involve reduced words avoiding those letters. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

theorem flipWord_cases (a : Test) (g : RW) :
    (∃ t, g.1 = a :: t ∧ (flipWord a g).1 = t) ∨ (flipWord a g).1 = a :: g.1 := by
  unfold flipWord
  split
  · rename_i h
    left
    obtain ⟨l, hl⟩ := g
    cases l with
    | nil => simp at h
    | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at h
      exact ⟨t, by simp [h], rfl⟩
  · right; rfl

/-- Reduction deletes letters in equal pairs. -/
theorem count_reduceRW (l : List Test) (i : Test) :
    ∃ k, l.count i = (reduceRW l).1.count i + 2 * k := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons a l ih =>
    obtain ⟨k, hk⟩ := ih
    simp only [reduceRW]
    rcases flipWord_cases a (reduceRW l) with ⟨t, h1, h2⟩ | h
    · rw [h2]
      rw [h1] at hk
      by_cases hia : a = i
      · subst hia
        refine ⟨k + 1, ?_⟩
        simp only [List.count_cons_self] at hk ⊢
        omega
      · refine ⟨k, ?_⟩
        simp only [List.count_cons, beq_iff_eq, hia, ↓reduceIte] at hk ⊢
        omega
    · rw [h]
      refine ⟨k, ?_⟩
      simp only [List.count_cons]
      omega

theorem count_reduceRW_le (l : List Test) (i : Test) : (reduceRW l).1.count i ≤ l.count i := by
  obtain ⟨k, hk⟩ := count_reduceRW l i
  omega

theorem mem_of_mem_reduceRW {l : List Test} {i : Test} (h : i ∈ (reduceRW l).1) : i ∈ l := by
  rw [← List.count_pos_iff] at h ⊢
  exact lt_of_lt_of_le h (count_reduceRW_le l i)

/-! ## Spanning and expansion -/

/-- The span of the group elements of all words. -/
def allWordSpan : Submodule ℝ (UniversalProjectionAlgebra 4) :=
  Submodule.span ℝ (Set.range groupElt)

theorem allWordSpan_mul {x y : UniversalProjectionAlgebra 4} (hx : x ∈ allWordSpan)
    (hy : y ∈ allWordSpan) : x * y ∈ allWordSpan := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, rfl⟩ := hu
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨m, rfl⟩ := hv
      rw [← groupElt_append]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

theorem allWordSpan_top : allWordSpan = ⊤ := by
  have key : ∀ f, projectionQuotient 4 f ∈ allWordSpan := by
    intro f
    induction f using FreeAlgebra.induction with
    | grade0 r =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
    | grade1 i =>
      have e : projectionQuotient 4 (FreeAlgebra.ι ℝ i) =
          (1 / 2 : ℝ) • (groupElt [] + groupElt [i]) := by
        change universalProjection i = _
        simp only [groupElt, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
          mul_one, specialSymmetry]
        change universalProjection i = (1 / 2 : ℝ) • (1 + ((2 : ℝ) • universalProjection i - 1))
        module
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩))
    | mul a b ha hb => rw [map_mul]; exact allWordSpan_mul ha hb
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨f, rfl⟩ := projectionQuotient_surjective 4 x
  exact key f

/-- The coefficient vector of an element on reduced words. -/
def coefVec : UniversalProjectionAlgebra 4 →ₗ[ℝ] RWSpace :=
  (LinearMap.applyₗ (Finsupp.single emptyRW (1 : ℝ))).comp regularRep.toLinearMap

theorem coefVec_apply (x : UniversalProjectionAlgebra 4) (g : RW) : coefVec x g = coef g x := rfl

/-- Expansion on reduced words. -/
def expandL : UniversalProjectionAlgebra 4 →ₗ[ℝ] UniversalProjectionAlgebra 4 :=
  (Finsupp.linearCombination ℝ (fun g : RW => groupElt g.1)).comp coefVec

theorem coefVec_groupElt (l : List Test) : coefVec (groupElt l) = Finsupp.single (reduceRW l) 1 :=
  regularRep_groupElt l

theorem expandL_eq_id : expandL = LinearMap.id := by
  apply LinearMap.ext_on_range (v := groupElt)
  · exact allWordSpan_top
  · intro l
    simp only [expandL, LinearMap.coe_comp, Function.comp_apply, coefVec_groupElt,
      Finsupp.linearCombination_single, one_smul, groupElt_reduceRW, LinearMap.id_apply]

/-- Every element is the sum of its coefficients times reduced words. -/
theorem expand_eq (x : UniversalProjectionAlgebra 4) :
    x = ∑ g ∈ (coefVec x).support, coef g x • groupElt g.1 := by
  have h := congrArg (fun f => f x) expandL_eq_id
  simp only [expandL, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
    Finsupp.linearCombination_apply, Finsupp.sum] at h
  exact h.symm

theorem mem_coefVec_support {x : UniversalProjectionAlgebra 4} {g : RW} :
    g ∈ (coefVec x).support ↔ coef g x ≠ 0 := Finsupp.mem_support_iff

/-! ## Reversal -/

theorem star_specialSymmetry (i : Test) : star (specialSymmetry i) = specialSymmetry i := by
  simp only [specialSymmetry, star_sub, star_smul, star_one, star_trivial]
  rw [show star (universalTests i) = universalTests i from universalProjection_selfAdjoint i]

theorem star_groupElt (l : List Test) : star (groupElt l) = groupElt l.reverse := by
  induction l with
  | nil => simp [groupElt]
  | cons a l ih =>
    rw [groupElt_cons, star_mul, ih, star_specialSymmetry, List.reverse_cons, groupElt_append]
    simp [groupElt]

theorem star_specialEval (F : JPoly Test) : star (specialEval F) = specialEval F := by
  induction F with
  | one => exact star_one _
  | var i => exact star_specialSymmetry i
  | add a b ha hb =>
    change star (specialEval a + specialEval b) = specialEval a + specialEval b
    rw [star_add, ha, hb]
  | smul r a ha =>
    change star (r • specialEval a) = r • specialEval a
    rw [star_smul, ha, star_trivial]
  | mul a b ha hb =>
    change star ((specialTarget _).mul (specialEval a) (specialEval b)) =
      (specialTarget _).mul (specialEval a) (specialEval b)
    rw [specialTarget_mul, star_smul, star_add, star_mul, star_mul, ha, hb, star_trivial,
      add_comm]

/-- A reversal-fixed element is the sum of its coefficients times reversal classes. -/
theorem expand_class (x : UniversalProjectionAlgebra 4) (hx : star x = x) :
    x = ∑ g ∈ (coefVec x).support, coef g x • classElt g.1 := by
  have h1 := expand_eq x
  have h2 : star x = ∑ g ∈ (coefVec x).support, coef g x • groupElt g.1.reverse := by
    conv_lhs => rw [h1]
    rw [star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [star_smul, star_trivial, star_groupElt]
  rw [hx] at h2
  symm
  calc ∑ g ∈ (coefVec x).support, coef g x • classElt g.1
      = (1 / 2 : ℝ) • (∑ g ∈ (coefVec x).support, coef g x • groupElt g.1 +
          ∑ g ∈ (coefVec x).support, coef g x • groupElt g.1.reverse) := by
        rw [← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [classElt, smul_add, smul_smul]
        module
    _ = (1 / 2 : ℝ) • (x + x) := by rw [← h1, ← h2]
    _ = x := by module

/-! ## Letter filter -/

/-- The span of the group elements of words whose letters satisfy `P`. -/
def letterSpan (P : Test → Prop) : Submodule ℝ (UniversalProjectionAlgebra 4) :=
  Submodule.span ℝ (groupElt '' {l | ∀ x ∈ l, P x})

theorem letterSpan_mul (P : Test → Prop) {x y : UniversalProjectionAlgebra 4}
    (hx : x ∈ letterSpan P) (hy : y ∈ letterSpan P) : x * y ∈ letterSpan P := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨m, hm, rfl⟩ := hv
      rw [← groupElt_append]
      refine Submodule.subset_span ⟨_, fun z hz => ?_, rfl⟩
      rcases List.mem_append.1 hz with h | h
      · exact hl z h
      · exact hm z h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

/-- Special values of expressions whose letters satisfy `P` lie in `letterSpan P`. -/
theorem specialEval_mem_letterSpan (P : Test → Prop) (F : JPoly Test)
    (hF : ∀ z, ¬ P z → F.FreeOf z) : specialEval F ∈ letterSpan P := by
  induction F with
  | one => exact Submodule.subset_span ⟨[], fun z hz => by simp at hz, rfl⟩
  | var i =>
    have hi : P i := by
      by_contra h
      cases hF i h with
      | var _ hne => exact hne rfl
    refine Submodule.subset_span ⟨[i], fun z hz => ?_, by simp [groupElt]; rfl⟩
    simp only [List.mem_singleton] at hz
    rw [hz]; exact hi
  | add a b ha hb =>
    have ha' := ha fun z hz => by cases hF z hz with | add _ _ h _ => exact h
    have hb' := hb fun z hz => by cases hF z hz with | add _ _ _ h => exact h
    exact Submodule.add_mem _ ha' hb'
  | smul r a ha =>
    have ha' := ha fun z hz => by cases hF z hz with | smul _ _ h => exact h
    exact Submodule.smul_mem _ r ha'
  | mul a b ha hb =>
    have ha' := ha fun z hz => by cases hF z hz with | mul _ _ h _ => exact h
    have hb' := hb fun z hz => by cases hF z hz with | mul _ _ _ h => exact h
    change (specialTarget _).mul (specialEval a) (specialEval b) ∈ _
    rw [specialTarget_mul]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (letterSpan_mul P ha' hb')
      (letterSpan_mul P hb' ha'))

/-- `coef g` vanishes on `letterSpan P` if `g` has a letter outside `P`. -/
theorem coef_eq_zero_of_letterSpan (P : Test → Prop) (g : RW) (z : Test) (hz : z ∈ g.1)
    (hPz : ¬ P z) {x : UniversalProjectionAlgebra 4} (hx : x ∈ letterSpan P) : coef g x = 0 := by
  have : letterSpan P ≤ LinearMap.ker (coef g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    change coef g (groupElt l) = 0
    rw [coef_groupElt, ite_eq_right]
    intro h
    rw [← h] at hz
    exact hPz (hl z (mem_of_mem_reduceRW hz))
  exact this hx

end AlbertSequential.HorizonFive
