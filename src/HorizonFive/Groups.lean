/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Symbols

/-! # Reduced words of `G = ℤ₂^{*4}` inside the universal projection algebra

The paper's special target is `ℝ[G]^+`, `G = ℤ₂^{*4}` with generators `r_i`; here it is the
universal projection algebra with `r_i = 2P_i - 1` (so `r_i² = 1`).  The degree-nine and
degree-eight steps of the final assembly read off coefficients of reduced words, i.e. they use
that the reduced words are linearly independent.  This file proves that, by the classical
action of `G` on the free vector space on reduced words (`r_i` acts by `flipWord i`, which
deletes a leading `i` or prepends one):

* `reduceRW l` is the reduced form of a word (computed by the action);
* `coef g` is a linear functional with `coef g (groupElt l) = [reduceRW l = g]`
  (`coef_groupElt`), hence the reduced words are linearly independent
  (`groupElt_linearIndependent`);
* (eq:cer:h5:filter), length form: the special value of an operator word with `a` operators `A`
  and `b` operators `C` lies in the span of words of length at most `a + 2b`
  (`opSpecial_single_mem_wordSpan`), so `coef g` kills it when `|g| > a + 2b`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- Reduced words: no two adjacent letters equal. -/
def reducedB : List Test → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a ≠ b) && reducedB (b :: l)

/-- Reduced words, i.e. the elements of `G`. -/
abbrev RW := {l : List Test // reducedB l = true}

theorem reducedB_tail (a : Test) (l : List Test) (h : reducedB (a :: l) = true) :
    reducedB l = true := by
  cases l with
  | nil => rfl
  | cons b l =>
    simp only [reducedB, Bool.and_eq_true] at h
    exact h.2

theorem reducedB_cons (a : Test) (l : List Test) (hl : reducedB l = true)
    (ha : l.head? ≠ some a) : reducedB (a :: l) = true := by
  cases l with
  | nil => rfl
  | cons b l =>
    simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun h => ha (by simp [h]), hl⟩

/-- Left multiplication by the generator `r_i` on reduced words. -/
def flipWord (i : Test) (g : RW) : RW :=
  if h : g.1.head? = some i then ⟨g.1.tail, by
    obtain ⟨l, hl⟩ := g
    cases l with
    | nil => exact rfl
    | cons a l => exact reducedB_tail a l hl⟩
  else ⟨i :: g.1, reducedB_cons i g.1 g.2 h⟩

theorem flipWord_flipWord (i : Test) (g : RW) : flipWord i (flipWord i g) = g := by
  obtain ⟨l, hl⟩ := g
  cases l with
  | nil => simp [flipWord]
  | cons a l =>
    by_cases ha : a = i
    · subst ha
      have hl' : l.head? ≠ some a := by
        cases l with
        | nil => simp
        | cons b l =>
          simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hl
          simp only [List.head?_cons, ne_eq, Option.some.injEq]
          exact fun h => hl.1 h.symm
      simp [flipWord, hl']
    · have h1 : (a :: l).head? ≠ some i := by simp [ha]
      have e1 : flipWord i ⟨a :: l, hl⟩ = ⟨i :: a :: l, reducedB_cons i _ hl h1⟩ := by
        unfold flipWord
        split
        · exact absurd ‹_› h1
        · rfl
      rw [e1]
      unfold flipWord
      split
      · rfl
      · exact absurd rfl ‹_›

/-- The reduced form, computed by the action: `reduceRW (a :: l) = r_a · reduceRW l`. -/
def reduceRW : List Test → RW
  | [] => ⟨[], rfl⟩
  | a :: l => flipWord a (reduceRW l)

theorem flipWord_length (i : Test) (g : RW) : (flipWord i g).1.length ≤ g.1.length + 1 := by
  unfold flipWord
  split
  · simp only [List.length_tail]; omega
  · simp

theorem reduceRW_length (l : List Test) : (reduceRW l).1.length ≤ l.length := by
  induction l with
  | nil => simp [reduceRW]
  | cons a l ih =>
    simp only [reduceRW, List.length_cons]
    exact le_trans (flipWord_length a _) (by omega)

theorem reduceRW_of_reduced (l : List Test) (hl : reducedB l = true) : reduceRW l = ⟨l, hl⟩ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [reduceRW]
    rw [ih (reducedB_tail a l hl)]
    have ha : l.head? ≠ some a := by
      cases l with
      | nil => simp
      | cons b l =>
        simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at hl
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact fun h => hl.1 h.symm
    simp [flipWord, ha]

/-! ## The regular action of the universal algebra -/

/-- The free vector space on reduced words. -/
abbrev RWSpace := RW →₀ ℝ

/-- `r_i` acting on `RWSpace`. -/
def flipLin (i : Test) : Module.End ℝ RWSpace := Finsupp.lmapDomain ℝ ℝ (flipWord i)

theorem flipLin_flipLin (i : Test) (x : RWSpace) : flipLin i (flipLin i x) = x := by
  simp only [flipLin, Finsupp.lmapDomain_apply]
  rw [← Finsupp.mapDomain_comp]
  have : (flipWord i ∘ flipWord i) = id := funext (flipWord_flipWord i)
  rw [this, Finsupp.mapDomain_id]

/-- `P_i = (1 + r_i)/2` acting on `RWSpace`. -/
def projOp (i : Test) : Module.End ℝ RWSpace := (1 / 2 : ℝ) • (1 + flipLin i)

theorem projOp_idem (i : Test) : projOp i * projOp i = projOp i := by
  apply LinearMap.ext
  intro x
  simp only [projOp, mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
    one_apply_eq_self, map_smul, map_add, flipLin_flipLin]
  module

/-- The regular representation of the universal projection algebra. -/
def regularRep : UniversalProjectionAlgebra 4 →ₐ[ℝ] Module.End ℝ RWSpace :=
  RingQuot.liftAlgHom ℝ ⟨FreeAlgebra.lift ℝ projOp, by
    intro x y h
    cases h with
    | generator i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      exact projOp_idem i⟩

theorem regularRep_universalTests (i : Test) : regularRep (universalTests i) = projOp i := by
  simp only [regularRep, universalTests, universalProjection, projectionQuotient]
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp only [FreeAlgebra.lift_ι_apply]

theorem regularRep_specialSymmetry (i : Test) : regularRep (specialSymmetry i) = flipLin i := by
  simp only [specialSymmetry, map_sub, map_smul, map_one, regularRep_universalTests, projOp]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self]
  module

/-- The group element of a (not necessarily reduced) word, `r_{l_1} ⋯ r_{l_k}`. -/
def groupElt (l : List Test) : UniversalProjectionAlgebra 4 := (l.map specialSymmetry).prod

theorem groupElt_cons (a : Test) (l : List Test) :
    groupElt (a :: l) = specialSymmetry a * groupElt l := by
  simp [groupElt]

theorem groupElt_append (l m : List Test) : groupElt (l ++ m) = groupElt l * groupElt m := by
  simp [groupElt, List.prod_append]

/-- The basis vector of the empty word. -/
def emptyRW : RW := ⟨[], rfl⟩

theorem regularRep_groupElt (l : List Test) :
    regularRep (groupElt l) (Finsupp.single emptyRW 1) = Finsupp.single (reduceRW l) 1 := by
  induction l with
  | nil => simp [groupElt, reduceRW, emptyRW]
  | cons a l ih =>
    rw [groupElt_cons, map_mul, mul_apply_eq_comp, ih, regularRep_specialSymmetry]
    simp only [flipLin, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, reduceRW]

/-- The coefficient of the reduced word `g`. -/
def coef (g : RW) : UniversalProjectionAlgebra 4 →ₗ[ℝ] ℝ :=
  (Finsupp.lapply g).comp ((LinearMap.applyₗ (Finsupp.single emptyRW (1 : ℝ))).comp
    regularRep.toLinearMap)

theorem coef_apply (g : RW) (x : UniversalProjectionAlgebra 4) :
    coef g x = regularRep x (Finsupp.single emptyRW 1) g := rfl

theorem coef_groupElt (g : RW) (l : List Test) :
    coef g (groupElt l) = if reduceRW l = g then 1 else 0 := by
  rw [coef_apply, regularRep_groupElt, Finsupp.single_apply]

theorem reduceRW_val (g : RW) : reduceRW g.1 = g := reduceRW_of_reduced g.1 g.2

/-- Reduced words are linearly independent in the universal projection algebra. -/
theorem groupElt_linearIndependent : LinearIndependent ℝ (fun g : RW => groupElt g.1) := by
  rw [linearIndependent_iff']
  intro s a hsum h hh
  have := congrArg (coef h) hsum
  rw [map_sum, map_zero] at this
  simp only [map_smul, coef_groupElt, reduceRW_val, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at this
  rw [Finset.sum_ite_eq' s h] at this
  simpa [hh] using this

/-! ## (eq:cer:h5:filter), length form -/

/-- The span of the group elements of words of length at most `n`. -/
def wordSpan (n : ℕ) : Submodule ℝ (UniversalProjectionAlgebra 4) :=
  Submodule.span ℝ (groupElt '' {l | l.length ≤ n})

theorem groupElt_mem_wordSpan {l : List Test} {n : ℕ} (h : l.length ≤ n) :
    groupElt l ∈ wordSpan n :=
  Submodule.subset_span ⟨l, h, rfl⟩

theorem wordSpan_mono {m n : ℕ} (h : m ≤ n) : wordSpan m ≤ wordSpan n :=
  Submodule.span_mono (Set.image_mono fun l (hl : l.length ≤ m) => le_trans hl h)

theorem left_mul_mem_wordSpan (i : Test) {n : ℕ} {x : UniversalProjectionAlgebra 4}
    (hx : x ∈ wordSpan n) : specialSymmetry i * x ∈ wordSpan (n + 1) := by
  have : wordSpan n ≤ (wordSpan (n + 1)).comap (LinearMap.mulLeft ℝ (specialSymmetry i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    change specialSymmetry i * groupElt l ∈ wordSpan (n + 1)
    rw [← groupElt_cons]
    exact groupElt_mem_wordSpan (by simp only [List.length_cons]; exact Nat.succ_le_succ hl)
  exact this hx

theorem right_mul_mem_wordSpan (i : Test) {n : ℕ} {x : UniversalProjectionAlgebra 4}
    (hx : x ∈ wordSpan n) : x * specialSymmetry i ∈ wordSpan (n + 1) := by
  have : wordSpan n ≤ (wordSpan (n + 1)).comap (LinearMap.mulRight ℝ (specialSymmetry i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    change groupElt l * specialSymmetry i ∈ wordSpan (n + 1)
    have : groupElt l * specialSymmetry i = groupElt (l ++ [i]) := by
      rw [groupElt_append]; simp [groupElt]
    rw [this]
    exact groupElt_mem_wordSpan (by
      simp only [List.length_append, List.length_singleton]; exact Nat.succ_le_succ hl)
  exact this hx

/-- The degree of an operator word: `A` counts one, `C` counts two. -/
def opDeg : List Op → ℕ
  | [] => 0
  | .A _ :: l => opDeg l + 1
  | .C _ :: l => opDeg l + 2

theorem specialTarget_Aop_eq (x y : UniversalProjectionAlgebra 4) :
    (specialTarget _).Aop x y = x * y + y * x := by
  simp only [JTarget.Aop, specialTarget_mul, smul_smul]
  norm_num

/-- (eq:cer:h5:filter), length form: special values of operator words. -/
theorem specialEval_opPoly_mem_wordSpan (l : List Op) :
    specialEval (opPoly l) ∈ wordSpan (opDeg l) := by
  induction l with
  | nil =>
    change (1 : UniversalProjectionAlgebra 4) ∈ wordSpan 0
    exact groupElt_mem_wordSpan (l := []) le_rfl
  | cons o l ih =>
    cases o with
    | A i =>
      change (specialTarget _).Aop (specialSymmetry i) (specialEval (opPoly l)) ∈ _
      rw [specialTarget_Aop_eq]
      exact Submodule.add_mem _ (left_mul_mem_wordSpan i ih) (right_mul_mem_wordSpan i ih)
    | C i =>
      change (specialTarget _).eval specialSymmetry (JPoly.U _ _) ∈ _
      rw [JTarget.eval_U, specialTarget_Uop]
      exact right_mul_mem_wordSpan i (left_mul_mem_wordSpan i ih)

/-- `coef g` kills `wordSpan n` when `|g| > n`. -/
theorem coef_eq_zero_of_mem_wordSpan (g : RW) {n : ℕ} (hg : n < g.1.length)
    {x : UniversalProjectionAlgebra 4} (hx : x ∈ wordSpan n) : coef g x = 0 := by
  have : wordSpan n ≤ LinearMap.ker (coef g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    change coef g (groupElt l) = 0
    rw [coef_groupElt, ite_eq_right]
    intro h
    have := reduceRW_length l
    rw [h] at this
    simp only [Set.mem_ofPred_eq] at hl
    omega
  exact this hx

end AlbertSequential.HorizonFive
