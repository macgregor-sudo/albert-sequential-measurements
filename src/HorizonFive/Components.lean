/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.ThreeLetters

/-! # Multidegree components of Jordan expressions

The paper grades `𝒫` by multidegree.  On the syntax `JPoly Test` this file defines the component
`compAll F μ` of multidegree `μ` (a Jordan expression, homogeneous of multidegree `μ` in the sense
of `IsHomog`), and proves, in every target:

* `eval_compAll_homog`: components of a homogeneous expression are itself or zero;
* `eval_compAll_big`: components of multidegree larger than the degree vanish;
* `eval_decomp`: an expression is the sum of its components over the box `boxMD n`, `n ≥ deg`;
* `homog_freeOf`, `homog_linearIn`, `homog_deg`: a homogeneous expression with `μ_j = 0` is free
  of `x_j`, with `μ_j = 1` has degree one in `x_j`, and has degree `|μ|`;
* (eq:cer:h5:filter) with parity: `specialEval_mem_mdSpan`, `coef_mdSpan`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- Multidegrees. -/
abbrev MD := Test → ℕ

/-- Total degree `|μ|`. -/
def mdSize (μ : MD) : ℕ := ∑ i, μ i

/-- Homogeneity for letter weights `x_i ↦ e_i`. -/
abbrev HomogP (μ : MD) (F : JPoly Test) : Prop := IsHomog (fun i => Pi.single i 1) μ F

theorem homog_cast {μ ν : MD} {F : JPoly Test} (h : HomogP μ F) (e : μ = ν) : HomogP ν F :=
  e ▸ h

/-- `x_i^n`. -/
def powP (i : Test) : ℕ → JPoly Test
  | 0 => .one
  | n + 1 => .mul (.var i) (powP i n)

theorem homog_powP (i : Test) (n : ℕ) : HomogP (n • Pi.single i 1) (powP i n) := by
  induction n with
  | zero => exact homog_cast IsHomog.one (by simp)
  | succ n ih =>
    exact homog_cast (IsHomog.mul _ _ _ _ (IsHomog.var i) ih)
      (by rw [succ_nsmul]; exact add_comm _ _)

/-- A homogeneous representative of multidegree `μ`. -/
def monoP (μ : MD) : JPoly Test :=
  .mul (.mul (powP 0 (μ 0)) (powP 1 (μ 1))) (.mul (powP 2 (μ 2)) (powP 3 (μ 3)))

theorem homog_monoP (μ : MD) : HomogP μ (monoP μ) := by
  refine homog_cast (IsHomog.mul _ _ _ _ (IsHomog.mul _ _ _ _ (homog_powP 0 _) (homog_powP 1 _))
    (IsHomog.mul _ _ _ _ (homog_powP 2 _) (homog_powP 3 _))) ?_
  funext i
  fin_cases i <;> simp [Pi.single_apply]

/-- The homogeneous zero of multidegree `μ`. -/
def zeroOf (μ : MD) : JPoly Test := .smul 0 (monoP μ)

theorem homog_zeroOf (μ : MD) : HomogP μ (zeroOf μ) := IsHomog.smul _ _ _ (homog_monoP μ)

theorem eval_zeroOf {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
    (μ : MD) : T.eval v (zeroOf μ) = 0 := by
  simp [zeroOf, JTarget.eval]

/-- Pointwise form of `ν ≤ μ` (stated with an explicit type so that `omega` sees it). -/
theorem md_le {ν μ : MD} (h : ν ≤ μ) (i : Test) : ν i ≤ μ i := h i

/-- Multidegrees below `μ`. -/
def belowMD (μ : MD) : Finset MD := Fintype.piFinset fun i => Finset.range (μ i + 1)

theorem mem_belowMD {μ ν : MD} : ν ∈ belowMD μ ↔ ν ≤ μ := by
  simp only [belowMD, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
  exact Iff.rfl

/-- The box of multidegrees with all entries at most `n`. -/
def boxMD (n : ℕ) : Finset MD := Fintype.piFinset fun _ => Finset.range (n + 1)

theorem mem_boxMD {n : ℕ} {ν : MD} : ν ∈ boxMD n ↔ ∀ i, ν i ≤ n := by
  simp only [boxMD, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

/-- `Σ` of a list, with homogeneous zero of multidegree `μ` at the end. -/
def hsumL (μ : MD) : List (JPoly Test) → JPoly Test
  | [] => zeroOf μ
  | F :: l => .add F (hsumL μ l)

theorem homog_hsumL (μ : MD) (l : List (JPoly Test)) (h : ∀ F ∈ l, HomogP μ F) :
    HomogP μ (hsumL μ l) := by
  induction l with
  | nil => exact homog_zeroOf μ
  | cons F l ih => exact IsHomog.add _ _ _ (h F (by simp)) (ih fun G hG => h G (by simp [hG]))

theorem eval_hsumL {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)
    (μ : MD) (l : List (JPoly Test)) : T.eval v (hsumL μ l) = (l.map (T.eval v)).sum := by
  induction l with
  | nil => simp [hsumL, eval_zeroOf]
  | cons F l ih => simp only [hsumL, JTarget.eval, ih, List.map_cons, List.sum_cons]

/-- The component of multidegree `μ`. -/
def compAll : JPoly Test → MD → JPoly Test
  | .one, μ => if μ = 0 then .one else zeroOf μ
  | .var i, μ => if μ = Pi.single i 1 then .var i else zeroOf μ
  | .add a b, μ => .add (compAll a μ) (compAll b μ)
  | .smul r a, μ => .smul r (compAll a μ)
  | .mul a b, μ => hsumL μ ((belowMD μ).toList.map fun ν => .mul (compAll a ν) (compAll b (μ - ν)))

theorem homog_compAll (F : JPoly Test) (μ : MD) : HomogP μ (compAll F μ) := by
  induction F generalizing μ with
  | one =>
    unfold compAll
    split_ifs with h
    · exact homog_cast IsHomog.one h.symm
    · exact homog_zeroOf μ
  | var i =>
    unfold compAll
    split_ifs with h
    · exact homog_cast (IsHomog.var i) h.symm
    · exact homog_zeroOf μ
  | add a b ha hb => exact IsHomog.add _ _ _ (ha μ) (hb μ)
  | smul r a ha => exact IsHomog.smul _ _ _ (ha μ)
  | mul a b ha hb =>
    refine homog_hsumL μ _ fun G hG => ?_
    simp only [List.mem_map, Finset.mem_toList] at hG
    obtain ⟨ν, hν, rfl⟩ := hG
    refine homog_cast (IsHomog.mul _ _ _ _ (ha ν) (hb (μ - ν))) ?_
    have := mem_belowMD.1 hν
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    have := md_le this i
    omega

/-! ## Bilinear sums in a target -/

theorem JTarget.zero_mul' {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (y : E) :
    T.mul 0 y = 0 := by
  have h := T.smul_mul 0 0 y
  rw [zero_smul, zero_smul] at h
  exact h

theorem JTarget.mul_zero' {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (y : E) :
    T.mul y 0 = 0 := by
  rw [T.comm, T.zero_mul']

theorem JTarget.sum_mul' {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) {ι : Type*}
    (s : Finset ι) (f : ι → E) (y : E) : T.mul (∑ i ∈ s, f i) y = ∑ i ∈ s, T.mul (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, T.zero_mul']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, T.add_mul, ih]

theorem JTarget.mul_sum' {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) {ι : Type*}
    (s : Finset ι) (f : ι → E) (y : E) : T.mul y (∑ i ∈ s, f i) = ∑ i ∈ s, T.mul y (f i) := by
  rw [T.comm, T.sum_mul']
  exact Finset.sum_congr rfl fun i _ => T.comm _ _

section Eval
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (v : Test → E)

theorem eval_compAll_mul (a b : JPoly Test) (μ : MD) :
    T.eval v (compAll (.mul a b) μ) =
      ∑ ν ∈ belowMD μ, T.mul (T.eval v (compAll a ν)) (T.eval v (compAll b (μ - ν))) := by
  rw [compAll, eval_hsumL, List.map_map]
  rw [← Finset.sum_map_toList]
  rfl

theorem eval_compAll_homog {α : MD} {H : JPoly Test} (hH : HomogP α H) (μ : MD) :
    T.eval v (compAll H μ) = if μ = α then T.eval v H else 0 := by
  induction hH generalizing μ with
  | one =>
    unfold compAll
    split_ifs <;> simp [JTarget.eval, eval_zeroOf]
  | var y =>
    unfold compAll
    split_ifs <;> simp [JTarget.eval, eval_zeroOf]
  | add μ' a b _ _ ha hb =>
    show T.eval v (compAll a μ) + T.eval v (compAll b μ) = _
    rw [ha, hb]
    split_ifs <;> simp [JTarget.eval]
  | smul μ' r a _ ha =>
    show r • T.eval v (compAll a μ) = _
    rw [ha]
    split_ifs <;> simp [JTarget.eval]
  | mul β γ a b _ _ ha hb =>
    rw [eval_compAll_mul]
    simp only [ha, hb]
    by_cases hμ : μ = β + γ
    · rw [ite_eq_left hμ, Finset.sum_eq_single β]
      · have : μ - β = γ := by subst hμ; funext i; simp
        rw [ite_eq_left rfl, ite_eq_left this]
        rfl
      · intro ν _ hν
        rw [ite_eq_right hν, T.zero_mul']
      · intro h
        exact absurd (mem_belowMD.2 (by subst hμ; intro i; simp)) h
    · rw [ite_eq_right hμ]
      refine Finset.sum_eq_zero fun ν hν => ?_
      by_cases h1 : ν = β
      · have h2 : μ - ν ≠ γ := by
          intro h2
          apply hμ
          have hle := mem_belowMD.1 hν
          funext i
          have := congrFun h2 i
          have := md_le hle i
          simp only [Pi.sub_apply] at *
          subst h1
          simp only [Pi.add_apply]
          omega
        rw [ite_eq_right h2, T.mul_zero']
      · rw [ite_eq_right h1, T.zero_mul']

theorem mdSize_sub_add {μ ν : MD} (h : ν ≤ μ) : mdSize ν + mdSize (μ - ν) = mdSize μ := by
  simp only [mdSize, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := md_le h i
  simp only [Pi.sub_apply]
  omega

theorem mdSize_single (i : Test) : mdSize (Pi.single i 1) = 1 := by
  simp [mdSize]

theorem eval_compAll_big (F : JPoly Test) (μ : MD) (h : F.deg < mdSize μ) :
    T.eval v (compAll F μ) = 0 := by
  induction F generalizing μ with
  | one =>
    unfold compAll
    have : μ ≠ 0 := by rintro rfl; simp [mdSize, JPoly.deg] at h
    rw [ite_eq_right this, eval_zeroOf]
  | var i =>
    unfold compAll
    have : μ ≠ Pi.single i 1 := by rintro rfl; rw [mdSize_single] at h; simp [JPoly.deg] at h
    rw [ite_eq_right this, eval_zeroOf]
  | add a b ha hb =>
    simp only [JPoly.deg, max_lt_iff] at h
    show T.eval v (compAll a μ) + T.eval v (compAll b μ) = 0
    rw [ha μ h.1, hb μ h.2, add_zero]
  | smul r a ha =>
    show r • T.eval v (compAll a μ) = 0
    rw [ha μ h, smul_zero]
  | mul a b ha hb =>
    simp only [JPoly.deg] at h
    rw [eval_compAll_mul]
    refine Finset.sum_eq_zero fun ν hν => ?_
    have hs := mdSize_sub_add (mem_belowMD.1 hν)
    by_cases h1 : a.deg < mdSize ν
    · rw [ha ν h1, T.zero_mul']
    · rw [hb (μ - ν) (by omega), T.mul_zero']

theorem le_of_mdSize_le {ν : MD} {n : ℕ} (h : mdSize ν ≤ n) (i : Test) : ν i ≤ n := by
  have : ν i ≤ mdSize ν := Finset.single_le_sum (fun j _ => Nat.zero_le (ν j)) (Finset.mem_univ i)
  omega

/-- An expression is the sum of its components (over any box containing its degree). -/
theorem eval_decomp (F : JPoly Test) (n : ℕ) (hn : F.deg ≤ n) :
    T.eval v F = ∑ μ ∈ boxMD n, T.eval v (compAll F μ) := by
  classical
  induction F generalizing n with
  | one =>
    rw [Finset.sum_eq_single 0]
    · simp [compAll, JTarget.eval]
    · intro μ _ hμ
      simp only [compAll, ite_eq_right hμ, eval_zeroOf]
    · intro h; exact absurd (mem_boxMD.2 fun _ => Nat.zero_le _) h
  | var i =>
    simp only [JPoly.deg] at hn
    rw [Finset.sum_eq_single (Pi.single i 1)]
    · simp [compAll, JTarget.eval]
    · intro μ _ hμ
      simp only [compAll, ite_eq_right hμ, eval_zeroOf]
    · intro h
      refine absurd (mem_boxMD.2 fun k => ?_) h
      simp only [Pi.single_apply]; split_ifs <;> omega
  | add a b ha hb =>
    simp only [JPoly.deg, max_le_iff] at hn
    show T.eval v a + T.eval v b = ∑ μ ∈ boxMD n, (T.eval v (compAll a μ) + T.eval v (compAll b μ))
    rw [Finset.sum_add_distrib, ← ha n hn.1, ← hb n hn.2]
  | smul r a ha =>
    simp only [JPoly.deg] at hn
    show r • T.eval v a = ∑ μ ∈ boxMD n, r • T.eval v (compAll a μ)
    rw [← Finset.smul_sum, ← ha n hn]
  | mul a b ha hb =>
    simp only [JPoly.deg] at hn
    show T.mul (T.eval v a) (T.eval v b) = _
    rw [ha n (by omega), hb n (by omega), T.sum_mul']
    simp only [T.mul_sum', eval_compAll_mul]
    rw [← Finset.sum_product', Finset.sum_sigma']
    refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_
    · intro x hx hne
      have h1 : mdSize x.1 ≤ a.deg := by
        by_contra hc; exact hne (by rw [eval_compAll_big T v a x.1 (by omega), T.zero_mul'])
      have h2 : mdSize x.2 ≤ b.deg := by
        by_contra hc; exact hne (by rw [eval_compAll_big T v b x.2 (by omega), T.mul_zero'])
      have hs : mdSize (x.1 + x.2) ≤ n := by
        simp only [mdSize, Pi.add_apply, Finset.sum_add_distrib]
        simp only [mdSize] at h1 h2
        omega
      refine Finset.mem_sigma.2 ⟨mem_boxMD.2 (le_of_mdSize_le hs), mem_belowMD.2 fun i => ?_⟩
      simp
    · intro x _ _ y _ _ hxy
      simp only [Sigma.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have h2' : x.1 = y.1 := eq_of_heq h2
      refine Prod.ext h2' ?_
      funext i
      have := congrFun h1 i
      have := congrFun h2' i
      simp only [Pi.add_apply] at *
      omega
    · intro z hz hne
      obtain ⟨hμ, hν⟩ := Finset.mem_sigma.1 hz
      have hle := mem_belowMD.1 hν
      refine ⟨(z.2, z.1 - z.2), ?_, ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨mem_boxMD.2 fun i => ?_, mem_boxMD.2 fun i => ?_⟩
        · exact le_trans (hle i) (mem_boxMD.1 hμ i)
        · simp only [Pi.sub_apply]; exact le_trans (Nat.sub_le _ _) (mem_boxMD.1 hμ i)
      · exact hne
      · have : z.2 + (z.1 - z.2) = z.1 := by funext i; have := md_le hle i; simp; omega
        simp only [this]
    · intro x _ _
      have : x.1 + x.2 - x.1 = x.2 := by funext i; simp
      simp only [this]

end Eval

/-! ## Homogeneity and letters -/

theorem homog_letters (j : Test) {μ : MD} {F : JPoly Test} (h : HomogP μ F) :
    (μ j = 0 → F.FreeOf j) ∧ (μ j = 1 → F.LinearIn j) := by
  induction h with
  | one => exact ⟨fun _ => .one, fun h => by simp at h⟩
  | var y =>
    refine ⟨fun h => .var y fun hy => ?_, fun h => ?_⟩
    · subst hy; simp at h
    · by_cases hy : y = j
      · subst hy; exact .var
      · simp [Pi.single_apply, Ne.symm hy] at h
  | add μ a b _ _ ha hb =>
    exact ⟨fun h => .add _ _ (ha.1 h) (hb.1 h), fun h => .add _ _ (ha.2 h) (hb.2 h)⟩
  | smul μ r a _ ha => exact ⟨fun h => .smul _ _ (ha.1 h), fun h => .smul _ _ (ha.2 h)⟩
  | mul μ ν a b _ _ ha hb =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply] at h
      exact .mul _ _ (ha.1 (by omega)) (hb.1 (by omega))
    · simp only [Pi.add_apply] at h
      rcases Nat.eq_zero_or_pos (μ j) with h0 | h0
      · exact .mulRight _ _ (ha.1 h0) (hb.2 (by omega))
      · exact .mulLeft _ _ (ha.2 (by omega)) (hb.1 (by omega))

theorem homog_deg {μ : MD} {F : JPoly Test} (h : HomogP μ F) : F.deg = mdSize μ := by
  induction h with
  | one => simp [JPoly.deg, mdSize]
  | var y => simp [JPoly.deg, mdSize_single]
  | add μ a b _ _ ha hb => simp [JPoly.deg, ha, hb]
  | smul μ r a _ ha => simp [JPoly.deg, ha]
  | mul μ ν a b _ _ ha hb =>
    simp only [JPoly.deg, ha, hb, mdSize, Pi.add_apply, Finset.sum_add_distrib]

/-! ## (eq:cer:h5:filter) with multidegrees -/

/-- The span of the group elements of words of multidegree exactly `μ`. -/
def mdSpan (μ : MD) : Submodule ℝ (UniversalProjectionAlgebra 4) :=
  Submodule.span ℝ (groupElt '' {l | ∀ i, l.count i = μ i})

theorem mdSpan_mul {μ ν : MD} {x y : UniversalProjectionAlgebra 4} (hx : x ∈ mdSpan μ)
    (hy : y ∈ mdSpan ν) : x * y ∈ mdSpan (μ + ν) := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, hm, rfl⟩ := hw
      rw [← groupElt_append]
      refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
      simp only [List.count_append, Pi.add_apply, hl i, hm i]
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

theorem specialEval_mem_mdSpan {μ : MD} {F : JPoly Test} (h : HomogP μ F) :
    specialEval F ∈ mdSpan μ := by
  induction h with
  | one => exact Submodule.subset_span ⟨[], fun i => by simp, rfl⟩
  | var y =>
    refine Submodule.subset_span ⟨[y], fun i => ?_, by simp [groupElt]; rfl⟩
    simp only [List.count_singleton, Pi.single_apply, beq_iff_eq]
    split_ifs <;> simp_all
  | add μ a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul μ r a _ ha => exact Submodule.smul_mem _ r ha
  | mul μ ν a b _ _ ha hb =>
    change (specialTarget _).mul (specialEval a) (specialEval b) ∈ _
    rw [specialTarget_mul]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ (mdSpan_mul ha hb) ?_)
    rw [add_comm μ ν]
    exact mdSpan_mul hb ha

/-- Coefficients on `mdSpan μ`: a reduced word with nonzero coefficient has multidegree
`μ - 2κ`. -/
theorem coef_mdSpan {μ : MD} (g : RW) {x : UniversalProjectionAlgebra 4} (hx : x ∈ mdSpan μ)
    (hg : coef g x ≠ 0) : ∀ i, ∃ k, μ i = g.1.count i + 2 * k := by
  by_contra hc
  apply hg
  have : mdSpan μ ≤ LinearMap.ker (coef g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    change coef g (groupElt l) = 0
    rw [coef_groupElt, ite_eq_right]
    intro h
    apply hc
    intro i
    obtain ⟨k, hk⟩ := count_reduceRW l i
    exact ⟨k, by rw [← hl i, hk, h]⟩
  exact this hx

end AlbertSequential.HorizonFive
