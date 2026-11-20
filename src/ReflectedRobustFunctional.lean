/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ReflectedRobustLedger
public import ReflectedRobustTransfer

/-! The actual positive reflected word functional and its five-test margin. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open LengthSeven LengthSeven.LemmaA LengthSeven.Robust

/-- The reflected tail coefficients with the deposited uniform Young penalty. -/
def reflectedRobustTailTerms : List (ℚ × Word Letter) :=
  uniformReflectionPenalty reflectedRobustEpsilon reflectedGramPairs

theorem reflectedRobustTailTerms_wordBudget (m : ℚ × Word Letter) (hm : m ∈ reflectedRobustTailTerms) :
    budgetCost (dropYesA m.2) ≤ 10 := uniformReflectionPenalty_wordBudget reflectedGramPairs_checked m hm

theorem reflectedRobustTailTerms_l1 : l1 reflectedRobustTailTerms < 32750000000000 := by
  refine (uniformReflectionPenalty_coeff_bound _ reflectedRobustEpsilon_pos _
    reflectedGramPairs_purityConstants).trans_lt ?_
  rw [reflectedGramPairs_table, reflectedGramPairs_defect]
  norm_num [reflectedRobustEpsilon]

theorem reflectedRobustTailTerms_nonnegative {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) :
    0 ≤ evalF (fun w => W.normSq (W.vec w)) reflectedRobustTailTerms :=
  uniformReflectionPenalty_nonneg W _ reflectedRobustEpsilon_pos reflectedRobustVector _
    reflectedGramPairs_spec reflectedGramPairs_ok

/-- Expand each anchored reflected word into the literal signed five-test terms. -/
def expandReflectedFunctional (L : List (ℚ × Word Letter)) : FiniteRealWordFunctional 5 where
  terms := L.flatMap fun m => (reflectedAnchoredTerms (dropYesA m.2)).map fun t =>
    ((m.1 : ℝ) * (t.1 : ℝ), t.2)

theorem evaluate_expandReflectedFunctional (L : List (ℚ × Word Letter))
    (g : Word (Fin 5) → ℝ) (f : Word Letter → ℝ)
    (h : ∀ u, reflectedAnchoredEvaluation g u = f ((0,true)::u)) :
    (expandReflectedFunctional L).evaluate g = (BlockB.toE3Functional L).evaluate f := by
  induction L with
  | nil => rfl
  | cons m L ih =>
    change (((reflectedAnchoredTerms (dropYesA m.2)).map (fun t => ((m.1 : ℝ)*(t.1 : ℝ), t.2))
      ++ (expandReflectedFunctional L).terms).map (fun t => t.1 * g t.2)).sum =
        (m.1 : ℝ) * f ((0,true) :: dropYesA m.2) + (BlockB.toE3Functional L).evaluate f
    change ((expandReflectedFunctional L).terms.map (fun t => t.1 * g t.2)).sum =
      (BlockB.toE3Functional L).evaluate f at ih
    rw [List.map_append, List.sum_append, ih, ← h (dropYesA m.2)]
    congr 1
    unfold reflectedAnchoredEvaluation
    rw [List.map_map, mul_sum_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    ring

private theorem reflectedAnchoredTerms_real_weight {u : Word Letter} (hu : budgetCost u ≤ 10) :
    ((reflectedAnchoredTerms u).map fun t => |(t.1 : ℝ)|).sum ≤ (5^5 : ℝ) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (reflectedAnchoredTerms_weight hu)
  rw [Nat.cast_list_sum, List.map_map] at h
  change ((reflectedAnchoredTerms u).map fun t => (t.1.natAbs : ℝ)).sum ≤ _ at h
  simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat] using h

theorem expandReflectedFunctional_norm (L : List (ℚ × Word Letter))
    (h : ∀ m ∈ L, budgetCost (dropYesA m.2) ≤ 10) :
    (expandReflectedFunctional L).coefficientNorm ≤ (5^5 : ℝ) * l1 L := by
  refine (expandReflectedFunctional L).coefficientNorm_le_rawCoefficientBound.trans ?_
  change ((((L.flatMap fun m => (reflectedAnchoredTerms (dropYesA m.2)).map fun t =>
    ((m.1 : ℝ) * (t.1 : ℝ), t.2))).map fun t => |t.1|).sum) ≤ _
  rw [sum_map_flatMap, l1, cast_sum_map, mul_sum_map]
  apply sum_map_le
  intro m hm
  simp only [List.map_map]
  change ((reflectedAnchoredTerms (dropYesA m.2)).map fun t => |(m.1 : ℝ) * (t.1 : ℝ)|).sum ≤ _
  rw [Rat.cast_abs]
  simp only [abs_mul, List.sum_map_mul_left]
  rw [mul_comm (5^5 : ℝ)]
  exact mul_le_mul_of_nonneg_left (reflectedAnchoredTerms_real_weight (h m hm)) (abs_nonneg _)

/-- The concrete reflected five-test functional. -/
def reflectedFiveTestFunctional : FiniteRealWordFunctional 5 :=
  expandReflectedFunctional reflectedRobustTailTerms

theorem reflectedFiveTestFunctional_support (w : Word (Fin 5))
    (hw : w ∈ reflectedFiveTestFunctional.coefficients.support) :
    w.head? = some (0,true) ∧ w.length ≤ 11 := by
  by_contra hn
  have hz : reflectedFiveTestFunctional.coefficients w = 0 := by
    apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
    intro t ht heq
    have ht' : t ∈ (expandReflectedFunctional reflectedRobustTailTerms).terms := ht
    obtain ⟨p,hp,ht'⟩ := List.mem_flatMap.mp ht'
    obtain ⟨r,hr,hr'⟩ := List.mem_map.mp ht'
    have hgood := reflectedAnchoredTerms_horizon (reflectedRobustTailTerms_wordBudget p hp) hr
    apply hn
    have he : r.2 = w := (congrArg Prod.snd hr').trans heq
    rwa [he] at hgood
  exact (Finsupp.mem_support_iff.mp hw) hz

theorem reflectedFiveTestFunctional_coefficientNorm :
    reflectedFiveTestFunctional.coefficientNorm < (5^5 : ℝ) * 32750000000000 := by
  refine (expandReflectedFunctional_norm _ reflectedRobustTailTerms_wordBudget).trans_lt ?_
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  exact_mod_cast reflectedRobustTailTerms_l1

theorem reflectedFiveTestFunctional_native :
    reflectedFiveTestFunctional.evaluate (nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit)) ≤
      -(11/11664 : ℝ) := by
  unfold reflectedFiveTestFunctional
  rw [evaluate_expandReflectedFunctional _ _ _ (fun u =>
      (nativeQuad_probability_eq_reflectedAnchoredEvaluation ((1/3 : ℝ) • albertUnit) u).symm),
    BlockB.toE3Functional_native_evaluation reflQuad reflQuad_isAtom, reflectedRobustTailTerms,
    eval_uniformReflectionPenalty reflectedTraceTable reflectedTraceTable_holds
      (tableValues_native reflQuad reflQuad_isAtom) _ _ reflectedGramPairs_octOk, reflectedGramPairs_value]
  norm_num

section Models

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem reflectedFiveTestFunctional_nonneg (M : AlgebraicProjectiveData (Fin 5) A) :
    0 ≤ reflectedFiveTestFunctional.evaluate M.probability := by
  unfold reflectedFiveTestFunctional
  rw [evaluate_expandReflectedFunctional _ _ _ (fun u =>
    (quadModel_probability_eq_reflectedAnchoredEvaluation M u).symm)]
  exact BlockB.toE3Functional_nonneg_of_walkForm (quadModel M) _ fun h =>
    reflectedRobustTailTerms_nonnegative (WalkForm.ofAlgebraic (quadModel M) h)

/-- The explicit separation threshold printed in the companion. -/
def reflectedFiveTestMargin : ℝ := (11/11664) / ((5:ℝ)^5 * 32750000000000)

theorem reflectedFiveTestMargin_gt : (9/10^21 : ℝ) < reflectedFiveTestMargin := by
  norm_num [reflectedFiveTestMargin]

theorem reflectedFiveTest_robust_algebraic (M : AlgebraicProjectiveData (Fin 5) A) :
    ∃ w : Word (Fin 5), w.head? = some (0,true) ∧ w.length ≤ 11 ∧
      reflectedFiveTestMargin <
        |M.probability w - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| := by
  by_contra hn
  have hδ : ∀ w ∈ reflectedFiveTestFunctional.coefficients.support,
      |M.probability w - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| ≤
        reflectedFiveTestMargin := by
    intro w hw
    obtain ⟨hhead,hlen⟩ := reflectedFiveTestFunctional_support w hw
    exact le_of_not_gt fun h => hn ⟨w,hhead,hlen,h⟩
  have hδpos : 0 < reflectedFiveTestMargin := by norm_num [reflectedFiveTestMargin]
  have h := reflectedFiveTestFunctional.separation_forces_error M.probability
    (nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit)) reflectedFiveTestMargin (11/11664)
    hδpos.le hδ (reflectedFiveTestFunctional_nonneg M) reflectedFiveTestFunctional_native
  have hstrict := mul_lt_mul_of_pos_right reflectedFiveTestFunctional_coefficientNorm hδpos
  have he : ((5^5 : ℝ) * 32750000000000) * reflectedFiveTestMargin = 11/11664 := by
    norm_num [reflectedFiveTestMargin]
  rw [he] at hstrict
  exact (not_lt_of_ge h) hstrict

end Models

theorem reflectedFiveTest_robust_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 5) 𝕜 H) :
    ∃ w : Word (Fin 5), w.head? = some (0,true) ∧ w.length ≤ 11 ∧
      reflectedFiveTestMargin <
        |M.probability w - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| := by
  obtain ⟨w,hh,hl,h⟩ := reflectedFiveTest_robust_algebraic M.toAlgebraic
  exact ⟨w,hh,hl,by simpa only [M.toAlgebraic_probability] using h⟩

theorem reflectedFiveTest_robust_quaternionic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 5) Q) :
    ∃ w : Word (Fin 5), w.head? = some (0,true) ∧ w.length ≤ 11 ∧
      reflectedFiveTestMargin <
        |M.state (M.wordEffect w) - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| := by
  obtain ⟨w,hh,hl,h⟩ := reflectedFiveTest_robust_algebraic M.toAlgebraic
  exact ⟨w,hh,hl,by simpa only [M.toAlgebraic_probability] using h⟩

end AlbertSequential.FiveTest
