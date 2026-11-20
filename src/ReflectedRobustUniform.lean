/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ReflectedRobustTranscript
public import PaperRobustResiduals
public import FiveTest.Quad
import Mathlib.Tactic.FieldSimp

/-! Uniform Young penalties for the reflected robustness argument. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open LengthSeven LengthSeven.LemmaA LengthSeven.Robust

/-- A schedule whose left-word bucket is one for every path. The assembly
uses this auxiliary table only to select a uniform penalty parameter. -/
def uniformSchedule : TraceTable := ⟨1,1,1,1,1,1,0,0,0,0,0,0,0⟩

private theorem uniformSchedule_oQ (a b : Letter) (h : a ≠ b) :
    uniformSchedule.oQ a b = 1 := by
  fin_cases a <;> fin_cases b <;>
    first | exact (h rfl).elim | rfl

private theorem uniformSchedule_chainQ :
    ∀ u : List Letter, chainQ uniformSchedule u = none ∨ chainQ uniformSchedule u = some 1
  | [] => Or.inr rfl
  | [_] => Or.inr rfl
  | a :: b :: u => by
      simp only [chainQ]
      split
      · exact Or.inl rfl
      · rename_i hab
        rcases uniformSchedule_chainQ (b :: u) with h | h
        · rw [h]
          exact Or.inl rfl
        · rw [h, Option.map_some, uniformSchedule_oQ a b hab, mul_one]
          exact Or.inr rfl

private theorem uniformSchedule_eps (ε : ℚ) (α : List Letter) : epsQ uniformSchedule ε α = ε := by
  have hp : piQ uniformSchedule α = 1 := by
    rcases uniformSchedule_chainQ (0 :: α) with h | h <;> simp [piQ, fvalQ, h]
  rw [epsQ, hp]
  have hr : rOf 64 1 (1 : ℚ) = 1 := by decide +kernel
  rw [hr, mul_one]

/-- The actual table and defect words with one Young parameter for all defects. -/
def uniformReflectionPenalty (ε : ℚ) (pairs : List (ℚ × Entry)) : List (ℚ × Word Letter) :=
  lam2 uniformSchedule ε pairs

theorem uniformReflectionPenalty_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) (ε : ℚ) (hε : 0 < ε)
    (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hp : pairs.map (fun p => (p.1,p.2.u1,p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    0 ≤ evalF (fun w => W.normSq (W.vec w)) (uniformReflectionPenalty ε pairs) :=
  lam2_nonneg W uniformSchedule ε hε vecs pairs hp hok

/-- The target value obtained by evaluating the actual table terms and the
left-word penalties. The calibrated residual-square polynomials vanish. -/
def uniformReflectionValueQ (T : TraceTable) (ε : ℚ) (pairs : List (ℚ × Entry)) : ℚ :=
  (pairs.map fun p =>
    (p.2.tabs.map fun m => p.1 * m.1 * (fvalQ T m.2).getD 0).sum +
    (p.2.defs.map fun d => |p.1 * d.y| * ε / 2 * piQ T d.α).sum).sum

theorem eval_uniformReflectionPenalty {τ : TraceData} {f : Word Letter → ℝ}
    (T : TraceTable) (h : T.Holds τ) (hT : TableValues τ f) (ε : ℚ)
    (pairs : List (ℚ × Entry)) (hok : octOk T pairs = true) :
    evalF f (uniformReflectionPenalty ε pairs) = uniformReflectionValueQ T ε pairs := by
  unfold uniformReflectionPenalty lam2 uniformReflectionValueQ
  rw [evalF_flatMap, cast_sum_map]
  congr 1
  apply List.map_congr_left
  intro p hm
  have hp := List.all_eq_true.mp hok p hm
  simp only [Bool.and_eq_true] at hp
  unfold entryTerms
  rw [evalF_append, evalF_tabs, evalF_flatMap, mul_sum_map, Rat.cast_add, cast_sum_map, cast_sum_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro m hm
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hp.1 m hm)
    rw [fvalQ_sound h hT m.2 v hv, hv]
    simp only [Option.getD_some]
    push_cast
    ring
  · congr 1
    apply List.map_congr_left
    intro d hd
    have hs := List.all_eq_true.mp hp.2 d hd
    simp only [Bool.and_eq_true] at hs
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hs.1
    have hα : f (yesWord d.α) = v := fvalQ_sound h hT (.yes d.α) v hv
    have hπ : piQ T d.α = v := by simp [piQ,hv]
    rw [evalF_defTerms, uniformSchedule_eps, hα, hπ, xok_sound h hT d hs.2]
    simp only [zero_div, add_zero]
    push_cast
    ring

theorem reflectedTraceTable_holds : reflectedTraceTable.Holds (nativeTraceData reflQuad) := by
  obtain ⟨o1,o2,o3,o4,o5,o6⟩ := reflQuad_overlaps
  obtain ⟨r1,r2,r3,r4⟩ := reflQuad_triangles
  obtain ⟨w1,w2,w3⟩ := reflQuad_omegas
  obtain ⟨n1,n2,n3⟩ := nativeTraceData_om reflQuad
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o1
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o2
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o3
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o4
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o5
  · simpa [reflectedTraceTable, nativeTraceData_o, fpOverlap] using o6
  · simpa [reflectedTraceTable, nativeTraceData_R, fpTriangle] using r1
  · simpa [reflectedTraceTable, nativeTraceData_R, fpTriangle] using r2
  · simpa [reflectedTraceTable, nativeTraceData_R, fpTriangle] using r3
  · simpa [reflectedTraceTable, nativeTraceData_R, fpTriangle] using r4
  · simpa [reflectedTraceTable] using n1.trans w1
  · simpa [reflectedTraceTable] using n2.trans w2
  · simpa [reflectedTraceTable] using n3.trans w3

/-- The uniform Young parameter of the deposited calculation. -/
def reflectedRobustEpsilon : ℚ := (11/1944) / ((713/9)^2 * (97/2))

theorem reflectedRobustEpsilon_pos : 0 < reflectedRobustEpsilon := by norm_num [reflectedRobustEpsilon]

private theorem l1_append (a b : List (ℚ × Word Letter)) :
    l1 (a ++ b) = l1 a + l1 b := by simp [l1]

private theorem l1_flatMap {α : Type} (u : List α) (f : α → List (ℚ × Word Letter)) :
    l1 (u.flatMap f) = (u.map fun a => l1 (f a)).sum := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.flatMap_cons, l1_append, ih, List.map_cons, List.sum_cons]

private theorem sum_map_le_rat {α : Type} (u : List α) (f g : α → ℚ)
    (h : ∀ x ∈ u, f x ≤ g x) : (u.map f).sum ≤ (u.map g).sum := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (List.mem_cons_self ..)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem uniformScheduledDefect_bound (ε : ℚ) (hε : 0 < ε) (k : ℚ) (d : Defect)
    (hc : 0 ≤ d.c) (hc' : d.c ≤ 1) :
    l1 (defTerms uniformSchedule ε k d) ≤ |k * d.y| * (ε / 2 + 2 / ε) := by
  let a := |k * d.y|
  have ha : 0 ≤ a := abs_nonneg _
  simp only [defTerms, uniformSchedule_eps, l1, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, abs_neg, add_zero]
  change |a * ε / 2| + (|a / (2 * ε)| + (|a * d.c / ε| + |a * (d.c * d.c) / (2 * ε)|)) ≤ _
  rw [abs_of_nonneg (by positivity : 0 ≤ a * ε / 2),
    abs_of_nonneg (by positivity : 0 ≤ a / (2 * ε)),
    abs_of_nonneg (by positivity : 0 ≤ a * d.c / ε),
    abs_of_nonneg (by positivity : 0 ≤ a * (d.c * d.c) / (2 * ε))]
  have hmid : a * d.c / ε ≤ a / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    exact (mul_le_mul_of_nonneg_left hc' ha).trans_eq (mul_one _)
  have hsq : d.c * d.c ≤ 1 := (mul_le_mul hc' hc' hc zero_le_one).trans_eq (one_mul _)
  have hlast : a * (d.c * d.c) / (2 * ε) ≤ a / (2 * ε) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_left hsq ha).trans_eq (mul_one _)
  calc
    _ ≤ a * ε / 2 + (a / (2 * ε) + (a / ε + a / (2 * ε))) := by linarith
    _ = _ := by field_simp; ring

theorem uniformReflectionPenalty_coeff_bound (ε : ℚ) (hε : 0 < ε)
    (pairs : List (ℚ × Entry))
    (h : ∀ p ∈ pairs, ∀ d ∈ p.2.defs, 0 ≤ d.c ∧ d.c ≤ 1) :
    l1 (uniformReflectionPenalty ε pairs) ≤ counterT pairs + reflectedDefectWeight pairs * (ε / 2 + 2 / ε) := by
  unfold uniformReflectionPenalty lam2 counterT reflectedDefectWeight
  rw [l1_flatMap, ← List.sum_map_mul_right, ← List.sum_map_add]
  apply sum_map_le_rat
  intro p hp
  simp only [entryTerms, l1_append, l1_flatMap]
  have ht :
      l1 (p.2.tabs.map fun m => (p.1 * m.1,m.2.toWord)) =
        |p.1| * (p.2.tabs.map fun m => |m.1|).sum := by
    rw [l1, List.map_map]
    change (p.2.tabs.map fun m => |p.1 * m.1|).sum = _
    simp only [abs_mul, List.sum_map_mul_left]
  rw [ht, ← List.sum_map_mul_right]
  apply add_le_add (le_refl _)
  apply sum_map_le_rat
  intro d hd
  exact uniformScheduledDefect_bound ε hε p.1 d (h p hp d hd).1 (h p hp d hd).2

theorem uniformReflectionPenalty_wordBudget {ε : ℚ} {pairs : List (ℚ × Entry)}
    (h : pairs.all (fun p => reflectedEntryCheck p.2) = true)
    (m : ℚ × Word Letter) (hm : m ∈ uniformReflectionPenalty ε pairs) :
    budgetCost (dropYesA m.2) ≤ 10 := by
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hm
  have he := List.all_eq_true.mp h p hp
  simp only [reflectedEntryCheck, Bool.and_eq_true, and_assoc] at he
  rcases List.mem_append.mp hm with ht | hd
  · change m ∈ p.2.tabs.map (fun t => (p.1 * t.1, t.2.toWord)) at ht
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp ht
    have hh := List.all_eq_true.mp he.2.1 t ht
    simp only [Bool.and_eq_true, reflectedSupportCheck, decide_eq_true_eq] at hh
    rw [← heq]
    exact hh.2
  · obtain ⟨d,hd,hm⟩ := List.mem_flatMap.mp hd
    have hh := List.all_eq_true.mp he.2.2.1 d hd
    simp only [Bool.and_eq_true, reflectedSupportCheck, decide_eq_true_eq, and_assoc] at hh
    simp only [defTerms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hh.2.2.2.2.1
    · exact hh.2.2.2.2.2.1
    · exact hh.2.2.2.2.2.2.1
    · exact hh.2.2.2.2.2.2.2

end AlbertSequential.FiveTest
