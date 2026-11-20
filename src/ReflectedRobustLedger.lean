/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustUniform
public import ReflectedRobustVector
public import ReflectedRobustData1
public import ReflectedRobustData2
public import ReflectedRobustData3
public import ReflectedRobustData4
public import ReflectedRobustData5
public import ReflectedRobustData6

/-! Check the complete reflected witness at its fixed native table. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open LengthSeven LengthSeven.LemmaA LengthSeven.Robust

def reflectedGramPairs : List (ℚ × Entry) :=
  reflectedGramBlock1 ++ reflectedGramBlock2 ++ reflectedGramBlock3 ++
    reflectedGramBlock4 ++ reflectedGramBlock5 ++ reflectedGramBlock6

theorem reflectedGramPairs_spec :
    reflectedGramPairs.map (fun p => (p.1,p.2.u1,p.2.u2)) = pairSpec reflectedRobustVector := by
  decide +kernel

theorem reflectedGramPairs_checked :
    reflectedGramPairs.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramPairs, List.all_append, reflectedGramBlock1_check,
    reflectedGramBlock2_check, reflectedGramBlock3_check, reflectedGramBlock4_check,
    reflectedGramBlock5_check, reflectedGramBlock6_check, Bool.and_self]

theorem reflectedGramPairs_ok : reflectedGramPairs.all (fun p => p.2.ok) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have h := List.all_eq_true.mp reflectedGramPairs_checked p hp
  simp only [reflectedEntryCheck, Bool.and_eq_true, and_assoc] at h
  exact h.1

theorem reflectedGramPairs_octOk : octOk reflectedTraceTable reflectedGramPairs = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have h := List.all_eq_true.mp reflectedGramPairs_checked p hp
  simp only [reflectedEntryCheck, Bool.and_eq_true, and_assoc] at h
  change (_ && _) = true
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro m hm
    have ht := List.all_eq_true.mp h.2.1 m hm
    simp only [Bool.and_eq_true] at ht
    exact ht.1
  · apply List.all_eq_true.mpr
    intro d hd
    have hh := List.all_eq_true.mp h.2.2.1 d hd
    simp only [Bool.and_eq_true, and_assoc] at hh
    simp only [Bool.and_eq_true]
    exact ⟨hh.1, hh.2.1⟩

theorem reflectedGramPairs_purityConstants :
    ∀ p ∈ reflectedGramPairs, ∀ d ∈ p.2.defs, 0 ≤ d.c ∧ d.c ≤ 1 := by
  intro p hp d hd
  have h := List.all_eq_true.mp reflectedGramPairs_checked p hp
  simp only [reflectedEntryCheck, Bool.and_eq_true, and_assoc] at h
  have hh := List.all_eq_true.mp h.2.2.1 d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hh
  exact ⟨hh.2.2.1,hh.2.2.2.1⟩

private theorem counterT_append (a b : List (ℚ × Entry)) :
    counterT (a++b) = counterT a + counterT b := by simp [counterT]

private theorem reflectedDefectWeight_append (a b : List (ℚ × Entry)) :
    reflectedDefectWeight (a++b) = reflectedDefectWeight a + reflectedDefectWeight b := by
  simp [reflectedDefectWeight]

private theorem uniformReflectionValueQ_append (T : TraceTable) (ε : ℚ) (a b : List (ℚ × Entry)) :
    uniformReflectionValueQ T ε (a++b) = uniformReflectionValueQ T ε a + uniformReflectionValueQ T ε b := by
  simp [uniformReflectionValueQ]

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock1_table :
    counterT reflectedGramBlock1 = (31380893/69984 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock1_defect :
    reflectedDefectWeight reflectedGramBlock1 = (10641377/1296 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock1_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock1 = (1606355458255/6902073042624 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock2_table :
    counterT reflectedGramBlock2 = (101077591/209952 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock2_defect :
    reflectedDefectWeight reflectedGramBlock2 = (9464833/1296 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock2_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock2 = (253918375351/1150345507104 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock3_table :
    counterT reflectedGramBlock3 = (29188663/34992 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock3_defect :
    reflectedDefectWeight reflectedGramBlock3 = (4898215/648 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock3_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock3 = (-7094757663785/13804146085248 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock4_table :
    counterT reflectedGramBlock4 = (7922659/11664 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock4_defect :
    reflectedDefectWeight reflectedGramBlock4 = (192407/27 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock4_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock4 = (122026838959/1200360529152 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock5_table :
    counterT reflectedGramBlock5 = (3723007/6561 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock5_defect :
    reflectedDefectWeight reflectedGramBlock5 = (3873569/648 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock5_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock5 = (-762385339171/9202764056832 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock6_table :
    counterT reflectedGramBlock6 = (10321393/104976 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock6_defect :
    reflectedDefectWeight reflectedGramBlock6 = (78655/72 : ℚ) := by decide +kernel

set_option maxHeartbeats 12000000 in
private theorem reflectedBlock6_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramBlock6 = (41526606689/1150345507104 : ℚ) := by decide +kernel

theorem reflectedGramPairs_table :
    counterT reflectedGramPairs = (40796195/13122 : ℚ) := by
  simp only [reflectedGramPairs, counterT_append, reflectedBlock1_table, reflectedBlock2_table, reflectedBlock3_table, reflectedBlock4_table, reflectedBlock5_table, reflectedBlock6_table]
  norm_num

theorem reflectedGramPairs_defect :
    reflectedDefectWeight reflectedGramPairs = (1006273/27 : ℚ) := by
  simp only [reflectedGramPairs, reflectedDefectWeight_append, reflectedBlock1_defect, reflectedBlock2_defect, reflectedBlock3_defect, reflectedBlock4_defect, reflectedBlock5_defect, reflectedBlock6_defect]
  norm_num

theorem reflectedGramPairs_value :
    uniformReflectionValueQ reflectedTraceTable reflectedRobustEpsilon reflectedGramPairs = (-76976323523/13804146085248 : ℚ) := by
  simp only [reflectedGramPairs, uniformReflectionValueQ_append, reflectedBlock1_value, reflectedBlock2_value, reflectedBlock3_value, reflectedBlock4_value, reflectedBlock5_value, reflectedBlock6_value]
  norm_num

end AlbertSequential.FiveTest
