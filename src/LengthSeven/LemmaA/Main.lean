/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.EntriesA
public import LengthSeven.LemmaA.EntriesB
public import LengthSeven.LemmaA.EntriesC
public import LengthSeven.LemmaA.EntriesD
public import Mathlib.Tactic.FinCases

/-! # Lemma A (lem:cer:gram28): the table fixes the Gram matrix of the 28 path vectors

* `lemmaA`: from the rule package `UsedRules` (the generated finite list of rule instances at every
  ordering of `B, C, D`, plus (R3_0)), all 784 entries `⟨[w_i], [w_j]⟩ = gram28 τ i j`.
* `lemmaA_of_gram28Rules`: the same from the interface package `Gram28Rules` (pure walk-form
  algebra, no table, no word set); `lemmaA_contract` is `Pending.LemmaAContract gram28`.
* `lemmaA_of_gram28Hyp`: hypotheses (i)-(iii) of lem:cer:gram28 on a word set `S`.
* `lemmaA_on`: finite-route form: the table on `S` with the used forcing words in `S`.
* `lemmaA_e3`, `lemmaA_budget`: the two word sets of the paper, coverage by `decide`:
  words from `p_A` of length at most six (= A-initial words of length at most seven from `e/3`),
  and the five-test budget `|u| + ν(u) ≤ 10` (reflected letters `C`, `D`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA

open AlbertSequential AlbertSequential.LengthSeven

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

theorem gram_sym {i j : Fin 28}
    (h : W.form (W.pathVec (word28 j)) (W.pathVec (word28 i)) = gram28 τ j i) :
    W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j := by
  rw [W.symm, h, gram28_symm]

theorem gram_row_0 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 j)) = gram28 τ 0 j := by
  fin_cases j
  exacts [gram_0_0 h, gram_0_1 h, gram_0_2 h, gram_0_3 h, gram_0_4 h, gram_0_5 h, gram_0_6 h, gram_0_7 h, gram_0_8 h, gram_0_9 h, gram_0_10 h, gram_0_11 h, gram_0_12 h, gram_0_13 h, gram_0_14 h, gram_0_15 h, gram_0_16 h, gram_0_17 h, gram_0_18 h, gram_0_19 h, gram_0_20 h, gram_0_21 h, gram_0_22 h, gram_0_23 h, gram_0_24 h, gram_0_25 h, gram_0_26 h, gram_0_27 h]

theorem gram_row_1 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 j)) = gram28 τ 1 j := by
  fin_cases j
  exacts [gram_sym (gram_0_1 h), gram_1_1 h, gram_1_2 h, gram_1_3 h, gram_1_4 h, gram_1_5 h, gram_1_6 h, gram_1_7 h, gram_1_8 h, gram_1_9 h, gram_1_10 h, gram_1_11 h, gram_1_12 h, gram_1_13 h, gram_1_14 h, gram_1_15 h, gram_1_16 h, gram_1_17 h, gram_1_18 h, gram_1_19 h, gram_1_20 h, gram_1_21 h, gram_1_22 h, gram_1_23 h, gram_1_24 h, gram_1_25 h, gram_1_26 h, gram_1_27 h]

theorem gram_row_2 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 j)) = gram28 τ 2 j := by
  fin_cases j
  exacts [gram_sym (gram_0_2 h), gram_sym (gram_1_2 h), gram_2_2 h, gram_2_3 h, gram_2_4 h, gram_2_5 h, gram_2_6 h, gram_2_7 h, gram_2_8 h, gram_2_9 h, gram_2_10 h, gram_2_11 h, gram_2_12 h, gram_2_13 h, gram_2_14 h, gram_2_15 h, gram_2_16 h, gram_2_17 h, gram_2_18 h, gram_2_19 h, gram_2_20 h, gram_2_21 h, gram_2_22 h, gram_2_23 h, gram_2_24 h, gram_2_25 h, gram_2_26 h, gram_2_27 h]

theorem gram_row_3 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 j)) = gram28 τ 3 j := by
  fin_cases j
  exacts [gram_sym (gram_0_3 h), gram_sym (gram_1_3 h), gram_sym (gram_2_3 h), gram_3_3 h, gram_3_4 h, gram_3_5 h, gram_3_6 h, gram_3_7 h, gram_3_8 h, gram_3_9 h, gram_3_10 h, gram_3_11 h, gram_3_12 h, gram_3_13 h, gram_3_14 h, gram_3_15 h, gram_3_16 h, gram_3_17 h, gram_3_18 h, gram_3_19 h, gram_3_20 h, gram_3_21 h, gram_3_22 h, gram_3_23 h, gram_3_24 h, gram_3_25 h, gram_3_26 h, gram_3_27 h]

theorem gram_row_4 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 j)) = gram28 τ 4 j := by
  fin_cases j
  exacts [gram_sym (gram_0_4 h), gram_sym (gram_1_4 h), gram_sym (gram_2_4 h), gram_sym (gram_3_4 h), gram_4_4 h, gram_4_5 h, gram_4_6 h, gram_4_7 h, gram_4_8 h, gram_4_9 h, gram_4_10 h, gram_4_11 h, gram_4_12 h, gram_4_13 h, gram_4_14 h, gram_4_15 h, gram_4_16 h, gram_4_17 h, gram_4_18 h, gram_4_19 h, gram_4_20 h, gram_4_21 h, gram_4_22 h, gram_4_23 h, gram_4_24 h, gram_4_25 h, gram_4_26 h, gram_4_27 h]

theorem gram_row_5 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 j)) = gram28 τ 5 j := by
  fin_cases j
  exacts [gram_sym (gram_0_5 h), gram_sym (gram_1_5 h), gram_sym (gram_2_5 h), gram_sym (gram_3_5 h), gram_sym (gram_4_5 h), gram_5_5 h, gram_5_6 h, gram_5_7 h, gram_5_8 h, gram_5_9 h, gram_5_10 h, gram_5_11 h, gram_5_12 h, gram_5_13 h, gram_5_14 h, gram_5_15 h, gram_5_16 h, gram_5_17 h, gram_5_18 h, gram_5_19 h, gram_5_20 h, gram_5_21 h, gram_5_22 h, gram_5_23 h, gram_5_24 h, gram_5_25 h, gram_5_26 h, gram_5_27 h]

theorem gram_row_6 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 j)) = gram28 τ 6 j := by
  fin_cases j
  exacts [gram_sym (gram_0_6 h), gram_sym (gram_1_6 h), gram_sym (gram_2_6 h), gram_sym (gram_3_6 h), gram_sym (gram_4_6 h), gram_sym (gram_5_6 h), gram_6_6 h, gram_6_7 h, gram_6_8 h, gram_6_9 h, gram_6_10 h, gram_6_11 h, gram_6_12 h, gram_6_13 h, gram_6_14 h, gram_6_15 h, gram_6_16 h, gram_6_17 h, gram_6_18 h, gram_6_19 h, gram_6_20 h, gram_6_21 h, gram_6_22 h, gram_6_23 h, gram_6_24 h, gram_6_25 h, gram_6_26 h, gram_6_27 h]

theorem gram_row_7 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 7)) (W.pathVec (word28 j)) = gram28 τ 7 j := by
  fin_cases j
  exacts [gram_sym (gram_0_7 h), gram_sym (gram_1_7 h), gram_sym (gram_2_7 h), gram_sym (gram_3_7 h), gram_sym (gram_4_7 h), gram_sym (gram_5_7 h), gram_sym (gram_6_7 h), gram_7_7 h, gram_7_8 h, gram_7_9 h, gram_7_10 h, gram_7_11 h, gram_7_12 h, gram_7_13 h, gram_7_14 h, gram_7_15 h, gram_7_16 h, gram_7_17 h, gram_7_18 h, gram_7_19 h, gram_7_20 h, gram_7_21 h, gram_7_22 h, gram_7_23 h, gram_7_24 h, gram_7_25 h, gram_7_26 h, gram_7_27 h]

theorem gram_row_8 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 8)) (W.pathVec (word28 j)) = gram28 τ 8 j := by
  fin_cases j
  exacts [gram_sym (gram_0_8 h), gram_sym (gram_1_8 h), gram_sym (gram_2_8 h), gram_sym (gram_3_8 h), gram_sym (gram_4_8 h), gram_sym (gram_5_8 h), gram_sym (gram_6_8 h), gram_sym (gram_7_8 h), gram_8_8 h, gram_8_9 h, gram_8_10 h, gram_8_11 h, gram_8_12 h, gram_8_13 h, gram_8_14 h, gram_8_15 h, gram_8_16 h, gram_8_17 h, gram_8_18 h, gram_8_19 h, gram_8_20 h, gram_8_21 h, gram_8_22 h, gram_8_23 h, gram_8_24 h, gram_8_25 h, gram_8_26 h, gram_8_27 h]

theorem gram_row_9 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 9)) (W.pathVec (word28 j)) = gram28 τ 9 j := by
  fin_cases j
  exacts [gram_sym (gram_0_9 h), gram_sym (gram_1_9 h), gram_sym (gram_2_9 h), gram_sym (gram_3_9 h), gram_sym (gram_4_9 h), gram_sym (gram_5_9 h), gram_sym (gram_6_9 h), gram_sym (gram_7_9 h), gram_sym (gram_8_9 h), gram_9_9 h, gram_9_10 h, gram_9_11 h, gram_9_12 h, gram_9_13 h, gram_9_14 h, gram_9_15 h, gram_9_16 h, gram_9_17 h, gram_9_18 h, gram_9_19 h, gram_9_20 h, gram_9_21 h, gram_9_22 h, gram_9_23 h, gram_9_24 h, gram_9_25 h, gram_9_26 h, gram_9_27 h]

theorem gram_row_10 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 10)) (W.pathVec (word28 j)) = gram28 τ 10 j := by
  fin_cases j
  exacts [gram_sym (gram_0_10 h), gram_sym (gram_1_10 h), gram_sym (gram_2_10 h), gram_sym (gram_3_10 h), gram_sym (gram_4_10 h), gram_sym (gram_5_10 h), gram_sym (gram_6_10 h), gram_sym (gram_7_10 h), gram_sym (gram_8_10 h), gram_sym (gram_9_10 h), gram_10_10 h, gram_10_11 h, gram_10_12 h, gram_10_13 h, gram_10_14 h, gram_10_15 h, gram_10_16 h, gram_10_17 h, gram_10_18 h, gram_10_19 h, gram_10_20 h, gram_10_21 h, gram_10_22 h, gram_10_23 h, gram_10_24 h, gram_10_25 h, gram_10_26 h, gram_10_27 h]

theorem gram_row_11 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 11)) (W.pathVec (word28 j)) = gram28 τ 11 j := by
  fin_cases j
  exacts [gram_sym (gram_0_11 h), gram_sym (gram_1_11 h), gram_sym (gram_2_11 h), gram_sym (gram_3_11 h), gram_sym (gram_4_11 h), gram_sym (gram_5_11 h), gram_sym (gram_6_11 h), gram_sym (gram_7_11 h), gram_sym (gram_8_11 h), gram_sym (gram_9_11 h), gram_sym (gram_10_11 h), gram_11_11 h, gram_11_12 h, gram_11_13 h, gram_11_14 h, gram_11_15 h, gram_11_16 h, gram_11_17 h, gram_11_18 h, gram_11_19 h, gram_11_20 h, gram_11_21 h, gram_11_22 h, gram_11_23 h, gram_11_24 h, gram_11_25 h, gram_11_26 h, gram_11_27 h]

theorem gram_row_12 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 12)) (W.pathVec (word28 j)) = gram28 τ 12 j := by
  fin_cases j
  exacts [gram_sym (gram_0_12 h), gram_sym (gram_1_12 h), gram_sym (gram_2_12 h), gram_sym (gram_3_12 h), gram_sym (gram_4_12 h), gram_sym (gram_5_12 h), gram_sym (gram_6_12 h), gram_sym (gram_7_12 h), gram_sym (gram_8_12 h), gram_sym (gram_9_12 h), gram_sym (gram_10_12 h), gram_sym (gram_11_12 h), gram_12_12 h, gram_12_13 h, gram_12_14 h, gram_12_15 h, gram_12_16 h, gram_12_17 h, gram_12_18 h, gram_12_19 h, gram_12_20 h, gram_12_21 h, gram_12_22 h, gram_12_23 h, gram_12_24 h, gram_12_25 h, gram_12_26 h, gram_12_27 h]

theorem gram_row_13 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 13)) (W.pathVec (word28 j)) = gram28 τ 13 j := by
  fin_cases j
  exacts [gram_sym (gram_0_13 h), gram_sym (gram_1_13 h), gram_sym (gram_2_13 h), gram_sym (gram_3_13 h), gram_sym (gram_4_13 h), gram_sym (gram_5_13 h), gram_sym (gram_6_13 h), gram_sym (gram_7_13 h), gram_sym (gram_8_13 h), gram_sym (gram_9_13 h), gram_sym (gram_10_13 h), gram_sym (gram_11_13 h), gram_sym (gram_12_13 h), gram_13_13 h, gram_13_14 h, gram_13_15 h, gram_13_16 h, gram_13_17 h, gram_13_18 h, gram_13_19 h, gram_13_20 h, gram_13_21 h, gram_13_22 h, gram_13_23 h, gram_13_24 h, gram_13_25 h, gram_13_26 h, gram_13_27 h]

theorem gram_row_14 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 j)) = gram28 τ 14 j := by
  fin_cases j
  exacts [gram_sym (gram_0_14 h), gram_sym (gram_1_14 h), gram_sym (gram_2_14 h), gram_sym (gram_3_14 h), gram_sym (gram_4_14 h), gram_sym (gram_5_14 h), gram_sym (gram_6_14 h), gram_sym (gram_7_14 h), gram_sym (gram_8_14 h), gram_sym (gram_9_14 h), gram_sym (gram_10_14 h), gram_sym (gram_11_14 h), gram_sym (gram_12_14 h), gram_sym (gram_13_14 h), gram_14_14 h, gram_14_15 h, gram_14_16 h, gram_14_17 h, gram_14_18 h, gram_14_19 h, gram_14_20 h, gram_14_21 h, gram_14_22 h, gram_14_23 h, gram_14_24 h, gram_14_25 h, gram_14_26 h, gram_14_27 h]

theorem gram_row_15 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 j)) = gram28 τ 15 j := by
  fin_cases j
  exacts [gram_sym (gram_0_15 h), gram_sym (gram_1_15 h), gram_sym (gram_2_15 h), gram_sym (gram_3_15 h), gram_sym (gram_4_15 h), gram_sym (gram_5_15 h), gram_sym (gram_6_15 h), gram_sym (gram_7_15 h), gram_sym (gram_8_15 h), gram_sym (gram_9_15 h), gram_sym (gram_10_15 h), gram_sym (gram_11_15 h), gram_sym (gram_12_15 h), gram_sym (gram_13_15 h), gram_sym (gram_14_15 h), gram_15_15 h, gram_15_16 h, gram_15_17 h, gram_15_18 h, gram_15_19 h, gram_15_20 h, gram_15_21 h, gram_15_22 h, gram_15_23 h, gram_15_24 h, gram_15_25 h, gram_15_26 h, gram_15_27 h]

theorem gram_row_16 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 j)) = gram28 τ 16 j := by
  fin_cases j
  exacts [gram_sym (gram_0_16 h), gram_sym (gram_1_16 h), gram_sym (gram_2_16 h), gram_sym (gram_3_16 h), gram_sym (gram_4_16 h), gram_sym (gram_5_16 h), gram_sym (gram_6_16 h), gram_sym (gram_7_16 h), gram_sym (gram_8_16 h), gram_sym (gram_9_16 h), gram_sym (gram_10_16 h), gram_sym (gram_11_16 h), gram_sym (gram_12_16 h), gram_sym (gram_13_16 h), gram_sym (gram_14_16 h), gram_sym (gram_15_16 h), gram_16_16 h, gram_16_17 h, gram_16_18 h, gram_16_19 h, gram_16_20 h, gram_16_21 h, gram_16_22 h, gram_16_23 h, gram_16_24 h, gram_16_25 h, gram_16_26 h, gram_16_27 h]

theorem gram_row_17 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 j)) = gram28 τ 17 j := by
  fin_cases j
  exacts [gram_sym (gram_0_17 h), gram_sym (gram_1_17 h), gram_sym (gram_2_17 h), gram_sym (gram_3_17 h), gram_sym (gram_4_17 h), gram_sym (gram_5_17 h), gram_sym (gram_6_17 h), gram_sym (gram_7_17 h), gram_sym (gram_8_17 h), gram_sym (gram_9_17 h), gram_sym (gram_10_17 h), gram_sym (gram_11_17 h), gram_sym (gram_12_17 h), gram_sym (gram_13_17 h), gram_sym (gram_14_17 h), gram_sym (gram_15_17 h), gram_sym (gram_16_17 h), gram_17_17 h, gram_17_18 h, gram_17_19 h, gram_17_20 h, gram_17_21 h, gram_17_22 h, gram_17_23 h, gram_17_24 h, gram_17_25 h, gram_17_26 h, gram_17_27 h]

theorem gram_row_18 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 j)) = gram28 τ 18 j := by
  fin_cases j
  exacts [gram_sym (gram_0_18 h), gram_sym (gram_1_18 h), gram_sym (gram_2_18 h), gram_sym (gram_3_18 h), gram_sym (gram_4_18 h), gram_sym (gram_5_18 h), gram_sym (gram_6_18 h), gram_sym (gram_7_18 h), gram_sym (gram_8_18 h), gram_sym (gram_9_18 h), gram_sym (gram_10_18 h), gram_sym (gram_11_18 h), gram_sym (gram_12_18 h), gram_sym (gram_13_18 h), gram_sym (gram_14_18 h), gram_sym (gram_15_18 h), gram_sym (gram_16_18 h), gram_sym (gram_17_18 h), gram_18_18 h, gram_18_19 h, gram_18_20 h, gram_18_21 h, gram_18_22 h, gram_18_23 h, gram_18_24 h, gram_18_25 h, gram_18_26 h, gram_18_27 h]

theorem gram_row_19 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 j)) = gram28 τ 19 j := by
  fin_cases j
  exacts [gram_sym (gram_0_19 h), gram_sym (gram_1_19 h), gram_sym (gram_2_19 h), gram_sym (gram_3_19 h), gram_sym (gram_4_19 h), gram_sym (gram_5_19 h), gram_sym (gram_6_19 h), gram_sym (gram_7_19 h), gram_sym (gram_8_19 h), gram_sym (gram_9_19 h), gram_sym (gram_10_19 h), gram_sym (gram_11_19 h), gram_sym (gram_12_19 h), gram_sym (gram_13_19 h), gram_sym (gram_14_19 h), gram_sym (gram_15_19 h), gram_sym (gram_16_19 h), gram_sym (gram_17_19 h), gram_sym (gram_18_19 h), gram_19_19 h, gram_19_20 h, gram_19_21 h, gram_19_22 h, gram_19_23 h, gram_19_24 h, gram_19_25 h, gram_19_26 h, gram_19_27 h]

theorem gram_row_20 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 j)) = gram28 τ 20 j := by
  fin_cases j
  exacts [gram_sym (gram_0_20 h), gram_sym (gram_1_20 h), gram_sym (gram_2_20 h), gram_sym (gram_3_20 h), gram_sym (gram_4_20 h), gram_sym (gram_5_20 h), gram_sym (gram_6_20 h), gram_sym (gram_7_20 h), gram_sym (gram_8_20 h), gram_sym (gram_9_20 h), gram_sym (gram_10_20 h), gram_sym (gram_11_20 h), gram_sym (gram_12_20 h), gram_sym (gram_13_20 h), gram_sym (gram_14_20 h), gram_sym (gram_15_20 h), gram_sym (gram_16_20 h), gram_sym (gram_17_20 h), gram_sym (gram_18_20 h), gram_sym (gram_19_20 h), gram_20_20 h, gram_20_21 h, gram_20_22 h, gram_20_23 h, gram_20_24 h, gram_20_25 h, gram_20_26 h, gram_20_27 h]

theorem gram_row_21 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 j)) = gram28 τ 21 j := by
  fin_cases j
  exacts [gram_sym (gram_0_21 h), gram_sym (gram_1_21 h), gram_sym (gram_2_21 h), gram_sym (gram_3_21 h), gram_sym (gram_4_21 h), gram_sym (gram_5_21 h), gram_sym (gram_6_21 h), gram_sym (gram_7_21 h), gram_sym (gram_8_21 h), gram_sym (gram_9_21 h), gram_sym (gram_10_21 h), gram_sym (gram_11_21 h), gram_sym (gram_12_21 h), gram_sym (gram_13_21 h), gram_sym (gram_14_21 h), gram_sym (gram_15_21 h), gram_sym (gram_16_21 h), gram_sym (gram_17_21 h), gram_sym (gram_18_21 h), gram_sym (gram_19_21 h), gram_sym (gram_20_21 h), gram_21_21 h, gram_21_22 h, gram_21_23 h, gram_21_24 h, gram_21_25 h, gram_21_26 h, gram_21_27 h]

theorem gram_row_22 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 j)) = gram28 τ 22 j := by
  fin_cases j
  exacts [gram_sym (gram_0_22 h), gram_sym (gram_1_22 h), gram_sym (gram_2_22 h), gram_sym (gram_3_22 h), gram_sym (gram_4_22 h), gram_sym (gram_5_22 h), gram_sym (gram_6_22 h), gram_sym (gram_7_22 h), gram_sym (gram_8_22 h), gram_sym (gram_9_22 h), gram_sym (gram_10_22 h), gram_sym (gram_11_22 h), gram_sym (gram_12_22 h), gram_sym (gram_13_22 h), gram_sym (gram_14_22 h), gram_sym (gram_15_22 h), gram_sym (gram_16_22 h), gram_sym (gram_17_22 h), gram_sym (gram_18_22 h), gram_sym (gram_19_22 h), gram_sym (gram_20_22 h), gram_sym (gram_21_22 h), gram_22_22 h, gram_22_23 h, gram_22_24 h, gram_22_25 h, gram_22_26 h, gram_22_27 h]

theorem gram_row_23 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 j)) = gram28 τ 23 j := by
  fin_cases j
  exacts [gram_sym (gram_0_23 h), gram_sym (gram_1_23 h), gram_sym (gram_2_23 h), gram_sym (gram_3_23 h), gram_sym (gram_4_23 h), gram_sym (gram_5_23 h), gram_sym (gram_6_23 h), gram_sym (gram_7_23 h), gram_sym (gram_8_23 h), gram_sym (gram_9_23 h), gram_sym (gram_10_23 h), gram_sym (gram_11_23 h), gram_sym (gram_12_23 h), gram_sym (gram_13_23 h), gram_sym (gram_14_23 h), gram_sym (gram_15_23 h), gram_sym (gram_16_23 h), gram_sym (gram_17_23 h), gram_sym (gram_18_23 h), gram_sym (gram_19_23 h), gram_sym (gram_20_23 h), gram_sym (gram_21_23 h), gram_sym (gram_22_23 h), gram_23_23 h, gram_23_24 h, gram_23_25 h, gram_23_26 h, gram_23_27 h]

theorem gram_row_24 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 24)) (W.pathVec (word28 j)) = gram28 τ 24 j := by
  fin_cases j
  exacts [gram_sym (gram_0_24 h), gram_sym (gram_1_24 h), gram_sym (gram_2_24 h), gram_sym (gram_3_24 h), gram_sym (gram_4_24 h), gram_sym (gram_5_24 h), gram_sym (gram_6_24 h), gram_sym (gram_7_24 h), gram_sym (gram_8_24 h), gram_sym (gram_9_24 h), gram_sym (gram_10_24 h), gram_sym (gram_11_24 h), gram_sym (gram_12_24 h), gram_sym (gram_13_24 h), gram_sym (gram_14_24 h), gram_sym (gram_15_24 h), gram_sym (gram_16_24 h), gram_sym (gram_17_24 h), gram_sym (gram_18_24 h), gram_sym (gram_19_24 h), gram_sym (gram_20_24 h), gram_sym (gram_21_24 h), gram_sym (gram_22_24 h), gram_sym (gram_23_24 h), gram_24_24 h, gram_24_25 h, gram_24_26 h, gram_24_27 h]

theorem gram_row_25 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 25)) (W.pathVec (word28 j)) = gram28 τ 25 j := by
  fin_cases j
  exacts [gram_sym (gram_0_25 h), gram_sym (gram_1_25 h), gram_sym (gram_2_25 h), gram_sym (gram_3_25 h), gram_sym (gram_4_25 h), gram_sym (gram_5_25 h), gram_sym (gram_6_25 h), gram_sym (gram_7_25 h), gram_sym (gram_8_25 h), gram_sym (gram_9_25 h), gram_sym (gram_10_25 h), gram_sym (gram_11_25 h), gram_sym (gram_12_25 h), gram_sym (gram_13_25 h), gram_sym (gram_14_25 h), gram_sym (gram_15_25 h), gram_sym (gram_16_25 h), gram_sym (gram_17_25 h), gram_sym (gram_18_25 h), gram_sym (gram_19_25 h), gram_sym (gram_20_25 h), gram_sym (gram_21_25 h), gram_sym (gram_22_25 h), gram_sym (gram_23_25 h), gram_sym (gram_24_25 h), gram_25_25 h, gram_25_26 h, gram_25_27 h]

theorem gram_row_26 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 26)) (W.pathVec (word28 j)) = gram28 τ 26 j := by
  fin_cases j
  exacts [gram_sym (gram_0_26 h), gram_sym (gram_1_26 h), gram_sym (gram_2_26 h), gram_sym (gram_3_26 h), gram_sym (gram_4_26 h), gram_sym (gram_5_26 h), gram_sym (gram_6_26 h), gram_sym (gram_7_26 h), gram_sym (gram_8_26 h), gram_sym (gram_9_26 h), gram_sym (gram_10_26 h), gram_sym (gram_11_26 h), gram_sym (gram_12_26 h), gram_sym (gram_13_26 h), gram_sym (gram_14_26 h), gram_sym (gram_15_26 h), gram_sym (gram_16_26 h), gram_sym (gram_17_26 h), gram_sym (gram_18_26 h), gram_sym (gram_19_26 h), gram_sym (gram_20_26 h), gram_sym (gram_21_26 h), gram_sym (gram_22_26 h), gram_sym (gram_23_26 h), gram_sym (gram_24_26 h), gram_sym (gram_25_26 h), gram_26_26 h, gram_26_27 h]

theorem gram_row_27 (h : UsedRules W τ) (j : Fin 28) :
    W.form (W.pathVec (word28 27)) (W.pathVec (word28 j)) = gram28 τ 27 j := by
  fin_cases j
  exacts [gram_sym (gram_0_27 h), gram_sym (gram_1_27 h), gram_sym (gram_2_27 h), gram_sym (gram_3_27 h), gram_sym (gram_4_27 h), gram_sym (gram_5_27 h), gram_sym (gram_6_27 h), gram_sym (gram_7_27 h), gram_sym (gram_8_27 h), gram_sym (gram_9_27 h), gram_sym (gram_10_27 h), gram_sym (gram_11_27 h), gram_sym (gram_12_27 h), gram_sym (gram_13_27 h), gram_sym (gram_14_27 h), gram_sym (gram_15_27 h), gram_sym (gram_16_27 h), gram_sym (gram_17_27 h), gram_sym (gram_18_27 h), gram_sym (gram_19_27 h), gram_sym (gram_20_27 h), gram_sym (gram_21_27 h), gram_sym (gram_22_27 h), gram_sym (gram_23_27 h), gram_sym (gram_24_27 h), gram_sym (gram_25_27 h), gram_sym (gram_26_27 h), gram_27_27 h]

/-- **Lemma A** (lem:cer:gram28), rule form: the used rule instances fix all Gram entries. -/
theorem lemmaA (h : UsedRules W τ) (i j : Fin 28) :
    W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j := by
  fin_cases i
  exacts [gram_row_0 h j, gram_row_1 h j, gram_row_2 h j, gram_row_3 h j, gram_row_4 h j, gram_row_5 h j, gram_row_6 h j, gram_row_7 h j, gram_row_8 h j, gram_row_9 h j, gram_row_10 h j, gram_row_11 h j, gram_row_12 h j, gram_row_13 h j, gram_row_14 h j, gram_row_15 h j, gram_row_16 h j, gram_row_17 h j, gram_row_18 h j, gram_row_19 h j, gram_row_20 h j, gram_row_21 h j, gram_row_22 h j, gram_row_23 h j, gram_row_24 h j, gram_row_25 h j, gram_row_26 h j, gram_row_27 h j]

/-- Lemma A from the interface rule package (no table, no word set). -/
theorem lemmaA_of_gram28Rules (h : Gram28Rules W τ) (i j : Fin 28) :
    W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  lemmaA (usedRules_of_gram28Rules h) i j

/-- The shape `Pending.LemmaAContract gram28` of the interface package. -/
theorem lemmaA_contract : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData), Gram28Rules W τ → ∀ i j : Fin 28,
      W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  fun _ _ _ _ _ h i j => lemmaA_of_gram28Rules h i j

/-- Lemma A from hypotheses (i)-(iii) of lem:cer:gram28 on a word set `S`. -/
theorem lemmaA_of_gram28Hyp {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hS : Gram28Hyp W τ S) (hrep : W.Reproduces S f) (hT : TableValues τ f) (i j : Fin 28) :
    W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  lemmaA_of_gram28Rules (WalkForm.Gram28Hyp.rules hS hrep hT) i j

/-- Lemma A, finite-route form: the forcing words of the used instances lie in `S`. -/
theorem lemmaA_on {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (hcov : ∀ x y z : Letter, IsOrderingBCD x y z → ∀ π ∈ usedInsts, π.Covered S x y z)
    (hB : Covers S (p3Words 1 2 3)) (hC : Covers S (p3Words 2 3 1)) (hD : Covers S (p3Words 3 2 1))
    (i j : Fin 28) :
    W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  lemmaA (usedRules_of_table hrep hT hcov hB hC hD) i j

/-! ## The two word sets -/

/-- Words from `p_A` of length at most six (from `e/3`: A-initial words of length at most seven). -/
def wordsE3 : Set (Word Letter) := {u | u.length ≤ 6}

instance : DecidablePred (· ∈ wordsE3) := fun u => inferInstanceAs (Decidable (u.length ≤ 6))

/-- Reflected letters of the five-test quadruple `(A, B, C, D) = (p0, p1, q3, q4)`. -/
def budgetRefl (c : Letter) : Bool := c == 2 || c == 3

/-- Number of maximal runs of reflected letters (outcomes ignored). -/
def budgetRuns : Bool → Word Letter → ℕ
  | _, [] => 0
  | prev, a :: u => (if budgetRefl a.1 && !prev then 1 else 0) + budgetRuns (budgetRefl a.1) u

/-- `ν(u) = 2·(runs of reflected letters) − [last letter reflected]`. -/
def budgetNu (u : Word Letter) : ℕ :=
  2 * budgetRuns false u - (match u.getLast? with | some a => if budgetRefl a.1 then 1 else 0 | none => 0)

/-- Five-test budget cost `|u| + ν(u)` of a word from `p_A`. -/
def budgetCost (u : Word Letter) : ℕ := u.length + budgetNu u

/-- The five-test budget word set `{u | |u| + ν(u) ≤ 10}`. -/
def wordsBudget : Set (Word Letter) := {u | budgetCost u ≤ 10}

instance : DecidablePred (· ∈ wordsBudget) := fun u => inferInstanceAs (Decidable (budgetCost u ≤ 10))

theorem cover_e3 : ∀ x y z : Letter, IsOrderingBCD x y z → ∀ π ∈ usedInsts, π.Covered wordsE3 x y z := by
  decide

theorem cover_budget : ∀ x y z : Letter, IsOrderingBCD x y z →
    ∀ π ∈ usedInsts, π.Covered wordsBudget x y z := by
  decide

theorem p3_e3 : Covers wordsE3 (p3Words 1 2 3) ∧ Covers wordsE3 (p3Words 2 3 1) ∧
    Covers wordsE3 (p3Words 3 2 1) := by decide

theorem p3_budget : Covers wordsBudget (p3Words 1 2 3) ∧ Covers wordsBudget (p3Words 2 3 1) ∧
    Covers wordsBudget (p3Words 3 2 1) := by decide

/-- Lemma A for the table on the words of length at most seven from `e/3` (read from `p_A`). -/
theorem lemmaA_e3 {f : Word Letter → ℝ} (hrep : W.Reproduces wordsE3 f) (hT : TableValues τ f)
    (i j : Fin 28) : W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  lemmaA_on hrep hT cover_e3 p3_e3.1 p3_e3.2.1 p3_e3.2.2 i j

/-- Lemma A for the table on the five-test budget words. -/
theorem lemmaA_budget {f : Word Letter → ℝ} (hrep : W.Reproduces wordsBudget f) (hT : TableValues τ f)
    (i j : Fin 28) : W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j :=
  lemmaA_on hrep hT cover_budget p3_budget.1 p3_budget.2.1 p3_budget.2.2 i j

end AlbertSequential.LengthSeven.LemmaA

#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA
#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA_of_gram28Rules
#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA_contract
#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA_of_gram28Hyp
#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA_e3
#print axioms AlbertSequential.LengthSeven.LemmaA.lemmaA_budget
