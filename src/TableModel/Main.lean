/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.EntriesAA
public import TableModel.EntriesAB
public import TableModel.EntriesAC
public import TableModel.EntriesAD
public import TableModel.EntriesBB
public import TableModel.EntriesBC
public import TableModel.EntriesBD
public import TableModel.EntriesCC
public import TableModel.EntriesCD
public import TableModel.EntriesDD
public import LemmaB.Conclusion

/-! # Table-model identity (lem:cer:tablemodel), assembled

* `tableModel`: for every trace datum `τ` with `o_AB o_AC o_AD ≠ 0` (no trace relation, no `𝒜 > 0`)
  and every pair `i j : Fin 28`, Lemma A's table entry `gram28 τ i j` equals Lemma B's model value
  `𝒬(û(w_i), û(w_j))` at the comparison parameters `(toTraces τ).toParams`.
* `tableModel_lemmaB`: the same with Lemma B's own `word28` (`word28_bridge`).
* `hgram_of_gram`: Lemma A's conclusion (as a hypothesis on any bilinear form and 28 vectors) plus the
  identity gives Lemma B's hypothesis `hgram`.
* `hgram_of_usedRules`, `hgram_of_gram28Rules`: the same from Lemma A's theorems.
* `no_walkForm_of_gram28Rules` / `no_walkForm_of_usedRules`: no `WalkForm` satisfies the length-seven
  rules with trace data obeying the trace relation, `𝒜 > 0` and `0 < o_Ax < 1`.
-/

@[expose] public section

set_option linter.unusedVariables false

namespace AlbertSequential.LengthSeven.TableModel

open AlbertSequential AlbertSequential.LengthSeven

/-- Symmetric entries. -/
theorem tm_symm {τ : TraceData} {p : LemmaB.Params ℝ} {i j : Fin 28}
    (h : LemmaA.gram28 τ i j = LemmaB.Q p (LemmaB.uhat p (word28 i)) (LemmaB.uhat p (word28 j))) :
    LemmaA.gram28 τ j i = LemmaB.Q p (LemmaB.uhat p (word28 j)) (LemmaB.uhat p (word28 i)) := by
  rw [LemmaA.gram28_symm, LemmaB.Q_symm]; exact h

theorem row_0 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 0 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_0_0 τ hB hC hD, tm_0_1 τ hB hC hD, tm_0_2 τ hB hC hD, tm_0_3 τ hB hC hD, tm_0_4 τ hB hC hD, tm_0_5 τ hB hC hD, tm_0_6 τ hB hC hD, tm_0_7 τ hB hC hD, tm_0_8 τ hB hC hD, tm_0_9 τ hB hC hD, tm_0_10 τ hB hC hD, tm_0_11 τ hB hC hD, tm_0_12 τ hB hC hD, tm_0_13 τ hB hC hD, tm_0_14 τ hB hC hD, tm_0_15 τ hB hC hD, tm_0_16 τ hB hC hD, tm_0_17 τ hB hC hD, tm_0_18 τ hB hC hD, tm_0_19 τ hB hC hD, tm_0_20 τ hB hC hD, tm_0_21 τ hB hC hD, tm_0_22 τ hB hC hD, tm_0_23 τ hB hC hD, tm_0_24 τ hB hC hD, tm_0_25 τ hB hC hD, tm_0_26 τ hB hC hD, tm_0_27 τ hB hC hD]

theorem row_1 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 1 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_1 τ hB hC hD), tm_1_1 τ hB hC hD, tm_1_2 τ hB hC hD, tm_1_3 τ hB hC hD, tm_1_4 τ hB hC hD, tm_1_5 τ hB hC hD, tm_1_6 τ hB hC hD, tm_1_7 τ hB hC hD, tm_1_8 τ hB hC hD, tm_1_9 τ hB hC hD, tm_1_10 τ hB hC hD, tm_1_11 τ hB hC hD, tm_1_12 τ hB hC hD, tm_1_13 τ hB hC hD, tm_1_14 τ hB hC hD, tm_1_15 τ hB hC hD, tm_1_16 τ hB hC hD, tm_1_17 τ hB hC hD, tm_1_18 τ hB hC hD, tm_1_19 τ hB hC hD, tm_1_20 τ hB hC hD, tm_1_21 τ hB hC hD, tm_1_22 τ hB hC hD, tm_1_23 τ hB hC hD, tm_1_24 τ hB hC hD, tm_1_25 τ hB hC hD, tm_1_26 τ hB hC hD, tm_1_27 τ hB hC hD]

theorem row_2 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 2 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_2 τ hB hC hD), tm_symm (tm_1_2 τ hB hC hD), tm_2_2 τ hB hC hD, tm_2_3 τ hB hC hD, tm_2_4 τ hB hC hD, tm_2_5 τ hB hC hD, tm_2_6 τ hB hC hD, tm_2_7 τ hB hC hD, tm_2_8 τ hB hC hD, tm_2_9 τ hB hC hD, tm_2_10 τ hB hC hD, tm_2_11 τ hB hC hD, tm_2_12 τ hB hC hD, tm_2_13 τ hB hC hD, tm_2_14 τ hB hC hD, tm_2_15 τ hB hC hD, tm_2_16 τ hB hC hD, tm_2_17 τ hB hC hD, tm_2_18 τ hB hC hD, tm_2_19 τ hB hC hD, tm_2_20 τ hB hC hD, tm_2_21 τ hB hC hD, tm_2_22 τ hB hC hD, tm_2_23 τ hB hC hD, tm_2_24 τ hB hC hD, tm_2_25 τ hB hC hD, tm_2_26 τ hB hC hD, tm_2_27 τ hB hC hD]

theorem row_3 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 3 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_3 τ hB hC hD), tm_symm (tm_1_3 τ hB hC hD), tm_symm (tm_2_3 τ hB hC hD), tm_3_3 τ hB hC hD, tm_3_4 τ hB hC hD, tm_3_5 τ hB hC hD, tm_3_6 τ hB hC hD, tm_3_7 τ hB hC hD, tm_3_8 τ hB hC hD, tm_3_9 τ hB hC hD, tm_3_10 τ hB hC hD, tm_3_11 τ hB hC hD, tm_3_12 τ hB hC hD, tm_3_13 τ hB hC hD, tm_3_14 τ hB hC hD, tm_3_15 τ hB hC hD, tm_3_16 τ hB hC hD, tm_3_17 τ hB hC hD, tm_3_18 τ hB hC hD, tm_3_19 τ hB hC hD, tm_3_20 τ hB hC hD, tm_3_21 τ hB hC hD, tm_3_22 τ hB hC hD, tm_3_23 τ hB hC hD, tm_3_24 τ hB hC hD, tm_3_25 τ hB hC hD, tm_3_26 τ hB hC hD, tm_3_27 τ hB hC hD]

theorem row_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 4 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_4 τ hB hC hD), tm_symm (tm_1_4 τ hB hC hD), tm_symm (tm_2_4 τ hB hC hD), tm_symm (tm_3_4 τ hB hC hD), tm_4_4 τ hB hC hD, tm_4_5 τ hB hC hD, tm_4_6 τ hB hC hD, tm_4_7 τ hB hC hD, tm_4_8 τ hB hC hD, tm_4_9 τ hB hC hD, tm_4_10 τ hB hC hD, tm_4_11 τ hB hC hD, tm_4_12 τ hB hC hD, tm_4_13 τ hB hC hD, tm_4_14 τ hB hC hD, tm_4_15 τ hB hC hD, tm_4_16 τ hB hC hD, tm_4_17 τ hB hC hD, tm_4_18 τ hB hC hD, tm_4_19 τ hB hC hD, tm_4_20 τ hB hC hD, tm_4_21 τ hB hC hD, tm_4_22 τ hB hC hD, tm_4_23 τ hB hC hD, tm_4_24 τ hB hC hD, tm_4_25 τ hB hC hD, tm_4_26 τ hB hC hD, tm_4_27 τ hB hC hD]

theorem row_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 5 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_5 τ hB hC hD), tm_symm (tm_1_5 τ hB hC hD), tm_symm (tm_2_5 τ hB hC hD), tm_symm (tm_3_5 τ hB hC hD), tm_symm (tm_4_5 τ hB hC hD), tm_5_5 τ hB hC hD, tm_5_6 τ hB hC hD, tm_5_7 τ hB hC hD, tm_5_8 τ hB hC hD, tm_5_9 τ hB hC hD, tm_5_10 τ hB hC hD, tm_5_11 τ hB hC hD, tm_5_12 τ hB hC hD, tm_5_13 τ hB hC hD, tm_5_14 τ hB hC hD, tm_5_15 τ hB hC hD, tm_5_16 τ hB hC hD, tm_5_17 τ hB hC hD, tm_5_18 τ hB hC hD, tm_5_19 τ hB hC hD, tm_5_20 τ hB hC hD, tm_5_21 τ hB hC hD, tm_5_22 τ hB hC hD, tm_5_23 τ hB hC hD, tm_5_24 τ hB hC hD, tm_5_25 τ hB hC hD, tm_5_26 τ hB hC hD, tm_5_27 τ hB hC hD]

theorem row_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 6 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_6 τ hB hC hD), tm_symm (tm_1_6 τ hB hC hD), tm_symm (tm_2_6 τ hB hC hD), tm_symm (tm_3_6 τ hB hC hD), tm_symm (tm_4_6 τ hB hC hD), tm_symm (tm_5_6 τ hB hC hD), tm_6_6 τ hB hC hD, tm_6_7 τ hB hC hD, tm_6_8 τ hB hC hD, tm_6_9 τ hB hC hD, tm_6_10 τ hB hC hD, tm_6_11 τ hB hC hD, tm_6_12 τ hB hC hD, tm_6_13 τ hB hC hD, tm_6_14 τ hB hC hD, tm_6_15 τ hB hC hD, tm_6_16 τ hB hC hD, tm_6_17 τ hB hC hD, tm_6_18 τ hB hC hD, tm_6_19 τ hB hC hD, tm_6_20 τ hB hC hD, tm_6_21 τ hB hC hD, tm_6_22 τ hB hC hD, tm_6_23 τ hB hC hD, tm_6_24 τ hB hC hD, tm_6_25 τ hB hC hD, tm_6_26 τ hB hC hD, tm_6_27 τ hB hC hD]

theorem row_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 7 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_7 τ hB hC hD), tm_symm (tm_1_7 τ hB hC hD), tm_symm (tm_2_7 τ hB hC hD), tm_symm (tm_3_7 τ hB hC hD), tm_symm (tm_4_7 τ hB hC hD), tm_symm (tm_5_7 τ hB hC hD), tm_symm (tm_6_7 τ hB hC hD), tm_7_7 τ hB hC hD, tm_7_8 τ hB hC hD, tm_7_9 τ hB hC hD, tm_7_10 τ hB hC hD, tm_7_11 τ hB hC hD, tm_7_12 τ hB hC hD, tm_7_13 τ hB hC hD, tm_7_14 τ hB hC hD, tm_7_15 τ hB hC hD, tm_7_16 τ hB hC hD, tm_7_17 τ hB hC hD, tm_7_18 τ hB hC hD, tm_7_19 τ hB hC hD, tm_7_20 τ hB hC hD, tm_7_21 τ hB hC hD, tm_7_22 τ hB hC hD, tm_7_23 τ hB hC hD, tm_7_24 τ hB hC hD, tm_7_25 τ hB hC hD, tm_7_26 τ hB hC hD, tm_7_27 τ hB hC hD]

theorem row_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 8 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_8 τ hB hC hD), tm_symm (tm_1_8 τ hB hC hD), tm_symm (tm_2_8 τ hB hC hD), tm_symm (tm_3_8 τ hB hC hD), tm_symm (tm_4_8 τ hB hC hD), tm_symm (tm_5_8 τ hB hC hD), tm_symm (tm_6_8 τ hB hC hD), tm_symm (tm_7_8 τ hB hC hD), tm_8_8 τ hB hC hD, tm_8_9 τ hB hC hD, tm_8_10 τ hB hC hD, tm_8_11 τ hB hC hD, tm_8_12 τ hB hC hD, tm_8_13 τ hB hC hD, tm_8_14 τ hB hC hD, tm_8_15 τ hB hC hD, tm_8_16 τ hB hC hD, tm_8_17 τ hB hC hD, tm_8_18 τ hB hC hD, tm_8_19 τ hB hC hD, tm_8_20 τ hB hC hD, tm_8_21 τ hB hC hD, tm_8_22 τ hB hC hD, tm_8_23 τ hB hC hD, tm_8_24 τ hB hC hD, tm_8_25 τ hB hC hD, tm_8_26 τ hB hC hD, tm_8_27 τ hB hC hD]

theorem row_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 9 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_9 τ hB hC hD), tm_symm (tm_1_9 τ hB hC hD), tm_symm (tm_2_9 τ hB hC hD), tm_symm (tm_3_9 τ hB hC hD), tm_symm (tm_4_9 τ hB hC hD), tm_symm (tm_5_9 τ hB hC hD), tm_symm (tm_6_9 τ hB hC hD), tm_symm (tm_7_9 τ hB hC hD), tm_symm (tm_8_9 τ hB hC hD), tm_9_9 τ hB hC hD, tm_9_10 τ hB hC hD, tm_9_11 τ hB hC hD, tm_9_12 τ hB hC hD, tm_9_13 τ hB hC hD, tm_9_14 τ hB hC hD, tm_9_15 τ hB hC hD, tm_9_16 τ hB hC hD, tm_9_17 τ hB hC hD, tm_9_18 τ hB hC hD, tm_9_19 τ hB hC hD, tm_9_20 τ hB hC hD, tm_9_21 τ hB hC hD, tm_9_22 τ hB hC hD, tm_9_23 τ hB hC hD, tm_9_24 τ hB hC hD, tm_9_25 τ hB hC hD, tm_9_26 τ hB hC hD, tm_9_27 τ hB hC hD]

theorem row_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 10 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_10 τ hB hC hD), tm_symm (tm_1_10 τ hB hC hD), tm_symm (tm_2_10 τ hB hC hD), tm_symm (tm_3_10 τ hB hC hD), tm_symm (tm_4_10 τ hB hC hD), tm_symm (tm_5_10 τ hB hC hD), tm_symm (tm_6_10 τ hB hC hD), tm_symm (tm_7_10 τ hB hC hD), tm_symm (tm_8_10 τ hB hC hD), tm_symm (tm_9_10 τ hB hC hD), tm_10_10 τ hB hC hD, tm_10_11 τ hB hC hD, tm_10_12 τ hB hC hD, tm_10_13 τ hB hC hD, tm_10_14 τ hB hC hD, tm_10_15 τ hB hC hD, tm_10_16 τ hB hC hD, tm_10_17 τ hB hC hD, tm_10_18 τ hB hC hD, tm_10_19 τ hB hC hD, tm_10_20 τ hB hC hD, tm_10_21 τ hB hC hD, tm_10_22 τ hB hC hD, tm_10_23 τ hB hC hD, tm_10_24 τ hB hC hD, tm_10_25 τ hB hC hD, tm_10_26 τ hB hC hD, tm_10_27 τ hB hC hD]

theorem row_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 11 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_11 τ hB hC hD), tm_symm (tm_1_11 τ hB hC hD), tm_symm (tm_2_11 τ hB hC hD), tm_symm (tm_3_11 τ hB hC hD), tm_symm (tm_4_11 τ hB hC hD), tm_symm (tm_5_11 τ hB hC hD), tm_symm (tm_6_11 τ hB hC hD), tm_symm (tm_7_11 τ hB hC hD), tm_symm (tm_8_11 τ hB hC hD), tm_symm (tm_9_11 τ hB hC hD), tm_symm (tm_10_11 τ hB hC hD), tm_11_11 τ hB hC hD, tm_11_12 τ hB hC hD, tm_11_13 τ hB hC hD, tm_11_14 τ hB hC hD, tm_11_15 τ hB hC hD, tm_11_16 τ hB hC hD, tm_11_17 τ hB hC hD, tm_11_18 τ hB hC hD, tm_11_19 τ hB hC hD, tm_11_20 τ hB hC hD, tm_11_21 τ hB hC hD, tm_11_22 τ hB hC hD, tm_11_23 τ hB hC hD, tm_11_24 τ hB hC hD, tm_11_25 τ hB hC hD, tm_11_26 τ hB hC hD, tm_11_27 τ hB hC hD]

theorem row_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 12 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_12 τ hB hC hD), tm_symm (tm_1_12 τ hB hC hD), tm_symm (tm_2_12 τ hB hC hD), tm_symm (tm_3_12 τ hB hC hD), tm_symm (tm_4_12 τ hB hC hD), tm_symm (tm_5_12 τ hB hC hD), tm_symm (tm_6_12 τ hB hC hD), tm_symm (tm_7_12 τ hB hC hD), tm_symm (tm_8_12 τ hB hC hD), tm_symm (tm_9_12 τ hB hC hD), tm_symm (tm_10_12 τ hB hC hD), tm_symm (tm_11_12 τ hB hC hD), tm_12_12 τ hB hC hD, tm_12_13 τ hB hC hD, tm_12_14 τ hB hC hD, tm_12_15 τ hB hC hD, tm_12_16 τ hB hC hD, tm_12_17 τ hB hC hD, tm_12_18 τ hB hC hD, tm_12_19 τ hB hC hD, tm_12_20 τ hB hC hD, tm_12_21 τ hB hC hD, tm_12_22 τ hB hC hD, tm_12_23 τ hB hC hD, tm_12_24 τ hB hC hD, tm_12_25 τ hB hC hD, tm_12_26 τ hB hC hD, tm_12_27 τ hB hC hD]

theorem row_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 13 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_13 τ hB hC hD), tm_symm (tm_1_13 τ hB hC hD), tm_symm (tm_2_13 τ hB hC hD), tm_symm (tm_3_13 τ hB hC hD), tm_symm (tm_4_13 τ hB hC hD), tm_symm (tm_5_13 τ hB hC hD), tm_symm (tm_6_13 τ hB hC hD), tm_symm (tm_7_13 τ hB hC hD), tm_symm (tm_8_13 τ hB hC hD), tm_symm (tm_9_13 τ hB hC hD), tm_symm (tm_10_13 τ hB hC hD), tm_symm (tm_11_13 τ hB hC hD), tm_symm (tm_12_13 τ hB hC hD), tm_13_13 τ hB hC hD, tm_13_14 τ hB hC hD, tm_13_15 τ hB hC hD, tm_13_16 τ hB hC hD, tm_13_17 τ hB hC hD, tm_13_18 τ hB hC hD, tm_13_19 τ hB hC hD, tm_13_20 τ hB hC hD, tm_13_21 τ hB hC hD, tm_13_22 τ hB hC hD, tm_13_23 τ hB hC hD, tm_13_24 τ hB hC hD, tm_13_25 τ hB hC hD, tm_13_26 τ hB hC hD, tm_13_27 τ hB hC hD]

theorem row_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 14 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_14 τ hB hC hD), tm_symm (tm_1_14 τ hB hC hD), tm_symm (tm_2_14 τ hB hC hD), tm_symm (tm_3_14 τ hB hC hD), tm_symm (tm_4_14 τ hB hC hD), tm_symm (tm_5_14 τ hB hC hD), tm_symm (tm_6_14 τ hB hC hD), tm_symm (tm_7_14 τ hB hC hD), tm_symm (tm_8_14 τ hB hC hD), tm_symm (tm_9_14 τ hB hC hD), tm_symm (tm_10_14 τ hB hC hD), tm_symm (tm_11_14 τ hB hC hD), tm_symm (tm_12_14 τ hB hC hD), tm_symm (tm_13_14 τ hB hC hD), tm_14_14 τ hB hC hD, tm_14_15 τ hB hC hD, tm_14_16 τ hB hC hD, tm_14_17 τ hB hC hD, tm_14_18 τ hB hC hD, tm_14_19 τ hB hC hD, tm_14_20 τ hB hC hD, tm_14_21 τ hB hC hD, tm_14_22 τ hB hC hD, tm_14_23 τ hB hC hD, tm_14_24 τ hB hC hD, tm_14_25 τ hB hC hD, tm_14_26 τ hB hC hD, tm_14_27 τ hB hC hD]

theorem row_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 15 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_15 τ hB hC hD), tm_symm (tm_1_15 τ hB hC hD), tm_symm (tm_2_15 τ hB hC hD), tm_symm (tm_3_15 τ hB hC hD), tm_symm (tm_4_15 τ hB hC hD), tm_symm (tm_5_15 τ hB hC hD), tm_symm (tm_6_15 τ hB hC hD), tm_symm (tm_7_15 τ hB hC hD), tm_symm (tm_8_15 τ hB hC hD), tm_symm (tm_9_15 τ hB hC hD), tm_symm (tm_10_15 τ hB hC hD), tm_symm (tm_11_15 τ hB hC hD), tm_symm (tm_12_15 τ hB hC hD), tm_symm (tm_13_15 τ hB hC hD), tm_symm (tm_14_15 τ hB hC hD), tm_15_15 τ hB hC hD, tm_15_16 τ hB hC hD, tm_15_17 τ hB hC hD, tm_15_18 τ hB hC hD, tm_15_19 τ hB hC hD, tm_15_20 τ hB hC hD, tm_15_21 τ hB hC hD, tm_15_22 τ hB hC hD, tm_15_23 τ hB hC hD, tm_15_24 τ hB hC hD, tm_15_25 τ hB hC hD, tm_15_26 τ hB hC hD, tm_15_27 τ hB hC hD]

theorem row_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 16 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_16 τ hB hC hD), tm_symm (tm_1_16 τ hB hC hD), tm_symm (tm_2_16 τ hB hC hD), tm_symm (tm_3_16 τ hB hC hD), tm_symm (tm_4_16 τ hB hC hD), tm_symm (tm_5_16 τ hB hC hD), tm_symm (tm_6_16 τ hB hC hD), tm_symm (tm_7_16 τ hB hC hD), tm_symm (tm_8_16 τ hB hC hD), tm_symm (tm_9_16 τ hB hC hD), tm_symm (tm_10_16 τ hB hC hD), tm_symm (tm_11_16 τ hB hC hD), tm_symm (tm_12_16 τ hB hC hD), tm_symm (tm_13_16 τ hB hC hD), tm_symm (tm_14_16 τ hB hC hD), tm_symm (tm_15_16 τ hB hC hD), tm_16_16 τ hB hC hD, tm_16_17 τ hB hC hD, tm_16_18 τ hB hC hD, tm_16_19 τ hB hC hD, tm_16_20 τ hB hC hD, tm_16_21 τ hB hC hD, tm_16_22 τ hB hC hD, tm_16_23 τ hB hC hD, tm_16_24 τ hB hC hD, tm_16_25 τ hB hC hD, tm_16_26 τ hB hC hD, tm_16_27 τ hB hC hD]

theorem row_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 17 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_17 τ hB hC hD), tm_symm (tm_1_17 τ hB hC hD), tm_symm (tm_2_17 τ hB hC hD), tm_symm (tm_3_17 τ hB hC hD), tm_symm (tm_4_17 τ hB hC hD), tm_symm (tm_5_17 τ hB hC hD), tm_symm (tm_6_17 τ hB hC hD), tm_symm (tm_7_17 τ hB hC hD), tm_symm (tm_8_17 τ hB hC hD), tm_symm (tm_9_17 τ hB hC hD), tm_symm (tm_10_17 τ hB hC hD), tm_symm (tm_11_17 τ hB hC hD), tm_symm (tm_12_17 τ hB hC hD), tm_symm (tm_13_17 τ hB hC hD), tm_symm (tm_14_17 τ hB hC hD), tm_symm (tm_15_17 τ hB hC hD), tm_symm (tm_16_17 τ hB hC hD), tm_17_17 τ hB hC hD, tm_17_18 τ hB hC hD, tm_17_19 τ hB hC hD, tm_17_20 τ hB hC hD, tm_17_21 τ hB hC hD, tm_17_22 τ hB hC hD, tm_17_23 τ hB hC hD, tm_17_24 τ hB hC hD, tm_17_25 τ hB hC hD, tm_17_26 τ hB hC hD, tm_17_27 τ hB hC hD]

theorem row_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 18 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_18 τ hB hC hD), tm_symm (tm_1_18 τ hB hC hD), tm_symm (tm_2_18 τ hB hC hD), tm_symm (tm_3_18 τ hB hC hD), tm_symm (tm_4_18 τ hB hC hD), tm_symm (tm_5_18 τ hB hC hD), tm_symm (tm_6_18 τ hB hC hD), tm_symm (tm_7_18 τ hB hC hD), tm_symm (tm_8_18 τ hB hC hD), tm_symm (tm_9_18 τ hB hC hD), tm_symm (tm_10_18 τ hB hC hD), tm_symm (tm_11_18 τ hB hC hD), tm_symm (tm_12_18 τ hB hC hD), tm_symm (tm_13_18 τ hB hC hD), tm_symm (tm_14_18 τ hB hC hD), tm_symm (tm_15_18 τ hB hC hD), tm_symm (tm_16_18 τ hB hC hD), tm_symm (tm_17_18 τ hB hC hD), tm_18_18 τ hB hC hD, tm_18_19 τ hB hC hD, tm_18_20 τ hB hC hD, tm_18_21 τ hB hC hD, tm_18_22 τ hB hC hD, tm_18_23 τ hB hC hD, tm_18_24 τ hB hC hD, tm_18_25 τ hB hC hD, tm_18_26 τ hB hC hD, tm_18_27 τ hB hC hD]

theorem row_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 19 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_19 τ hB hC hD), tm_symm (tm_1_19 τ hB hC hD), tm_symm (tm_2_19 τ hB hC hD), tm_symm (tm_3_19 τ hB hC hD), tm_symm (tm_4_19 τ hB hC hD), tm_symm (tm_5_19 τ hB hC hD), tm_symm (tm_6_19 τ hB hC hD), tm_symm (tm_7_19 τ hB hC hD), tm_symm (tm_8_19 τ hB hC hD), tm_symm (tm_9_19 τ hB hC hD), tm_symm (tm_10_19 τ hB hC hD), tm_symm (tm_11_19 τ hB hC hD), tm_symm (tm_12_19 τ hB hC hD), tm_symm (tm_13_19 τ hB hC hD), tm_symm (tm_14_19 τ hB hC hD), tm_symm (tm_15_19 τ hB hC hD), tm_symm (tm_16_19 τ hB hC hD), tm_symm (tm_17_19 τ hB hC hD), tm_symm (tm_18_19 τ hB hC hD), tm_19_19 τ hB hC hD, tm_19_20 τ hB hC hD, tm_19_21 τ hB hC hD, tm_19_22 τ hB hC hD, tm_19_23 τ hB hC hD, tm_19_24 τ hB hC hD, tm_19_25 τ hB hC hD, tm_19_26 τ hB hC hD, tm_19_27 τ hB hC hD]

theorem row_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 20 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_20 τ hB hC hD), tm_symm (tm_1_20 τ hB hC hD), tm_symm (tm_2_20 τ hB hC hD), tm_symm (tm_3_20 τ hB hC hD), tm_symm (tm_4_20 τ hB hC hD), tm_symm (tm_5_20 τ hB hC hD), tm_symm (tm_6_20 τ hB hC hD), tm_symm (tm_7_20 τ hB hC hD), tm_symm (tm_8_20 τ hB hC hD), tm_symm (tm_9_20 τ hB hC hD), tm_symm (tm_10_20 τ hB hC hD), tm_symm (tm_11_20 τ hB hC hD), tm_symm (tm_12_20 τ hB hC hD), tm_symm (tm_13_20 τ hB hC hD), tm_symm (tm_14_20 τ hB hC hD), tm_symm (tm_15_20 τ hB hC hD), tm_symm (tm_16_20 τ hB hC hD), tm_symm (tm_17_20 τ hB hC hD), tm_symm (tm_18_20 τ hB hC hD), tm_symm (tm_19_20 τ hB hC hD), tm_20_20 τ hB hC hD, tm_20_21 τ hB hC hD, tm_20_22 τ hB hC hD, tm_20_23 τ hB hC hD, tm_20_24 τ hB hC hD, tm_20_25 τ hB hC hD, tm_20_26 τ hB hC hD, tm_20_27 τ hB hC hD]

theorem row_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 21 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_21 τ hB hC hD), tm_symm (tm_1_21 τ hB hC hD), tm_symm (tm_2_21 τ hB hC hD), tm_symm (tm_3_21 τ hB hC hD), tm_symm (tm_4_21 τ hB hC hD), tm_symm (tm_5_21 τ hB hC hD), tm_symm (tm_6_21 τ hB hC hD), tm_symm (tm_7_21 τ hB hC hD), tm_symm (tm_8_21 τ hB hC hD), tm_symm (tm_9_21 τ hB hC hD), tm_symm (tm_10_21 τ hB hC hD), tm_symm (tm_11_21 τ hB hC hD), tm_symm (tm_12_21 τ hB hC hD), tm_symm (tm_13_21 τ hB hC hD), tm_symm (tm_14_21 τ hB hC hD), tm_symm (tm_15_21 τ hB hC hD), tm_symm (tm_16_21 τ hB hC hD), tm_symm (tm_17_21 τ hB hC hD), tm_symm (tm_18_21 τ hB hC hD), tm_symm (tm_19_21 τ hB hC hD), tm_symm (tm_20_21 τ hB hC hD), tm_21_21 τ hB hC hD, tm_21_22 τ hB hC hD, tm_21_23 τ hB hC hD, tm_21_24 τ hB hC hD, tm_21_25 τ hB hC hD, tm_21_26 τ hB hC hD, tm_21_27 τ hB hC hD]

theorem row_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 22 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_22 τ hB hC hD), tm_symm (tm_1_22 τ hB hC hD), tm_symm (tm_2_22 τ hB hC hD), tm_symm (tm_3_22 τ hB hC hD), tm_symm (tm_4_22 τ hB hC hD), tm_symm (tm_5_22 τ hB hC hD), tm_symm (tm_6_22 τ hB hC hD), tm_symm (tm_7_22 τ hB hC hD), tm_symm (tm_8_22 τ hB hC hD), tm_symm (tm_9_22 τ hB hC hD), tm_symm (tm_10_22 τ hB hC hD), tm_symm (tm_11_22 τ hB hC hD), tm_symm (tm_12_22 τ hB hC hD), tm_symm (tm_13_22 τ hB hC hD), tm_symm (tm_14_22 τ hB hC hD), tm_symm (tm_15_22 τ hB hC hD), tm_symm (tm_16_22 τ hB hC hD), tm_symm (tm_17_22 τ hB hC hD), tm_symm (tm_18_22 τ hB hC hD), tm_symm (tm_19_22 τ hB hC hD), tm_symm (tm_20_22 τ hB hC hD), tm_symm (tm_21_22 τ hB hC hD), tm_22_22 τ hB hC hD, tm_22_23 τ hB hC hD, tm_22_24 τ hB hC hD, tm_22_25 τ hB hC hD, tm_22_26 τ hB hC hD, tm_22_27 τ hB hC hD]

theorem row_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 23 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_23 τ hB hC hD), tm_symm (tm_1_23 τ hB hC hD), tm_symm (tm_2_23 τ hB hC hD), tm_symm (tm_3_23 τ hB hC hD), tm_symm (tm_4_23 τ hB hC hD), tm_symm (tm_5_23 τ hB hC hD), tm_symm (tm_6_23 τ hB hC hD), tm_symm (tm_7_23 τ hB hC hD), tm_symm (tm_8_23 τ hB hC hD), tm_symm (tm_9_23 τ hB hC hD), tm_symm (tm_10_23 τ hB hC hD), tm_symm (tm_11_23 τ hB hC hD), tm_symm (tm_12_23 τ hB hC hD), tm_symm (tm_13_23 τ hB hC hD), tm_symm (tm_14_23 τ hB hC hD), tm_symm (tm_15_23 τ hB hC hD), tm_symm (tm_16_23 τ hB hC hD), tm_symm (tm_17_23 τ hB hC hD), tm_symm (tm_18_23 τ hB hC hD), tm_symm (tm_19_23 τ hB hC hD), tm_symm (tm_20_23 τ hB hC hD), tm_symm (tm_21_23 τ hB hC hD), tm_symm (tm_22_23 τ hB hC hD), tm_23_23 τ hB hC hD, tm_23_24 τ hB hC hD, tm_23_25 τ hB hC hD, tm_23_26 τ hB hC hD, tm_23_27 τ hB hC hD]

theorem row_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 24 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 24)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_24 τ hB hC hD), tm_symm (tm_1_24 τ hB hC hD), tm_symm (tm_2_24 τ hB hC hD), tm_symm (tm_3_24 τ hB hC hD), tm_symm (tm_4_24 τ hB hC hD), tm_symm (tm_5_24 τ hB hC hD), tm_symm (tm_6_24 τ hB hC hD), tm_symm (tm_7_24 τ hB hC hD), tm_symm (tm_8_24 τ hB hC hD), tm_symm (tm_9_24 τ hB hC hD), tm_symm (tm_10_24 τ hB hC hD), tm_symm (tm_11_24 τ hB hC hD), tm_symm (tm_12_24 τ hB hC hD), tm_symm (tm_13_24 τ hB hC hD), tm_symm (tm_14_24 τ hB hC hD), tm_symm (tm_15_24 τ hB hC hD), tm_symm (tm_16_24 τ hB hC hD), tm_symm (tm_17_24 τ hB hC hD), tm_symm (tm_18_24 τ hB hC hD), tm_symm (tm_19_24 τ hB hC hD), tm_symm (tm_20_24 τ hB hC hD), tm_symm (tm_21_24 τ hB hC hD), tm_symm (tm_22_24 τ hB hC hD), tm_symm (tm_23_24 τ hB hC hD), tm_24_24 τ hB hC hD, tm_24_25 τ hB hC hD, tm_24_26 τ hB hC hD, tm_24_27 τ hB hC hD]

theorem row_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 25 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 25)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_25 τ hB hC hD), tm_symm (tm_1_25 τ hB hC hD), tm_symm (tm_2_25 τ hB hC hD), tm_symm (tm_3_25 τ hB hC hD), tm_symm (tm_4_25 τ hB hC hD), tm_symm (tm_5_25 τ hB hC hD), tm_symm (tm_6_25 τ hB hC hD), tm_symm (tm_7_25 τ hB hC hD), tm_symm (tm_8_25 τ hB hC hD), tm_symm (tm_9_25 τ hB hC hD), tm_symm (tm_10_25 τ hB hC hD), tm_symm (tm_11_25 τ hB hC hD), tm_symm (tm_12_25 τ hB hC hD), tm_symm (tm_13_25 τ hB hC hD), tm_symm (tm_14_25 τ hB hC hD), tm_symm (tm_15_25 τ hB hC hD), tm_symm (tm_16_25 τ hB hC hD), tm_symm (tm_17_25 τ hB hC hD), tm_symm (tm_18_25 τ hB hC hD), tm_symm (tm_19_25 τ hB hC hD), tm_symm (tm_20_25 τ hB hC hD), tm_symm (tm_21_25 τ hB hC hD), tm_symm (tm_22_25 τ hB hC hD), tm_symm (tm_23_25 τ hB hC hD), tm_symm (tm_24_25 τ hB hC hD), tm_25_25 τ hB hC hD, tm_25_26 τ hB hC hD, tm_25_27 τ hB hC hD]

theorem row_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 26 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 26)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_26 τ hB hC hD), tm_symm (tm_1_26 τ hB hC hD), tm_symm (tm_2_26 τ hB hC hD), tm_symm (tm_3_26 τ hB hC hD), tm_symm (tm_4_26 τ hB hC hD), tm_symm (tm_5_26 τ hB hC hD), tm_symm (tm_6_26 τ hB hC hD), tm_symm (tm_7_26 τ hB hC hD), tm_symm (tm_8_26 τ hB hC hD), tm_symm (tm_9_26 τ hB hC hD), tm_symm (tm_10_26 τ hB hC hD), tm_symm (tm_11_26 τ hB hC hD), tm_symm (tm_12_26 τ hB hC hD), tm_symm (tm_13_26 τ hB hC hD), tm_symm (tm_14_26 τ hB hC hD), tm_symm (tm_15_26 τ hB hC hD), tm_symm (tm_16_26 τ hB hC hD), tm_symm (tm_17_26 τ hB hC hD), tm_symm (tm_18_26 τ hB hC hD), tm_symm (tm_19_26 τ hB hC hD), tm_symm (tm_20_26 τ hB hC hD), tm_symm (tm_21_26 τ hB hC hD), tm_symm (tm_22_26 τ hB hC hD), tm_symm (tm_23_26 τ hB hC hD), tm_symm (tm_24_26 τ hB hC hD), tm_symm (tm_25_26 τ hB hC hD), tm_26_26 τ hB hC hD, tm_26_27 τ hB hC hD]

theorem row_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (j : Fin 28) : LemmaA.gram28 τ 27 j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 27)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases j
  exacts [tm_symm (tm_0_27 τ hB hC hD), tm_symm (tm_1_27 τ hB hC hD), tm_symm (tm_2_27 τ hB hC hD), tm_symm (tm_3_27 τ hB hC hD), tm_symm (tm_4_27 τ hB hC hD), tm_symm (tm_5_27 τ hB hC hD), tm_symm (tm_6_27 τ hB hC hD), tm_symm (tm_7_27 τ hB hC hD), tm_symm (tm_8_27 τ hB hC hD), tm_symm (tm_9_27 τ hB hC hD), tm_symm (tm_10_27 τ hB hC hD), tm_symm (tm_11_27 τ hB hC hD), tm_symm (tm_12_27 τ hB hC hD), tm_symm (tm_13_27 τ hB hC hD), tm_symm (tm_14_27 τ hB hC hD), tm_symm (tm_15_27 τ hB hC hD), tm_symm (tm_16_27 τ hB hC hD), tm_symm (tm_17_27 τ hB hC hD), tm_symm (tm_18_27 τ hB hC hD), tm_symm (tm_19_27 τ hB hC hD), tm_symm (tm_20_27 τ hB hC hD), tm_symm (tm_21_27 τ hB hC hD), tm_symm (tm_22_27 τ hB hC hD), tm_symm (tm_23_27 τ hB hC hD), tm_symm (tm_24_27 τ hB hC hD), tm_symm (tm_25_27 τ hB hC hD), tm_symm (tm_26_27 τ hB hC hD), tm_27_27 τ hB hC hD]

/-- **lem:cer:tablemodel** (broader form: no trace relation, no `𝒜 > 0`). For every trace datum
with `o_AB o_AC o_AD ≠ 0`, every entry of Lemma A's table is the model value of the two path
vectors at the comparison parameters of the traces. -/
theorem tableModel (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (i j : Fin 28) : LemmaA.gram28 τ i j = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 i)) (LemmaB.uhat (toTraces τ).toParams (word28 j)) := by
  fin_cases i
  exacts [row_0 τ hB hC hD j, row_1 τ hB hC hD j, row_2 τ hB hC hD j, row_3 τ hB hC hD j, row_4 τ hB hC hD j, row_5 τ hB hC hD j, row_6 τ hB hC hD j, row_7 τ hB hC hD j, row_8 τ hB hC hD j, row_9 τ hB hC hD j, row_10 τ hB hC hD j, row_11 τ hB hC hD j, row_12 τ hB hC hD j, row_13 τ hB hC hD j, row_14 τ hB hC hD j, row_15 τ hB hC hD j, row_16 τ hB hC hD j, row_17 τ hB hC hD j, row_18 τ hB hC hD j, row_19 τ hB hC hD j, row_20 τ hB hC hD j, row_21 τ hB hC hD j, row_22 τ hB hC hD j, row_23 τ hB hC hD j, row_24 τ hB hC hD j, row_25 τ hB hC hD j, row_26 τ hB hC hD j, row_27 τ hB hC hD j]

/-- The identity with Lemma B's word list. -/
theorem tableModel_lemmaB (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (k l : Fin 28) : LemmaA.gram28 τ k l = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 k))
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 l)) := by
  rw [word28_bridge, word28_bridge]; exact tableModel τ hB hC hD k l

/-- Lemma A's conclusion (as a hypothesis) plus the table-model identity give Lemma B's `hgram`. -/
theorem hgram_of_gram {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (pv : Fin 28 → E) (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (hA : ∀ k l, B (pv k) (pv l) = LemmaA.gram28 τ k l) :
    ∀ k l, B (pv k) (pv l) = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 k))
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 l)) := fun k l => by
  rw [hA, tableModel_lemmaB τ hB hC hD]

/-- Lemma A (`UsedRules`) composed with the identity: Lemma B's `hgram` for the path vectors. -/
theorem hgram_of_usedRules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (h : LemmaA.UsedRules W τ)
    (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    ∀ k l, W.form (W.pathVec (word28 k)) (W.pathVec (word28 l)) = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 k))
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 l)) :=
  hgram_of_gram W.form (fun k => W.pathVec (word28 k)) τ hB hC hD (LemmaA.lemmaA h)

/-- Lemma A (`Gram28Rules`) composed with the identity. -/
theorem hgram_of_gram28Rules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (h : Gram28Rules W τ)
    (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    ∀ k l, W.form (W.pathVec (word28 k)) (W.pathVec (word28 l)) = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 k))
      (LemmaB.uhat (toTraces τ).toParams (LemmaB.word28 l)) :=
  hgram_of_usedRules W τ (LemmaA.usedRules_of_gram28Rules h) hB hC hD

/-- **Assembled**: no `WalkForm` satisfies Lemma A's rule package for trace data that obey the trace
relation, have `𝒜 > 0` and `0 < o_Ax < 1` (`x = B, C, D`). Trace relation and `𝒜` are Lemma B's,
read through `toTraces` (`t_1 = (ω_C+ω_D)/2` etc., so Lemma B's `ω_r` is `τ.om r`). -/
theorem no_walkForm_of_usedRules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (h : LemmaA.UsedRules W τ)
    (hTR : (toTraces τ).TraceRelation) (hA : 0 < (toTraces τ).Acal)
    (hB0 : 0 < τ.o 0 1) (hB1 : τ.o 0 1 < 1) (hC0 : 0 < τ.o 0 2) (hC1 : τ.o 0 2 < 1)
    (hD0 : 0 < τ.o 0 3) (hD1 : τ.o 0 3 < 1) : False :=
  LemmaB.no_psd_realisation_traces (toTraces τ) hTR hA hB0 hB1 hC0 hC1 hD0 hD1 W.form W.symm W.psd
    (fun k => W.pathVec (word28 k)) (hgram_of_usedRules W τ h hB0.ne' hC0.ne' hD0.ne')

theorem no_walkForm_of_gram28Rules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (h : Gram28Rules W τ)
    (hTR : (toTraces τ).TraceRelation) (hA : 0 < (toTraces τ).Acal)
    (hB0 : 0 < τ.o 0 1) (hB1 : τ.o 0 1 < 1) (hC0 : 0 < τ.o 0 2) (hC1 : τ.o 0 2 < 1)
    (hD0 : 0 < τ.o 0 3) (hD1 : τ.o 0 3 < 1) : False :=
  no_walkForm_of_usedRules W τ (LemmaA.usedRules_of_gram28Rules h) hTR hA hB0 hB1 hC0 hC1 hD0 hD1

end AlbertSequential.LengthSeven.TableModel
