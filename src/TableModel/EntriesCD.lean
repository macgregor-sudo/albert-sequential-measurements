/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeCD
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames C, D): the entries

`tm_i_j`: Lemma A's table entry `gram28 τ i j` equals Lemma B's model value
`𝒬(û(w_i), û(w_j))` at the parameters of the traces, for `o_AB o_AC o_AD ≠ 0`. -/

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AlbertSequential.LengthSeven.TableModel

open AlbertSequential AlbertSequential.LengthSeven

theorem tm_14_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 14 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_14_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 14 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 14 = [2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_14_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 14 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_14_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 14 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_14_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 14 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_14_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 14 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_14_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 14 27 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_14_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 15 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_15_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 15 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_15_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 15 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_15_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 15 24 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_15_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 15 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_15_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 15 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_15_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 15 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_15_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 16 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_16_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 16 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_16_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 16 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_16_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 16 24 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_16_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 16 25 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_16_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 16 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_16_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 16 27 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_16_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 17 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_17_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 17 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_17_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 17 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_17_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 17 24 = LemmaA.TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]), (-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_17_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 17 25 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_17_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 17 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_17_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 17 27 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_17_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 18 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_18_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 18 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_18_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 18 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_18_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 18 24 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_18_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 18 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_18_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 18 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_18_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 18 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_18_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 19 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_19_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 19 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_19_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 19 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_19_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 19 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_19_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 19 25 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_19_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 19 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_19_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 19 27 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (-1, [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_19_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 20 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_20_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 20 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_20_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 20 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_20_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 20 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_20_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 20 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_20_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 20 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_20_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 20 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp20, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_20_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
