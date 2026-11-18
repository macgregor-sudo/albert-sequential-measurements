/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeBB
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames B, B): the entries

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

theorem tm_7_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 7 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp7, LemmaB.TableModel.qg_7_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 7 8 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_7_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 7 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_7_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 7 10 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_7_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 7 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_7_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 7 12 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 7 = [1] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_7_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 7 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_7_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 8 8 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp8, LemmaB.TableModel.qg_8_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 8 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_8_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 8 10 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_8_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 8 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_8_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 8 12 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_8_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 8 13 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_8_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 9 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp9, LemmaB.TableModel.qg_9_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 9 10 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_9_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 9 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_9_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 9 12 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_9_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 9 13 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_9_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 10 10 = LemmaA.TracePoly.eval τ [(1, [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp10, LemmaB.TableModel.qg_10_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 10 11 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_10_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 10 12 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_10_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 10 13 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_10_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 11 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp11, LemmaB.TableModel.qg_11_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 11 12 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_11_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 11 13 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_11_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 12 12 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp12, LemmaB.TableModel.qg_12_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 12 13 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_12_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 13 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp13, LemmaB.TableModel.qg_13_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
