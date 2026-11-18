/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeBD
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames B, D): the entries

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

theorem tm_7_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 7 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_7_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 7 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_7_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 7 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 7 = [1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_7_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 7 24 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_7_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 7 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_7_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 7 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_7_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 7 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_7_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 8 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_8_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 8 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_8_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 8 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_8_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 8 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_8_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 8 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_8_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 8 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_8_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 8 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_8_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 9 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_9_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 9 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_9_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 9 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_9_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 9 24 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_9_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 9 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_9_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 9 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_9_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 9 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_9_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 10 21 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_10_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 10 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_10_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 10 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_10_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 10 24 = LemmaA.TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]), (-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_10_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 10 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_10_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 10 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_10_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 10 27 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_10_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 11 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_11_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 11 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_11_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 11 23 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_11_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 11 24 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_11_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 11 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_11_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 11 26 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_11_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 11 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_11_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 12 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_12_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 12 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_12_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 12 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_12_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 12 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_12_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 12 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_12_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 12 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_12_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 12 27 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_12_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 13 21 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_13_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 13 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_13_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 13 23 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_13_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 13 24 = LemmaA.TracePoly.eval τ [(-1, [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_13_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 13 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_13_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 13 26 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (-1, [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_13_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 13 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_13_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
