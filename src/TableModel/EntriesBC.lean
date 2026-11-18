/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeBC
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames B, C): the entries

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

theorem tm_7_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 7 14 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_7_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 7 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_7_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 7 16 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_7_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 7 17 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_7_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 7 18 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_7_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 7 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 7 = [1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_7_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_7_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 7 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 7)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 7 20 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 7 = [1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame7, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp7, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_7_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_7_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 8 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_8_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 8 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_8_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 8 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_8_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 8 17 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_8_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 8 18 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_8_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 8 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_8_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_8_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 8 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 8)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 8 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 8 = [2, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame8, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp8, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_8_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_8_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 9 14 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_9_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 9 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_9_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 9 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_9_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 9 17 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_9_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 9 18 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_9_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 9 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_9_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_9_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 9 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 9)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 9 20 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 9 = [3, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame9, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp9, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_9_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_9_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 10 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_10_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 10 15 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_10_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 10 16 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_10_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 10 17 = LemmaA.TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]), (-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_10_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 10 18 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_10_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 10 19 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_10_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_10_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 10 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 10)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 10 20 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl,
    show word28 10 = [2, 3, 0, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame10, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp10, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_10_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_10_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 11 14 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_11_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 11 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_11_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 11 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_11_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 11 17 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_11_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 11 18 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_11_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 11 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_11_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_11_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 11 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 11)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 11 20 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 11 = [3, 2, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame11, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp11, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_11_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_11_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 12 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_12_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 12 15 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_12_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 12 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_12_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 12 17 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_12_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 12 18 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_12_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 12 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_12_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_12_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 12 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 12)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 12 20 = LemmaA.TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (-1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 12 = [2, 3, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame12, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp12, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_12_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_12_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 13 14 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_13_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 13 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_13_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 13 16 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_13_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 13 17 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_13_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 13 18 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_13_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 13 19 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_13_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_13_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 13 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 13)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 13 20 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 13 = [1, 3, 2, 1] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame13, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp13, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_13_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_13_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
