/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeCC
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames C, C): the entries

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

theorem tm_14_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 14 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp14, LemmaB.TableModel.qg_14_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 14 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_14_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 14 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_14_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 14 17 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_14_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 14 18 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 14 = [2] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_14_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 14 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_14_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_14_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 14 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 14)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 14 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 14 = [2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame14, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp14, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_14_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_14_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 15 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp15, LemmaB.TableModel.qg_15_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 15 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_15_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 15 17 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_15_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 15 18 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_15_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 15 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_15_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_15_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 15 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 15)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 15 20 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 15 = [3, 2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame15, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp15, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_15_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_15_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 16 16 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp16, LemmaB.TableModel.qg_16_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 16 17 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_16_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 16 18 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_16_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 16 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_16_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_16_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 16 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 16)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 16 20 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 16 = [1, 2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame16, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp16, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_16_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_16_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 17 17 = LemmaA.TracePoly.eval τ [(1, [1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp17, LemmaB.TableModel.qg_17_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 17 18 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_17_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 17 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_17_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_17_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 17 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 17)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 17 20 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 17 = [3, 1, 0, 2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame17, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp17, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_17_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_17_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 18 18 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp18, LemmaB.TableModel.qg_18_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 18 19 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_18_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_18_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 18 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 18)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 18 20 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 18 = [1, 3, 2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame18, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp18, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_18_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_18_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 19 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp19, LemmaB.TableModel.qg_19_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_19_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 19 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 19)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 19 20 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 19 = [3, 1, 2] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame19, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp19, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_19_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_19_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_20_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 20 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 20)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 20 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp20, LemmaB.TableModel.qg_20_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_20_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
