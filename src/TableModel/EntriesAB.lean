/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeAB
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames A, B): the entries

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

theorem tm_0_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 0 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_0_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 0 8 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_0_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 0 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_0_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 0 10 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_0_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 0 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_0_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 0 12 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 0 = [] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_0_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 0 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_0_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 1 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_1_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 1 8 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_1_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 1 9 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_1_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 1 10 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_1_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 1 11 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_1_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 1 12 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_1_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 1 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_1_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 2 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_2_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 2 8 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_2_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 2 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_2_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 2 10 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (-1, [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_2_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 2 11 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_2_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 2 12 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_2_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 2 13 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_2_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 3 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_3_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 3 8 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_3_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 3 9 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (-1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_3_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 3 10 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_3_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 3 11 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_3_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 3 12 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_3_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 3 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_3_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 4 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_4_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 4 8 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_4_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 4 9 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_4_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 4 10 = LemmaA.TracePoly.eval τ [(-1, [1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_4_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 4 11 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_4_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 4 12 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_4_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 4 13 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_4_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 5 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_5_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 5 8 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_5_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 5 9 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_5_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 5 10 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_5_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 5 11 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_5_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 5 12 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_5_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 5 13 = LemmaA.TracePoly.eval τ [(-1, [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_5_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_7 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 7 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 7)) := by
  rw [show LemmaA.gram28 τ 6 7 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 7 = [1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame7,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp7, LemmaB.TableModel.qg_6_7_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_7]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_8 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 8 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 8)) := by
  rw [show LemmaA.gram28 τ 6 8 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 8 = [2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame8,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp8, LemmaB.TableModel.qg_6_8_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_8]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_9 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 9 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 9)) := by
  rw [show LemmaA.gram28 τ 6 9 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 9 = [3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame9,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp9, LemmaB.TableModel.qg_6_9_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_9]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_10 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 10 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 10)) := by
  rw [show LemmaA.gram28 τ 6 10 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 10 = [2, 3, 0, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame10,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp10, LemmaB.TableModel.qg_6_10_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_10]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_11 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 11 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 11)) := by
  rw [show LemmaA.gram28 τ 6 11 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 11 = [3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame11,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp11, LemmaB.TableModel.qg_6_11_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_11]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_12 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 12 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 12)) := by
  rw [show LemmaA.gram28 τ 6 12 = LemmaA.TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 12 = [2, 3, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame12,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp12, LemmaB.TableModel.qg_6_12_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_12]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_13 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 13 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 13)) := by
  rw [show LemmaA.gram28 τ 6 13 = LemmaA.TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (-2, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0]), (-2, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (1, [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 13 = [1, 3, 2, 1] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame13,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp13, LemmaB.TableModel.qg_6_13_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_13]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
