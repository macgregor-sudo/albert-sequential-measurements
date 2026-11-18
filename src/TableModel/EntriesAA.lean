/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeAA
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames A, A): the entries

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

theorem tm_0_0 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 0 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 0)) := by
  rw [show LemmaA.gram28 τ 0 0 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0,
    LemmaB.TableModel.amp0, LemmaB.TableModel.qg_0_0_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_0]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_1 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 1 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 1)) := by
  rw [show LemmaA.gram28 τ 0 1 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 1 = [2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame1,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp1, LemmaB.TableModel.qg_0_1_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_1]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_2 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 2 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 2)) := by
  rw [show LemmaA.gram28 τ 0 2 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 2 = [3, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame2,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp2, LemmaB.TableModel.qg_0_2_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_2]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_3 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 3 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 3)) := by
  rw [show LemmaA.gram28 τ 0 3 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 3 = [1, 3, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame3,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp3, LemmaB.TableModel.qg_0_3_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_3]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 4 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 4)) := by
  rw [show LemmaA.gram28 τ 0 4 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 4 = [3, 2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame4,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp4, LemmaB.TableModel.qg_0_4_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_4]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 0 5 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 0 = [] from rfl, show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp5, LemmaB.TableModel.qg_0_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 0 6 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_0_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_1 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 1 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 1)) := by
  rw [show LemmaA.gram28 τ 1 1 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1,
    LemmaB.TableModel.amp1, LemmaB.TableModel.qg_1_1_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_1]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_2 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 2 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 2)) := by
  rw [show LemmaA.gram28 τ 1 2 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 2 = [3, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame2,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp2, LemmaB.TableModel.qg_1_2_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_2]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_3 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 3 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 3)) := by
  rw [show LemmaA.gram28 τ 1 3 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 3 = [1, 3, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame3,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp3, LemmaB.TableModel.qg_1_3_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_3]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 4 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 4)) := by
  rw [show LemmaA.gram28 τ 1 4 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 4 = [3, 2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame4,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp4, LemmaB.TableModel.qg_1_4_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_4]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 1 5 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp5, LemmaB.TableModel.qg_1_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 1 6 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_1_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_2 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 2 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 2)) := by
  rw [show LemmaA.gram28 τ 2 2 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2,
    LemmaB.TableModel.amp2, LemmaB.TableModel.qg_2_2_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_2]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_3 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 3 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 3)) := by
  rw [show LemmaA.gram28 τ 2 3 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 3 = [1, 3, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame3,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp3, LemmaB.TableModel.qg_2_3_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_3]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 4 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 4)) := by
  rw [show LemmaA.gram28 τ 2 4 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 4 = [3, 2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame4,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp4, LemmaB.TableModel.qg_2_4_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_4]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 2 5 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp5, LemmaB.TableModel.qg_2_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 2 6 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_2_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_3 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 3 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 3)) := by
  rw [show LemmaA.gram28 τ 3 3 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3,
    LemmaB.TableModel.amp3, LemmaB.TableModel.qg_3_3_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_3]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 4 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 4)) := by
  rw [show LemmaA.gram28 τ 3 4 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 4 = [3, 2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame4,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp4, LemmaB.TableModel.qg_3_4_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_4]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 3 5 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp5, LemmaB.TableModel.qg_3_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 3 6 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_3_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_4 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 4 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 4)) := by
  rw [show LemmaA.gram28 τ 4 4 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4,
    LemmaB.TableModel.amp4, LemmaB.TableModel.qg_4_4_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_4]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 4 5 = LemmaA.TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp5, LemmaB.TableModel.qg_4_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 4 6 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_4_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_5 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 5 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 5)) := by
  rw [show LemmaA.gram28 τ 5 5 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5,
    LemmaB.TableModel.amp5, LemmaB.TableModel.qg_5_5_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_5]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 5 6 = LemmaA.TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp6, LemmaB.TableModel.qg_5_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_6 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 6 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 6)) := by
  rw [show LemmaA.gram28 τ 6 6 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6,
    LemmaB.TableModel.amp6, LemmaB.TableModel.qg_6_6_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_6]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
