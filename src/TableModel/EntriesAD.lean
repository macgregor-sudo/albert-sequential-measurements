/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeAD
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames A, D): the entries

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

theorem tm_0_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 0 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_0_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 0 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_0_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 0 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_0_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 0 24 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_0_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 0 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_0_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 0 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_0_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 0 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_0_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 1 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_1_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 1 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_1_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 1 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_1_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 1 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (-1, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_1_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 1 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_1_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 1 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_1_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 1 27 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_1_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 2 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_2_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 2 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_2_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 2 23 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (-1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_2_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 2 24 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_2_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 2 25 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_2_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 2 26 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_2_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 2 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_2_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 3 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_3_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 3 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_3_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 3 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_3_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 3 24 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_3_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 3 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_3_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 3 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_3_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 3 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_3_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 4 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_4_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 4 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_4_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 4 23 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_4_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 4 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_4_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 4 25 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_4_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 4 26 = LemmaA.TracePoly.eval τ [(-1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_4_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 4 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_4_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 5 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_5_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 5 22 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_5_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 5 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_5_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 5 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_5_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 5 25 = LemmaA.TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_5_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 5 26 = LemmaA.TracePoly.eval τ [(-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_5_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 5 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (4, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0]), (-2, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]), (-2, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_5_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 6 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp21, LemmaB.TableModel.qg_6_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 6 22 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_6_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 6 23 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_6_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 6 24 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_6_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 6 25 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_6_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 6 26 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_6_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 6 27 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_6_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
