/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeDD
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames D, D): the entries

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

theorem tm_21_21 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 21 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 21)) := by
  rw [show LemmaA.gram28 τ 21 21 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 21 = [3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21,
    LemmaB.TableModel.amp21, LemmaB.TableModel.qg_21_21_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_21]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 21 22 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp22, LemmaB.TableModel.qg_21_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 21 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_21_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 21 24 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_21_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 21 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_21_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 21 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_21_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_21_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 21 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 21)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 21 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 21 = [3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame21, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp21, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_21_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_21_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_22 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 22 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 22)) := by
  rw [show LemmaA.gram28 τ 22 22 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 22 = [1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22,
    LemmaB.TableModel.amp22, LemmaB.TableModel.qg_22_22_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_22]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 22 23 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 22 = [1, 3] from rfl, show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp22, LemmaB.TableModel.amp23, LemmaB.TableModel.qg_22_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 22 24 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 22 = [1, 3] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp22, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_22_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 22 25 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 22 = [1, 3] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp22, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_22_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 22 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 22 = [1, 3] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp22, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_22_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_22_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 22 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 22)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 22 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 22 = [1, 3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame22, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp22, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_22_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_22_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_23_23 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 23 23 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 23)) := by
  rw [show LemmaA.gram28 τ 23 23 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 23 = [2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame23,
    LemmaB.TableModel.amp23, LemmaB.TableModel.qg_23_23_eq,
    toParams_toTraces, LemmaB.TableModel.qn_23_23]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_23_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 23 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 23 24 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 23 = [2, 3] from rfl, show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame23, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp23, LemmaB.TableModel.amp24, LemmaB.TableModel.qg_23_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_23_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_23_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 23 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 23 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 23 = [2, 3] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame23, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp23, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_23_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_23_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_23_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 23 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 23 26 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 23 = [2, 3] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame23, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp23, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_23_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_23_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_23_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 23 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 23)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 23 27 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 23 = [2, 3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame23, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp23, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_23_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_23_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_24_24 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 24 24 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 24)) (LemmaB.uhat (toTraces τ).toParams (word28 24)) := by
  rw [show LemmaA.gram28 τ 24 24 = LemmaA.TracePoly.eval τ [(1, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 24 = [1, 2, 0, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame24,
    LemmaB.TableModel.amp24, LemmaB.TableModel.qg_24_24_eq,
    toParams_toTraces, LemmaB.TableModel.qn_24_24]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_24_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 24 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 24)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 24 25 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 24 = [1, 2, 0, 3] from rfl, show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame24, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp24, LemmaB.TableModel.amp25, LemmaB.TableModel.qg_24_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_24_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_24_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 24 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 24)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 24 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 24 = [1, 2, 0, 3] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame24, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp24, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_24_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_24_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_24_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 24 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 24)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 24 27 = LemmaA.TracePoly.eval τ [(-2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl,
    show word28 24 = [1, 2, 0, 3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame24, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp24, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_24_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_24_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_25_25 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 25 25 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 25)) (LemmaB.uhat (toTraces τ).toParams (word28 25)) := by
  rw [show LemmaA.gram28 τ 25 25 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 25 = [2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame25,
    LemmaB.TableModel.amp25, LemmaB.TableModel.qg_25_25_eq,
    toParams_toTraces, LemmaB.TableModel.qn_25_25]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_25_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 25 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 25)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 25 26 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 25 = [2, 1, 3] from rfl, show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame25, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp25, LemmaB.TableModel.amp26, LemmaB.TableModel.qg_25_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_25_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_25_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 25 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 25)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 25 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 25 = [2, 1, 3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame25, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp25, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_25_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_25_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_26_26 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 26 26 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 26)) (LemmaB.uhat (toTraces τ).toParams (word28 26)) := by
  rw [show LemmaA.gram28 τ 26 26 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 26 = [1, 2, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame26,
    LemmaB.TableModel.amp26, LemmaB.TableModel.qg_26_26_eq,
    toParams_toTraces, LemmaB.TableModel.qn_26_26]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_26_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 26 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 26)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 26 27 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl,
    show word28 26 = [1, 2, 3] from rfl, show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame26, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp26, LemmaB.TableModel.amp27, LemmaB.TableModel.qg_26_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_26_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_27_27 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 27 27 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 27)) (LemmaB.uhat (toTraces τ).toParams (word28 27)) := by
  rw [show LemmaA.gram28 τ 27 27 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 27 = [3, 2, 1, 3] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame27,
    LemmaB.TableModel.amp27, LemmaB.TableModel.qg_27_27_eq,
    toParams_toTraces, LemmaB.TableModel.qn_27_27]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
