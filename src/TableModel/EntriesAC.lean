/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.GaugeAC
public import TableModel.Defs

/-! # Table-model identity, part 3 (frames A, C): the entries

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

theorem tm_0_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 0 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_0_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 0 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_0_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 0 16 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_0_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 0 17 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_0_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 0 18 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 0 = [] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_0_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 0 19 = LemmaA.TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_0_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_0_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 0 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 0)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 0 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 0 = [] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame0, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp0, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_0_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_0_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 1 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_1_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 1 15 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_1_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 1 16 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (-1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_1_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 1 17 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_1_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 1 18 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_1_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 1 19 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_1_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_1_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 1 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 1)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 1 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 1 = [2, 1, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame1, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp1, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_1_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_1_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 2 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_2_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 2 15 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_2_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 2 16 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_2_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 2 17 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_2_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 2 18 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_2_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 2 19 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_2_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_2_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 2 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 2)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 2 20 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 2 = [3, 2, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame2, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp2, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_2_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_2_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 3 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_3_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 3 15 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_3_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 3 16 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_3_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 3 17 = LemmaA.TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (-1, [1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_3_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 3 18 = LemmaA.TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_3_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 3 19 = LemmaA.TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_3_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_3_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 3 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 3)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 3 20 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 3 = [1, 3, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame3, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp3, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_3_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_3_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 4 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_4_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 4 15 = LemmaA.TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_4_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 4 16 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_4_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 4 17 = LemmaA.TracePoly.eval τ [(1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_4_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 4 18 = LemmaA.TracePoly.eval τ [(-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_4_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 4 19 = LemmaA.TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_4_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_4_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 4 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 4)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 4 20 = LemmaA.TracePoly.eval τ [(-4, [0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl,
    show word28 4 = [3, 2, 1, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame4, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp4, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_4_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_4_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 5 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_5_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 5 15 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_5_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 5 16 = LemmaA.TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_5_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 5 17 = LemmaA.TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_5_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 5 18 = LemmaA.TracePoly.eval τ [(-1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_5_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 5 19 = LemmaA.TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_5_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_5_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 5 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 5)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 5 20 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl,
    show word28 5 = [2, 3, 1, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame5, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp5, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_5_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_5_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_14 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 14 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 14)) := by
  rw [show LemmaA.gram28 τ 6 14 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 14 = [2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame14,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp14, LemmaB.TableModel.qg_6_14_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_14]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_15 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 15 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 15)) := by
  rw [show LemmaA.gram28 τ 6 15 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 15 = [3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame15,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp15, LemmaB.TableModel.qg_6_15_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_15]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_16 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 16 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 16)) := by
  rw [show LemmaA.gram28 τ 6 16 = LemmaA.TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 16 = [1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame16,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp16, LemmaB.TableModel.qg_6_16_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_16]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_17 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 17 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 17)) := by
  rw [show LemmaA.gram28 τ 6 17 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 17 = [3, 1, 0, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame17,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp17, LemmaB.TableModel.qg_6_17_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_17]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_18 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 18 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 18)) := by
  rw [show LemmaA.gram28 τ 6 18 = LemmaA.TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 18 = [1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame18,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp18, LemmaB.TableModel.qg_6_18_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_18]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_19 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 19 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 19)) := by
  rw [show LemmaA.gram28 τ 6 19 = LemmaA.TracePoly.eval τ [(1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 19 = [3, 1, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame19,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp19, LemmaB.TableModel.qg_6_19_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_19]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

theorem tm_6_20 (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaA.gram28 τ 6 20 = LemmaB.Q (toTraces τ).toParams
      (LemmaB.uhat (toTraces τ).toParams (word28 6)) (LemmaB.uhat (toTraces τ).toParams (word28 20)) := by
  rw [show LemmaA.gram28 τ 6 20 = LemmaA.TracePoly.eval τ [(-1, [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl,
    show word28 6 = [3, 1, 2, 0] from rfl, show word28 20 = [2, 1, 3, 2] from rfl,
    LemmaB.TableModel.Q_uhat, LemmaB.TableModel.frame6, LemmaB.TableModel.frame20,
    LemmaB.TableModel.amp6, LemmaB.TableModel.amp20, LemmaB.TableModel.qg_6_20_eq,
    toParams_toTraces, LemmaB.TableModel.qn_6_20]
  simp only [LemmaA.TracePoly.eval, LemmaA.monoEval, LemmaA.traceVars, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, LemmaB.mOf, LemmaB.TableModel.paramsN, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try field_simp)
  all_goals ring

end AlbertSequential.LengthSeven.TableModel
