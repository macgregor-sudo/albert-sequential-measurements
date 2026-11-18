/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.Walks
public import LengthSeven.LemmaA.Table

/-! # Lemma A: Gram entries (frame C rows)

Each entry: `⟨[w_i], [w_j]⟩ = L(w_i w̄_j)` (`form_pathVec`), `canon` of that walk equals `canon`
of an instance of a walk lemma at concrete letters (`decide`), then the walk lemma and the
evaluation of the table polynomial. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA

open AlbertSequential AlbertSequential.LengthSeven

set_option hygiene false in
/-- Evaluate a table polynomial and sort the arguments of the trace atoms. -/
local macro "gram_nf" : tactic =>
  `(tactic| (simp only [TracePoly.eval, monoEval, traceVars,
    τ.o_symm 1 0,
    τ.o_symm 2 0,
    τ.o_symm 3 0,
    τ.o_symm 2 1,
    τ.o_symm 3 1,
    τ.o_symm 3 2,
    R_213 τ 0 1 2,
    R_132 τ 0 1 2,
    R_231 τ 0 1 2,
    R_312 τ 0 1 2,
    R_321 τ 0 1 2,
    R_213 τ 0 1 3,
    R_132 τ 0 1 3,
    R_231 τ 0 1 3,
    R_312 τ 0 1 3,
    R_321 τ 0 1 3,
    R_213 τ 0 2 3,
    R_132 τ 0 2 3,
    R_231 τ 0 2 3,
    R_312 τ 0 2 3,
    R_321 τ 0 2 3,
    R_213 τ 1 2 3,
    R_132 τ 1 2 3,
    R_231 τ 1 2 3,
    R_312 τ 1 2 3,
    R_321 τ 1 2 3]; (try push_cast); ring))

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

theorem gram_14_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 14)) = gram28 τ 14 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2]) (by decide),
    walk_W02 h 2 1 3 (by decide),
    show gram28 τ 14 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 15)) = gram28 τ 14 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 14 15 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 16)) = gram28 τ 14 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2]) (by decide),
    walk_W03 h 1 2 3 (by decide),
    show gram28 τ 14 16 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 17)) = gram28 τ 14 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 1, 3]) (by decide),
    walk_W08 h 2 1 3 (by decide),
    show gram28 τ 14 17 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 18)) = gram28 τ 14 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 14 18 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_14_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 19)) = gram28 τ 14 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3]) (by decide),
    walk_W05 h 2 1 3 (by decide),
    show gram28 τ 14 19 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_14_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 20)) = gram28 τ 14 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2]) (by decide),
    walk_W10 h 2 1 3 (by decide),
    show gram28 τ 14 20 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 21)) = gram28 τ 14 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 14 21 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 22)) = gram28 τ 14 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 14 22 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_14_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 23)) = gram28 τ 14 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2]) (by decide),
    walk_W04 h 2 3 1 (by decide),
    show gram28 τ 14 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 24)) = gram28 τ 14 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 2, 1]) (by decide),
    walk_W15 h 2 3 1 (by decide),
    show gram28 τ 14 24 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_14_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 25)) = gram28 τ 14 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2]) (by decide),
    walk_W10 h 2 1 3 (by decide),
    show gram28 τ 14 25 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 26)) = gram28 τ 14 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 1]) (by decide),
    walk_W09 h 2 3 1 (by decide),
    show gram28 τ 14 26 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_14_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 14)) (W.pathVec (word28 27)) = gram28 τ 14 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 2, 3]) (by decide),
    walk_W20 h 2 3 1 (by decide),
    show gram28 τ 14 27 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_15_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 15)) = gram28 τ 15 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3]) (by decide),
    walk_W04 h 3 2 1 (by decide),
    show gram28 τ 15 15 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 16)) = gram28 τ 15 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 15 16 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_15_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 17)) = gram28 τ 15 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3]) (by decide),
    walk_W18 h 3 1 2 (by decide),
    show gram28 τ 15 17 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_15_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 18)) = gram28 τ 15 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1]) (by decide),
    walk_W09 h 3 2 1 (by decide),
    show gram28 τ 15 18 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 19)) = gram28 τ 15 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3]) (by decide),
    walk_W10 h 3 1 2 (by decide),
    show gram28 τ 15 19 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 20)) = gram28 τ 15 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1, 2]) (by decide),
    walk_W19 h 3 2 1 (by decide),
    show gram28 τ 15 20 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_15_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 21)) = gram28 τ 15 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3]) (by decide),
    walk_W04 h 3 2 1 (by decide),
    show gram28 τ 15 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 22)) = gram28 τ 15 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1]) (by decide),
    walk_W09 h 3 2 1 (by decide),
    show gram28 τ 15 22 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 23)) = gram28 τ 15 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 3]) (by decide),
    walk_S01 h 2 3 1 (by decide),
    show gram28 τ 15 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 24)) = gram28 τ 15 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 3]) (by decide),
    walk_W28 h 1 2 3 (by decide),
    show gram28 τ 15 24 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_15_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 25)) = gram28 τ 15 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1, 2]) (by decide),
    walk_W19 h 3 2 1 (by decide),
    show gram28 τ 15 25 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_15_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 26)) = gram28 τ 15 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 2, 1]) (by decide),
    walk_S02 h 3 2 1 (by decide),
    show gram28 τ 15 26 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_15_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 15)) (W.pathVec (word28 27)) = gram28 τ 15 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1, 2, 3]) (by decide),
    walk_S04 h 3 2 1 (by decide),
    show gram28 τ 15 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 16)) = gram28 τ 16 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 1]) (by decide),
    walk_W04 h 1 2 3 (by decide),
    show gram28 τ 16 16 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 17)) = gram28 τ 16 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 1, 3]) (by decide),
    walk_W15 h 1 2 3 (by decide),
    show gram28 τ 16 17 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_16_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 18)) = gram28 τ 16 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1]) (by decide),
    walk_W10 h 1 2 3 (by decide),
    show gram28 τ 16 18 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 19)) = gram28 τ 16 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 1, 3]) (by decide),
    walk_W09 h 1 2 3 (by decide),
    show gram28 τ 16 19 = TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 20)) = gram28 τ 16 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1, 2]) (by decide),
    walk_W20 h 1 2 3 (by decide),
    show gram28 τ 16 20 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_16_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 21)) = gram28 τ 16 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 16 21 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_16_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 22)) = gram28 τ 16 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1]) (by decide),
    walk_W10 h 1 2 3 (by decide),
    show gram28 τ 16 22 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 23)) = gram28 τ 16 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 1]) (by decide),
    walk_W09 h 2 3 1 (by decide),
    show gram28 τ 16 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 24)) = gram28 τ 16 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 1]) (by decide),
    walk_W27 h 1 2 3 (by decide),
    show gram28 τ 16 24 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 25)) = gram28 τ 16 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1, 2]) (by decide),
    walk_W20 h 1 2 3 (by decide),
    show gram28 τ 16 25 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_16_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 26)) = gram28 τ 16 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 2, 1]) (by decide),
    walk_S05 h 1 2 3 (by decide),
    show gram28 τ 16 26 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_16_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 16)) (W.pathVec (word28 27)) = gram28 τ 16 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1, 2, 3]) (by decide),
    walk_S16 h 1 2 3 (by decide),
    show gram28 τ 16 27 = TracePoly.eval τ [(-1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_17_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 17)) = gram28 τ 17 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 0, 1, 3]) (by decide),
    walk_W34 h 3 1 2 (by decide),
    show gram28 τ 17 17 = TracePoly.eval τ [(1, [1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 18)) = gram28 τ 17 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 1]) (by decide),
    walk_W25 h 3 1 2 (by decide),
    show gram28 τ 17 18 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 19)) = gram28 τ 17 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 1, 3]) (by decide),
    walk_W27 h 3 1 2 (by decide),
    show gram28 τ 17 19 = TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 20)) = gram28 τ 17 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 1, 2]) (by decide),
    walk_W35 h 3 1 2 (by decide),
    show gram28 τ 17 20 = TracePoly.eval τ [(-2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_17_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 21)) = gram28 τ 17 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3]) (by decide),
    walk_W18 h 3 1 2 (by decide),
    show gram28 τ 17 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_17_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 22)) = gram28 τ 17 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 1]) (by decide),
    walk_W25 h 3 1 2 (by decide),
    show gram28 τ 17 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 23)) = gram28 τ 17 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 2]) (by decide),
    walk_W26 h 3 1 2 (by decide),
    show gram28 τ 17 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 24)) = gram28 τ 17 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 0, 2, 1]) (by decide),
    walk_W45 h 3 1 2 (by decide),
    show gram28 τ 17 24 = TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]), (-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_17_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 25)) = gram28 τ 17 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 1, 2]) (by decide),
    walk_W35 h 3 1 2 (by decide),
    show gram28 τ 17 25 = TracePoly.eval τ [(-2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_17_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 26)) = gram28 τ 17 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 2, 1]) (by decide),
    walk_W36 h 3 1 2 (by decide),
    show gram28 τ 17 26 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_17_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 17)) (W.pathVec (word28 27)) = gram28 τ 17 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3, 1, 2, 3]) (by decide),
    walk_W46 h 3 1 2 (by decide),
    show gram28 τ 17 27 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_18_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 18)) = gram28 τ 18 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 3, 1]) (by decide),
    walk_S05 h 1 3 2 (by decide),
    show gram28 τ 18 18 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 19)) = gram28 τ 18 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 1, 3]) (by decide),
    walk_W20 h 1 3 2 (by decide),
    show gram28 τ 18 19 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_18_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 20)) = gram28 τ 18 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 1]) (by decide),
    walk_S06 h 2 1 3 (by decide),
    show gram28 τ 18 20 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 21)) = gram28 τ 18 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1]) (by decide),
    walk_W09 h 3 2 1 (by decide),
    show gram28 τ 18 21 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 22)) = gram28 τ 18 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 3, 1]) (by decide),
    walk_S05 h 1 3 2 (by decide),
    show gram28 τ 18 22 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 23)) = gram28 τ 18 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 3, 1]) (by decide),
    walk_S02 h 2 3 1 (by decide),
    show gram28 τ 18 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_18_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 24)) = gram28 τ 18 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 3, 1]) (by decide),
    walk_W38 h 1 2 3 (by decide),
    show gram28 τ 18 24 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_18_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 25)) = gram28 τ 18 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 1]) (by decide),
    walk_S06 h 2 1 3 (by decide),
    show gram28 τ 18 25 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 26)) = gram28 τ 18 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 2, 3, 1]) (by decide),
    walk_S07 h 1 2 3 (by decide),
    show gram28 τ 18 26 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_18_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 18)) (W.pathVec (word28 27)) = gram28 τ 18 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 3, 2, 3, 1]) (by decide),
    walk_S08 h 3 2 1 (by decide),
    show gram28 τ 18 27 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_19_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 19)) = gram28 τ 19 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 1, 3]) (by decide),
    walk_S05 h 3 1 2 (by decide),
    show gram28 τ 19 19 = TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_19_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 20)) = gram28 τ 19 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 1, 3]) (by decide),
    walk_S16 h 2 1 3 (by decide),
    show gram28 τ 19 20 = TracePoly.eval τ [(-1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_19_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 21)) = gram28 τ 19 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3]) (by decide),
    walk_W10 h 3 1 2 (by decide),
    show gram28 τ 19 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_19_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 22)) = gram28 τ 19 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 1, 3]) (by decide),
    walk_W20 h 1 3 2 (by decide),
    show gram28 τ 19 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_19_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 23)) = gram28 τ 19 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 1, 3]) (by decide),
    walk_W19 h 2 3 1 (by decide),
    show gram28 τ 19 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_19_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 24)) = gram28 τ 19 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 1, 3]) (by decide),
    walk_W37 h 1 2 3 (by decide),
    show gram28 τ 19 24 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl]
  gram_nf

theorem gram_19_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 25)) = gram28 τ 19 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 1, 3]) (by decide),
    walk_S16 h 2 1 3 (by decide),
    show gram28 τ 19 25 = TracePoly.eval τ [(-1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_19_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 26)) = gram28 τ 19 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3, 2, 1]) (by decide),
    walk_S06 h 3 1 2 (by decide),
    show gram28 τ 19 26 = TracePoly.eval τ [(1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_19_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 19)) (W.pathVec (word28 27)) = gram28 τ 19 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3, 1, 2, 3]) (by decide),
    walk_S17 h 3 1 2 (by decide),
    show gram28 τ 19 27 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (-1, [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 20)) = gram28 τ 20 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 1, 2]) (by decide),
    walk_S13 h 2 1 3 (by decide),
    show gram28 τ 20 20 = TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 21)) = gram28 τ 20 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 3, 1, 2]) (by decide),
    walk_W19 h 3 2 1 (by decide),
    show gram28 τ 20 21 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_20_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 22)) = gram28 τ 20 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 1]) (by decide),
    walk_S06 h 2 1 3 (by decide),
    show gram28 τ 20 22 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 23)) = gram28 τ 20 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 3, 1, 2]) (by decide),
    walk_S03 h 2 3 1 (by decide),
    show gram28 τ 20 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 24)) = gram28 τ 20 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 3, 1, 2]) (by decide),
    walk_W47 h 1 2 3 (by decide),
    show gram28 τ 20 24 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 25)) = gram28 τ 20 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 1, 2]) (by decide),
    walk_S13 h 2 1 3 (by decide),
    show gram28 τ 20 25 = TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_20_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 26)) = gram28 τ 20 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2, 3, 2, 1]) (by decide),
    walk_S09 h 2 1 3 (by decide),
    show gram28 τ 20 26 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_20_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 20)) (W.pathVec (word28 27)) = gram28 τ 20 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 3, 2, 3, 1, 2]) (by decide),
    walk_S14 h 3 2 1 (by decide),
    show gram28 τ 20 27 = TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf


end AlbertSequential.LengthSeven.LemmaA
