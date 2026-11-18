/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.Walks
public import LengthSeven.LemmaA.Table

/-! # Lemma A: Gram entries (frame A rows)

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

theorem gram_0_0 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 0)) = gram28 τ 0 0 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := []) (by decide),
    walk_W01 h 1 2 3 (by decide),
    show gram28 τ 0 0 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_1 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 1)) = gram28 τ 0 1 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2]) (by decide),
    walk_W03 h 1 2 3 (by decide),
    show gram28 τ 0 1 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_2 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 2)) = gram28 τ 0 2 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 0 2 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_3 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 3)) = gram28 τ 0 3 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3]) (by decide),
    walk_W03 h 1 3 2 (by decide),
    show gram28 τ 0 3 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_4 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 4)) = gram28 τ 0 4 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 0 4 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_0_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 5)) = gram28 τ 0 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 0 5 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_0_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 6)) = gram28 τ 0 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3]) (by decide),
    walk_W05 h 2 1 3 (by decide),
    show gram28 τ 0 6 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_0_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 7)) = gram28 τ 0 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1]) (by decide),
    walk_W02 h 1 2 3 (by decide),
    show gram28 τ 0 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 8)) = gram28 τ 0 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2]) (by decide),
    walk_W03 h 1 2 3 (by decide),
    show gram28 τ 0 8 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 9)) = gram28 τ 0 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3]) (by decide),
    walk_W03 h 1 3 2 (by decide),
    show gram28 τ 0 9 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 10)) = gram28 τ 0 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 3, 2]) (by decide),
    walk_W08 h 1 3 2 (by decide),
    show gram28 τ 0 10 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 11)) = gram28 τ 0 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 0 11 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_0_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 12)) = gram28 τ 0 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 0 12 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_0_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 13)) = gram28 τ 0 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1]) (by decide),
    walk_W10 h 1 2 3 (by decide),
    show gram28 τ 0 13 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 14)) = gram28 τ 0 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2]) (by decide),
    walk_W02 h 2 1 3 (by decide),
    show gram28 τ 0 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 15)) = gram28 τ 0 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 0 15 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 16)) = gram28 τ 0 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2]) (by decide),
    walk_W03 h 1 2 3 (by decide),
    show gram28 τ 0 16 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 17)) = gram28 τ 0 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 1, 3]) (by decide),
    walk_W08 h 2 1 3 (by decide),
    show gram28 τ 0 17 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 18)) = gram28 τ 0 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 0 18 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_0_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 19)) = gram28 τ 0 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3]) (by decide),
    walk_W05 h 2 1 3 (by decide),
    show gram28 τ 0 19 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_0_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 20)) = gram28 τ 0 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2]) (by decide),
    walk_W10 h 2 1 3 (by decide),
    show gram28 τ 0 20 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 21)) = gram28 τ 0 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3]) (by decide),
    walk_W02 h 3 1 2 (by decide),
    show gram28 τ 0 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 22)) = gram28 τ 0 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3]) (by decide),
    walk_W03 h 1 3 2 (by decide),
    show gram28 τ 0 22 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 23)) = gram28 τ 0 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 0 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 24)) = gram28 τ 0 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 2, 1]) (by decide),
    walk_W08 h 3 2 1 (by decide),
    show gram28 τ 0 24 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_0_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 25)) = gram28 τ 0 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3]) (by decide),
    walk_W05 h 2 1 3 (by decide),
    show gram28 τ 0 25 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_0_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 26)) = gram28 τ 0 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 0 26 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_0_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 0)) (W.pathVec (word28 27)) = gram28 τ 0 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3]) (by decide),
    walk_W10 h 3 1 2 (by decide),
    show gram28 τ 0 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_1 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 1)) = gram28 τ 1 1 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2]) (by decide),
    walk_W16 h 2 1 3 (by decide),
    show gram28 τ 1 1 = TracePoly.eval τ [(1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_2 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 2)) = gram28 τ 1 2 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 3]) (by decide),
    walk_W15 h 2 1 3 (by decide),
    show gram28 τ 1 2 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_1_3 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 3)) = gram28 τ 1 3 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2]) (by decide),
    walk_W15 h 1 3 2 (by decide),
    show gram28 τ 1 3 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_1_4 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 4)) = gram28 τ 1 4 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2, 3]) (by decide),
    walk_W23 h 2 1 3 (by decide),
    show gram28 τ 1 4 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 5)) = gram28 τ 1 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 3, 2]) (by decide),
    walk_W24 h 2 1 3 (by decide),
    show gram28 τ 1 5 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 6)) = gram28 τ 1 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 1, 3]) (by decide),
    walk_W21 h 2 1 3 (by decide),
    show gram28 τ 1 6 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 7)) = gram28 τ 1 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 1, 2]) (by decide),
    walk_W06 h 1 2 3 (by decide),
    show gram28 τ 1 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 8)) = gram28 τ 1 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2]) (by decide),
    walk_W16 h 2 1 3 (by decide),
    show gram28 τ 1 8 = TracePoly.eval τ [(1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 9)) = gram28 τ 1 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 3]) (by decide),
    walk_W17 h 2 1 3 (by decide),
    show gram28 τ 1 9 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_1_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 10)) = gram28 τ 1 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 0, 3, 2]) (by decide),
    walk_W31 h 2 1 3 (by decide),
    show gram28 τ 1 10 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_1_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 11)) = gram28 τ 1 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2, 3]) (by decide),
    walk_W23 h 2 1 3 (by decide),
    show gram28 τ 1 11 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 12)) = gram28 τ 1 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 3, 2]) (by decide),
    walk_W24 h 2 1 3 (by decide),
    show gram28 τ 1 12 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 13)) = gram28 τ 1 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2, 3, 1]) (by decide),
    walk_W32 h 2 1 3 (by decide),
    show gram28 τ 1 13 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_1_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 14)) = gram28 τ 1 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 1, 2]) (by decide),
    walk_W07 h 2 1 3 (by decide),
    show gram28 τ 1 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 15)) = gram28 τ 1 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 3]) (by decide),
    walk_W15 h 2 1 3 (by decide),
    show gram28 τ 1 15 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_1_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 16)) = gram28 τ 1 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 1, 2]) (by decide),
    walk_W14 h 1 2 3 (by decide),
    show gram28 τ 1 16 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (-1, [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 17)) = gram28 τ 1 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 0, 1, 3]) (by decide),
    walk_W29 h 2 1 3 (by decide),
    show gram28 τ 1 17 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_1_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 18)) = gram28 τ 1 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 3, 1]) (by decide),
    walk_W22 h 2 1 3 (by decide),
    show gram28 τ 1 18 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 19)) = gram28 τ 1 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 1, 3]) (by decide),
    walk_W21 h 2 1 3 (by decide),
    show gram28 τ 1 19 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 20)) = gram28 τ 1 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 3, 1, 2]) (by decide),
    walk_W30 h 2 1 3 (by decide),
    show gram28 τ 1 20 = TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_1_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 21)) = gram28 τ 1 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 1, 2]) (by decide),
    walk_W08 h 3 1 2 (by decide),
    show gram28 τ 1 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 22)) = gram28 τ 1 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2]) (by decide),
    walk_W15 h 1 3 2 (by decide),
    show gram28 τ 1 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_1_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 23)) = gram28 τ 1 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 3, 2]) (by decide),
    walk_W18 h 2 1 3 (by decide),
    show gram28 τ 1 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_1_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 24)) = gram28 τ 1 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 0, 1, 2]) (by decide),
    walk_W33 h 1 2 3 (by decide),
    show gram28 τ 1 24 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (-1, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 25)) = gram28 τ 1 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 3, 1, 2]) (by decide),
    walk_W27 h 2 1 3 (by decide),
    show gram28 τ 1 25 = TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 26)) = gram28 τ 1 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 3, 2, 1]) (by decide),
    walk_W25 h 2 1 3 (by decide),
    show gram28 τ 1 26 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_1_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 1)) (W.pathVec (word28 27)) = gram28 τ 1 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 3, 1, 2, 3]) (by decide),
    walk_W37 h 2 1 3 (by decide),
    show gram28 τ 1 27 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl]
  gram_nf

theorem gram_2_2 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 2)) = gram28 τ 2 2 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 3]) (by decide),
    walk_W16 h 3 2 1 (by decide),
    show gram28 τ 2 2 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_3 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 3)) = gram28 τ 2 3 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 1]) (by decide),
    walk_W15 h 3 2 1 (by decide),
    show gram28 τ 2 3 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_4 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 4)) = gram28 τ 2 4 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 2, 3]) (by decide),
    walk_W27 h 3 2 1 (by decide),
    show gram28 τ 2 4 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 5)) = gram28 τ 2 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 3, 2]) (by decide),
    walk_W25 h 3 2 1 (by decide),
    show gram28 τ 2 5 = TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 6)) = gram28 τ 2 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 1, 3]) (by decide),
    walk_W24 h 3 2 1 (by decide),
    show gram28 τ 2 6 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 7)) = gram28 τ 2 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 2, 3]) (by decide),
    walk_W08 h 1 2 3 (by decide),
    show gram28 τ 2 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 8)) = gram28 τ 2 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 3]) (by decide),
    walk_W15 h 2 1 3 (by decide),
    show gram28 τ 2 8 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_2_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 9)) = gram28 τ 2 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 3]) (by decide),
    walk_W18 h 3 1 2 (by decide),
    show gram28 τ 2 9 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 10)) = gram28 τ 2 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 0, 2, 3]) (by decide),
    walk_W33 h 2 3 1 (by decide),
    show gram28 τ 2 10 = TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (-1, [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 11)) = gram28 τ 2 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 2, 3]) (by decide),
    walk_W27 h 3 2 1 (by decide),
    show gram28 τ 2 11 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 12)) = gram28 τ 2 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 3, 2]) (by decide),
    walk_W25 h 3 2 1 (by decide),
    show gram28 τ 2 12 = TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 13)) = gram28 τ 2 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 2, 3, 1]) (by decide),
    walk_W37 h 3 2 1 (by decide),
    show gram28 τ 2 13 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl]
  gram_nf

theorem gram_2_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 14)) = gram28 τ 2 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 2, 3]) (by decide),
    walk_W06 h 2 3 1 (by decide),
    show gram28 τ 2 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 15)) = gram28 τ 2 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 3]) (by decide),
    walk_W16 h 3 2 1 (by decide),
    show gram28 τ 2 15 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 16)) = gram28 τ 2 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 2, 3]) (by decide),
    walk_W17 h 1 2 3 (by decide),
    show gram28 τ 2 16 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_2_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 17)) = gram28 τ 2 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 0, 1, 3]) (by decide),
    walk_W31 h 3 2 1 (by decide),
    show gram28 τ 2 17 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 18)) = gram28 τ 2 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 3, 1]) (by decide),
    walk_W23 h 3 2 1 (by decide),
    show gram28 τ 2 18 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 19)) = gram28 τ 2 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 1, 3]) (by decide),
    walk_W24 h 3 2 1 (by decide),
    show gram28 τ 2 19 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 20)) = gram28 τ 2 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 3, 1, 2]) (by decide),
    walk_W32 h 3 2 1 (by decide),
    show gram28 τ 2 20 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_2_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 21)) = gram28 τ 2 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 2, 3]) (by decide),
    walk_W07 h 3 2 1 (by decide),
    show gram28 τ 2 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 22)) = gram28 τ 2 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 1]) (by decide),
    walk_W15 h 3 2 1 (by decide),
    show gram28 τ 2 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_2_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 23)) = gram28 τ 2 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 2, 3]) (by decide),
    walk_W14 h 2 3 1 (by decide),
    show gram28 τ 2 23 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (-1, [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 24)) = gram28 τ 2 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 0, 2, 1]) (by decide),
    walk_W29 h 3 2 1 (by decide),
    show gram28 τ 2 24 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_2_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 25)) = gram28 τ 2 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 1, 2]) (by decide),
    walk_W22 h 3 2 1 (by decide),
    show gram28 τ 2 25 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_2_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 26)) = gram28 τ 2 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 2, 1]) (by decide),
    walk_W21 h 3 2 1 (by decide),
    show gram28 τ 2 26 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_2_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 2)) (W.pathVec (word28 27)) = gram28 τ 2 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 1, 2, 3]) (by decide),
    walk_W30 h 3 2 1 (by decide),
    show gram28 τ 2 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_3 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 3)) = gram28 τ 3 3 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 1]) (by decide),
    walk_W16 h 1 3 2 (by decide),
    show gram28 τ 3 3 = TracePoly.eval τ [(1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_4 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 4)) = gram28 τ 3 4 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2, 3]) (by decide),
    walk_W22 h 1 3 2 (by decide),
    show gram28 τ 3 4 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 5)) = gram28 τ 3 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 3, 2]) (by decide),
    walk_W21 h 1 3 2 (by decide),
    show gram28 τ 3 5 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 6)) = gram28 τ 3 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 1, 3]) (by decide),
    walk_W25 h 1 3 2 (by decide),
    show gram28 τ 3 6 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 7)) = gram28 τ 3 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 3, 1]) (by decide),
    walk_W07 h 1 3 2 (by decide),
    show gram28 τ 3 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 8)) = gram28 τ 3 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2]) (by decide),
    walk_W15 h 1 3 2 (by decide),
    show gram28 τ 3 8 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 9)) = gram28 τ 3 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 3]) (by decide),
    walk_W14 h 1 3 2 (by decide),
    show gram28 τ 3 9 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (-1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 10)) = gram28 τ 3 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 0, 3, 2]) (by decide),
    walk_W29 h 1 3 2 (by decide),
    show gram28 τ 3 10 = TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_3_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 11)) = gram28 τ 3 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2, 3]) (by decide),
    walk_W22 h 1 3 2 (by decide),
    show gram28 τ 3 11 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 12)) = gram28 τ 3 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 3, 2]) (by decide),
    walk_W21 h 1 3 2 (by decide),
    show gram28 τ 3 12 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 13)) = gram28 τ 3 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2, 3, 1]) (by decide),
    walk_W30 h 1 3 2 (by decide),
    show gram28 τ 3 13 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_3_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 14)) = gram28 τ 3 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 3, 1]) (by decide),
    walk_W08 h 2 3 1 (by decide),
    show gram28 τ 3 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 15)) = gram28 τ 3 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 3, 1]) (by decide),
    walk_W15 h 3 2 1 (by decide),
    show gram28 τ 3 15 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (-1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_3_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 16)) = gram28 τ 3 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 1]) (by decide),
    walk_W18 h 1 2 3 (by decide),
    show gram28 τ 3 16 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 17)) = gram28 τ 3 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 0, 1, 3]) (by decide),
    walk_W33 h 1 3 2 (by decide),
    show gram28 τ 3 17 = TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (-1, [1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 18)) = gram28 τ 3 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 3, 1]) (by decide),
    walk_W27 h 1 3 2 (by decide),
    show gram28 τ 3 18 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 19)) = gram28 τ 3 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 1, 3]) (by decide),
    walk_W25 h 1 3 2 (by decide),
    show gram28 τ 3 19 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 20)) = gram28 τ 3 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 3, 1, 2]) (by decide),
    walk_W37 h 1 3 2 (by decide),
    show gram28 τ 3 20 = TracePoly.eval τ [(2, [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (-2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_3_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 21)) = gram28 τ 3 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 3, 1]) (by decide),
    walk_W06 h 3 1 2 (by decide),
    show gram28 τ 3 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 22)) = gram28 τ 3 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 1]) (by decide),
    walk_W16 h 1 3 2 (by decide),
    show gram28 τ 3 22 = TracePoly.eval τ [(1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 23)) = gram28 τ 3 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 2]) (by decide),
    walk_W17 h 1 3 2 (by decide),
    show gram28 τ 3 23 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_3_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 24)) = gram28 τ 3 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 0, 2, 1]) (by decide),
    walk_W31 h 1 3 2 (by decide),
    show gram28 τ 3 24 = TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_3_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 25)) = gram28 τ 3 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 1, 2]) (by decide),
    walk_W23 h 1 3 2 (by decide),
    show gram28 τ 3 25 = TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 26)) = gram28 τ 3 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 2, 1]) (by decide),
    walk_W24 h 1 3 2 (by decide),
    show gram28 τ 3 26 = TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_3_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 3)) (W.pathVec (word28 27)) = gram28 τ 3 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 3, 1, 2, 3]) (by decide),
    walk_W32 h 1 3 2 (by decide),
    show gram28 τ 3 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_4 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 4)) = gram28 τ 4 4 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 1, 2, 3]) (by decide),
    walk_S11 h 3 2 1 (by decide),
    show gram28 τ 4 4 = TracePoly.eval τ [(1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 5)) = gram28 τ 4 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 2, 3]) (by decide),
    walk_S10 h 2 3 1 (by decide),
    show gram28 τ 4 5 = TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_4_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 6)) = gram28 τ 4 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 2, 3]) (by decide),
    walk_S19 h 3 1 2 (by decide),
    show gram28 τ 4 6 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_4_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 7)) = gram28 τ 4 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 1, 2, 3]) (by decide),
    walk_W11 h 1 2 3 (by decide),
    show gram28 τ 4 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 8)) = gram28 τ 4 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 2, 3]) (by decide),
    walk_W23 h 2 1 3 (by decide),
    show gram28 τ 4 8 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 9)) = gram28 τ 4 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 1, 2, 3]) (by decide),
    walk_W24 h 3 1 2 (by decide),
    show gram28 τ 4 9 = TracePoly.eval τ [(1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 10)) = gram28 τ 4 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 0, 1, 2, 3]) (by decide),
    walk_W43 h 2 3 1 (by decide),
    show gram28 τ 4 10 = TracePoly.eval τ [(-1, [1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 11)) = gram28 τ 4 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 1, 2, 3]) (by decide),
    walk_S11 h 3 2 1 (by decide),
    show gram28 τ 4 11 = TracePoly.eval τ [(1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 12)) = gram28 τ 4 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 2, 3]) (by decide),
    walk_S10 h 2 3 1 (by decide),
    show gram28 τ 4 12 = TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_4_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 13)) = gram28 τ 4 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 1, 2, 3, 1]) (by decide),
    walk_S12 h 3 2 1 (by decide),
    show gram28 τ 4 13 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 14)) = gram28 τ 4 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 1, 2, 3]) (by decide),
    walk_W12 h 2 1 3 (by decide),
    show gram28 τ 4 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 15)) = gram28 τ 4 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 2, 3]) (by decide),
    walk_W27 h 3 2 1 (by decide),
    show gram28 τ 4 15 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 16)) = gram28 τ 4 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 1, 2, 3]) (by decide),
    walk_W21 h 1 2 3 (by decide),
    show gram28 τ 4 16 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 17)) = gram28 τ 4 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 0, 1, 2, 3]) (by decide),
    walk_W42 h 3 1 2 (by decide),
    show gram28 τ 4 17 = TracePoly.eval τ [(1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 18)) = gram28 τ 4 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 2, 3, 1]) (by decide),
    walk_X01 h 3 2 1 (by decide),
    show gram28 τ 4 18 = TracePoly.eval τ [(-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl]
  gram_nf

theorem gram_4_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 19)) = gram28 τ 4 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 2, 3]) (by decide),
    walk_S19 h 3 1 2 (by decide),
    show gram28 τ 4 19 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_4_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 20)) = gram28 τ 4 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 2, 3, 1, 2]) (by decide),
    walk_S20 h 3 2 1 (by decide),
    show gram28 τ 4 20 = TracePoly.eval τ [(-4, [0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 21)) = gram28 τ 4 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 1, 2, 3]) (by decide),
    walk_W13 h 3 1 2 (by decide),
    show gram28 τ 4 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 22)) = gram28 τ 4 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 2, 3]) (by decide),
    walk_W22 h 1 3 2 (by decide),
    show gram28 τ 4 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 23)) = gram28 τ 4 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 2, 3]) (by decide),
    walk_W25 h 2 3 1 (by decide),
    show gram28 τ 4 23 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_4_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 24)) = gram28 τ 4 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 0, 1, 2, 3]) (by decide),
    walk_W39 h 1 2 3 (by decide),
    show gram28 τ 4 24 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (-1, [1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_4_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 25)) = gram28 τ 4 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 0, 1, 2, 3]) (by decide),
    walk_X01 h 2 1 3 (by decide),
    show gram28 τ 4 25 = TracePoly.eval τ [(-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl]
  gram_nf

theorem gram_4_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 26)) = gram28 τ 4 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 0, 1, 2, 3]) (by decide),
    walk_S22 h 1 2 3 (by decide),
    show gram28 τ 4 26 = TracePoly.eval τ [(-1, [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0])] from rfl]
  gram_nf

theorem gram_4_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 4)) (W.pathVec (word28 27)) = gram28 τ 4 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 0, 3, 1, 2, 3]) (by decide),
    walk_S24 h 3 2 1 (by decide),
    show gram28 τ 4 27 = TracePoly.eval τ [(1, [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_5 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 5)) = gram28 τ 5 5 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 3, 2]) (by decide),
    walk_S11 h 2 3 1 (by decide),
    show gram28 τ 5 5 = TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 6)) = gram28 τ 5 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 3, 2]) (by decide),
    walk_X01 h 3 1 2 (by decide),
    show gram28 τ 5 6 = TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_5_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 7)) = gram28 τ 5 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 1, 3, 2]) (by decide),
    walk_W11 h 1 3 2 (by decide),
    show gram28 τ 5 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 8)) = gram28 τ 5 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 1, 3, 2]) (by decide),
    walk_W24 h 2 1 3 (by decide),
    show gram28 τ 5 8 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 9)) = gram28 τ 5 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 1, 3, 2]) (by decide),
    walk_W23 h 3 1 2 (by decide),
    show gram28 τ 5 9 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 10)) = gram28 τ 5 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 0, 1, 3, 2]) (by decide),
    walk_W44 h 2 3 1 (by decide),
    show gram28 τ 5 10 = TracePoly.eval τ [(1, [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 11)) = gram28 τ 5 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 2, 3]) (by decide),
    walk_S10 h 2 3 1 (by decide),
    show gram28 τ 5 11 = TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_5_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 12)) = gram28 τ 5 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 3, 2]) (by decide),
    walk_S11 h 2 3 1 (by decide),
    show gram28 τ 5 12 = TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 13)) = gram28 τ 5 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 1, 2, 3, 1]) (by decide),
    walk_S18 h 2 3 1 (by decide),
    show gram28 τ 5 13 = TracePoly.eval τ [(-1, [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 14)) = gram28 τ 5 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 1, 3, 2]) (by decide),
    walk_W13 h 2 1 3 (by decide),
    show gram28 τ 5 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 15)) = gram28 τ 5 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 1, 3, 2]) (by decide),
    walk_W25 h 3 2 1 (by decide),
    show gram28 τ 5 15 = TracePoly.eval τ [(-1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 16)) = gram28 τ 5 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 1, 3, 2]) (by decide),
    walk_W22 h 1 2 3 (by decide),
    show gram28 τ 5 16 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 17)) = gram28 τ 5 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 0, 1, 3, 2]) (by decide),
    walk_W41 h 3 1 2 (by decide),
    show gram28 τ 5 17 = TracePoly.eval τ [(1, [1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 18)) = gram28 τ 5 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 0, 1, 3, 2]) (by decide),
    walk_S22 h 1 3 2 (by decide),
    show gram28 τ 5 18 = TracePoly.eval τ [(-1, [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2])] from rfl]
  gram_nf

theorem gram_5_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 19)) = gram28 τ 5 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 3, 2]) (by decide),
    walk_X01 h 3 1 2 (by decide),
    show gram28 τ 5 19 = TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_5_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 20)) = gram28 τ 5 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 2, 3, 1, 2]) (by decide),
    walk_S23 h 2 3 1 (by decide),
    show gram28 τ 5 20 = TracePoly.eval τ [(-1, [0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 21)) = gram28 τ 5 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 1, 3, 2]) (by decide),
    walk_W12 h 3 1 2 (by decide),
    show gram28 τ 5 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_5_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 22)) = gram28 τ 5 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 1, 3, 2]) (by decide),
    walk_W21 h 1 3 2 (by decide),
    show gram28 τ 5 22 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (-1, [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 23)) = gram28 τ 5 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 3, 2]) (by decide),
    walk_W27 h 2 3 1 (by decide),
    show gram28 τ 5 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 24)) = gram28 τ 5 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 0, 1, 3, 2]) (by decide),
    walk_W40 h 1 2 3 (by decide),
    show gram28 τ 5 24 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (-1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_5_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 25)) = gram28 τ 5 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 0, 1, 3, 2]) (by decide),
    walk_S19 h 2 1 3 (by decide),
    show gram28 τ 5 25 = TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_5_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 26)) = gram28 τ 5 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 3, 2, 1]) (by decide),
    walk_X01 h 2 3 1 (by decide),
    show gram28 τ 5 26 = TracePoly.eval τ [(-2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])] from rfl]
  gram_nf

theorem gram_5_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 5)) (W.pathVec (word28 27)) = gram28 τ 5 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 0, 3, 1, 2, 3]) (by decide),
    walk_S21 h 2 3 1 (by decide),
    show gram28 τ 5 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]), (4, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0]), (-2, [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]), (-2, [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_6_6 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 6)) = gram28 τ 6 6 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 2, 1, 3]) (by decide),
    walk_S11 h 3 1 2 (by decide),
    show gram28 τ 6 6 = TracePoly.eval τ [(1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_7 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 7)) = gram28 τ 6 7 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 0, 2, 1, 3]) (by decide),
    walk_W12 h 1 2 3 (by decide),
    show gram28 τ 6 7 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_6_8 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 8)) = gram28 τ 6 8 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 0, 2, 1, 3]) (by decide),
    walk_W21 h 2 1 3 (by decide),
    show gram28 τ 6 8 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_9 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 9)) = gram28 τ 6 9 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 1, 3]) (by decide),
    walk_W27 h 3 1 2 (by decide),
    show gram28 τ 6 9 = TracePoly.eval τ [(1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_10 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 10)) = gram28 τ 6 10 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 1, 0, 2, 1, 3]) (by decide),
    walk_W40 h 2 3 1 (by decide),
    show gram28 τ 6 10 = TracePoly.eval τ [(2, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_11 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 11)) = gram28 τ 6 11 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 2, 3]) (by decide),
    walk_S19 h 3 1 2 (by decide),
    show gram28 τ 6 11 = TracePoly.eval τ [(2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_6_12 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 12)) = gram28 τ 6 12 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 3, 2]) (by decide),
    walk_X01 h 3 1 2 (by decide),
    show gram28 τ 6 12 = TracePoly.eval τ [(-2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])] from rfl]
  gram_nf

theorem gram_6_13 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 13)) = gram28 τ 6 13 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 1, 2, 3, 1]) (by decide),
    walk_S21 h 3 1 2 (by decide),
    show gram28 τ 6 13 = TracePoly.eval τ [(4, [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (-2, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0]), (-2, [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (1, [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_14 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 14)) = gram28 τ 6 14 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 0, 2, 1, 3]) (by decide),
    walk_W11 h 2 1 3 (by decide),
    show gram28 τ 6 14 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_6_15 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 15)) = gram28 τ 6 15 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 0, 2, 1, 3]) (by decide),
    walk_W24 h 3 2 1 (by decide),
    show gram28 τ 6 15 = TracePoly.eval τ [(1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_16 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 16)) = gram28 τ 6 16 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 2, 1, 3]) (by decide),
    walk_W23 h 1 2 3 (by decide),
    show gram28 τ 6 16 = TracePoly.eval τ [(1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_17 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 17)) = gram28 τ 6 17 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 0, 2, 0, 2, 1, 3]) (by decide),
    walk_W44 h 3 1 2 (by decide),
    show gram28 τ 6 17 = TracePoly.eval τ [(1, [0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_18 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 18)) = gram28 τ 6 18 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2, 0, 2, 1, 3]) (by decide),
    walk_S10 h 1 3 2 (by decide),
    show gram28 τ 6 18 = TracePoly.eval τ [(2, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (-1, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_6_19 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 19)) = gram28 τ 6 19 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 2, 1, 3]) (by decide),
    walk_S11 h 3 1 2 (by decide),
    show gram28 τ 6 19 = TracePoly.eval τ [(1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_20 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 20)) = gram28 τ 6 20 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 2, 3, 1, 2]) (by decide),
    walk_S18 h 3 1 2 (by decide),
    show gram28 τ 6 20 = TracePoly.eval τ [(-1, [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_6_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 21)) = gram28 τ 6 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 2, 1, 3]) (by decide),
    walk_W13 h 3 2 1 (by decide),
    show gram28 τ 6 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_6_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 22)) = gram28 τ 6 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 0, 2, 1, 3]) (by decide),
    walk_W25 h 1 3 2 (by decide),
    show gram28 τ 6 22 = TracePoly.eval τ [(-1, [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_6_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 23)) = gram28 τ 6 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 2, 1, 3]) (by decide),
    walk_W22 h 2 3 1 (by decide),
    show gram28 τ 6 23 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (-1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 24)) = gram28 τ 6 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 0, 2, 1, 3]) (by decide),
    walk_W41 h 1 2 3 (by decide),
    show gram28 τ 6 24 = TracePoly.eval τ [(1, [0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_6_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 25)) = gram28 τ 6 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 0, 2, 1, 3]) (by decide),
    walk_S22 h 2 1 3 (by decide),
    show gram28 τ 6 25 = TracePoly.eval τ [(-1, [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0])] from rfl]
  gram_nf

theorem gram_6_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 26)) = gram28 τ 6 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 0, 2, 1, 3]) (by decide),
    walk_X01 h 1 2 3 (by decide),
    show gram28 τ 6 26 = TracePoly.eval τ [(-2, [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl]
  gram_nf

theorem gram_6_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 6)) (W.pathVec (word28 27)) = gram28 τ 6 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 0, 3, 1, 2, 3]) (by decide),
    walk_S23 h 3 1 2 (by decide),
    show gram28 τ 6 27 = TracePoly.eval τ [(-1, [0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (2, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0])] from rfl]
  gram_nf


end AlbertSequential.LengthSeven.LemmaA
