/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.Walks
public import LengthSeven.LemmaA.Table

/-! # Lemma A: Gram entries (frame D rows)

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

theorem gram_21_21 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 21)) = gram28 τ 21 21 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3]) (by decide),
    walk_W02 h 3 1 2 (by decide),
    show gram28 τ 21 21 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_21_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 22)) = gram28 τ 21 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3]) (by decide),
    walk_W03 h 1 3 2 (by decide),
    show gram28 τ 21 22 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_21_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 23)) = gram28 τ 21 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3]) (by decide),
    walk_W03 h 2 3 1 (by decide),
    show gram28 τ 21 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_21_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 24)) = gram28 τ 21 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 0, 2, 1]) (by decide),
    walk_W08 h 3 2 1 (by decide),
    show gram28 τ 21 24 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_21_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 25)) = gram28 τ 21 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3]) (by decide),
    walk_W05 h 2 1 3 (by decide),
    show gram28 τ 21 25 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_21_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 26)) = gram28 τ 21 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3]) (by decide),
    walk_W05 h 1 2 3 (by decide),
    show gram28 τ 21 26 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_21_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 21)) (W.pathVec (word28 27)) = gram28 τ 21 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 1, 2, 3]) (by decide),
    walk_W10 h 3 1 2 (by decide),
    show gram28 τ 21 27 = TracePoly.eval τ [(1, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_22_22 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 22)) = gram28 τ 22 22 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 1]) (by decide),
    walk_W04 h 1 3 2 (by decide),
    show gram28 τ 22 22 = TracePoly.eval τ [(1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_22_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 23)) = gram28 τ 22 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 2]) (by decide),
    walk_W05 h 1 3 2 (by decide),
    show gram28 τ 22 23 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_22_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 24)) = gram28 τ 22 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 1]) (by decide),
    walk_W18 h 1 2 3 (by decide),
    show gram28 τ 22 24 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_22_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 25)) = gram28 τ 22 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 1, 2]) (by decide),
    walk_W09 h 1 3 2 (by decide),
    show gram28 τ 22 25 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_22_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 26)) = gram28 τ 22 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1]) (by decide),
    walk_W10 h 1 2 3 (by decide),
    show gram28 τ 22 26 = TracePoly.eval τ [(1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_22_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 22)) (W.pathVec (word28 27)) = gram28 τ 22 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 3, 1, 2, 3]) (by decide),
    walk_W19 h 1 3 2 (by decide),
    show gram28 τ 22 27 = TracePoly.eval τ [(1, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_23_23 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 23)) = gram28 τ 23 23 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2]) (by decide),
    walk_W04 h 2 3 1 (by decide),
    show gram28 τ 23 23 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_23_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 24)) = gram28 τ 23 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 0, 2, 1]) (by decide),
    walk_W15 h 2 3 1 (by decide),
    show gram28 τ 23 24 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (-1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_23_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 25)) = gram28 τ 23 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 2]) (by decide),
    walk_W10 h 2 1 3 (by decide),
    show gram28 τ 23 25 = TracePoly.eval τ [(1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_23_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 26)) = gram28 τ 23 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 2, 1]) (by decide),
    walk_W09 h 2 3 1 (by decide),
    show gram28 τ 23 26 = TracePoly.eval τ [(1, [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_23_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 23)) (W.pathVec (word28 27)) = gram28 τ 23 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 3, 1, 2, 3]) (by decide),
    walk_W20 h 2 3 1 (by decide),
    show gram28 τ 23 27 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (-1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0])] from rfl]
  gram_nf

theorem gram_24_24 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 24)) (W.pathVec (word28 24)) = gram28 τ 24 24 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 0, 2, 1]) (by decide),
    walk_W34 h 1 2 3 (by decide),
    show gram28 τ 24 24 = TracePoly.eval τ [(1, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_24_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 24)) (W.pathVec (word28 25)) = gram28 τ 24 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 1, 2]) (by decide),
    walk_W25 h 1 2 3 (by decide),
    show gram28 τ 24 25 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (-1, [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_24_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 24)) (W.pathVec (word28 26)) = gram28 τ 24 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 2, 1]) (by decide),
    walk_W27 h 1 2 3 (by decide),
    show gram28 τ 24 26 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_24_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 24)) (W.pathVec (word28 27)) = gram28 τ 24 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 0, 3, 1, 2, 3]) (by decide),
    walk_W35 h 1 2 3 (by decide),
    show gram28 τ 24 27 = TracePoly.eval τ [(-2, [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (1, [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0])] from rfl]
  gram_nf

theorem gram_25_25 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 25)) (W.pathVec (word28 25)) = gram28 τ 25 25 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [2, 1, 3, 1, 2]) (by decide),
    walk_S05 h 2 1 3 (by decide),
    show gram28 τ 25 25 = TracePoly.eval τ [(1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_25_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 25)) (W.pathVec (word28 26)) = gram28 τ 25 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1, 2]) (by decide),
    walk_W20 h 1 2 3 (by decide),
    show gram28 τ 25 26 = TracePoly.eval τ [(2, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (-1, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])] from rfl]
  gram_nf

theorem gram_25_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 25)) (W.pathVec (word28 27)) = gram28 τ 25 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 3, 1, 2]) (by decide),
    walk_S06 h 3 2 1 (by decide),
    show gram28 τ 25 27 = TracePoly.eval τ [(1, [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_26_26 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 26)) (W.pathVec (word28 26)) = gram28 τ 26 26 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 2, 1]) (by decide),
    walk_S05 h 1 2 3 (by decide),
    show gram28 τ 26 26 = TracePoly.eval τ [(1, [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf

theorem gram_26_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 26)) (W.pathVec (word28 27)) = gram28 τ 26 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [1, 2, 3, 1, 2, 3]) (by decide),
    walk_S16 h 1 2 3 (by decide),
    show gram28 τ 26 27 = TracePoly.eval τ [(-1, [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0])] from rfl]
  gram_nf

theorem gram_27_27 (h : UsedRules W τ) :
    W.form (W.pathVec (word28 27)) (W.pathVec (word28 27)) = gram28 τ 27 27 := by
  rw [W.form_pathVec, L_eq_of_canon W (b := [3, 2, 1, 3, 1, 2, 3]) (by decide),
    walk_S13 h 3 2 1 (by decide),
    show gram28 τ 27 27 = TracePoly.eval τ [(1, [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0])] from rfl]
  gram_nf


end AlbertSequential.LengthSeven.LemmaA
