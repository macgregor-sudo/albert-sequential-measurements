/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.WordsAndCertificates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.EqualityCountermodels

/-- A deterministic test reads a bit and updates the state while preserving the bit it read. -/
structure RepeatableProcess (I S : Type*) where
  outcome : I → S → Bool
  next : I → S → S
  stable : ∀ i s, outcome i (next i s) = outcome i s

def RepeatableProcess.run {I S : Type*} (M : RepeatableProcess I S) (s : S) : Word I → Option S
  | [] => some s
  | (i, b) :: w => if M.outcome i s = b then M.run (M.next i s) w else none

def RepeatableProcess.probability {I S : Type*} (M : RepeatableProcess I S) (s : S) (w : Word I) : ℝ :=
  if (M.run s w).isSome then 1 else 0

private theorem RepeatableProcess.run_append {I S : Type*} (M : RepeatableProcess I S)
    (s : S) (u v : Word I) :
    M.run s (u ++ v) = (M.run s u).bind (fun t => M.run t v) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih =>
    rcases a with ⟨i, b⟩
    simp only [List.cons_append, RepeatableProcess.run]
    split
    · exact ih _
    · rfl

/-- The three families of printed basic equalities, at all finite word lengths. -/
def BasicWordEqualities {I : Type*} (P : Word I → ℝ) : Prop :=
  (∀ u i, P (u ++ [(i, true)]) + P (u ++ [(i, false)]) = P u) ∧
  (∀ u v i b, P (u ++ [(i, b), (i, b)] ++ v) = P (u ++ [(i, b)] ++ v)) ∧
  (∀ u v i b, P (u ++ [(i, b), (i, !b)] ++ v) = 0)

private theorem RepeatableProcess.run_repeated {I S : Type*} (M : RepeatableProcess I S)
    (hid : ∀ i s, M.next i (M.next i s) = M.next i s)
    (s : S) (i : I) (b : Bool) (v : Word I) :
    M.run s ((i, b) :: (i, b) :: v) = M.run s ((i, b) :: v) := by
  simp only [RepeatableProcess.run]
  split
  · rename_i he
    rw [M.stable, ite_eq_left he, hid]
  · rfl

/-- The two printed witnesses are even idempotent as state updates. -/
theorem RepeatableProcess.basicWordEqualities {I S : Type*} (M : RepeatableProcess I S)
    (hid : ∀ i s, M.next i (M.next i s) = M.next i s) (s : S) :
    BasicWordEqualities (M.probability s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u i
    simp only [RepeatableProcess.probability, M.run_append]
    cases hu : M.run s u with
    | none => simp
    | some t =>
      cases hi : M.outcome i t <;> simp [RepeatableProcess.run, hi]
  · intro u v i b
    simp only [List.append_assoc, RepeatableProcess.probability, M.run_append, List.cons_append,
      List.nil_append]
    cases hu : M.run s u with
    | none => rfl
    | some t =>
      change (if (M.run t ((i, b) :: (i, b) :: v)).isSome then (1 : ℝ) else 0) =
        (if (M.run t ((i, b) :: v)).isSome then 1 else 0)
      rw [M.run_repeated hid]
  · intro u v i b
    simp only [List.append_assoc, RepeatableProcess.probability, M.run_append,
      List.cons_append, List.nil_append]
    cases hu : M.run s u with
    | none => rfl
    | some t =>
      change (if (M.run t ((i, b) :: (i, !b) :: v)).isSome then (1 : ℝ) else 0) = 0
      simp only [RepeatableProcess.run, M.stable]
      cases b <;> cases M.outcome i t <;> rfl

/-- Test zero reads the first bit and clears the second. Test one reads the second bit. -/
def resetSecond : RepeatableProcess (Fin 2) (Bool × Bool) where
  outcome i s := if i = 0 then s.1 else s.2
  next i s := if i = 0 then (s.1, false) else s
  stable := by intro i s; split <;> simp_all

/-- Test one reads the second bit and clears the first on yes. Test zero reads the first bit. -/
def resetFirstOnYes : RepeatableProcess (Fin 2) (Bool × Bool) where
  outcome i s := if i = 0 then s.1 else s.2
  next i s := if i = 1 ∧ s.2 = true then (false, s.2) else s
  stable := by
    intro i s
    rcases s with ⟨x, y⟩
    fin_cases i <;> cases y <;> rfl

theorem resetSecond_basic : BasicWordEqualities (resetSecond.probability (true, true)) := by
  apply resetSecond.basicWordEqualities
  intro i s
  fin_cases i <;> cases s <;> rfl

theorem resetFirstOnYes_basic : BasicWordEqualities (resetFirstOnYes.probability (true, true)) := by
  apply resetFirstOnYes.basicWordEqualities
  intro i s
  fin_cases i
  · rfl
  · rcases s with ⟨x,y⟩
    cases y <;> rfl

/-- The two sides of the first additional equality on the printed repeatable process. -/
theorem resetSecond_extraOne :
    let P := resetSecond.probability (true, true)
    P [(0, false), (1, true)] - P [(0, true), (1, true)] - P [(1, true)] = -1 ∧
    P [(1, false), (0, true)] - P [(1, true), (0, true)] - P [(0, true)] = -2 := by
  norm_num [RepeatableProcess.probability, RepeatableProcess.run, resetSecond]

/-- The two sides of the second additional equality on the printed repeatable process. -/
theorem resetFirstOnYes_extraTwo :
    let P := resetFirstOnYes.probability (true, true)
    P [(0, true), (1, true), (0, false)] = 1 ∧
    P [(0, true), (1, false), (0, false)] = 0 := by
  norm_num [RepeatableProcess.probability, RepeatableProcess.run, resetFirstOnYes]

theorem basicWordEqualities_do_not_imply_extraOne :
    ¬ (∀ P : Word (Fin 2) → ℝ, BasicWordEqualities P →
      P [(0, false), (1, true)] - P [(0, true), (1, true)] - P [(1, true)] =
        P [(1, false), (0, true)] - P [(1, true), (0, true)] - P [(0, true)]) := by
  intro h
  have he := h _ resetSecond_basic
  rw [resetSecond_extraOne.1, resetSecond_extraOne.2] at he
  norm_num at he

theorem basicWordEqualities_do_not_imply_extraTwo :
    ¬ (∀ P : Word (Fin 2) → ℝ, BasicWordEqualities P →
      P [(0, true), (1, true), (0, false)] = P [(0, true), (1, false), (0, false)]) := by
  intro h
  have he := h _ resetFirstOnYes_basic
  rw [resetFirstOnYes_extraTwo.1, resetFirstOnYes_extraTwo.2] at he
  norm_num at he

def relabelTable {I J : Type*} (f : I → J) (P : Word J → ℝ) (w : Word I) : ℝ :=
  P (w.map fun a => (f a.1, a.2))

theorem BasicWordEqualities.relabel {I J : Type*} {P : Word J → ℝ}
    (h : BasicWordEqualities P) (f : I → J) : BasicWordEqualities (relabelTable f P) := by
  obtain ⟨hA, hR, hO⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro u i
    simpa only [relabelTable, List.map_append, List.map_cons, List.map_nil] using hA _ (f i)
  · intro u v i b
    simpa only [relabelTable, List.map_append, List.map_cons, List.map_nil] using hR _ _ (f i) b
  · intro u v i b
    simpa only [relabelTable, List.map_append, List.map_cons, List.map_nil] using hO _ _ (f i) b

/-- The first nonconsequence holds for every selected pair of distinct labels. -/
theorem basicWordEqualities_do_not_imply_extraOne_at {I : Type*} {i j : I} (hij : i ≠ j) :
    ¬ (∀ P : Word I → ℝ, BasicWordEqualities P →
      P [(i, false), (j, true)] - P [(i, true), (j, true)] - P [(j, true)] =
        P [(j, false), (i, true)] - P [(j, true), (i, true)] - P [(i, true)]) := by
  classical
  let f : I → Fin 2 := fun k => if k = i then 0 else 1
  have hi : f i = 0 := by simp [f]
  have hj : f j = 1 := by simp [f, hij.symm]
  intro h
  have he := h _ (resetSecond_basic.relabel f)
  simp only [relabelTable, List.map_cons, List.map_nil, hi, hj] at he
  rw [resetSecond_extraOne.1, resetSecond_extraOne.2] at he
  norm_num at he

/-- The second nonconsequence also holds for every selected pair of distinct labels. -/
theorem basicWordEqualities_do_not_imply_extraTwo_at {I : Type*} {i j : I} (hij : i ≠ j) :
    ¬ (∀ P : Word I → ℝ, BasicWordEqualities P →
      P [(i, true), (j, true), (i, false)] = P [(i, true), (j, false), (i, false)]) := by
  classical
  let f : I → Fin 2 := fun k => if k = i then 0 else 1
  have hi : f i = 0 := by simp [f]
  have hj : f j = 1 := by simp [f, hij.symm]
  intro h
  have he := h _ (resetFirstOnYes_basic.relabel f)
  simp only [relabelTable, List.map_cons, List.map_nil, hi, hj] at he
  rw [resetFirstOnYes_extraTwo.1, resetFirstOnYes_extraTwo.2] at he
  norm_num at he

end AlbertSequential.EqualityCountermodels
