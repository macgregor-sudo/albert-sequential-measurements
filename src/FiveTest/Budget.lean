/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Transfer
public import LengthSeven.LemmaA.Main
public import LengthSeven.Adapters
public import LengthSeven.NativeBinding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # The five-test budget, bound once

* The budget word set is Lemma A's `LemmaA.wordsBudget = {u | |u| + ν(u) ≤ 10}` (reflected
  letters `C, D`).  `quadCost_fst_eq_budgetCost`: the transfer cost `(quadCost u).1` of
  `FiveTest.Transfer` IS `budgetCost u = |u| + ν(u)`, so both modules use one budget.
* `wordsBudget_short`: every word of length at most five is within the budget
  (hypothesis (i) of lem:cer:gram28 for the budget; paper item (1) of "The budget"), from
  `|u| + ν(u) ≤ 2|u|`.
* `quadModel`: a representation of the five tests gives one of the quadruple
  `(P₀, P₁, ΣP₃Σ, ΣP₄Σ)` with the same state (lem:five:reflect(d)), and
  `quadModel_probability`: if it reproduces the five-test words of length `≤ L` from `ρ`, the
  quadruple representation reproduces every quadruple word with `|u| + ν(u) ≤ L` from `ρ`.
* `reflQuad_lemmaA`: a representation of the quadruple reproducing the budget words from `p₀`
  satisfies the conclusion of Lemma A (all 784 Gram entries), given the native table values
  `TableValues (nativeTraceData reflQuad) (nativeWordProbability reflQuad p₀)` as an explicit
  hypothesis (discharged in `FiveTest.Main` by `tableValues_native`). -/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.LemmaA
open AlbertSequential.NativeAnalysis

/-! ## The cost function is the budget function -/

theorem quadRefl_eq_budgetRefl : quadRefl = budgetRefl := rfl

/-- `[last letter reflected]`, as in `budgetNu`. -/
def lastRefl (u : Word Letter) : ℕ :=
  match u.getLast? with | some a => if budgetRefl a.1 then 1 else 0 | none => 0

theorem budgetNu_eq (u : Word Letter) : budgetNu u = 2 * budgetRuns false u - lastRefl u := rfl

theorem budgetRuns_cons (prev : Bool) (a : Outcome Letter) (u : Word Letter) :
    budgetRuns prev (a :: u) = (if budgetRefl a.1 && !prev then 1 else 0) + budgetRuns (budgetRefl a.1) u :=
  rfl

theorem quadCost_cons (a : Outcome Letter) (u : Word Letter) :
    quadCost (a :: u) = if quadRefl a.1 then ((quadCost u).2 + 2, (quadCost u).2 + 1)
      else ((quadCost u).1 + 1, (quadCost u).1 + 2) := rfl

theorem quadCost_spec (u : Word Letter) :
    (quadCost u).1 + lastRefl u = u.length + 2 * budgetRuns false u ∧
    (quadCost u).2 + lastRefl u = u.length + 2 * budgetRuns true u + (if u = [] then 0 else 1) ∧
    lastRefl u ≤ 2 * budgetRuns false u := by
  induction u with
  | nil => simp [quadCost, lastRefl, budgetRuns]
  | cons a w ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      rcases w with _ | ⟨b, w'⟩
      · cases h : budgetRefl a.1 <;>
          simp [quadCost, lastRefl, budgetRuns, quadRefl_eq_budgetRefl, h]
      · have hl : lastRefl (a :: b :: w') = lastRefl (b :: w') := by
          simp only [lastRefl, List.getLast?_cons_cons]
        rw [hl]
        have hne : (b :: w' : Word Letter) ≠ [] := List.cons_ne_nil _ _
        simp only [hne, ↓reduceIte] at ih2
        have hlen : (a :: b :: w').length = (b :: w').length + 1 := rfl
        have hle : lastRefl (b :: w') ≤ 1 := by
          unfold lastRefl; split
          · split <;> omega
          · omega
        have hRf := budgetRuns_cons false a (b :: w')
        have hRt := budgetRuns_cons true a (b :: w')
        have hQ1 : (quadCost (a :: b :: w')).1 = if quadRefl a.1 then (quadCost (b :: w')).2 + 2
            else (quadCost (b :: w')).1 + 1 := by rw [quadCost_cons]; split <;> rfl
        have hQ2 : (quadCost (a :: b :: w')).2 = if quadRefl a.1 then (quadCost (b :: w')).2 + 1
            else (quadCost (b :: w')).1 + 2 := by rw [quadCost_cons]; split <;> rfl
        simp only [reduceCtorEq, ↓reduceIte, List.cons_ne_nil, ite_false]
        rw [quadRefl_eq_budgetRefl] at hQ1 hQ2
        cases h : budgetRefl a.1 <;> simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
            Bool.not_false, Bool.and_true, Bool.not_true, Bool.and_false, Bool.true_and] at hRf hRt hQ1 hQ2 <;>
          refine ⟨by omega, by omega, by omega⟩

/-- The transfer cost is the budget cost `|u| + ν(u)`. -/
theorem quadCost_fst_eq_budgetCost (u : Word Letter) : (quadCost u).1 = budgetCost u := by
  obtain ⟨h1, -, h3⟩ := quadCost_spec u
  rw [budgetCost, budgetNu_eq]
  omega

theorem quadCost_le (u : Word Letter) : (quadCost u).1 ≤ 2 * u.length ∧ (quadCost u).2 ≤ 2 * u.length := by
  induction u with
  | nil => simp [quadCost]
  | cons a w ih =>
      simp only [quadCost, List.length_cons]
      split <;> constructor <;> omega

/-- Hypothesis (i) of lem:cer:gram28 for the budget: words of length `≤ 5` are within it. -/
theorem wordsBudget_short (u : Word Letter) (hu : u.length ≤ 5) : u ∈ wordsBudget := by
  change budgetCost u ≤ 10
  rw [← quadCost_fst_eq_budgetCost]
  have := (quadCost_le u).1
  omega

/-! ## Conditioning on a certain first outcome -/

section Model

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- If `Pr(A) = 1` then a leading yes on `A` does not change any word probability
(the conditioned vector satisfies `P_A ξ = ξ`; Cauchy–Schwarz for the state). -/
theorem prob_cons_yesA (M : AlgebraicProjectiveData Letter A)
    (h1 : M.probability [(0, true)] = 1) (u : Word Letter) :
    M.probability ((0, true) :: u) = M.probability u := by
  set P0 := M.projection 0 with hP0
  have hidem : P0 * P0 = P0 := M.idempotent 0
  have hst : star P0 = P0 := M.selfAdjoint 0
  have hstate1 : M.state P0 = 1 := by
    rw [← h1, probability_yesA, hst, hidem]
  have hpos : 0 < M.probability [(0, true)] := by rw [h1]; exact one_pos
  let W := WalkForm.ofAlgebraic M hpos
  have hform : ∀ X Y : A, W.form X Y = M.state (star X * Y) := by
    intro X Y
    change algForm M (M.probability [(0, true)])⁻¹ X Y = _
    rw [algForm_apply, h1, inv_one, one_mul]
  have hz : W.form (1 - P0) (1 - P0) = 0 := by
    rw [hform, star_sub, star_one, hst, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul,
      hidem, sub_self, sub_zero, map_sub, M.state_unit, hstate1, sub_self]
  have hleft : ∀ Y : A, M.state ((1 - P0) * Y) = 0 := by
    intro Y
    have := W.null_pair (1 - P0) hz Y
    rwa [hform, star_sub, star_one, hst] at this
  have hright : ∀ Y : A, M.state (Y * (1 - P0)) = 0 := by
    intro Y
    rw [← M.state_star, star_mul, star_sub, star_one, hst]
    exact hleft _
  change M.state (wordOperator M.projection ((0, true) :: u)) = M.state (wordOperator M.projection u)
  rw [wordOperator_cons M.projection M.selfAdjoint]
  have hout : algebraicOutcome M.projection (0, true) = P0 := rfl
  rw [hout]
  set Z := wordOperator M.projection u
  have hdec : Z = P0 * Z * P0 + ((1 - P0) * Z + (P0 * Z) * (1 - P0)) := by noncomm_ring
  conv_rhs => rw [hdec]
  rw [map_add, map_add, hleft, hright, add_zero, add_zero]

/-- A representation of the five tests gives one of the reflected quadruple with the same
state (lem:five:reflect(b,d)): projections `(P₀, P₁, ΣP₃Σ, ΣP₄Σ)`, `Σ = 2P₂ − 1`. -/
def quadModel (M : AlgebraicProjectiveData (Fin 5) A) : AlgebraicProjectiveData Letter A where
  projection := quadProj M.projection
  idempotent := quadProj_idem M.projection M.idempotent M.selfAdjoint
  selfAdjoint := quadProj_star M.projection M.idempotent M.selfAdjoint
  state := M.state
  state_unit := M.state_unit
  state_star := M.state_star
  state_positive := M.state_positive

/-- The trace pairing with a fixed state, as a linear functional. -/
def tracePairingLin (ρ : Albert) : Albert →ₗ[ℝ] ℝ where
  toFun := tracePairing ρ
  map_add' := tracePairing_add_right ρ
  map_smul' r x := by rw [tracePairing_smul_right, smul_eq_mul, RingHom.id_apply]

/-- **lem:five:reflect(d) with cost.**  If the five-test representation reproduces from `ρ` every
five-test word of length `≤ L`, the quadruple representation reproduces from `ρ` every quadruple
word with `|u| + ν(u) ≤ L`. -/
theorem quadModel_probability (M : AlgebraicProjectiveData (Fin 5) A) (ρ : Albert) (L : ℕ)
    (hM : ∀ w : Word (Fin 5), w.length ≤ L → M.probability w = nativeWordProbability pentadF ρ w)
    (u : Word Letter) (hu : budgetCost u ≤ L) :
    (quadModel M).probability u = nativeWordProbability reflQuad ρ u := by
  have hl := (quad_lift M.projection M.idempotent M.selfAdjoint u).1
  rw [quadCost_fst_eq_budgetCost] at hl
  have hl' := liftSpace_mono M.projection (nativeWordEffect pentadF) hu hl
  have hmatch : ∀ w : Word (Fin 5), w.length ≤ L →
      M.state (wordOperator M.projection w) = tracePairingLin ρ (nativeWordEffect pentadF w) := by
    intro w hw
    change M.probability w = tracePairing ρ _
    rw [hM w hw, nativeWordProbability_eq_pairing]
  have := liftSpace_expectation M.projection (nativeWordEffect pentadF) M.state
    (tracePairingLin ρ) hmatch hl'
  change M.state (wordOperator (quadProj M.projection) u) = _
  rw [this, nativeWordProbability_eq_pairing]
  rfl

/-- **Lemma A on the budget, for the reflected quadruple.**  A representation of `(A,B,C,D)`
that reproduces from `p₀` every word with `|u| + ν(u) ≤ 10` has `Pr(A) = 1`, and its conditioned
walk form has the Gram matrix `gram28` of the native traces on `𝒲₂₈` (conditional on the
native table values `hTV`). -/
theorem reflQuad_lemmaA
    (hTV : TableValues (nativeTraceData reflQuad) (nativeWordProbability reflQuad (reflQuad 0)))
    (M : AlgebraicProjectiveData Letter A)
    (hM : ∀ u ∈ wordsBudget, M.probability u = nativeWordProbability reflQuad (reflQuad 0) u) :
    ∃ h : 0 < M.probability [(0, true)], ∀ i j : Fin 28,
      (WalkForm.ofAlgebraic M h).form ((WalkForm.ofAlgebraic M h).pathVec (word28 i))
        ((WalkForm.ofAlgebraic M h).pathVec (word28 j)) = gram28 (nativeTraceData reflQuad) i j := by
  have h1 : M.probability [(0, true)] = 1 := by
    rw [hM [(0, true)] (by decide), hTV.yesA_head [], hTV.empty]
  have hpos : 0 < M.probability [(0, true)] := by rw [h1]; exact one_pos
  refine ⟨hpos, fun i j => lemmaA_budget ?_ hTV i j⟩
  apply WalkForm.ofAlgebraic_reproduces
  intro u hu
  rw [h1, div_one, prob_cons_yesA M h1, hM u hu]

end Model

end AlbertSequential.FiveTest
