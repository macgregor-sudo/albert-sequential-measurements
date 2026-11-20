/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Budget
public import FiveTest.ReflectedBudgetArithmetic
public import NativeAlbertTableMixtures
public import WordRelabelling

/-! Literal signed reflection transfer with the leading anchor kept in every word. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.FiveTest

open LengthSeven LengthSeven.LemmaA NativeAnalysis

/-- The marked copy of each chronological quadruple letter in the five tests. -/
def robustMarkedWord (u : Word Letter) : MarkedWord (Fin 5) :=
  relabelWord (fun i => (quadLetter i, quadRefl i)) u

private theorem robustMarkedWord_cost (u : Word Letter) :
    (quadCost u).1 = u.length + reflectionSwitchCount false (robustMarkedWord u) ∧
    (quadCost u).2 = u.length + reflectionSwitchCount true (robustMarkedWord u) := by
  induction u with
  | nil => exact ⟨rfl,rfl⟩
  | cons a u ih =>
      obtain ⟨h0,h1⟩ := ih
      rw [show robustMarkedWord (a :: u) =
        ((quadLetter a.1, quadRefl a.1), a.2) :: robustMarkedWord u from rfl]
      cases h : quadRefl a.1 <;>
        simp only [quadCost_cons, List.length_cons, h, Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, reflectionSwitchCount, h0,h1] <;> omega

theorem robustMarkedWord_budget (u : Word Letter) :
    (robustMarkedWord u).length + reflectionSwitchCount false (robustMarkedWord u) = budgetCost u := by
  change (relabelWord _ u).length + _ = _
  rw [relabelWord_length, ← (robustMarkedWord_cost u).1, quadCost_fst_eq_budgetCost]

/-- Signed tail expansion followed by the original yes on A. -/
def reflectedAnchoredTerms (u : Word Letter) : List (ℤ × Word (Fin 5)) :=
  (signedReflectionTerms 2 (robustMarkedWord u)).map (fun t => (t.1, (0,true) :: t.2))

theorem reflectedAnchoredTerms_eq (u : Word Letter) :
    signedReflectionTerms 2 (robustMarkedWord ((0,true) :: u)) = reflectedAnchoredTerms u := by rfl

theorem reflectedAnchoredTerms_horizon {u : Word Letter} (hu : budgetCost u ≤ 10)
    {m : ℤ × Word (Fin 5)} (hm : m ∈ reflectedAnchoredTerms u) :
    m.2.head? = some (0,true) ∧ m.2.length ≤ 11 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
  have hlen := (signedReflectionTerms_support 2 (robustMarkedWord u) t ht).2
  rw [robustMarkedWord_budget] at hlen
  exact ⟨rfl, Nat.succ_le_succ (hlen.trans hu)⟩

theorem reflectedAnchoredTerms_weight {u : Word Letter} (hu : budgetCost u ≤ 10) :
    ((reflectedAnchoredTerms u).map (fun m => m.1.natAbs)).sum ≤ 5^5 := by
  unfold reflectedAnchoredTerms
  rw [List.map_map]
  change ((signedReflectionTerms 2 (robustMarkedWord u)).map (fun m => m.1.natAbs)).sum ≤ _
  exact signedReflectionTerms_sumNatAbs_budget 2 (robustMarkedWord u)
    ((robustMarkedWord_budget u).symm ▸ hu)

/-- Evaluate a real table on a signed reflected expansion. -/
def reflectedAnchoredEvaluation (g : Word (Fin 5) → ℝ) (u : Word Letter) : ℝ :=
  ((reflectedAnchoredTerms u).map (fun m => (m.1 : ℝ) * g m.2)).sum

section Physical

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem quadModel_probability_eq_reflectedAnchoredEvaluation
    (M : AlgebraicProjectiveData (Fin 5) A) (u : Word Letter) :
    (quadModel M).probability ((0,true) :: u) = reflectedAnchoredEvaluation M.probability u := by
  have H : (markedProjectionMenu M.projection 2) ∘ (fun i => (quadLetter i, quadRefl i)) =
      quadProj M.projection := by
    funext i
    exact markedProjectionMenu_apply M.projection M.selfAdjoint 2 (quadLetter i, quadRefl i)
  change M.state (wordOperator (quadProj M.projection) ((0,true)::u)) = _
  rw [← H, ← wordOperator_relabel, show relabelWord _ ((0,true)::u) =
    robustMarkedWord ((0,true)::u) from rfl,
    signedReflectionTransfer_operator M.projection M.idempotent M.selfAdjoint,
    reflectedAnchoredTerms_eq, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_smul, smul_eq_mul,
    AlgebraicProjectiveData.probability, reflectedAnchoredEvaluation]

end Physical

private theorem sequentialEffect_relabel {E I J : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : J → E) (f : I → J) (u : Word I) :
    P.sequentialWordEffect p (relabelWord f u) = P.sequentialWordEffect (p ∘ f) u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      rw [relabelWord_cons, UnitalJordanProduct.sequentialWordEffect,
        UnitalJordanProduct.sequentialWordEffect, ih]
      rfl

private theorem nativeReflection_eq (x : Albert) :
    nativeAlbertProduct.idempotentReflection (pentadF 2) x = quadraticMap reflR x := by
  change nativeAlbertProduct.quadraticRepresentation reflR x = quadraticMap reflR x
  rw [UnitalJordanProduct.quadraticRepresentation_apply]
  simp only [quadraticMap, two_smul]
  rfl

theorem nativeQuad_probability_eq_reflectedAnchoredEvaluation (ρ : Albert) (u : Word Letter) :
    nativeWordProbability reflQuad ρ ((0,true)::u) =
      reflectedAnchoredEvaluation (nativeWordProbability pentadF ρ) u := by
  have H : markedJordanMenu nativeAlbertProduct pentadF 2 ∘
    (fun i => (quadLetter i, quadRefl i)) = reflQuad := by
    funext i
    fin_cases i <;> first
      | rfl
      | exact nativeReflection_eq _
  let P := nativeAlbertProduct
  have hp : P.product (pentadF 2) (pentadF 2) = pentadF 2 := (pentadF_isAtom 2).1
  rw [nativeWordProbability_eq_pairing, ← nativeAlbertProduct_wordEffect, ← H,
    ← sequentialEffect_relabel, show relabelWord _ ((0,true)::u) =
      robustMarkedWord ((0,true)::u) from rfl,
    signedReflectionTransfer_jordan P pentadF 2 hp, reflectedAnchoredTerms_eq]
  change tracePairingLin ρ _ = _
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def, reflectedAnchoredEvaluation]
  congr 1
  apply List.map_congr_left
  intro t _
  change tracePairing ρ ((t.1 : ℝ) • P.sequentialWordEffect pentadF t.2) =
    (t.1 : ℝ) * nativeWordProbability pentadF ρ t.2
  rw [tracePairing_smul_right, show P.sequentialWordEffect pentadF t.2 = _ from
    nativeAlbertProduct_wordEffect pentadF t.2, nativeWordProbability_eq_pairing]

end AlbertSequential.FiveTest
