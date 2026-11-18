/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SupportedPurityLeaves
public import RealWordFunctionals
public import Mathlib.Tactic.FieldSimp

/-! Constructive finite separators from an explicit supplied residual telescope.
The telescope and native residual-zero/margin bindings are not inferred here.
Occurrences and genuine-word left expansions remain explicit finite data. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure ResidualTelescopeOccurrence (n : ℕ) where
  leaf : SupportedPurityLeaf (Fin n)
  leftTerms : FiniteRealWordFunctional n

namespace ResidualTelescopeOccurrence
variable {n : ℕ} (o : ResidualTelescopeOccurrence n)

def leftElement {A : Type*} [Ring A] [Module ℝ A] (P : Fin n → A) : A :=
  o.leftTerms.amplitudeValue P

def coefficientBound : ℝ := o.leftTerms.rawCoefficientBound

end ResidualTelescopeOccurrence

def residualCoefficientBudget {n : ℕ} (occ : List (ResidualTelescopeOccurrence n)) : ℝ :=
  (occ.map (fun o => o.coefficientBound ^ 2)).sum

theorem residualCoefficientBudget_nonneg {n : ℕ} (occ : List (ResidualTelescopeOccurrence n)) :
    0 ≤ residualCoefficientBudget occ := by
  induction occ with
  | nil => exact le_refl _
  | cons o occ ih => exact add_nonneg (sq_nonneg _) ih

def residualPenaltyParameter {n : ℕ} (occ : List (ResidualTelescopeOccurrence n)) (m : ℝ) : ℝ :=
  (residualCoefficientBudget occ + 1) / (2 * m)

theorem residualPenaltyParameter_pos {n : ℕ} (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m) : 0 < residualPenaltyParameter occ m := by
  apply div_pos
  · linarith [residualCoefficientBudget_nonneg occ]
  · positivity

theorem residualPenalty_remainder {n : ℕ} (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m) :
    residualCoefficientBudget occ / (4 * residualPenaltyParameter occ m) ≤ m / 2 := by
  have ha := residualPenaltyParameter_pos occ m hm
  have hden : 0 < 4 * residualPenaltyParameter occ m := by positivity
  apply (div_le_iff₀ hden).mpr
  have hvalue : m / 2 * (4 * residualPenaltyParameter occ m) =
      residualCoefficientBudget occ + 1 := by
    unfold residualPenaltyParameter
    field_simp
    ring
  rw [hvalue]
  linarith

def residualSumFunctional {n : ℕ} (occ : List (ResidualTelescopeOccurrence n)) :
    FiniteRealWordFunctional n :=
  FiniteRealWordFunctional.combine (occ.map (fun o => o.leaf.wordFunctional))

theorem residualSumFunctional_evaluate {n : ℕ} (occ : List (ResidualTelescopeOccurrence n))
    (f : Word (Fin n) → ℝ) :
    (residualSumFunctional occ).evaluate f =
      (occ.map (fun o => o.leaf.wordFunctional.evaluate f)).sum := by
  simp only [residualSumFunctional, FiniteRealWordFunctional.evaluate_combine,
    List.map_map, Function.comp_def]

def constructiveResidualSeparator {n : ℕ} (base : FiniteRealWordFunctional n)
    (occ : List (ResidualTelescopeOccurrence n)) (m : ℝ) : FiniteRealWordFunctional n :=
  FiniteRealWordFunctional.append
    (FiniteRealWordFunctional.append
      (FiniteRealWordFunctional.scale (residualPenaltyParameter occ m) (residualSumFunctional occ))
      (FiniteRealWordFunctional.scale (-1) base))
    (FiniteRealWordFunctional.emptyWordTerm (m / 2))

theorem constructiveResidualSeparator_evaluate {n : ℕ} (base : FiniteRealWordFunctional n)
    (occ : List (ResidualTelescopeOccurrence n)) (m : ℝ) (f : Word (Fin n) → ℝ) :
    (constructiveResidualSeparator base occ m).evaluate f =
      residualPenaltyParameter occ m * (occ.map (fun o => o.leaf.wordFunctional.evaluate f)).sum -
      base.evaluate f + (m / 2) * f [] := by
  simp only [constructiveResidualSeparator, FiniteRealWordFunctional.evaluate_append,
    FiniteRealWordFunctional.evaluate_scale, residualSumFunctional_evaluate,
    FiniteRealWordFunctional.evaluate_emptyWordTerm]
  ring

namespace AlgebraicProjectiveData
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData ι A)

theorem positiveSquare_young (U r : A) (a : ℝ) (ha : 0 < a) :
    M.state (star U * r) ≤ a * M.squareMass r + M.squareMass U / (4 * a) := by
  have hp := M.state_positive ((2 * a) • r - U)
  have hexpand : M.state (star ((2 * a) • r - U) * ((2 * a) • r - U)) =
      4 * a ^ 2 * M.squareMass r - 4 * a * M.state (star U * r) + M.squareMass U := by
    simp only [star_sub, star_smul, star_trivial, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, map_sub, map_smul, smul_eq_mul, squareMass]
    rw [positiveForm_symmetric M.state M.state_star r U]
    ring
  rw [hexpand] at hp
  have hscaled : (4 * a) * M.state (star U * r) ≤
      4 * a ^ 2 * M.squareMass r + M.squareMass U := by linarith
  have hden : 0 < 4 * a := by positivity
  have hscaled' : M.state (star U * r) * (4 * a) ≤
      4 * a ^ 2 * M.squareMass r + M.squareMass U := by
    calc
      M.state (star U * r) * (4 * a) = (4 * a) * M.state (star U * r) := mul_comm _ _
      _ ≤ _ := hscaled
  have h := (le_div_iff₀ hden).mpr hscaled'
  calc
    M.state (star U * r) ≤
        (4 * a ^ 2 * M.squareMass r + M.squareMass U) / (4 * a) := h
    _ = _ := by field_simp

end AlgebraicProjectiveData

section ModelEstimate
variable {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData (Fin n) A)

theorem residualOccurrence_young (o : ResidualTelescopeOccurrence n) (a : ℝ) (ha : 0 < a) :
    M.state (star (o.leftElement M.projection) * o.leaf.residualElement M.projection) ≤
      a * o.leaf.wordFunctional.evaluate M.probability + o.coefficientBound ^ 2 / (4 * a) := by
  have hU : M.squareMass (o.leftElement M.projection) ≤ o.coefficientBound ^ 2 :=
    M.amplitudeCombination_squareMass_bound o.leftTerms.terms
  calc
    M.state (star (o.leftElement M.projection) * o.leaf.residualElement M.projection) ≤
        a * M.squareMass (o.leaf.residualElement M.projection) +
          M.squareMass (o.leftElement M.projection) / (4 * a) :=
      M.positiveSquare_young _ _ a ha
    _ ≤ a * M.squareMass (o.leaf.residualElement M.projection) +
          o.coefficientBound ^ 2 / (4 * a) := by
      have hdiv : M.squareMass (o.leftElement M.projection) / (4 * a) ≤
          o.coefficientBound ^ 2 / (4 * a) :=
        div_le_div_of_nonneg_right hU (show 0 ≤ 4 * a by positivity)
      exact add_le_add (le_refl _) hdiv
    _ = _ := by rw [o.leaf.residual_eq_wordFunctional M]

theorem residualTelescope_sum_le (occ : List (ResidualTelescopeOccurrence n))
    (a : ℝ) (ha : 0 < a) :
    (occ.map (fun o => M.state
      (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum ≤
      a * (occ.map (fun o => o.leaf.wordFunctional.evaluate M.probability)).sum +
        residualCoefficientBudget occ / (4 * a) := by
  induction occ with
  | nil => simp only [List.map_nil, List.sum_nil, residualCoefficientBudget, mul_zero, zero_div, add_zero, le_refl]
  | cons o occ ih =>
      simp only [List.map_cons, List.sum_cons, residualCoefficientBudget] at ih ⊢
      calc
        _ ≤ (a * o.leaf.wordFunctional.evaluate M.probability + o.coefficientBound ^ 2 / (4 * a)) +
            (a * (occ.map (fun o => o.leaf.wordFunctional.evaluate M.probability)).sum +
              (occ.map (fun o => o.coefficientBound ^ 2)).sum / (4 * a)) :=
          add_le_add (residualOccurrence_young M o a ha) ih
        _ = _ := by ring

theorem constructiveResidualSeparator_model_nonnegative
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m)
    (hTelescope : base.evaluate M.probability =
      (occ.map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum) :
    0 ≤ (constructiveResidualSeparator base occ m).evaluate M.probability := by
  have ha := residualPenaltyParameter_pos occ m hm
  have hbound : base.evaluate M.probability ≤
      residualPenaltyParameter occ m *
        (occ.map (fun o => o.leaf.wordFunctional.evaluate M.probability)).sum + m / 2 := by
    rw [hTelescope]
    exact (residualTelescope_sum_le M occ _ ha).trans
      (add_le_add (le_refl _) (residualPenalty_remainder occ m hm))
  rw [constructiveResidualSeparator_evaluate, M.probability_nil, mul_one]
  linarith

end ModelEstimate

theorem constructiveResidualSeparator_models_nonnegative
    {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m)
    (hTelescope : ∀ M : AlgebraicProjectiveData (Fin n) A,
      base.evaluate M.probability = (occ.map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum) :
    ∀ M : AlgebraicProjectiveData (Fin n) A,
      0 ≤ (constructiveResidualSeparator base occ m).evaluate M.probability := by
  intro M
  exact constructiveResidualSeparator_model_nonnegative M base occ m hm (hTelescope M)

theorem constructiveResidualSeparator_target_margin {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (_hm : 0 < m) (g : Word (Fin n) → ℝ) (hunit : g [] = 1)
    (hzero : ∀ o ∈ occ, o.leaf.wordFunctional.evaluate g = 0)
    (hmargin : m ≤ base.evaluate g) :
    (constructiveResidualSeparator base occ m).evaluate g ≤ -(m / 2) := by
  have hsum : (occ.map (fun o => o.leaf.wordFunctional.evaluate g)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    rcases List.mem_map.mp hx with ⟨o, ho, rfl⟩
    exact hzero o ho
  rw [constructiveResidualSeparator_evaluate, hsum, mul_zero, zero_sub, hunit, mul_one]
  linarith

theorem constructiveResidualSeparator_hasHorizon {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (L : ℕ) (hbase : base.HasHorizon L)
    (hleaves : ∀ o ∈ occ, o.leaf.wordFunctional.HasHorizon L) :
    (constructiveResidualSeparator base occ m).HasHorizon L := by
  unfold constructiveResidualSeparator
  apply FiniteRealWordFunctional.hasHorizon_append
  · apply FiniteRealWordFunctional.hasHorizon_append
    · apply FiniteRealWordFunctional.hasHorizon_scale
      apply FiniteRealWordFunctional.hasHorizon_combine
      intro c hc
      rcases List.mem_map.mp hc with ⟨o, ho, rfl⟩
      exact hleaves o ho
    · exact FiniteRealWordFunctional.hasHorizon_scale _ _ _ hbase
  · exact FiniteRealWordFunctional.hasHorizon_emptyWordTerm _ _

end AlbertSequential
