/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ResidualTelescopeSeparator

/-! Conservative coefficient budgets and approximation bounds for the actual
constructed finite separator. Canonical norm merges coincident words; the raw
list budget is only an upper bound. Native sign and margin premises stay visible. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

namespace SupportedPurityLeaf
variable {n : ℕ} (l : SupportedPurityLeaf (Fin n))

theorem wordFunctional_rawCoefficientBound :
    l.wordFunctional.rawCoefficientBound = 1 + 2 * |l.constant| + l.constant ^ 2 := by
  simp only [wordFunctional, FiniteRealWordFunctional.rawCoefficientBound,
    wordAmplitudeCoefficientBound, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, abs_one, abs_mul, abs_neg]
  rw [abs_of_nonneg (sq_nonneg l.constant)]
  norm_num
  ring

theorem wordFunctional_rawCoefficientBound_of_nonnegative (h : 0 ≤ l.constant) :
    l.wordFunctional.rawCoefficientBound = 1 + 2 * l.constant + l.constant ^ 2 := by
  rw [l.wordFunctional_rawCoefficientBound, abs_of_nonneg h]

end SupportedPurityLeaf

def residualMeasuredCoefficientBudget {n : ℕ} (occ : List (ResidualTelescopeOccurrence n)) : ℝ :=
  (occ.map (fun o => 1 + 2 * |o.leaf.constant| + o.leaf.constant ^ 2)).sum

theorem residualSumFunctional_rawCoefficientBound {n : ℕ}
    (occ : List (ResidualTelescopeOccurrence n)) :
    (residualSumFunctional occ).rawCoefficientBound = residualMeasuredCoefficientBudget occ := by
  simp only [residualSumFunctional, FiniteRealWordFunctional.rawCoefficientBound_combine,
    List.map_map, Function.comp_def, SupportedPurityLeaf.wordFunctional_rawCoefficientBound,
    residualMeasuredCoefficientBudget]

theorem constructiveResidualSeparator_rawCoefficientBound {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m) :
    (constructiveResidualSeparator base occ m).rawCoefficientBound =
      residualPenaltyParameter occ m * residualMeasuredCoefficientBudget occ +
        base.rawCoefficientBound + m / 2 := by
  have ha := residualPenaltyParameter_pos occ m hm
  simp only [constructiveResidualSeparator, FiniteRealWordFunctional.rawCoefficientBound_append,
    FiniteRealWordFunctional.rawCoefficientBound_scale,
    FiniteRealWordFunctional.rawCoefficientBound_emptyWordTerm,
    residualSumFunctional_rawCoefficientBound, abs_of_pos ha, abs_neg, abs_one, one_mul,
    abs_of_nonneg (show 0 ≤ m / 2 by positivity)]

theorem constructiveResidualSeparator_coefficientNorm_le {n : ℕ}
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m) :
    (constructiveResidualSeparator base occ m).coefficientNorm ≤
      residualPenaltyParameter occ m * residualMeasuredCoefficientBudget occ +
        base.rawCoefficientBound + m / 2 := by
  calc
    _ ≤ _ := (constructiveResidualSeparator base occ m).coefficientNorm_le_rawCoefficientBound
    _ = _ := constructiveResidualSeparator_rawCoefficientBound base occ m hm

theorem constructiveResidualSeparator_forces_error
    {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A)
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m)
    (hTelescope : base.evaluate M.probability =
      (occ.map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum)
    (g : Word (Fin n) → ℝ) (hunit : g [] = 1)
    (hzero : ∀ o ∈ occ, o.leaf.wordFunctional.evaluate g = 0)
    (hmargin : m ≤ base.evaluate g)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herror : ∀ w ∈ (constructiveResidualSeparator base occ m).coefficients.support,
      |M.probability w - g w| ≤ ε) :
    m / 2 ≤ (constructiveResidualSeparator base occ m).coefficientNorm * ε := by
  exact FiniteRealWordFunctional.separation_forces_error _ _ _ _ _ hε herror
    (constructiveResidualSeparator_model_nonnegative M base occ m hm hTelescope)
    (constructiveResidualSeparator_target_margin base occ m hm g hunit hzero hmargin)

theorem constructiveResidualSeparator_forces_error_raw
    {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A)
    (base : FiniteRealWordFunctional n) (occ : List (ResidualTelescopeOccurrence n))
    (m : ℝ) (hm : 0 < m)
    (hTelescope : base.evaluate M.probability =
      (occ.map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum)
    (g : Word (Fin n) → ℝ) (hunit : g [] = 1)
    (hzero : ∀ o ∈ occ, o.leaf.wordFunctional.evaluate g = 0)
    (hmargin : m ≤ base.evaluate g)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herror : ∀ w ∈ (constructiveResidualSeparator base occ m).coefficients.support,
      |M.probability w - g w| ≤ ε) :
    m / 2 ≤ (residualPenaltyParameter occ m * residualMeasuredCoefficientBudget occ +
        base.rawCoefficientBound + m / 2) * ε := by
  exact (constructiveResidualSeparator_forces_error M base occ m hm hTelescope g hunit
    hzero hmargin ε hε herror).trans
      (mul_le_mul_of_nonneg_right
        (constructiveResidualSeparator_coefficientNorm_le base occ m hm) hε)

end AlbertSequential
