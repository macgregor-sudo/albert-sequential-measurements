/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PurityOccurrenceRelabelling
public import ConstructedCornerTelescope
public import ResidualSeparatorBounds

/-! Literal finite weighted sums of the generic one-base telescopes and their
conditional explicit witness. Native purity/margin and every other paper input
remain separate hypotheses or excluded applications. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def cornerBaseFunctional (d : CornerNumericalData) : FiniteRealWordFunctional 4 where
  terms := [(d.scalarParameters.discriminant, [(0, true)])]

theorem cornerBaseFunctional_evaluate (d : CornerNumericalData) (g : Word (Fin 4) → ℝ) :
    (cornerBaseFunctional d).evaluate g = d.scalarParameters.discriminant * g [(0, true)] := by
  simp only [cornerBaseFunctional, FiniteRealWordFunctional.evaluate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem cornerBaseFunctional_horizon (d : CornerNumericalData) (L : ℕ) (hL : 1 ≤ L) :
    (cornerBaseFunctional d).HasHorizon L := by
  intro t ht
  have he := List.mem_singleton.mp ht
  rw [he]
  exact hL

section Family
variable {n k : ℕ} (d : Fin k → CornerNumericalData)
  (C : Fin k → Fin 4 → Word (Fin 4) → ℝ) (r : Fin k → Fin 4 → Fin n)
  (weight : Fin k → ℝ)

def combinedCornerBase : FiniteRealWordFunctional n :=
  FiniteRealWordFunctional.combine (List.ofFn (fun j : Fin k =>
    FiniteRealWordFunctional.scale (weight j)
      (FiniteRealWordFunctional.relabel (r j) (cornerBaseFunctional (d j)))))

def combinedCornerOccurrences : List (ResidualTelescopeOccurrence n) :=
  ResidualOccurrenceExpression.combine (List.ofFn (fun j : Fin k =>
    ResidualOccurrenceExpression.scale (weight j)
      (ResidualOccurrenceExpression.relabel (r j) (cornerResidualTelescopeOccurrences (d j) (C j)))))

def combinedCornerWitness (m : ℝ) : FiniteRealWordFunctional n :=
  constructiveResidualSeparator (combinedCornerBase d r weight) (combinedCornerOccurrences d C r weight) m

section Models
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem relabelledCornerTelescope_identity (e : CornerNumericalData)
    (c : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions e c)
    (f : Fin 4 → Fin n) (M : AlgebraicProjectiveData (Fin n) A) :
    (FiniteRealWordFunctional.relabel f (cornerBaseFunctional e)).evaluate M.probability =
      ResidualOccurrenceExpression.value M.state M.projection
        (ResidualOccurrenceExpression.relabel f (cornerResidualTelescopeOccurrences e c)) := by
  rw [FiniteRealWordFunctional.evaluate_relabel, cornerBaseFunctional_evaluate,
    ResidualOccurrenceExpression.value_relabel]
  have he := cornerResidualTelescope_identity e c hc (AlgebraicProjectiveData.comap f M)
  change e.scalarParameters.discriminant * (AlgebraicProjectiveData.comap f M).probability [(0, true)] =
    ResidualOccurrenceExpression.value M.state (M.projection ∘ f) (cornerResidualTelescopeOccurrences e c) at he
  rw [AlgebraicProjectiveData.comap_probability] at he
  exact he

theorem combinedCornerTelescope_identity (hc : ∀ j, CornerScalarConditions (d j) (C j))
    (M : AlgebraicProjectiveData (Fin n) A) :
    (combinedCornerBase d r weight).evaluate M.probability =
      ((combinedCornerOccurrences d C r weight).map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum := by
  change _ = ResidualOccurrenceExpression.value M.state M.projection _
  simp only [combinedCornerBase, combinedCornerOccurrences,
    FiniteRealWordFunctional.evaluate_combine, ResidualOccurrenceExpression.value_combine,
    List.map_ofFn, Function.comp_def, FiniteRealWordFunctional.evaluate_scale, ResidualOccurrenceExpression.value_scale]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext j
  rw [relabelledCornerTelescope_identity (d j) (C j) (hc j) (r j) M]

theorem combinedCornerWitness_model_nonnegative (hc : ∀ j, CornerScalarConditions (d j) (C j))
    (M : AlgebraicProjectiveData (Fin n) A) (m : ℝ) (hm : 0 < m) :
    0 ≤ (combinedCornerWitness d C r weight m).evaluate M.probability :=
  constructiveResidualSeparator_model_nonnegative M _ _ m hm
    (combinedCornerTelescope_identity d C r weight hc M)

end Models

theorem combinedCornerBase_horizon : (combinedCornerBase d r weight).HasHorizon 11 := by
  apply FiniteRealWordFunctional.hasHorizon_combine
  intro b hb
  rcases List.mem_ofFn.mp hb with ⟨j, rfl⟩
  apply FiniteRealWordFunctional.hasHorizon_scale
  exact FiniteRealWordFunctional.hasHorizon_relabel _ _ _ (cornerBaseFunctional_horizon _ _ (by decide))

theorem combinedCornerOccurrences_horizon :
    ∀ o ∈ combinedCornerOccurrences d C r weight, o.leaf.wordFunctional.HasHorizon 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  apply ResidualOccurrenceExpression.hasHorizon_scale
  exact ResidualOccurrenceExpression.hasHorizon_relabel _ _ _ (cornerResidualTelescope_horizon _ _)

theorem combinedCornerWitness_horizon (m : ℝ) :
    (combinedCornerWitness d C r weight m).HasHorizon 11 :=
  constructiveResidualSeparator_hasHorizon _ _ m 11
    (combinedCornerBase_horizon d r weight) (combinedCornerOccurrences_horizon d C r weight)

theorem combinedCornerWitness_target_margin (m : ℝ) (hm : 0 < m) (g : Word (Fin n) → ℝ)
    (hunit : g [] = 1)
    (hzero : ∀ o ∈ combinedCornerOccurrences d C r weight, o.leaf.wordFunctional.evaluate g = 0)
    (hmargin : m ≤ (combinedCornerBase d r weight).evaluate g) :
    (combinedCornerWitness d C r weight m).evaluate g ≤ -(m / 2) :=
  constructiveResidualSeparator_target_margin _ _ m hm g hunit hzero hmargin

theorem combinedCornerWitness_coefficientNorm_le (m : ℝ) (hm : 0 < m) :
    (combinedCornerWitness d C r weight m).coefficientNorm ≤
      residualPenaltyParameter (combinedCornerOccurrences d C r weight) m *
          residualMeasuredCoefficientBudget (combinedCornerOccurrences d C r weight) +
        (combinedCornerBase d r weight).rawCoefficientBound + m / 2 :=
  constructiveResidualSeparator_coefficientNorm_le _ _ m hm

theorem combinedCornerWitness_forces_error
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (hc : ∀ j, CornerScalarConditions (d j) (C j)) (M : AlgebraicProjectiveData (Fin n) A)
    (m : ℝ) (hm : 0 < m) (g : Word (Fin n) → ℝ) (hunit : g [] = 1)
    (hzero : ∀ o ∈ combinedCornerOccurrences d C r weight, o.leaf.wordFunctional.evaluate g = 0)
    (hmargin : m ≤ (combinedCornerBase d r weight).evaluate g)
    (ε : ℝ) (hε : 0 ≤ ε) (herror : ∀ w, w.length ≤ 11 → |M.probability w - g w| ≤ ε) :
    m / 2 ≤ (combinedCornerWitness d C r weight m).coefficientNorm * ε := by
  exact FiniteRealWordFunctional.separation_forces_error _ _ _ ε (m / 2) hε
    (fun w hw => herror w ((combinedCornerWitness d C r weight m).coefficient_support_hasHorizon 11
      (combinedCornerWitness_horizon d C r weight m) w hw))
    (combinedCornerWitness_model_nonnegative d C r weight hc M m hm)
    (combinedCornerWitness_target_margin d C r weight m hm g hunit hzero hmargin)

end Family
end AlbertSequential
