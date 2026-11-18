/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PrimitivePurityDecomposition
public import ResidualTelescopeSeparator

/-! Literal occurrence-list binder for primitive residual expansions. A common
left amplitude polynomial and every actual signed term are retained. The right
history is explicitly historyPrefix ++ [yes a], so its one-letter cost is visible. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

namespace FiniteRealWordFunctional
theorem amplitudeValue_scale {n : ℕ} {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (r : ℝ) (c : FiniteRealWordFunctional n) :
    (scale r c).amplitudeValue P = r • c.amplitudeValue P := by
  change wordAmplitudeCombination P (c.terms.map (fun t => (r * t.1, t.2))) =
      r • wordAmplitudeCombination P c.terms
  induction c.terms with
  | nil => simp only [List.map_nil, wordAmplitudeCombination_nil, smul_zero]
  | cons t ts ih =>
      simp only [List.map_cons, wordAmplitudeCombination_cons]
      rw [ih, wordAmplitudeCombination_cons, mul_smul, smul_add]
end FiniteRealWordFunctional

def primitiveResidualOccurrences {n : ℕ} (a : Fin n) (c : Word (Fin n) → ℝ)
    (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) : List (ResidualTelescopeOccurrence n) :=
  ts.map (fun t =>
    { leaf := ⟨historyPrefix, (a, true), t.2, c t.2⟩
      leftTerms := FiniteRealWordFunctional.scale t.1 left })

theorem primitiveResidualOccurrences_length {n : ℕ} (a : Fin n)
    (c : Word (Fin n) → ℝ) (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) :
    (primitiveResidualOccurrences a c ts historyPrefix left).length = ts.length := by
  exact List.length_map _

theorem primitiveResidualOccurrences_coefficientBudget {n : ℕ} (a : Fin n)
    (c : Word (Fin n) → ℝ) (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) :
    residualCoefficientBudget (primitiveResidualOccurrences a c ts historyPrefix left) =
      (ts.map (fun t => (|t.1| * left.rawCoefficientBound) ^ 2)).sum := by
  simp only [residualCoefficientBudget, primitiveResidualOccurrences, List.map_map,
    Function.comp_def, ResidualTelescopeOccurrence.coefficientBound,
    FiniteRealWordFunctional.rawCoefficientBound_scale]

theorem primitiveResidualOccurrences_horizon {n : ℕ} (a : Fin n)
    (c : Word (Fin n) → ℝ) (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) (L : ℕ)
    (h : ∀ t ∈ ts, historyPrefix.length + 1 + 2 * t.2.length ≤ L) :
    ∀ o ∈ primitiveResidualOccurrences a c ts historyPrefix left, o.leaf.wordFunctional.HasHorizon L := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨t, ht, rfl⟩
  apply SupportedPurityLeaf.wordFunctional_hasHorizon
  simpa only [SupportedPurityLeaf.history, List.length_append, List.length_singleton] using h t ht

theorem primitiveResidualOccurrences_pairing
    {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) (a : Fin n) (c : Word (Fin n) → ℝ)
    (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) :
    ((primitiveResidualOccurrences a c ts historyPrefix left).map (fun o => M.state
      (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum =
      M.state (star (left.amplitudeValue M.projection) *
        (weightedPurityResidual M.projection a c ts *
          wordAmplitude M.projection (historyPrefix ++ [(a, true)]))) := by
  induction ts with
  | nil => simp only [primitiveResidualOccurrences, List.map_nil, List.sum_nil,
      weightedPurityResidual, zero_mul, mul_zero, map_zero]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      simp only [primitiveResidualOccurrences, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      change M.state (star ((FiniteRealWordFunctional.scale r left).amplitudeValue M.projection) *
          (outcomePurityElement M.projection (a, true) w (c w) *
            wordAmplitude M.projection (historyPrefix ++ [(a, true)]))) +
          M.state (star (left.amplitudeValue M.projection) *
            (weightedPurityResidual M.projection a c ts *
              wordAmplitude M.projection (historyPrefix ++ [(a, true)]))) =
        M.state (star (left.amplitudeValue M.projection) *
          ((r • outcomePurityElement M.projection (a, true) w (c w) +
            weightedPurityResidual M.projection a c ts) *
              wordAmplitude M.projection (historyPrefix ++ [(a, true)])))
      rw [FiniteRealWordFunctional.amplitudeValue_scale]
      simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
        add_mul, mul_add, map_add]

end AlbertSequential
