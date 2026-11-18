/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerScalarResiduals

/-! Structural eleven-letter bounds for the literal scalar residual lists.
No hypothesis supplies their horizons, ranks or prescribed word census. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression
open HolonomyPath (baseCombination skewAction)

theorem pairAgainst_square_bound (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (U : FiniteRealWordFunctional 4) (i : Fin 3) (e : HolonomyPath.Combination) (depth : ℕ)
    (hd : HolonomyPath.HasDepth e depth) (hdepth : depth ≤ 2) :
    ResidualOccurrenceExpression.HasHorizon (pairAgainst U (squareOnCombination d C i e)) 11 :=
  ResidualOccurrenceExpression.hasHorizon_pairAgainst _ _ _
    (hasHorizon_mono (squareOnCombination_horizon d C i e depth hd) (by omega))

theorem pairAgainst_pair_bound (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (U : FiniteRealWordFunctional 4) (i j : Fin 3) (e : HolonomyPath.Combination) (depth : ℕ)
    (hd : HolonomyPath.HasDepth e depth) (hdepth : depth ≤ 1) :
    ResidualOccurrenceExpression.HasHorizon (pairAgainst U (allPairs d C e i j)) 11 :=
  ResidualOccurrenceExpression.hasHorizon_pairAgainst _ _ _
    (hasHorizon_mono (allPairs_horizon d C e depth hd i j) (by omega))

theorem gramAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (i j : Fin 3) :
    ResidualOccurrenceExpression.HasHorizon (gramAtBase d C i j) 11 :=
  ResidualOccurrenceExpression.hasHorizon_scale _ _ _
    (pairAgainst_pair_bound d C _ i j _ 0 HolonomyPath.baseCombination_hasDepth (by decide))

theorem crossFirstAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ResidualOccurrenceExpression.HasHorizon (crossFirstAtBase d C) 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 0 HolonomyPath.baseCombination_hasDepth (by decide))

theorem crossSecondAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ResidualOccurrenceExpression.HasHorizon (crossSecondAtBase d C) 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 1
        (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) (by decide))
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_pair_bound d C _ _ _ _ 0 HolonomyPath.baseCombination_hasDepth (by decide))

theorem crossThirdAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ResidualOccurrenceExpression.HasHorizon (crossThirdAtBase d C) 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 0 HolonomyPath.baseCombination_hasDepth (by decide))
  · apply ResidualOccurrenceExpression.hasHorizon_pairAgainst
    apply hasHorizon_append
    · apply hasHorizon_leftMultiply
      exact allPairs_horizon d C _ 1
        (by intro t ht; have h := HolonomyPath.baseCombination_hasDepth t ht; omega) _ _
    · apply hasHorizon_scale
      exact allPairs_horizon d C _ 1
        (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) _ _

theorem crossAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) :
    ResidualOccurrenceExpression.HasHorizon (crossAtBase d C i) 11 := by
  fin_cases i
  · exact crossFirstAtBase_horizon d C
  · exact crossSecondAtBase_horizon d C
  · exact crossThirdAtBase_horizon d C

theorem normAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    ResidualOccurrenceExpression.HasHorizon (normAtBase d C) 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 2 (HolonomyPath.twoSkew_base_hasDepth _ _) (by decide))
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 1
        (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) (by decide))
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (pairAgainst_square_bound d C _ _ _ 0 HolonomyPath.baseCombination_hasDepth (by decide))

end CornerResidualBuilder
end AlbertSequential
