/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerMixedVectors

/-! Actual symmetric Clifford-pair syntax. Only Cij, never Tij, is symmetric.
Diagonal entries retain twice the actual square-defect vector expression. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy

def allPairs (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (e : HolonomyPath.Combination) : Fin 3 → Fin 3 → PurityVectorExpression 4 :=
  ![![scale 2 (squareOnCombination d C 0 e), pairOnCombination d C 0 e, pairOnCombination d C 2 e],
    ![pairOnCombination d C 0 e, scale 2 (squareOnCombination d C 1 e), pairOnCombination d C 1 e],
    ![pairOnCombination d C 2 e, pairOnCombination d C 1 e, scale 2 (squareOnCombination d C 2 e)]]

theorem cliffordPairDefect_diagonal {A : Type*} [Ring A] [Module ℝ A]
    (N : Fin 3 → A) (s : CliffordScalarParameters) (i : Fin 3) (ξ : A) :
    cliffordPairDefect N s i i ξ = (2 : ℝ) • cliffordSquareDefect N s i ξ := by
  simp only [cliffordPairDefect, cliffordSquareDefect, s.gramMatrix_diagonal, smul_add, smul_smul]
  module

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar hc in
theorem allPairs_value (i j : Fin 3) (e : HolonomyPath.Combination) :
    evaluate P (allPairs d C e i j) =
      cliffordPairDefect
        (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
        d.scalarParameters i j (HolonomyPath.combinationValue P d e) := by
  fin_cases i <;> fin_cases j <;>
    simp only [allPairs, Matrix.cons_val_zero', Matrix.cons_val_succ', evaluate_scale,
      squareOnCombination_value P hp hstar d C hc, pairOnCombination_value P hp hstar d C hc,
      nextHolonomy, cliffordPairDefect_diagonal]
  all_goals first | rfl | apply cliffordPairDefect_swap

end Values

theorem allPairs_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (e : HolonomyPath.Combination) (depth : ℕ) (hd : HolonomyPath.HasDepth e depth)
    (i j : Fin 3) : (allPairs d C e i j).HasHorizon (8 + 3 * depth) := by
  fin_cases i <;> fin_cases j <;>
    simp only [allPairs, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
    | exact pairOnCombination_horizon d C _ e depth hd
    | exact hasHorizon_scale _ _ _ (hasHorizon_mono (squareOnCombination_horizon d C _ e depth hd) (by omega))

end CornerResidualBuilder
end AlbertSequential
