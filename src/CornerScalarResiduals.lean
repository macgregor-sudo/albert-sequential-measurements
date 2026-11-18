/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerDataVolumeVectors
public import ResidualOccurrenceAlgebra
public import CliffordDefectPairings

/-! Actual Eij, Zi and Z0 residual-occurrence lists. Multiplicity is retained;
these are scalar pairings of the already constructed vector expressions. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy
open HolonomyPath (baseCombination skewAction)

def oneSkewPolynomial (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  CornerOperatorPolynomial.applyBase (CornerOperatorPolynomial.skew d i)
def twoSkewPolynomial (d : CornerNumericalData) (i j : Fin 3) : FiniteRealWordFunctional 4 :=
  CornerOperatorPolynomial.applyBase (FiniteRealWordFunctional.amplitudeMultiply
    (CornerOperatorPolynomial.skew d i) (CornerOperatorPolynomial.skew d j))

def gramAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (i j : Fin 3) :
    List (ResidualTelescopeOccurrence 4) :=
  ResidualOccurrenceExpression.scale (-(1 / 2))
    (pairAgainst (CornerOperatorPolynomial.projection 0) (allPairs d C baseCombination i j))

def crossFirstAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    List (ResidualTelescopeOccurrence 4) := ResidualOccurrenceExpression.combine
  [ResidualOccurrenceExpression.scale (-d.scalarParameters.m1) (gramAtBase d C 1 2),
    ResidualOccurrenceExpression.scale (-1) (pairAgainst (twoSkewPolynomial d 1 2)
      (squareOnCombination d C 0 baseCombination))]

def crossSecondAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    List (ResidualTelescopeOccurrence 4) := ResidualOccurrenceExpression.combine
  [ResidualOccurrenceExpression.scale d.scalarParameters.m2 (gramAtBase d C 0 2),
    ResidualOccurrenceExpression.scale (-2 * d.scalarParameters.u) (gramAtBase d C 1 2),
    ResidualOccurrenceExpression.scale (-1) (pairAgainst (oneSkewPolynomial d 2)
      (squareOnCombination d C 1 (skewAction 0 baseCombination))),
    ResidualOccurrenceExpression.scale (-1) (pairAgainst (twoSkewPolynomial d 1 2)
      (allPairs d C baseCombination 0 1))]

def crossThirdAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    List (ResidualTelescopeOccurrence 4) := ResidualOccurrenceExpression.combine
  [ResidualOccurrenceExpression.scale (-d.scalarParameters.m3) (gramAtBase d C 0 1),
    ResidualOccurrenceExpression.scale (2 * d.scalarParameters.v) (gramAtBase d C 1 2),
    ResidualOccurrenceExpression.scale (-2 * d.scalarParameters.w) (gramAtBase d C 0 2),
    ResidualOccurrenceExpression.scale (-1) (pairAgainst (twoSkewPolynomial d 0 1)
      (squareOnCombination d C 2 baseCombination)),
    pairAgainst (oneSkewPolynomial d 2)
      (leftMultiply (CornerOperatorPolynomial.skew d 0) (allPairs d C baseCombination 1 2) ++
        scale (-1) (allPairs d C (skewAction 1 baseCombination) 0 2))]

def crossAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    Fin 3 → List (ResidualTelescopeOccurrence 4) :=
  ![crossFirstAtBase d C, crossSecondAtBase d C, crossThirdAtBase d C]

def normAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    List (ResidualTelescopeOccurrence 4) := ResidualOccurrenceExpression.combine
  [ResidualOccurrenceExpression.scale (-1) (pairAgainst (twoSkewPolynomial d 1 2)
      (squareOnCombination d C 0 (skewAction 1 (skewAction 2 baseCombination)))),
    ResidualOccurrenceExpression.scale (-d.scalarParameters.m1) (pairAgainst (oneSkewPolynomial d 2)
      (squareOnCombination d C 1 (skewAction 2 baseCombination))),
    ResidualOccurrenceExpression.scale (-d.scalarParameters.m1 * d.scalarParameters.m2)
      (pairAgainst (CornerOperatorPolynomial.projection 0) (squareOnCombination d C 2 baseCombination))]

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ) (hφ : ∀ x, φ (star x) = φ x)
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar in
theorem oneSkewPolynomial_value (i : Fin 3) : (oneSkewPolynomial d i).amplitudeValue P =
    skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) * P 0 := by
  rw [oneSkewPolynomial, CornerOperatorPolynomial.applyBase_value,
    CornerOperatorPolynomial.skew_value P hp hstar d]

include hp hstar in
theorem twoSkewPolynomial_value (i j : Fin 3) : (twoSkewPolynomial d i j).amplitudeValue P =
    skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) *
      skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 j) * P 0 := by
  simp only [twoSkewPolynomial, CornerOperatorPolynomial.applyBase_value,
    FiniteRealWordFunctional.amplitudeValue_multiply, CornerOperatorPolynomial.skew_value P hp hstar d]

include hφ hp hstar hc in
theorem gramAtBase_value (i j : Fin 3) : ResidualOccurrenceExpression.value φ P (gramAtBase d C i j) =
    cliffordGramDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters i j := by
  rw [gramAtBase, ResidualOccurrenceExpression.value_scale,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    CornerOperatorPolynomial.projection_value, allPairs_value P hp hstar d C hc,
    HolonomyPath.combinationValue_base]
  exact (cliffordGramDefect_pair φ hφ _ (fun i => skewHermitianPart_skew _) _ _ i j).symm

include hφ hp hstar hc in
theorem crossFirstAtBase_value : ResidualOccurrenceExpression.value φ P (crossFirstAtBase d C) =
    cliffordCrossDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters 0 := by
  rw [cliffordCrossDefect_first φ hφ _ (fun i => skewHermitianPart_skew _)]
  simp only [crossFirstAtBase, ResidualOccurrenceExpression.value_combine,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ResidualOccurrenceExpression.value_scale, gramAtBase_value φ hφ P hp hstar d C hc,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    twoSkewPolynomial_value P hp hstar d, squareOnCombination_value P hp hstar d C hc,
    HolonomyPath.combinationValue_base]
  ring

include hφ hp hstar hc in
theorem crossSecondAtBase_value : ResidualOccurrenceExpression.value φ P (crossSecondAtBase d C) =
    cliffordCrossDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters 1 := by
  rw [cliffordCrossDefect_second φ hφ _ (fun i => skewHermitianPart_skew _)]
  simp only [crossSecondAtBase, ResidualOccurrenceExpression.value_combine,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ResidualOccurrenceExpression.value_scale, gramAtBase_value φ hφ P hp hstar d C hc,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    oneSkewPolynomial_value P hp hstar d, twoSkewPolynomial_value P hp hstar d,
    squareOnCombination_value P hp hstar d C hc, allPairs_value P hp hstar d C hc,
    HolonomyPath.combinationValue_skewAction P hp hstar, HolonomyPath.combinationValue_base]
  ring

include hφ hp hstar hc in
theorem crossThirdAtBase_value : ResidualOccurrenceExpression.value φ P (crossThirdAtBase d C) =
    cliffordCrossDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters 2 := by
  rw [cliffordCrossDefect_third φ hφ _ (fun i => skewHermitianPart_skew _)]
  simp only [crossThirdAtBase, ResidualOccurrenceExpression.value_combine,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ResidualOccurrenceExpression.value_scale, gramAtBase_value φ hφ P hp hstar d C hc,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    oneSkewPolynomial_value P hp hstar d, twoSkewPolynomial_value P hp hstar d,
    evaluate_append, evaluate_leftMultiply, evaluate_scale,
    CornerOperatorPolynomial.skew_value P hp hstar d,
    squareOnCombination_value P hp hstar d C hc, allPairs_value P hp hstar d C hc,
    HolonomyPath.combinationValue_skewAction P hp hstar, HolonomyPath.combinationValue_base]
  simp only [realStarPairing_symmetric φ hφ
    (skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 2) * P 0),
    realStarPairing_add_left, realStarPairing_smul_left, realStarPairing_sub_left]
  ring

include hφ hp hstar hc in
theorem crossAtBase_value (i : Fin 3) : ResidualOccurrenceExpression.value φ P (crossAtBase d C i) =
    cliffordCrossDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters i := by
  fin_cases i
  · exact crossFirstAtBase_value φ hφ P hp hstar d C hc
  · exact crossSecondAtBase_value φ hφ P hp hstar d C hc
  · exact crossThirdAtBase_value φ hφ P hp hstar d C hc

include hp hstar hc in
theorem normAtBase_value : ResidualOccurrenceExpression.value φ P (normAtBase d C) =
    cliffordNormDefect φ
      (fun k => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 k))
      (P 0) d.scalarParameters := by
  rw [cliffordNormDefect_reduction φ _ (fun i => skewHermitianPart_skew _)]
  simp only [normAtBase, ResidualOccurrenceExpression.value_combine,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ResidualOccurrenceExpression.value_scale,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    oneSkewPolynomial_value P hp hstar d, twoSkewPolynomial_value P hp hstar d,
    CornerOperatorPolynomial.projection_value, squareOnCombination_value P hp hstar d C hc,
    HolonomyPath.combinationValue_skewAction P hp hstar, HolonomyPath.combinationValue_base, mul_assoc]
  ring

end Values
end CornerResidualBuilder
end AlbertSequential
