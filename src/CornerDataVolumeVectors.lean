/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AllCornerPairVectors
public import CornerCubicVectors
public import CliffordVolumeDefect

/-! Literal six-term H product and data/volume residual lists. Right-path
depths are proved from the expressions, not supplied as a ledger invariant. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy
open HolonomyPath (baseCombination generatorAction positiveIndex negativeIndex skewAction)

def hermitianProductAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    PurityVectorExpression 4 :=
  scale (1 / 2)
    (hermitianOnCombination d C 0 (generatorAction (positiveIndex 1) (generatorAction (positiveIndex 2) baseCombination)) ++
      leftMultiply (CornerOperatorPolynomial.approximation d 0)
        (hermitianOnCombination d C 1 (generatorAction (positiveIndex 2) baseCombination)) ++
      leftMultiply (FiniteRealWordFunctional.amplitudeMultiply
        (CornerOperatorPolynomial.approximation d 0) (CornerOperatorPolynomial.approximation d 1))
        (hermitianOnCombination d C 2 baseCombination) ++
      hermitianOnCombination d C 2 (generatorAction (negativeIndex 1) (generatorAction (negativeIndex 0) baseCombination)) ++
      leftMultiply (FiniteRealWordFunctional.amplitudeStar (CornerOperatorPolynomial.approximation d 2))
        (hermitianOnCombination d C 1 (generatorAction (negativeIndex 0) baseCombination)) ++
      leftMultiply (FiniteRealWordFunctional.amplitudeMultiply
        (FiniteRealWordFunctional.amplitudeStar (CornerOperatorPolynomial.approximation d 2))
        (FiniteRealWordFunctional.amplitudeStar (CornerOperatorPolynomial.approximation d 1)))
        (hermitianOnCombination d C 0 baseCombination))

def dataAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    PurityVectorExpression 4 :=
  cubicAtBase d C ++ scale (-1) (hermitianProductAtBase d C) ++
    scale (-(1 / 2))
      (scale (d.hermitianConstants 0) (allPairs d C baseCombination 1 2) ++
        scale (d.hermitianConstants 1) (allPairs d C baseCombination 0 2) ++
        scale (d.hermitianConstants 2) (allPairs d C baseCombination 0 1))

def volumeAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    PurityVectorExpression 4 :=
  scale (-(1 / 2)) (allPairs d C (skewAction 0 baseCombination) 1 2) ++
    scale (1 / 2) (leftMultiply (CornerOperatorPolynomial.skew d 1)
      (allPairs d C baseCombination 0 2)) ++
    scale (-(1 / 2)) (allPairs d C (skewAction 2 baseCombination) 0 1)

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar hc in
theorem hermitianProductAtBase_value : evaluate P (hermitianProductAtBase d C) =
    hermitianProductTelescope (P 0)
      (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2)
      d.hermitianConstants * P 0 := by
  simp only [hermitianProductAtBase, evaluate_scale, evaluate_append, evaluate_leftMultiply,
    hermitianOnCombination_value P hp hstar d C hc,
    FiniteRealWordFunctional.amplitudeValue_multiply,
    FiniteRealWordFunctional.amplitudeValue_star P hstar,
    CornerOperatorPolynomial.approximation_value P hp hstar d,
    HolonomyPath.combinationValue_generatorAction P d hp, HolonomyPath.generator_positive,
    HolonomyPath.generator_negative P hstar, HolonomyPath.combinationValue_base,
    hermitianProductTelescope, add_mul, smul_mul_assoc, mul_assoc]

include hp hstar hc in
theorem dataAtBase_value : evaluate P (dataAtBase d C) =
    cliffordDataError
      (fun i => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i))
      (P 0) d.scalarParameters := by
  unfold CornerNumericalData.scalarParameters
  rw [cornerDataError_expansion (P 0) (hp 0) (hstar 0) _
    (normalizedCyclicHolonomies_supported _ _ _ _ (hp 0) _ _ _)
    d.hermitianConstants d.mixed12 d.mixed13 d.mixed23 d.cubicConstant (P 0) (hp 0)]
  simp only [dataAtBase, evaluate_append, evaluate_scale, cubicAtBase_value P hp hstar d C hc,
    hermitianProductAtBase_value P hp hstar d C hc, allPairs_value P hp hstar d C hc,
    HolonomyPath.combinationValue_base, sub_mul]
  simp only [CornerNumericalData.scalarParameters]
  module

include hp hstar hc in
theorem volumeAtBase_value : evaluate P (volumeAtBase d C) =
    cliffordVolumeError
      (fun i => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i))
      (P 0) d.scalarParameters := by
  rw [cliffordVolumeError_expansion]
  simp only [volumeAtBase, evaluate_append, evaluate_scale, evaluate_leftMultiply,
    allPairs_value P hp hstar d C hc, HolonomyPath.combinationValue_skewAction P hp hstar,
    HolonomyPath.combinationValue_base, CornerOperatorPolynomial.skew_value P hp hstar d]
  module

end Values

theorem hermitianProductAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    (hermitianProductAtBase d C).HasHorizon 11 := by
  apply hasHorizon_scale
  refine hasHorizon_append _ _ _ (hasHorizon_append _ _ _ (hasHorizon_append _ _ _
    (hasHorizon_append _ _ _ (hasHorizon_append _ _ _ ?_ ?_) ?_) ?_) ?_) ?_
  · exact hermitianOnCombination_horizon d C 0 _ 2 (HolonomyPath.twoGenerator_base_hasDepth _ _)
  · apply hasHorizon_leftMultiply
    exact hasHorizon_mono (hermitianOnCombination_horizon d C 1 _ 1
      (HolonomyPath.hasDepth_generatorAction _ _ _ HolonomyPath.baseCombination_hasDepth)) (by decide)
  · apply hasHorizon_leftMultiply
    exact hasHorizon_mono (hermitianOnCombination_horizon d C 2 _ 0 HolonomyPath.baseCombination_hasDepth) (by decide)
  · exact hermitianOnCombination_horizon d C 2 _ 2 (HolonomyPath.twoGenerator_base_hasDepth _ _)
  · apply hasHorizon_leftMultiply
    exact hasHorizon_mono (hermitianOnCombination_horizon d C 1 _ 1
      (HolonomyPath.hasDepth_generatorAction _ _ _ HolonomyPath.baseCombination_hasDepth)) (by decide)
  · apply hasHorizon_leftMultiply
    exact hasHorizon_mono (hermitianOnCombination_horizon d C 0 _ 0 HolonomyPath.baseCombination_hasDepth) (by decide)

theorem dataAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    (dataAtBase d C).HasHorizon 11 := by
  apply hasHorizon_append
  · apply hasHorizon_append
    · exact hasHorizon_mono (cubicAtBase_horizon d C) (by decide)
    · exact hasHorizon_scale _ _ _ (hermitianProductAtBase_horizon d C)
  · apply hasHorizon_scale
    refine hasHorizon_append _ _ _ (hasHorizon_append _ _ _ ?_ ?_) ?_
    all_goals apply hasHorizon_scale
    all_goals exact (hasHorizon_mono (allPairs_horizon d C _ 0 HolonomyPath.baseCombination_hasDepth _ _) (by decide))

theorem volumeAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    (volumeAtBase d C).HasHorizon 11 := by
  refine hasHorizon_append _ _ _ (hasHorizon_append _ _ _ ?_ ?_) ?_
  · apply hasHorizon_scale
    exact allPairs_horizon d C _ 1
      (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) _ _
  · apply hasHorizon_scale
    apply hasHorizon_leftMultiply
    exact hasHorizon_mono (allPairs_horizon d C _ 0 HolonomyPath.baseCombination_hasDepth _ _) (by decide)
  · apply hasHorizon_scale
    exact allPairs_horizon d C _ 1
      (HolonomyPath.hasDepth_skewAction _ _ _ HolonomyPath.baseCombination_hasDepth) _ _

end CornerResidualBuilder
end AlbertSequential
