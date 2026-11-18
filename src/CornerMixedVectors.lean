/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerSquareVectors

/-! Ordered mixed contractions. The third slot is (h2,h0), with Q312;
imperfect T02 and T20 are never identified. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy FiniteRealWordFunctional

def nextHolonomy : Fin 3 → Fin 3 := ![1, 2, 0]
def mixedConstant (d : CornerNumericalData) : Fin 3 → ℝ := ![d.mixed12, d.mixed23, d.mixed13]

def mixedOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  PurityVectorExpression.scale ((2 * d.normalizer i * d.normalizer (nextHolonomy i))⁻¹)
    (pairOnWord C (faceSecond i) 0 (HolonomyPath.word p ++ [(faceThird i, true)])
        (amplitudeMultiply (CornerOperatorPolynomial.projection 0) (CornerOperatorPolynomial.projection (faceFirst i))) ++
      pairOnWord C (faceSecond i) 0 (HolonomyPath.word p ++ [(faceFirst i, true)])
        (amplitudeMultiply (CornerOperatorPolynomial.projection 0) (CornerOperatorPolynomial.projection (faceThird i))) ++
      tripleBaseOnPath C i p (emptyWordTerm (d.overlap 0 (faceSecond i))))

def pairOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  PurityVectorExpression.scale 2 (mixedOnPath d C i p) ++
    PurityVectorExpression.scale (-1)
      (PurityVectorExpression.scale ((d.normalizer (nextHolonomy i))⁻¹)
          (hermitianOnPath d C i (HolonomyPath.positiveIndex (nextHolonomy i) :: p)) ++
        leftMultiply (CornerOperatorPolynomial.approximation d i)
          (hermitianOnPath d C (nextHolonomy i) p) ++
        PurityVectorExpression.scale ((d.normalizer i)⁻¹)
          (hermitianOnPath d C (nextHolonomy i) (HolonomyPath.negativeIndex i :: p)) ++
        leftMultiply (amplitudeStar (CornerOperatorPolynomial.approximation d (nextHolonomy i)))
          (hermitianOnPath d C i p))

def pairOnCombination (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) : PurityVectorExpression 4 :=
  extendPaths d (pairOnPath d C i) e

theorem faceThird_ne_zero (i : Fin 3) : faceThird i ≠ 0 := by fin_cases i <;> decide
theorem next_faceFirst (i : Fin 3) : faceFirst (nextHolonomy i) = faceSecond i := by fin_cases i <;> rfl
theorem next_faceSecond (i : Fin 3) : faceSecond (nextHolonomy i) = faceThird i := by fin_cases i <;> rfl
theorem mixedConstant_fraction (d : CornerNumericalData) (i : Fin 3) :
    mixedConstant d i = d.overlap 0 (faceSecond i) * faceQ d i /
      (d.normalizer i * d.normalizer (nextHolonomy i)) := by
  fin_cases i
  · rfl
  · rfl
  · exact d.mixed13_reverse_denominator

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar hc in
theorem mixedOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (mixedOnPath d C i p) =
      pairProductDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 (nextHolonomy i))
        (mixedConstant d i) * wordAmplitude P (HolonomyPath.word p) := by
  rw [mixedOnPath, PurityVectorExpression.evaluate_scale,
    PurityVectorExpression.evaluate_append, PurityVectorExpression.evaluate_append,
    pairOnWord_value P hp hstar d C hc _ _ (faceSecond_ne_zero i),
    pairOnWord_value P hp hstar d C hc _ _ (faceSecond_ne_zero i),
    tripleBaseOnPath_value P hp hstar d C hc,
    amplitudeValue_multiply, amplitudeValue_multiply,
    CornerOperatorPolynomial.projection_value, CornerOperatorPolynomial.projection_value,
    CornerOperatorPolynomial.projection_value, amplitudeValue_emptyWordTerm,
    wordAmplitude_append_singleton, wordAmplitude_append_singleton]
  simp only [algebraicOutcome, ite_true, smul_mul_assoc, one_mul, mul_assoc]
  have he := normalizedPairProduct_defect_expansion (P 0) (P (faceFirst i))
    (P (faceSecond i)) (P (faceThird i)) (hp 0) (hstar 0) (hstar _) (hstar _) (hstar _)
    (d.overlap 0 (faceSecond i)) (faceQ d i) (d.normalizer i) (d.normalizer (nextHolonomy i))
    (hc.normalizers_nonzero i) (hc.normalizers_nonzero (nextHolonomy i))
  have hn : 2 * d.normalizer i * d.normalizer (nextHolonomy i) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (hc.normalizers_nonzero i))
      (hc.normalizers_nonzero (nextHolonomy i))
  have he' := congrArg (fun X : A => (2 * d.normalizer i * d.normalizer (nextHolonomy i))⁻¹ •
    (X * wordAmplitude P (HolonomyPath.word p))) he
  simp only [smul_mul_assoc, smul_smul, inv_mul_cancel₀ hn, one_smul] at he'
  rw [holonomy_face P d i, holonomy_face P d (nextHolonomy i), next_faceFirst, next_faceSecond,
    mixedConstant_fraction, d.overlap_symmetric (faceSecond i) 0]
  simpa only [add_mul, smul_mul_assoc, mul_assoc,
    HolonomyPath.amplitude_supported P hp] using he'.symm

include hp in
omit [StarRing A] [StarModule ℝ A] [SMulCommClass ℝ A A] in
theorem scaled_amplitude_cons (a : Fin 6) (p : List (Fin 6)) :
    (d.normalizer (HolonomyPath.normalizerIndex a))⁻¹ • wordAmplitude P (HolonomyPath.word (a :: p)) =
      HolonomyPath.generatorOperator P d a * wordAmplitude P (HolonomyPath.word p) := by
  rw [HolonomyPath.amplitude_cons P hp]
  simp only [HolonomyPath.generatorOperator, normalizedCornerWord, smul_mul_assoc]

include hp hstar hc in
theorem pairOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (pairOnPath d C i p) =
      pairCliffordDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 (nextHolonomy i))
        (d.hermitianConstants i) (d.hermitianConstants (nextHolonomy i)) (mixedConstant d i) *
          wordAmplitude P (HolonomyPath.word p) := by
  simp only [pairOnPath, PurityVectorExpression.evaluate_append, PurityVectorExpression.evaluate_scale,
    evaluate_leftMultiply, hermitianOnPath_value P hp hstar d C hc,
    mixedOnPath_value P hp hstar d C hc,
    CornerOperatorPolynomial.approximation_value P hp hstar d,
    amplitudeValue_star P hstar]
  have hindexp (j : Fin 3) : HolonomyPath.normalizerIndex (HolonomyPath.positiveIndex j) = j := by fin_cases j <;> rfl
  have hindexn (j : Fin 3) : HolonomyPath.normalizerIndex (HolonomyPath.negativeIndex j) = j := by fin_cases j <;> rfl
  have hp' (j : Fin 3) := scaled_amplitude_cons P hp d (HolonomyPath.positiveIndex j) p
  have hn' (j : Fin 3) := scaled_amplitude_cons P hp d (HolonomyPath.negativeIndex j) p
  simp only [hindexp, HolonomyPath.generator_positive] at hp'
  simp only [hindexn, HolonomyPath.generator_negative P hstar] at hn'
  simp only [← mul_smul_comm]
  rw [hp', hn']
  rw [pairDefect_reduction (P 0) _ _ (hp 0) (hstar 0)
    (normalizedCyclicHolonomies_supported _ _ _ _ (hp 0) _ _ _ i)
    (normalizedCyclicHolonomies_supported _ _ _ _ (hp 0) _ _ _ (nextHolonomy i))]
  simp only [sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, neg_one_smul]
  module

theorem gramMatrix_cycle (i : Fin 3) :
    d.scalarParameters.gramMatrix i (nextHolonomy i) =
      d.hermitianConstants i * d.hermitianConstants (nextHolonomy i) - mixedConstant d i := by
  fin_cases i
  · rfl
  · rfl
  · change d.hermitianConstants 0 * d.hermitianConstants 2 - d.mixed13 =
      d.hermitianConstants 2 * d.hermitianConstants 0 - d.mixed13
    rw [mul_comm]

omit [StarModule ℝ A] [SMulCommClass ℝ A A] in
theorem cyclicPair_binding (i : Fin 3) (ξ : A) (hξ : P 0 * ξ = ξ) :
    pairCliffordDefect (P 0)
      (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
      (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 (nextHolonomy i))
      (d.hermitianConstants i) (d.hermitianConstants (nextHolonomy i)) (mixedConstant d i) * ξ =
    cliffordPairDefect
      (fun j => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 j))
      d.scalarParameters i (nextHolonomy i) ξ := by
  rw [cliffordPairDefect, gramMatrix_cycle]
  exact pairDefect_action _ _ _ _ _ _ ξ hξ

include hp hstar hc in
theorem pairOnCombination_value (i : Fin 3) (e : HolonomyPath.Combination) :
    evaluate P (pairOnCombination d C i e) =
      cliffordPairDefect
        (fun j => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 j))
        d.scalarParameters i (nextHolonomy i) (HolonomyPath.combinationValue P d e) := by
  rw [pairOnCombination, extendPaths_value P d _ (leftAction _)
    (pairOnPath_value P hp hstar d C hc i)]
  exact cyclicPair_binding P d i _ (HolonomyPath.combinationValue_supported P d hp e)

end Values

theorem mixedOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : (mixedOnPath d C i p).HasHorizon (7 + 3 * p.length) := by
  apply PurityVectorExpression.hasHorizon_scale
  apply PurityVectorExpression.hasHorizon_append
  · apply PurityVectorExpression.hasHorizon_append
    · apply hasHorizon_mono (pairOnWord_horizon C _ _ _ _)
      simp only [List.length_append, HolonomyPath.word_length, List.length_singleton]
      omega
    · apply hasHorizon_mono (pairOnWord_horizon C _ _ _ _)
      simp only [List.length_append, HolonomyPath.word_length, List.length_singleton]
      omega
  · exact tripleBaseOnPath_horizon C i p _

theorem pairOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : (pairOnPath d C i p).HasHorizon (8 + 3 * p.length) := by
  apply PurityVectorExpression.hasHorizon_append
  · apply PurityVectorExpression.hasHorizon_scale
    exact hasHorizon_mono (mixedOnPath_horizon d C i p) (by omega)
  · apply PurityVectorExpression.hasHorizon_scale
    apply PurityVectorExpression.hasHorizon_append
    · apply PurityVectorExpression.hasHorizon_append
      · apply PurityVectorExpression.hasHorizon_append
        · apply PurityVectorExpression.hasHorizon_scale
          exact hasHorizon_mono (hermitianOnPath_horizon d C i _) (by simp only [List.length_cons]; omega)
        · apply hasHorizon_leftMultiply
          exact hasHorizon_mono (hermitianOnPath_horizon d C _ p) (by omega)
      · apply PurityVectorExpression.hasHorizon_scale
        exact hasHorizon_mono (hermitianOnPath_horizon d C _ _) (by simp only [List.length_cons]; omega)
    · apply hasHorizon_leftMultiply
      exact hasHorizon_mono (hermitianOnPath_horizon d C i p) (by omega)

theorem pairOnCombination_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) (depth : ℕ) (hd : HolonomyPath.HasDepth e depth) :
    (pairOnCombination d C i e).HasHorizon (8 + 3 * depth) := by
  apply extendPaths_horizon d _ e depth _ hd
  intro p hp
  exact hasHorizon_mono (pairOnPath_horizon d C i p) (by omega)

end CornerResidualBuilder
end AlbertSequential
