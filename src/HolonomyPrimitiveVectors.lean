/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PrimitiveVectorBuilders
public import CornerOperatorPolynomials

/-! Literal H and unitarity residual-vector lists. Normalizer inverses are
state-independent; no history probability is divided by. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression FiniteRealWordFunctional CornerHolonomy

def hermitianOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  triangleBaseOnPath C i p (emptyWordTerm ((2 * d.normalizer i)⁻¹))

/-- The unscaled reverse-product identity, with the shared trailing base
removed from the actual right history. -/
def reverseProductOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (k l : Fin 4) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  pairOnWord C k 0 (HolonomyPath.word p ++ [(l, true)])
      (amplitudeMultiply (CornerOperatorPolynomial.projection 0) (CornerOperatorPolynomial.projection l)) ++
    pairOnWord C l k (HolonomyPath.word p)
      (scale (d.overlap k 0) (CornerOperatorPolynomial.projection 0)) ++
    pairBaseOnPath C l p (emptyWordTerm (d.overlap k 0 * d.overlap l k))

def leftUnitarityOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  PurityVectorExpression.scale ((d.normalizer i ^ 2)⁻¹)
    (reverseProductOnPath d C (faceFirst i) (faceSecond i) p)

def rightUnitarityOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  PurityVectorExpression.scale ((d.normalizer i ^ 2)⁻¹)
    (reverseProductOnPath d C (faceSecond i) (faceFirst i) p)

theorem faceFirst_ne_zero (i : Fin 3) : faceFirst i ≠ 0 := by fin_cases i <;> decide
theorem faceSecond_ne_zero (i : Fin 3) : faceSecond i ≠ 0 := by fin_cases i <;> decide
theorem faceFirst_ne_second (i : Fin 3) : faceFirst i ≠ faceSecond i := by fin_cases i <;> decide

theorem normalizerSquare_face (d : CornerNumericalData) (i : Fin 3) :
    d.normalizerSquare i = d.overlap (faceFirst i) 0 *
      d.overlap (faceSecond i) (faceFirst i) * d.overlap 0 (faceSecond i) := by
  fin_cases i <;> rfl

theorem constant_face (d : CornerNumericalData) (i : Fin 3) :
    d.hermitianConstants i = faceTriangle d i / d.normalizer i := by fin_cases i <;> rfl

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

omit [StarRing A] [StarModule ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem holonomy_face (i : Fin 3) :
    normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i =
      normalizedCornerWord (P 0) (P (faceFirst i)) (P (faceSecond i)) (d.normalizer i) := by
  fin_cases i <;> rfl

include hp hstar hc in
theorem hermitianOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (hermitianOnPath d C i p) =
      hermitianDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
        (d.hermitianConstants i) * wordAmplitude P (HolonomyPath.word p) := by
  rw [hermitianOnPath, triangleBaseOnPath_value P hp hstar d C hc,
    amplitudeValue_emptyWordTerm, smul_mul_assoc, one_mul, holonomy_face P d,
    constant_face]
  have he := normalizedHermitian_defect_expansion (P 0) (P (faceFirst i)) (P (faceSecond i))
    (hstar 0) (hstar _) (hstar _) (faceTriangle d i) (d.normalizer i) (hc.normalizers_nonzero i)
  rw [← he, smul_mul_assoc, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) (hc.normalizers_nonzero i)), one_smul]

include hp hstar hc in
omit [StarModule ℝ A] in
theorem reverseProductOnPath_value (k l : Fin 4) (hk : k ≠ 0) (hl : l ≠ 0)
    (hkl : k ≠ l) (p : List (Fin 6)) :
    evaluate P (reverseProductOnPath d C k l p) =
      (P 0 * P l * pairDefectElement (P k) (P 0) (d.overlap k 0) * P l * P 0 +
        d.overlap k 0 • (P 0 * pairDefectElement (P l) (P k) (d.overlap l k) * P 0) +
        (d.overlap k 0 * d.overlap l k) • pairDefectElement (P 0) (P l) (d.overlap 0 l)) *
          wordAmplitude P (HolonomyPath.word p) := by
  rw [reverseProductOnPath, PurityVectorExpression.evaluate_append, PurityVectorExpression.evaluate_append,
    pairOnWord_value P hp hstar d C hc k 0 hk,
    pairOnWord_value P hp hstar d C hc l k hkl.symm,
    pairBaseOnPath_value P hp hstar d C hc l hl.symm,
    amplitudeValue_multiply, CornerOperatorPolynomial.projection_value,
    CornerOperatorPolynomial.projection_value,
    amplitudeValue_scale, CornerOperatorPolynomial.projection_value,
    amplitudeValue_emptyWordTerm, wordAmplitude_append_singleton]
  simp only [algebraicOutcome, ite_true, smul_mul_assoc, add_mul, mul_assoc, one_mul]
  rw [HolonomyPath.amplitude_supported P hp]

include hp hstar hc in
theorem leftUnitarityOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (leftUnitarityOnPath d C i p) =
      leftUnitarityDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) *
          wordAmplitude P (HolonomyPath.word p) := by
  rw [leftUnitarityOnPath, PurityVectorExpression.evaluate_scale,
    reverseProductOnPath_value P hp hstar d C hc _ _ (faceFirst_ne_zero i)
      (faceSecond_ne_zero i) (faceFirst_ne_second i)]
  have hs := hc.normalizers_square i
  rw [normalizerSquare_face] at hs
  have he := normalizedLeftUnitarity_defect_expansion (P 0) (P (faceFirst i)) (P (faceSecond i))
    (hp 0) (hstar 0) (hstar _) (hstar _)
    (d.overlap (faceFirst i) 0) (d.overlap (faceSecond i) (faceFirst i))
    (d.overlap 0 (faceSecond i)) (d.normalizer i) (hc.normalizers_nonzero i) hs
  rw [← he, smul_mul_assoc, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hc.normalizers_nonzero i)), one_smul,
    holonomy_face P d]

include hp hstar hc in
theorem rightUnitarityOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (rightUnitarityOnPath d C i p) =
      rightUnitarityDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) *
          wordAmplitude P (HolonomyPath.word p) := by
  rw [rightUnitarityOnPath, PurityVectorExpression.evaluate_scale,
    reverseProductOnPath_value P hp hstar d C hc _ _ (faceSecond_ne_zero i)
      (faceFirst_ne_zero i) (faceFirst_ne_second i).symm]
  have hs := hc.normalizers_square i
  rw [normalizerSquare_face] at hs
  have he := normalizedRightUnitarity_defect_expansion (P 0) (P (faceFirst i)) (P (faceSecond i))
    (hp 0) (hstar 0) (hstar _) (hstar _)
    (d.overlap (faceFirst i) 0) (d.overlap (faceSecond i) (faceFirst i))
    (d.overlap 0 (faceSecond i)) (d.normalizer i) (hc.normalizers_nonzero i) hs
  rw [d.overlap_symmetric (faceSecond i) 0, d.overlap_symmetric (faceFirst i) (faceSecond i)]
  rw [d.overlap_symmetric (faceFirst i) 0] at he
  rw [← he, smul_mul_assoc, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hc.normalizers_nonzero i)), one_smul,
    holonomy_face P d]

end Values

theorem hasHorizon_mono {e : PurityVectorExpression 4} {a b : ℕ}
    (he : e.HasHorizon a) (hab : a ≤ b) : e.HasHorizon b := by
  intro t ht w hw
  exact (he t ht w hw).trans hab

theorem hermitianOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) :
    (hermitianOnPath d C i p).HasHorizon (5 + 3 * p.length) :=
  triangleBaseOnPath_horizon C i p _

theorem reverseProductOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (k l : Fin 4) (p : List (Fin 6)) :
    (reverseProductOnPath d C k l p).HasHorizon (5 + 3 * p.length) := by
  apply PurityVectorExpression.hasHorizon_append
  · apply PurityVectorExpression.hasHorizon_append
    · apply hasHorizon_mono (pairOnWord_horizon C k 0 _ _)
      simp only [List.length_append, HolonomyPath.word_length, List.length_singleton]
      omega
    · apply hasHorizon_mono (pairOnWord_horizon C l k _ _)
      rw [HolonomyPath.word_length]
      omega
  · exact hasHorizon_mono (pairBaseOnPath_horizon C l p _) (by omega)

theorem leftUnitarityOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) :
    (leftUnitarityOnPath d C i p).HasHorizon (5 + 3 * p.length) :=
  PurityVectorExpression.hasHorizon_scale _ _ _ (reverseProductOnPath_horizon d C _ _ p)

theorem rightUnitarityOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) :
    (rightUnitarityOnPath d C i p).HasHorizon (5 + 3 * p.length) :=
  PurityVectorExpression.hasHorizon_scale _ _ _ (reverseProductOnPath_horizon d C _ _ p)

end CornerResidualBuilder
end AlbertSequential
