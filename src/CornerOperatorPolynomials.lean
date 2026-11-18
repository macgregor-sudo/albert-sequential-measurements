/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HolonomyPathCombinations

/-! Actual finite left coefficient polynomials. Their words are genuine
amplitudes; they are not additional measured support or probability products. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerOperatorPolynomial
open FiniteRealWordFunctional

def projection (i : Fin 4) : FiniteRealWordFunctional 4 := amplitudeWord [(i, true)]
def holonomy (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  HolonomyPath.polynomial d [HolonomyPath.positiveIndex i]
def hermitian (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  scale (1 / 2) (append (holonomy d i) (amplitudeStar (holonomy d i)))
def skew (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  scale (1 / 2) (append (holonomy d i) (scale (-1) (amplitudeStar (holonomy d i))))
def approximation (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  append (scale (d.hermitianConstants i) (projection 0)) (skew d i)
def squareLeading (d : CornerNumericalData) (i : Fin 3) : FiniteRealWordFunctional 4 :=
  append (hermitian d i) (scale (d.hermitianConstants i) (projection 0))
def product3 (a b c : FiniteRealWordFunctional 4) : FiniteRealWordFunctional 4 :=
  amplitudeMultiply (amplitudeMultiply a b) c
def volume (d : CornerNumericalData) : FiniteRealWordFunctional 4 :=
  scale (1 / 2) (append (product3 (skew d 0) (skew d 1) (skew d 2))
    (scale (-1) (product3 (skew d 2) (skew d 1) (skew d 0))))
def applyBase (U : FiniteRealWordFunctional 4) : FiniteRealWordFunctional 4 :=
  amplitudeMultiply U (projection 0)
def gramVector (d : CornerNumericalData) : FiniteRealWordFunctional 4 :=
  combine [applyBase (product3 (skew d 0) (skew d 1) (skew d 2)),
    scale d.scalarParameters.w (applyBase (skew d 0)),
    scale (-d.scalarParameters.v) (applyBase (skew d 1)),
    scale d.scalarParameters.u (applyBase (skew d 2))]
def dataLeftVector (d : CornerNumericalData) : FiniteRealWordFunctional 4 :=
  append (applyBase (volume d)) (scale d.scalarParameters.d0 (projection 0))
def volumeLeftVector (d : CornerNumericalData) : FiniteRealWordFunctional 4 :=
  append (applyBase (volume d)) (gramVector d)

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData)

omit [StarRing A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem projection_value (i : Fin 4) : (projection i).amplitudeValue P = P i := by
  simp only [projection, amplitudeValue_word, wordAmplitude_singleton, algebraicOutcome, ite_true]

include hp in
omit [StarRing A] [StarModule ℝ A] in
theorem holonomy_value (i : Fin 3) : (holonomy d i).amplitudeValue P =
    CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i := by
  rw [holonomy, HolonomyPath.polynomial_evaluates_operator P hp,
    HolonomyPath.operator, HolonomyPath.operator, HolonomyPath.generator_positive]
  exact (CornerHolonomy.normalizedCyclicHolonomies_supported
    (P 0) (P 1) (P 2) (P 3) (hp 0) d.ν0 d.ν1 d.ν2 i).2

include hp hstar in
theorem hermitian_value (i : Fin 3) : (hermitian d i).amplitudeValue P =
    CornerHolonomy.hermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) := by
  simp only [hermitian, amplitudeValue_scale, amplitudeValue_append,
    amplitudeValue_star P hstar, holonomy_value P hp d, CornerHolonomy.hermitianPart]

include hp hstar in
theorem skew_value (i : Fin 3) : (skew d i).amplitudeValue P =
    CornerHolonomy.skewHermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) := by
  simp only [skew, amplitudeValue_scale, amplitudeValue_append,
    amplitudeValue_star P hstar, holonomy_value P hp d,
    CornerHolonomy.skewHermitianPart, neg_one_smul, sub_eq_add_neg]

include hp hstar in
theorem approximation_value (i : Fin 3) : (approximation d i).amplitudeValue P =
    CornerHolonomy.centeredApproximation (P 0)
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
      (d.hermitianConstants i) := by
  simp only [approximation, amplitudeValue_append, amplitudeValue_scale,
    projection_value, skew_value P hp hstar d, CornerHolonomy.centeredApproximation]

include hp hstar in
theorem squareLeading_value (i : Fin 3) : (squareLeading d i).amplitudeValue P =
    CornerHolonomy.hermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) +
        d.hermitianConstants i • P 0 := by
  simp only [squareLeading, amplitudeValue_append, amplitudeValue_scale,
    projection_value, hermitian_value P hp hstar d]

omit [StarRing A] [StarModule ℝ A] in
theorem product3_value (a b c : FiniteRealWordFunctional 4) :
    (product3 a b c).amplitudeValue P = a.amplitudeValue P * b.amplitudeValue P * c.amplitudeValue P := by
  simp only [product3, amplitudeValue_multiply]

include hp hstar in
theorem volume_value : (volume d).amplitudeValue P =
    cliffordVolume (fun i => CornerHolonomy.skewHermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)) := by
  simp only [volume, amplitudeValue_scale, amplitudeValue_append, product3_value,
    skew_value P hp hstar d, cliffordVolume, neg_one_smul, sub_eq_add_neg]

omit [StarRing A] [StarModule ℝ A] in
theorem applyBase_value (U : FiniteRealWordFunctional 4) :
    (applyBase U).amplitudeValue P = U.amplitudeValue P * P 0 := by
  simp only [applyBase, amplitudeValue_multiply, projection_value]

include hp hstar in
theorem gramVector_value : (gramVector d).amplitudeValue P =
    cliffordGramVector (fun i => CornerHolonomy.skewHermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)) (P 0)
      d.scalarParameters := by
  simp only [gramVector, amplitudeValue_combine, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, amplitudeValue_scale, applyBase_value, product3_value,
    skew_value P hp hstar d, cliffordGramVector, cliffordTripleVector]
  module

include hp hstar in
theorem dataLeftVector_value : (dataLeftVector d).amplitudeValue P =
    cliffordVolume (fun i => CornerHolonomy.skewHermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)) * P 0 +
        d.scalarParameters.d0 • P 0 := by
  simp only [dataLeftVector, amplitudeValue_append, applyBase_value,
    amplitudeValue_scale, projection_value, volume_value P hp hstar d]

include hp hstar in
theorem volumeLeftVector_value : (volumeLeftVector d).amplitudeValue P =
    cliffordVolume (fun i => CornerHolonomy.skewHermitianPart
      (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)) * P 0 +
      cliffordGramVector (fun i => CornerHolonomy.skewHermitianPart
        (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)) (P 0)
          d.scalarParameters := by
  simp only [volumeLeftVector, amplitudeValue_append, applyBase_value,
    volume_value P hp hstar d, gramVector_value P hp hstar d]

end Values
end CornerOperatorPolynomial
end AlbertSequential
