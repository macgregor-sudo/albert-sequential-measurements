/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ResidualPathLinearExtension

/-! The literal square-defect vector builder and its extension. Every
unitarity and Hermitian defect remains in the produced residual list. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy

def squareOnPath (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) : PurityVectorExpression 4 :=
  leftMultiply (CornerOperatorPolynomial.squareLeading d i) (hermitianOnPath d C i p) ++
    scale (-(1 / 2)) (rightUnitarityOnPath d C i p ++ leftUnitarityOnPath d C i p)

def hermitianOnCombination (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) : PurityVectorExpression 4 :=
  extendPaths d (hermitianOnPath d C i) e

def squareOnCombination (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) : PurityVectorExpression 4 :=
  extendPaths d (squareOnPath d C i) e

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar hc in
theorem squareOnPath_value (i : Fin 3) (p : List (Fin 6)) :
    evaluate P (squareOnPath d C i p) =
      squareCliffordDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
        (d.hermitianConstants i) * wordAmplitude P (HolonomyPath.word p) := by
  rw [squareOnPath, evaluate_append, evaluate_leftMultiply, evaluate_scale, evaluate_append,
    hermitianOnPath_value P hp hstar d C hc,
    rightUnitarityOnPath_value P hp hstar d C hc,
    leftUnitarityOnPath_value P hp hstar d C hc,
    CornerOperatorPolynomial.squareLeading_value P hp hstar d,
    squareDefect_reduction (P 0) _ (hp 0) (hstar 0)
      (normalizedCyclicHolonomies_supported (P 0) (P 1) (P 2) (P 3) (hp 0) d.ν0 d.ν1 d.ν2 i)]
  simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc]
  module

include hp hstar hc in
theorem hermitianOnCombination_value (i : Fin 3) (e : HolonomyPath.Combination) :
    evaluate P (hermitianOnCombination d C i e) =
      hermitianDefect (P 0)
        (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
        (d.hermitianConstants i) * HolonomyPath.combinationValue P d e := by
  exact extendPaths_value P d _ (leftAction _) (hermitianOnPath_value P hp hstar d C hc i) e

include hp hstar hc in
theorem squareOnCombination_value (i : Fin 3) (e : HolonomyPath.Combination) :
    evaluate P (squareOnCombination d C i e) =
      cliffordSquareDefect
        (fun j => skewHermitianPart (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 j))
        d.scalarParameters i (HolonomyPath.combinationValue P d e) := by
  rw [squareOnCombination, extendPaths_value P d _ (leftAction _)
    (squareOnPath_value P hp hstar d C hc i)]
  exact cornerSquareDefect_binding (P 0) _ d.hermitianConstants d.mixed12 d.mixed13 d.mixed23
    d.cubicConstant _ (HolonomyPath.combinationValue_supported P d hp e) i

end Values

theorem squareOnPath_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (p : List (Fin 6)) :
    (squareOnPath d C i p).HasHorizon (5 + 3 * p.length) :=
  hasHorizon_append _ _ _
    (hasHorizon_leftMultiply _ _ _ (hermitianOnPath_horizon d C i p))
    (hasHorizon_scale _ _ _ (hasHorizon_append _ _ _
      (rightUnitarityOnPath_horizon d C i p) (leftUnitarityOnPath_horizon d C i p)))

theorem hermitianOnCombination_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) (depth : ℕ) (hd : HolonomyPath.HasDepth e depth) :
    (hermitianOnCombination d C i e).HasHorizon (5 + 3 * depth) := by
  apply extendPaths_horizon d _ e depth _ hd
  intro p hp
  exact hasHorizon_mono (hermitianOnPath_horizon d C i p) (by omega)

theorem squareOnCombination_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) (e : HolonomyPath.Combination) (depth : ℕ) (hd : HolonomyPath.HasDepth e depth) :
    (squareOnCombination d C i e).HasHorizon (5 + 3 * depth) := by
  apply extendPaths_horizon d _ e depth _ hd
  intro p hp
  exact hasHorizon_mono (squareOnPath_horizon d C i p) (by omega)

end CornerResidualBuilder
end AlbertSequential
