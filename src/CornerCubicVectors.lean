/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerMixedVectors

/-! The six actual far-face residual terms at the base vector. Literal right
histories have at most three letters; no fixed array or rank input is used. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression CornerHolonomy

def projectionProduct : List (Fin 4) → FiniteRealWordFunctional 4
  | [] => FiniteRealWordFunctional.emptyWordTerm 1
  | i :: is => FiniteRealWordFunctional.amplitudeMultiply
      (CornerOperatorPolynomial.projection i) (projectionProduct is)

def cubicAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    PurityVectorExpression 4 :=
  scale ((2 * (d.ν0 * d.ν1 * d.ν2))⁻¹)
    (pairOnWord C 3 0 [(0, true), (1, true)] (projectionProduct [0, 1, 2, 0, 2]) ++
      scale d.o03 (pairOnWord C 2 0 [(0, true), (1, true), (3, true)] (projectionProduct [0, 1])) ++
      pairOnWord C 2 0 [(0, true), (1, true)] (projectionProduct [0, 1, 3, 0, 3]) ++
      scale d.o02 (pairOnWord C 3 0 [(0, true), (1, true), (2, true)] (projectionProduct [0, 1])) ++
      scale (d.o02 * d.o03) (triangleFarOnWord C [(0, true)] (projectionProduct [0])) ++
      scale (2 * d.o02 * d.o03 * d.r123)
        (pairBaseOnPath C 1 [] (FiniteRealWordFunctional.emptyWordTerm 1)))

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

omit [StarRing A] [StarModule ℝ A] in
theorem projectionProduct_value (is : List (Fin 4)) :
    (projectionProduct is).amplitudeValue P = is.foldr (fun i x => P i * x) 1 := by
  induction is with
  | nil => simp only [projectionProduct, FiniteRealWordFunctional.amplitudeValue_emptyWordTerm, one_smul, List.foldr_nil]
  | cons i is ih =>
      rw [projectionProduct, FiniteRealWordFunctional.amplitudeValue_multiply,
        CornerOperatorPolynomial.projection_value, ih]
      rfl

include hp hstar hc in
theorem cubicAtBase_value : evaluate P (cubicAtBase d C) =
    cornerCubicDefect (P 0)
      (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2)
      d.cubicConstant * P 0 := by
  simp only [cubicAtBase, evaluate_scale, evaluate_append,
    pairOnWord_value P hp hstar d C hc 3 0 (by decide),
    pairOnWord_value P hp hstar d C hc 2 0 (by decide),
    triangleFarOnWord_value P hp hstar d C hc,
    pairBaseOnPath_value P hp hstar d C hc 1 (by decide), projectionProduct_value,
    FiniteRealWordFunctional.amplitudeValue_emptyWordTerm,
    List.foldr_cons, List.foldr_nil, mul_one, one_mul,
    wordAmplitude_cons, wordAmplitude_nil, HolonomyPath.word,
    algebraicOutcome, ite_true]
  have hn0 := hc.normalizers_nonzero 0
  have hn1 := hc.normalizers_nonzero 1
  have hn2 := hc.normalizers_nonzero 2
  change d.ν0 ≠ 0 at hn0
  change d.ν1 ≠ 0 at hn1
  change d.ν2 ≠ 0 at hn2
  have he := normalizedCubic_defect_expansion (P 0) (P 1) (P 2) (P 3) (hp 0)
    (hstar 0) (hstar 1) (hstar 2) (hstar 3) d.o01 d.o02 d.o03 d.r123
    d.ν0 d.ν1 d.ν2 hn0 hn1 hn2
  have hn : 2 * (d.ν0 * d.ν1 * d.ν2) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
  have he' := congrArg (fun x : A => (2 * (d.ν0 * d.ν1 * d.ν2))⁻¹ • (x * P 0)) he
  simp only [smul_mul_assoc, smul_smul, inv_mul_cancel₀ hn, one_smul] at he'
  simp only [add_mul, smul_mul_assoc, mul_assoc, hp 0,
    pairDefect_right_support (P 0) (P 1) (hp 0)] at he'
  simpa only [CornerNumericalData.overlap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    one_smul, one_mul, CornerNumericalData.cubicConstant, smul_mul_assoc, mul_assoc,
    pairDefect_right_support (P 0) (P 1) (hp 0)] using he'.symm

end Values

theorem cubicAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    (cubicAtBase d C).HasHorizon 6 := by
  apply hasHorizon_scale
  repeat' apply hasHorizon_append
  · exact hasHorizon_mono (pairOnWord_horizon C 3 0 _ _) (by decide)
  · exact hasHorizon_scale _ _ _ (pairOnWord_horizon C 2 0 _ _)
  · exact hasHorizon_mono (pairOnWord_horizon C 2 0 _ _) (by decide)
  · exact hasHorizon_scale _ _ _ (pairOnWord_horizon C 3 0 _ _)
  · exact hasHorizon_scale _ _ _ (triangleFarOnWord_horizon C _ _)
  · exact hasHorizon_scale _ _ _ (hasHorizon_mono (pairBaseOnPath_horizon C 1 [] _) (by decide))

end CornerResidualBuilder
end AlbertSequential
