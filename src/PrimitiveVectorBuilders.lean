/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PurityVectorExpressions
public import HolonomyPathCombinations
public import CornerPrimitiveBinding
public import PrimitiveWordSupport

/-! Actual primitive vector lists and measured-history bounds used by the full
constructor. Efficient base-0 paths do not acquire a spurious extra base letter. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression

def faceFirst (i : Fin 3) : Fin 4 := HolonomyPath.firstLabel (HolonomyPath.positiveIndex i)
def faceSecond (i : Fin 3) : Fin 4 := HolonomyPath.secondLabel (HolonomyPath.positiveIndex i)
def faceThird : Fin 3 → Fin 4 := ![3, 1, 2]
def faceTriangle (d : CornerNumericalData) : Fin 3 → ℝ := ![d.r012, d.r023, d.r031]
def faceQ (d : CornerNumericalData) : Fin 3 → ℝ := ![d.q123, d.q231, d.q312]

def pairOnWord (C : Fin 4 → Word (Fin 4) → ℝ) (a b : Fin 4)
    (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) : PurityVectorExpression 4 :=
  ofPrimitiveTerms a (C a) [(1, [(b, true)])] t U

def pairBaseOnPath (C : Fin 4 → Word (Fin 4) → ℝ) (b : Fin 4)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) : PurityVectorExpression 4 :=
  ofPrimitiveTerms 0 (C 0) [(1, [(b, true)])] (HolonomyPath.historyPrefix p) U

def triangleBaseOnPath (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) : PurityVectorExpression 4 :=
  ofPrimitiveTerms 0 (C 0) (accessWordTerms (faceFirst i) [(faceSecond i, true)])
    (HolonomyPath.historyPrefix p) U

def tripleBaseOnPath (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) : PurityVectorExpression 4 :=
  ofPrimitiveTerms 0 (C 0) (polarizedTripleWordTerms (faceFirst i) (faceSecond i) (faceThird i))
    (HolonomyPath.historyPrefix p) (FiniteRealWordFunctional.scale (1 / 2) U)

def triangleFarOnWord (C : Fin 4 → Word (Fin 4) → ℝ)
    (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) : PurityVectorExpression 4 :=
  ofPrimitiveTerms 1 (C 1) (accessWordTerms 2 [(3, true)]) t U

theorem triangle_access (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (hc : CornerScalarConditions d C) (i : Fin 3) :
    C 0 [(faceSecond i, true)] + C 0 [(faceFirst i, true), (faceSecond i, true)] -
      C 0 [(faceFirst i, false), (faceSecond i, true)] = 2 * faceTriangle d i := by
  fin_cases i
  · exact hc.triangle_012
  · exact hc.triangle_023
  · exact hc.triangle_031

theorem triple_access (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (hc : CornerScalarConditions d C) (i : Fin 3) :
    weightedWordScalar (C 0) (polarizedTripleWordTerms (faceFirst i) (faceSecond i) (faceThird i)) =
      4 * faceQ d i := by
  fin_cases i
  · exact hc.triple_123
  · exact hc.triple_231
  · exact hc.triple_312

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
  (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)

include hp hstar hc in
theorem pairOnWord_value (a b : Fin 4) (hne : a ≠ b) (t : Word (Fin 4))
    (U : FiniteRealWordFunctional 4) :
    evaluate P (pairOnWord C a b t U) =
      U.amplitudeValue P * (pairDefectElement (P a) (P b) (d.overlap a b) * wordAmplitude P t) := by
  rw [pairOnWord, evaluate_ofPrimitiveTerms]
  simp only [weightedPurityResidual, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, one_smul, add_zero]
  rw [outcomePurityElement_append_base P hp,
    ← pairDefectElement_primitive P hp hstar a b, hc.pair_access a b hne]

include hp hstar hc in
theorem pairBaseOnPath_value (b : Fin 4) (hne : (0 : Fin 4) ≠ b) (p : List (Fin 6))
    (U : FiniteRealWordFunctional 4) :
    evaluate P (pairBaseOnPath C b p U) = U.amplitudeValue P *
      (pairDefectElement (P 0) (P b) (d.overlap 0 b) * wordAmplitude P (HolonomyPath.word p)) := by
  rw [pairBaseOnPath, evaluate_ofPrimitiveTerms, ← HolonomyPath.word_eq_prefix p]
  simp only [weightedPurityResidual, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, one_smul, add_zero]
  rw [← pairDefectElement_primitive P hp hstar 0 b, hc.pair_access 0 b hne]

include hp hstar hc in
theorem triangleBaseOnPath_value (i : Fin 3) (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    evaluate P (triangleBaseOnPath C i p U) = U.amplitudeValue P *
      (triangleDefectElement (P 0) (P (faceFirst i)) (P (faceSecond i)) (faceTriangle d i) *
        wordAmplitude P (HolonomyPath.word p)) := by
  rw [triangleBaseOnPath, evaluate_ofPrimitiveTerms, ← HolonomyPath.word_eq_prefix p,
    ← triangleDefectElement_primitive P hp hstar 0 (faceFirst i) (faceSecond i) (C 0)
      (faceTriangle d i) (triangle_access d C hc i)]

include hp hstar hc in
theorem tripleBaseOnPath_value (i : Fin 3) (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    evaluate P (tripleBaseOnPath C i p U) = U.amplitudeValue P *
      (tripleDefectElement (P 0) (P (faceFirst i)) (P (faceSecond i)) (P (faceThird i)) (faceQ d i) *
        wordAmplitude P (HolonomyPath.word p)) := by
  rw [tripleBaseOnPath, evaluate_ofPrimitiveTerms, ← HolonomyPath.word_eq_prefix p,
    FiniteRealWordFunctional.amplitudeValue_scale,
    tripleDefectElement_primitive P hp hstar 0 (faceFirst i) (faceSecond i) (faceThird i)
      (C 0) (faceQ d i) (triple_access d C hc i)]
  simp only [smul_mul_assoc, mul_smul_comm]

include hp hstar hc in
theorem triangleFarOnWord_value (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) :
    evaluate P (triangleFarOnWord C t U) = U.amplitudeValue P *
      (triangleDefectElement (P 1) (P 2) (P 3) d.r123 * wordAmplitude P t) := by
  rw [triangleFarOnWord, evaluate_ofPrimitiveTerms,
    ← triangleDefectElement_primitive P hp hstar 1 2 3 (C 1) d.r123 hc.triangle_123,
    triangleDefect_history_support P hp]

end Values

theorem pairOnWord_horizon (C : Fin 4 → Word (Fin 4) → ℝ) (a b : Fin 4)
    (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) :
    (pairOnWord C a b t U).HasHorizon (t.length + 3) := by
  apply hasHorizon_ofPrimitiveTerms
  intro x hx
  have hx' : x = (1, [(b, true)]) := List.mem_singleton.mp hx
  rw [hx']
  simp only [List.length_singleton]
  omega

theorem pairBaseOnPath_horizon (C : Fin 4 → Word (Fin 4) → ℝ) (b : Fin 4)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    (pairBaseOnPath C b p U).HasHorizon (3 + 3 * p.length) := by
  apply hasHorizon_ofPrimitiveTerms
  intro x hx
  have hx' : x = (1, [(b, true)]) := List.mem_singleton.mp hx
  rw [hx', HolonomyPath.prefix_length]
  simp only [List.length_singleton]
  omega

theorem triangleBaseOnPath_horizon (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    (triangleBaseOnPath C i p U).HasHorizon (5 + 3 * p.length) := by
  apply hasHorizon_ofPrimitiveTerms
  intro x hx
  have h := accessWordTerms_wordLength (faceFirst i) [(faceSecond i, true)] x hx
  rw [HolonomyPath.prefix_length]
  simp only [List.length_singleton] at h
  omega

theorem tripleBaseOnPath_horizon (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3)
    (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    (tripleBaseOnPath C i p U).HasHorizon (7 + 3 * p.length) := by
  apply hasHorizon_ofPrimitiveTerms
  intro x hx
  have h := polarizedTripleWordTerms_wordLength (faceFirst i) (faceSecond i) (faceThird i) x hx
  rw [HolonomyPath.prefix_length]
  omega

theorem triangleFarOnWord_horizon (C : Fin 4 → Word (Fin 4) → ℝ)
    (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) :
    (triangleFarOnWord C t U).HasHorizon (t.length + 5) := by
  apply hasHorizon_ofPrimitiveTerms
  intro x hx
  have h := accessWordTerms_wordLength (2 : Fin 4) [(3, true)] x hx
  simp only [List.length_singleton] at h
  omega

end CornerResidualBuilder
end AlbertSequential
