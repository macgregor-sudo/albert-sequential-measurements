/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertProjectiveData

/-! Concrete chronological operator effects and their exact class-(I) state
values. The raw Hilbert-space definitions use composition and adjoint; the
algebraic word definitions are bound to them for every outcome word. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {ι 𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

def boundedOutcome (P : ι → H →L[𝕜] H) (a : Outcome ι) : H →L[𝕜] H :=
  if a.2 then P a.1 else ContinuousLinearMap.id 𝕜 H - P a.1

/-- Chronological outcomes act on the left of the accumulated amplitude. -/
def boundedWordAmplitude (P : ι → H →L[𝕜] H) (w : Word ι) : H →L[𝕜] H :=
  w.foldl (fun T a => (boundedOutcome P a).comp T) (ContinuousLinearMap.id 𝕜 H)

/-- The first chronological outcome is the outermost Heisenberg compression. -/
def boundedWordEffect (P : ι → H →L[𝕜] H) : Word ι → H →L[𝕜] H
  | [] => ContinuousLinearMap.id 𝕜 H
  | a :: w => ((boundedOutcome P a).comp (boundedWordEffect P w)).comp (boundedOutcome P a)

omit [CompleteSpace H] in
theorem boundedWordAmplitude_eq_wordAmplitude (P : ι → H →L[𝕜] H) (w : Word ι) :
    boundedWordAmplitude P w = wordAmplitude P w := rfl

omit [CompleteSpace H] in
theorem boundedWordAmplitude_append (P : ι → H →L[𝕜] H) (u v : Word ι) :
    boundedWordAmplitude P (u ++ v) =
      (boundedWordAmplitude P v).comp (boundedWordAmplitude P u) := by
  simp only [boundedWordAmplitude_eq_wordAmplitude, wordAmplitude_append]
  rfl

theorem boundedWordEffect_eq_wordOperator (P : ι → H →L[𝕜] H)
    (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    boundedWordEffect P w = wordOperator P w := by
  induction w with
  | nil => rw [wordOperator_nil]; rfl
  | cons a w ih =>
    rw [boundedWordEffect, wordOperator_cons P hstar, ← ih]
    rfl

theorem boundedWordEffect_eq_star_mul (P : ι → H →L[𝕜] H)
    (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    boundedWordEffect P w =
      (ContinuousLinearMap.adjoint (boundedWordAmplitude P w)).comp
        (boundedWordAmplitude P w) := by
  rw [boundedWordEffect_eq_wordOperator P hstar]
  rfl

theorem boundedWordEffect_singleton (P : ι → H →L[𝕜] H)
    (hP : ∀ i, IsStarProjection (P i)) (a : Outcome ι) :
    boundedWordEffect P [a] = boundedOutcome P a := by
  rw [boundedWordEffect_eq_wordOperator P (fun i => (hP i).isSelfAdjoint),
    wordOperator_singleton P (fun i => (hP i).isIdempotentElem)
      (fun i => (hP i).isSelfAdjoint)]
  rfl

theorem boundedWordEffect_isPositive (P : ι → H →L[𝕜] H)
    (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    (boundedWordEffect P w).IsPositive := by
  rw [boundedWordEffect_eq_star_mul P hstar]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

omit [CompleteSpace H] in
theorem operatorValue_algebraicOutcome (P : ι → HilbertOperatorAlgebra 𝕜 H)
    (a : Outcome ι) : operatorValue 𝕜 H (algebraicOutcome P a) =
      boundedOutcome (fun i => operatorValue 𝕜 H (P i)) a := by
  rcases a with ⟨i, b⟩
  cases b <;> rfl

omit [CompleteSpace H] in
theorem operatorValue_wordAmplitude (P : ι → HilbertOperatorAlgebra 𝕜 H)
    (w : Word ι) : operatorValue 𝕜 H (wordAmplitude P w) =
      boundedWordAmplitude (fun i => operatorValue 𝕜 H (P i)) w := by
  rw [boundedWordAmplitude_eq_wordAmplitude]
  induction w with
  | nil => exact map_one _
  | cons a w ih =>
    rw [wordAmplitude_cons, wordAmplitude_cons, map_mul, ih,
      operatorValue_algebraicOutcome]
    rfl

theorem operatorValue_wordOperator_eq_star_mul (P : ι → HilbertOperatorAlgebra 𝕜 H)
    (w : Word ι) : operatorValue 𝕜 H (wordOperator P w) =
      (ContinuousLinearMap.adjoint
        (boundedWordAmplitude (fun i => operatorValue 𝕜 H (P i)) w)).comp
        (boundedWordAmplitude (fun i => operatorValue 𝕜 H (P i)) w) := by
  rw [wordOperator, map_mul, operatorValue_star, operatorValue_wordAmplitude]
  rfl

namespace HilbertProjectiveData

def wordEffect (M : HilbertProjectiveData ι 𝕜 H) (w : Word ι) :
    selfAdjoint (HilbertOperatorAlgebra 𝕜 H) :=
  ⟨wordOperator M.projection w, wordOperator_star M.projection w⟩

def probability (M : HilbertProjectiveData ι 𝕜 H) (w : Word ι) : ℝ :=
  M.state (M.wordEffect w)

theorem wordEffect_operatorValue (M : HilbertProjectiveData ι 𝕜 H) (w : Word ι) :
    operatorValue 𝕜 H (M.wordEffect w).val = boundedWordEffect M.operatorProjection w := by
  rw [wordEffect, operatorValue_wordOperator_eq_star_mul,
    boundedWordEffect_eq_star_mul M.operatorProjection
      (fun i => (M.operatorProjection_isStarProjection i).isSelfAdjoint)]
  rfl

theorem toAlgebraic_probability (M : HilbertProjectiveData ι 𝕜 H) (w : Word ι) :
    M.toAlgebraic.probability w = M.probability w :=
  extendSelfAdjointState_on_selfAdjoint M.state _ (wordOperator_star M.projection w)

theorem probability_mem_Icc (M : HilbertProjectiveData ι 𝕜 H) (w : Word ι) :
    M.probability w ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← M.toAlgebraic_probability w]
  exact M.toAlgebraic.probability_mem_Icc w

def Matches (M : HilbertProjectiveData ι 𝕜 H) (p : ι → Albert) (ρ : Albert) : Prop :=
  ∀ w, M.probability w = nativeWordProbability p ρ w

theorem toAlgebraic_matches_iff (M : HilbertProjectiveData ι 𝕜 H)
    (p : ι → Albert) (ρ : Albert) :
    M.toAlgebraic.Matches p ρ ↔ M.Matches p ρ := by
  simp only [AlgebraicProjectiveData.Matches, Matches, M.toAlgebraic_probability]

end HilbertProjectiveData
end AlbertSequential
