/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SequentialEffectLifts

/-!
Literal reflection-orbit labels and their projection-side identities.
The generator label is retained even when two labels name the same native
point; identifying such labels is a consequence of all-history descent.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev ReflectionOrbitLabel (ι : Type*) := List ι × ι

def reflectedOrbitLabel {ι : Type*} (α β : ReflectionOrbitLabel ι) : ReflectionOrbitLabel ι :=
  (α.1 ++ [α.2] ++ α.1.reverse ++ β.1, β.2)

section Labels
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem projection_mem_wordVectorSpan (P : ι → A) (i : ι) : P i ∈ WordVectorSpan P := by
  simpa only [wordAmplitude_singleton, algebraicOutcome, ↓reduceIte] using
    wordAmplitude_mem_wordVectorSpan P [(i, true)]

theorem projectionReflection_mem_wordVectorSpan (P : ι → A) (i : ι) :
    projectionReflection P i ∈ WordVectorSpan P :=
  (WordVectorSpan P).sub_mem
    ((WordVectorSpan P).smul_mem (2 : ℝ) (projection_mem_wordVectorSpan P i))
    (one_mem_wordVectorSpan P)

theorem projectionReflectionWord_mem_wordVectorSpan (P : ι → A) (g : List ι) :
    projectionReflectionWord P g ∈ WordVectorSpan P := by
  induction g with
  | nil => exact one_mem_wordVectorSpan P
  | cons i g ih => exact mul_mem_wordVectorSpan P (projectionReflection_mem_wordVectorSpan P i) ih

theorem orbitProjection_mem_wordVectorSpan (P : ι → A)
    (hstar : ∀ i, star (P i) = P i) (g : List ι) (i : ι) :
    orbitProjection P g i ∈ WordVectorSpan P := by
  unfold orbitProjection
  rw [← projectionReflectionWord_reverse P hstar]
  exact mul_mem_wordVectorSpan P
    (mul_mem_wordVectorSpan P (projectionReflectionWord_mem_wordVectorSpan P g)
      (projection_mem_wordVectorSpan P i))
    (projectionReflectionWord_mem_wordVectorSpan P _)

theorem orbitProjection_reflected_label (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (α β : ReflectionOrbitLabel ι) :
    orbitProjection P (reflectedOrbitLabel α β).1 (reflectedOrbitLabel α β).2 =
      ((2 : ℝ) • orbitProjection P α.1 α.2 - 1) * orbitProjection P β.1 β.2 *
        ((2 : ℝ) • orbitProjection P α.1 α.2 - 1) := by
  rw [← conjugate_projectionReflection P hp hstar α.1 α.2]
  simp only [reflectedOrbitLabel, orbitProjection, projectionReflectionWord_append,
    projectionReflectionWord, mul_one, projectionReflectionWord_reverse P hstar,
    star_mul, star_star, projectionReflection_star P hstar, mul_assoc]

end Labels
end AlbertSequential
