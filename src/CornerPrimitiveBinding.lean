/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerContractionDefects
public import PrimitiveResidualOccurrences

/-! Exact connector from the retained contraction defects to primitive leaves.
Native scalar-access equalities remain explicit; base insertion costs a letter.
Chronological right-history identities do not assume positive preparation mass. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
section PrimitiveBinding
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem pairDefectElement_primitive (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a b : ι) (o : ℝ) :
    pairDefectElement (P a) (P b) o = outcomePurityElement P (a, true) [(b, true)] o :=
  pairDefect_primitive_decomposition P hp hstar a b o

theorem triangleDefectElement_primitive (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a b d : ι) (c : Word ι → ℝ) (R : ℝ)
    (hscalar : c [(d, true)] + c [(b, true), (d, true)] -
      c [(b, false), (d, true)] = 2 * R) :
    triangleDefectElement (P a) (P b) (P d) R =
      weightedPurityResidual P a c (accessWordTerms b [(d, true)]) :=
  triangleDefect_primitive_decomposition P hp hstar a b d c R hscalar

theorem tripleDefectElement_primitive (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a k l m : ι) (c : Word ι → ℝ) (Q : ℝ)
    (hscalar : weightedWordScalar c (polarizedTripleWordTerms k l m) = 4 * Q) :
    tripleDefectElement (P a) (P k) (P l) (P m) Q =
      (1 / 2 : ℝ) • weightedPurityResidual P a c (polarizedTripleWordTerms k l m) :=
  symmetricTripleDefect_primitive_decomposition P hp hstar a k l m c Q hscalar

omit [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem append_base_of_right_support (P : ι → A) (Z : A) (i : ι)
    (hZ : Z * P i = Z) (t : Word ι) :
    Z * wordAmplitude P (t ++ [(i, true)]) = Z * wordAmplitude P t := by
  rw [wordAmplitude_append_singleton]
  change Z * (P i * wordAmplitude P t) = _
  rw [← mul_assoc, hZ]

omit [StarRing A] [SMulCommClass ℝ A A] in
theorem triangleDefect_history_support (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (a b d : ι) (R : ℝ) (t : Word ι) :
    triangleDefectElement (P a) (P b) (P d) R * wordAmplitude P (t ++ [(a, true)]) =
      triangleDefectElement (P a) (P b) (P d) R * wordAmplitude P t :=
  append_base_of_right_support P _ a (triangleDefect_right_support _ _ _ (hp a) R) t

omit [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem right_history_after_base (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (j : ι) (w : Word ι) :
    wordAmplitude P w * P j * wordAmplitude P [(j, true)] =
      wordAmplitude P ([(j, true)] ++ w) := by
  rw [wordAmplitude_append, wordAmplitude_singleton]
  change wordAmplitude P w * P j * P j = wordAmplitude P w * P j
  rw [mul_assoc, hp j]

end PrimitiveBinding
end AlbertSequential
