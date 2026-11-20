/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralSimplexWeights
public import WindowProbabilitySpectralPublishedDensity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped ENNReal

/-- The law after independently choosing one of the six eigenvalue labellings uniformly. -/
def uniformlyRelabelledFourColumnEigenvalueLaw : Measure (ℝ × ℝ) :=
  (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6,
    ((standardComplexGaussianMatrix 4).map normalizedFourColumnEigenvaluePair).map (simplexRelabel i)

theorem uniformlyRelabelledFourColumnEigenvalueLaw_eq_density :
    uniformlyRelabelledFourColumnEigenvalueLaw = normalizedFourColumnSymmetricSimplexDensity := by
  unfold uniformlyRelabelledFourColumnEigenvalueLaw
  rw [normalizedFourColumnEigenvaluePair_law_eq_density]
  exact relabelled_orderedSimplexDensity_eq_symmetricDensity

end AlbertSequential.WindowProbability
