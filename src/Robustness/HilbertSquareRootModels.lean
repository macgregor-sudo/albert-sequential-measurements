/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.RealOperatorSpectralRounding
public import Robustness.HilbertWordRounding

/-! One fixed projective family for all unconditional histories, on the same
real/complex Hilbert space and with the same arbitrary positive state. The
canonical-root corollaries bind the paper's actual square-root instruments. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential

theorem exists_complex_rounded_word_model
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℂ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℂ H),
      (operatorValue ℂ H T.val).IsPositive → 0 ≤ psi T)
    (E sYes sNo : ι → H →L[ℂ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    (hYes : ∀ i, (sYes i).IsPositive) (hNo : ∀ i, (sNo i).IsPositive)
    (hYesSq : ∀ i, sYes i * sYes i = E i)
    (hNoSq : ∀ i, sNo i * sNo i = 1 - E i)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : HilbertProjectiveData ι ℂ H, M.state = psi ∧
      ∀ w : Word ι,
        |psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
          M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) := by
  apply exists_hilbert_projective_word_approximation psi hnormalized hpositive sYes sNo
    (Real.sqrt_nonneg _)
  intro i
  obtain ⟨P, hP, _, hY, hN, hnY, hnN, hnP, hnQ⟩ :=
    exists_complex_rounded_projection (E i) (sYes i) (sNo i)
      (hE i) (hEc i) (hYes i) (hNo i) (hYesSq i) (hNoSq i) (hdefect i) hepsilon
  exact ⟨P, hP, hY, hN, hnY, hnN, hnP, hnQ⟩

theorem exists_real_rounded_word_model
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℝ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℝ H),
      (operatorValue ℝ H T.val).IsPositive → 0 ≤ psi T)
    (E sYes sNo : ι → H →L[ℝ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    (hYes : ∀ i, (sYes i).IsPositive) (hNo : ∀ i, (sNo i).IsPositive)
    (hYesSq : ∀ i, sYes i * sYes i = E i)
    (hNoSq : ∀ i, sNo i * sNo i = 1 - E i)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : HilbertProjectiveData ι ℝ H, M.state = psi ∧
      ∀ w : Word ι,
        |psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
          M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) := by
  apply exists_hilbert_projective_word_approximation psi hnormalized hpositive sYes sNo
    (Real.sqrt_nonneg _)
  intro i
  obtain ⟨P, hP, _, hY, hN, hnY, hnN, hnP, hnQ⟩ :=
    exists_real_rounded_projection (E i) (sYes i) (sNo i)
      (hE i) (hEc i) (hYes i) (hNo i) (hYesSq i) (hNoSq i) (hdefect i) hepsilon
  exact ⟨P, hP, hY, hN, hnY, hnN, hnP, hnQ⟩

theorem exists_complex_canonical_root_word_model
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℂ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℂ H),
      (operatorValue ℂ H T.val).IsPositive → 0 ≤ psi T)
    (E : ι → H →L[ℂ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : HilbertProjectiveData ι ℂ H, M.state = psi ∧
      ∀ w : Word ι,
        |psi (hilbertAmplitudeEffect (chronologicalProduct
          (binaryBranchOperator (fun i => cfc Real.sqrt (E i))
            (fun i => cfc Real.sqrt (1 - E i))) w)) - M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) :=
  exists_complex_rounded_word_model psi hnormalized hpositive E _ _ hE hEc
    (fun i => (complex_operator_cfc_sqrt_positive_and_square (E i) (hE i)).1)
    (fun i => (complex_operator_cfc_sqrt_positive_and_square (1 - E i) (hEc i)).1)
    (fun i => (complex_operator_cfc_sqrt_positive_and_square (E i) (hE i)).2)
    (fun i => (complex_operator_cfc_sqrt_positive_and_square (1 - E i) (hEc i)).2) hdefect hepsilon

theorem exists_real_canonical_root_word_model
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℝ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℝ H),
      (operatorValue ℝ H T.val).IsPositive → 0 ≤ psi T)
    (E : ι → H →L[ℝ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : HilbertProjectiveData ι ℝ H, M.state = psi ∧
      ∀ w : Word ι,
        |psi (hilbertAmplitudeEffect (chronologicalProduct
          (binaryBranchOperator (fun i => realPositiveSquareRoot (E i) (hE i))
            (fun i => realPositiveSquareRoot (1 - E i) (hEc i))) w)) -
          M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) :=
  exists_real_rounded_word_model psi hnormalized hpositive E _ _ hE hEc
    (fun i => (realPositiveSquareRoot_positive_and_square (E i) (hE i)).1)
    (fun i => (realPositiveSquareRoot_positive_and_square (1 - E i) (hEc i)).1)
    (fun i => (realPositiveSquareRoot_positive_and_square (E i) (hE i)).2)
    (fun i => (realPositiveSquareRoot_positive_and_square (1 - E i) (hEc i)).2) hdefect hepsilon

end AlbertSequential
