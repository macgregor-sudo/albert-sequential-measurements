/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.HilbertAmplitudeErrors
public import Mathlib.Tactic.Choose

/-! Exact chronological probability transport to an actual projective model
on the same R/C Hilbert space with its original arbitrary self-adjoint state.
The two original branches are supplied separately; the false branch is not
defined as one minus the true branch. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential

def binaryBranchOperator {ι A : Type*} (yes no : ι → A) (a : Outcome ι) : A :=
  if a.2 then yes a.1 else no a.1

theorem binaryBranchOperator_norm_le_one {ι A : Type*} [Norm A]
    (yes no : ι → A) (hYes : ∀ i, ‖yes i‖ ≤ 1) (hNo : ∀ i, ‖no i‖ ≤ 1)
    (a : Outcome ι) : ‖binaryBranchOperator yes no a‖ ≤ 1 := by
  rcases a with ⟨i, b⟩
  cases b
  · exact hNo i
  · exact hYes i

variable {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem projective_hilbertAmplitudeEffect_eq
    (P : ι → H →L[𝕜] H) (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    hilbertAmplitudeEffect (chronologicalProduct (boundedOutcome P) w) =
      boundedSelfAdjointWordEffect P hstar w := by
  apply Subtype.ext
  apply (operatorValue 𝕜 H).injective
  rw [hilbertAmplitudeEffect_value]
  change star (chronologicalProduct (boundedOutcome P) w) *
      chronologicalProduct (boundedOutcome P) w =
    operatorValue 𝕜 H ((operatorValue 𝕜 H).symm (boundedWordEffect P w))
  rw [(operatorValue 𝕜 H).apply_symm_apply]
  exact (boundedWordEffect_eq_star_mul P hstar w).symm

theorem hilbert_projective_word_error
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    (sYes sNo P : ι → H →L[𝕜] H) (hP : ∀ i, IsStarProjection (P i))
    (hnYes : ∀ i, ‖sYes i‖ ≤ 1) (hnNo : ∀ i, ‖sNo i‖ ≤ 1)
    (hnP : ∀ i, ‖P i‖ ≤ 1) (hnQ : ∀ i, ‖1 - P i‖ ≤ 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hYes : ∀ i, ‖sYes i - P i‖ ≤ delta)
    (hNo : ∀ i, ‖sNo i - (1 - P i)‖ ≤ delta) (w : Word ι) :
    |psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
      (HilbertProjectiveData.ofBoundedProjections P hP psi hnormalized hpositive).toAlgebraic.probability w| ≤
      2 * (w.length : ℝ) * delta := by
  rw [HilbertProjectiveData.ofBoundedProjections_probability]
  have hstar : ∀ i, star (P i) = P i := fun i => (hP i).isSelfAdjoint
  change |psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
    psi (boundedSelfAdjointWordEffect P hstar w)| ≤ 2 * (w.length : ℝ) * delta
  rw [← projective_hilbertAmplitudeEffect_eq P hstar w]
  apply hilbert_state_word_error psi hnormalized hpositive
    (binaryBranchOperator sYes sNo) (boundedOutcome P)
    (binaryBranchOperator_norm_le_one sYes sNo hnYes hnNo) ?_ hdelta ?_ w
  · rintro ⟨i, b⟩
    cases b
    · exact hnQ i
    · exact hnP i
  · rintro ⟨i, b⟩
    cases b
    · exact hNo i
    · exact hYes i

/-- Independent per-test rounding choices give one stationary projective
model for every word. No continuity/equivariance of those choices is claimed. -/
theorem exists_hilbert_projective_word_approximation
    {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra 𝕜 H),
      (operatorValue 𝕜 H T.val).IsPositive → 0 ≤ psi T)
    (sYes sNo : ι → H →L[𝕜] H) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hround : ∀ i, ∃ P : H →L[𝕜] H, IsStarProjection P ∧
      ‖sYes i - P‖ ≤ delta ∧ ‖sNo i - (1 - P)‖ ≤ delta ∧
      ‖sYes i‖ ≤ 1 ∧ ‖sNo i‖ ≤ 1 ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1) :
    ∃ M : HilbertProjectiveData ι 𝕜 H, M.state = psi ∧
      ∀ w : Word ι,
        |psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
          M.toAlgebraic.probability w| ≤ 2 * (w.length : ℝ) * delta := by
  classical
  choose P hP hY hN hnY hnN hnP hnQ using hround
  refine ⟨HilbertProjectiveData.ofBoundedProjections P hP psi hnormalized hpositive, rfl, ?_⟩
  intro w
  exact hilbert_projective_word_error psi hnormalized hpositive sYes sNo P hP
    hnY hnN hnP hnQ hdelta hY hN w

end AlbertSequential
