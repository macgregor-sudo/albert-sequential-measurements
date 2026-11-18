/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.QuaternionicOperatorSpectralRounding
public import Robustness.QuaternionicStateBounds
public import Robustness.HilbertWordRounding

/-! All-history approximation on the original quaternionic commutant and its
original arbitrary positive real-linear self-adjoint state. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem QuaternionicProjectiveData.probability_eq_amplitude_state
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData ι Q) (w : Word ι) :
    M.toAlgebraic.probability w =
      M.state (operatorSubalgebraAmplitudeEffect Q.operatorAlgebra
        (chronologicalProduct (algebraicOutcome M.projection) w)) := by
  rw [M.toAlgebraic_probability]
  apply congrArg M.state
  apply Subtype.ext
  rfl

namespace RightQuaternionicHilbertStructure

def canonicalPositiveSquareRoot (S : RightQuaternionicHilbertStructure H)
    (E : S.toOperatorStructure.operatorAlgebra) (hE : S.IsQuaternionPositive E) :
    S.toOperatorStructure.operatorAlgebra :=
  S.toOperatorStructure.positiveSquareRoot E ((S.positive_iff_real_operator E).mp hE)

theorem canonicalPositiveSquareRoot_positive_and_square
    (S : RightQuaternionicHilbertStructure H)
    (E : S.toOperatorStructure.operatorAlgebra) (hE : S.IsQuaternionPositive E) :
    S.IsQuaternionPositive (S.canonicalPositiveSquareRoot E hE) ∧
      S.canonicalPositiveSquareRoot E hE * S.canonicalPositiveSquareRoot E hE = E :=
  S.quaternionic_positiveSquareRoot_positive_and_square E hE

theorem canonicalPositiveSquareRoot_unique
    (S : RightQuaternionicHilbertStructure H) (E A : S.toOperatorStructure.operatorAlgebra)
    (hE : S.IsQuaternionPositive E) (hA : S.IsQuaternionPositive A) (hSq : A * A = E) :
    A = S.canonicalPositiveSquareRoot E hE :=
  S.toOperatorStructure.positiveSquareRoot_unique E A
    ((S.positive_iff_real_operator E).mp hE) ((S.positive_iff_real_operator A).mp hA) hSq

theorem exists_projective_word_approximation
    (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (sYes sNo : ι → S.toOperatorStructure.operatorAlgebra)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hround : ∀ i, ∃ P : S.toOperatorStructure.operatorAlgebra, IsStarProjection P ∧
      ‖(sYes i).val - P.val‖ ≤ delta ∧ ‖(sNo i).val - (1 - P.val)‖ ≤ delta ∧
      ‖(sYes i).val‖ ≤ 1 ∧ ‖(sNo i).val‖ ≤ 1 ∧ ‖P.val‖ ≤ 1 ∧ ‖1 - P.val‖ ≤ 1) :
    ∃ M : QuaternionicProjectiveData ι S.toOperatorStructure, M.state = psi ∧
      ∀ w : Word ι,
        |psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
          (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
          M.toAlgebraic.probability w| ≤ 2 * (w.length : ℝ) * delta := by
  classical
  choose P hP hY hN hnY hnN hnP hnQ using hround
  let M : QuaternionicProjectiveData ι S.toOperatorStructure := {
    projection := P
    isStarProjection := hP
    state := psi
    normalized := hnormalized
    positive := fun T hT => hpositive T ((S.positive_iff_real_operator T.val).mpr hT) }
  refine ⟨M, rfl, ?_⟩
  intro w
  rw [M.probability_eq_amplitude_state]
  change |psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
      (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
    psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
      (chronologicalProduct (algebraicOutcome P) w))| ≤ 2 * (w.length : ℝ) * delta
  apply S.positive_state_word_error psi hnormalized hpositive
    (binaryBranchOperator sYes sNo) (algebraicOutcome P) ?_ ?_ hdelta ?_ w
  · rintro ⟨i, b⟩
    cases b
    · exact hnN i
    · exact hnY i
  · rintro ⟨i, b⟩
    cases b
    · exact hnQ i
    · exact hnP i
  · rintro ⟨i, b⟩
    cases b
    · exact hN i
    · exact hY i

theorem exists_quaternionic_rounded_word_model
    (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (E sYes sNo : ι → S.toOperatorStructure.operatorAlgebra)
    (hE : ∀ i, S.IsQuaternionPositive (E i))
    (hEc : ∀ i, S.IsQuaternionPositive (1 - E i))
    (hYes : ∀ i, S.IsQuaternionPositive (sYes i))
    (hNo : ∀ i, S.IsQuaternionPositive (sNo i))
    (hYesSq : ∀ i, sYes i * sYes i = E i)
    (hNoSq : ∀ i, sNo i * sNo i = 1 - E i)
    {epsilon : ℝ} (hdefect : ∀ i, ‖(E i).val * (E i).val - (E i).val‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : QuaternionicProjectiveData ι S.toOperatorStructure, M.state = psi ∧
      ∀ w : Word ι,
        |psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
          (chronologicalProduct (binaryBranchOperator sYes sNo) w)) -
          M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) := by
  apply S.exists_projective_word_approximation psi hnormalized hpositive sYes sNo (Real.sqrt_nonneg _)
  intro i
  obtain ⟨P, hP, _, hY, hN, hnY, hnN, hnP, hnQ⟩ :=
    S.exists_quaternionic_rounded_projection (E i) (sYes i) (sNo i)
      (hE i) (hEc i) (hYes i) (hNo i) (hYesSq i) (hNoSq i) (hdefect i) hepsilon
  exact ⟨P, hP, hY, hN, hnY, hnN, hnP, hnQ⟩

theorem exists_quaternionic_canonical_root_word_model
    (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (E : ι → S.toOperatorStructure.operatorAlgebra)
    (hE : ∀ i, S.IsQuaternionPositive (E i))
    (hEc : ∀ i, S.IsQuaternionPositive (1 - E i))
    {epsilon : ℝ} (hdefect : ∀ i, ‖(E i).val * (E i).val - (E i).val‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ M : QuaternionicProjectiveData ι S.toOperatorStructure, M.state = psi ∧
      ∀ w : Word ι,
        |psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
          (chronologicalProduct
            (binaryBranchOperator (fun i => S.canonicalPositiveSquareRoot (E i) (hE i))
              (fun i => S.canonicalPositiveSquareRoot (1 - E i) (hEc i))) w)) -
          M.toAlgebraic.probability w| ≤
          2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError epsilon) :=
  S.exists_quaternionic_rounded_word_model psi hnormalized hpositive E _ _ hE hEc
    (fun i => (S.canonicalPositiveSquareRoot_positive_and_square (E i) (hE i)).1)
    (fun i => (S.canonicalPositiveSquareRoot_positive_and_square (1 - E i) (hEc i)).1)
    (fun i => (S.canonicalPositiveSquareRoot_positive_and_square (E i) (hE i)).2)
    (fun i => (S.canonicalPositiveSquareRoot_positive_and_square (1 - E i) (hEc i)).2) hdefect hepsilon

end RightQuaternionicHilbertStructure
end AlbertSequential
