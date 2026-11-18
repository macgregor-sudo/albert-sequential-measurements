/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.RealOperatorSpectralRounding
public import QuaternionicRightLinearOperators

/-! Same-space quaternionic rounding in the actual right-scalar
commutant. No quaternionic CFC class or extension of an original state is used.
The result stays on the original underlying Hilbert space. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace QuaternionicOperatorStructure

theorem realPositiveSquareRoot_mem_operatorAlgebra
    (Q : QuaternionicOperatorStructure H) (E : Q.operatorAlgebra) (hE : E.val.IsPositive) :
    realPositiveSquareRoot E.val hE ∈ Q.operatorAlgebra := by
  have hm := (Q.mem_operatorAlgebra_iff E.val).mp E.property
  apply (Q.mem_operatorAlgebra_iff _).mpr
  constructor
  · exact (realPositiveSquareRoot_commute E.val Q.rightI hE hm.1.symm).eq.symm
  · exact (realPositiveSquareRoot_commute E.val Q.rightJ hE hm.2.symm).eq.symm

def positiveSquareRoot
    (Q : QuaternionicOperatorStructure H) (E : Q.operatorAlgebra) (hE : E.val.IsPositive) :
    Q.operatorAlgebra :=
  ⟨realPositiveSquareRoot E.val hE, Q.realPositiveSquareRoot_mem_operatorAlgebra E hE⟩

theorem positiveSquareRoot_positive_and_square
    (Q : QuaternionicOperatorStructure H) (E : Q.operatorAlgebra) (hE : E.val.IsPositive) :
    (Q.positiveSquareRoot E hE).val.IsPositive ∧
      Q.positiveSquareRoot E hE * Q.positiveSquareRoot E hE = E := by
  refine ⟨(realPositiveSquareRoot_positive_and_square E.val hE).1, ?_⟩
  apply Subtype.ext
  exact (realPositiveSquareRoot_positive_and_square E.val hE).2

theorem positiveSquareRoot_unique
    (Q : QuaternionicOperatorStructure H) (E S : Q.operatorAlgebra)
    (hE : E.val.IsPositive) (hS : S.val.IsPositive) (hSq : S * S = E) :
    S = Q.positiveSquareRoot E hE := by
  apply Subtype.ext
  exact realPositiveSquareRoot_unique E.val S.val hE hS (congrArg Subtype.val hSq)

theorem exists_rounded_projection
    (Q : QuaternionicOperatorStructure H) (E sYes sNo : Q.operatorAlgebra)
    (hE : E.val.IsPositive) (hEc : (1 - E.val).IsPositive)
    (hYes : sYes.val.IsPositive) (hNo : sNo.val.IsPositive)
    (hYesSq : sYes * sYes = E) (hNoSq : sNo * sNo = 1 - E)
    {epsilon : ℝ} (hdefect : ‖E.val * E.val - E.val‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ P : Q.operatorAlgebra, IsStarProjection P ∧
      ‖sYes.val - P.val‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sNo.val - (1 - P.val)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sYes.val‖ ≤ 1 ∧ ‖sNo.val‖ ≤ 1 ∧ ‖P.val‖ ≤ 1 ∧ ‖1 - P.val‖ ≤ 1 := by
  obtain ⟨P, hP, hcomm, hY, hN, hnY, hnN, hnP, hnQ⟩ :=
    exists_real_rounded_projection E.val sYes.val sNo.val hE hEc hYes hNo
      (congrArg Subtype.val hYesSq) (congrArg Subtype.val hNoSq) hdefect hepsilon
  have hmE := (Q.mem_operatorAlgebra_iff E.val).mp E.property
  have hmP : P ∈ Q.operatorAlgebra := by
    apply (Q.mem_operatorAlgebra_iff P).mpr
    exact ⟨(hcomm Q.rightI hmE.1.symm).eq.symm, (hcomm Q.rightJ hmE.2.symm).eq.symm⟩
  let PQ : Q.operatorAlgebra := ⟨P, hmP⟩
  have hPQ : IsStarProjection PQ := by
    constructor
    · apply Subtype.ext
      exact hP.isIdempotentElem
    · apply Subtype.ext
      exact hP.isSelfAdjoint
  exact ⟨PQ, hPQ, hY, hN, hnY, hnN, hnP, hnQ⟩

end QuaternionicOperatorStructure

namespace RightQuaternionicHilbertStructure

theorem quaternionic_positiveSquareRoot_positive_and_square
    (S : RightQuaternionicHilbertStructure H)
    (E : S.toOperatorStructure.operatorAlgebra) (hE : S.IsQuaternionPositive E) :
    S.IsQuaternionPositive
      (S.toOperatorStructure.positiveSquareRoot E ((S.positive_iff_real_operator E).mp hE)) ∧
      S.toOperatorStructure.positiveSquareRoot E ((S.positive_iff_real_operator E).mp hE) *
        S.toOperatorStructure.positiveSquareRoot E ((S.positive_iff_real_operator E).mp hE) = E := by
  have hroot := S.toOperatorStructure.positiveSquareRoot_positive_and_square E
    ((S.positive_iff_real_operator E).mp hE)
  exact ⟨(S.positive_iff_real_operator _).mpr hroot.1, hroot.2⟩

/-- Ordinary quaternionic source hypotheses, with explicit all-quaternion
right-linearity of the rounded projection on the original real carrier. -/
theorem exists_quaternionic_rounded_projection
    (S : RightQuaternionicHilbertStructure H)
    (E sYes sNo : S.toOperatorStructure.operatorAlgebra)
    (hE : S.IsQuaternionPositive E) (hEc : S.IsQuaternionPositive (1 - E))
    (hYes : S.IsQuaternionPositive sYes) (hNo : S.IsQuaternionPositive sNo)
    (hYesSq : sYes * sYes = E) (hNoSq : sNo * sNo = 1 - E)
    {epsilon : ℝ} (hdefect : ‖E.val * E.val - E.val‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4) :
    ∃ P : S.toOperatorStructure.operatorAlgebra,
      IsStarProjection P ∧ S.IsRightLinear P.val ∧
      ‖sYes.val - P.val‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sNo.val - (1 - P.val)‖ ≤ Real.sqrt (spectralRoundingError epsilon) ∧
      ‖sYes.val‖ ≤ 1 ∧ ‖sNo.val‖ ≤ 1 ∧ ‖P.val‖ ≤ 1 ∧ ‖1 - P.val‖ ≤ 1 := by
  obtain ⟨P, hP, hY, hN, hnY, hnN, hnP, hnQ⟩ :=
    S.toOperatorStructure.exists_rounded_projection E sYes sNo
      ((S.positive_iff_real_operator E).mp hE)
      ((S.positive_iff_real_operator (1 - E)).mp hEc)
      ((S.positive_iff_real_operator sYes).mp hYes)
      ((S.positive_iff_real_operator sNo).mp hNo) hYesSq hNoSq hdefect hepsilon
  exact ⟨P, hP, (S.mem_operatorAlgebra_iff_rightLinear P.val).mp P.property,
    hY, hN, hnY, hnN, hnP, hnQ⟩

end RightQuaternionicHilbertStructure
end AlbertSequential
