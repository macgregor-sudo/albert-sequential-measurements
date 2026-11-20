module

import HilbertTraceComplexIdeal

open AlbertSequential.HilbertTrace
open scoped InnerProductSpace

section NativeConsumer

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℂ H)

example (M : ComplexInstrument b) (hM : M.IsIdealTest b) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧
      (∀ X : signedFiniteTrace b,
        (M.branchOne X).val = P * X.val * P ∧
        (M.branchZero X).val = (1 - P) * X.val * (1 - P)) ∧
      (∀ X, signedTrace b (M.branchOne X) = signedTracePairing b P X) := by
  obtain ⟨P, hP, h1, h0, hA⟩ := (M.idealTest_iff_projection b).mp hM
  let Q : H →L[ℂ] H := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  refine ⟨P, hP, ?_, hA⟩
  intro X
  rw [h1, h0]
  change P * X.val * star P = P * X.val * P ∧ Q * X.val * star Q = Q * X.val * Q
  rw [hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
  exact ⟨rfl, rfl⟩

theorem projection_consumer (P : H →L[ℂ] H) (hP : IsStarProjection P) :
    ∃ M : ComplexInstrument b, M.IsIdealTest b ∧
      M.branchOne = complexSandwich b P ∧ M.branchZero = complexSandwich b (1 - P) := by
  let Q : H →L[ℂ] H := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  let M : ComplexInstrument b :=
    { branchOne := complexSandwich b P
      branchZero := complexSandwich b Q
      one_positive := complexSandwich_positive b P
      zero_positive := complexSandwich_positive b Q
      trace_preserving := by
        intro X
        rw [map_add, signedTrace_complexSandwich, signedTrace_complexSandwich,
          hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
          hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
        change signedTracePairing b P X + signedTracePairing b (1 - P) X = signedTrace b X
        rw [complexTracePairing_complement_eq]
        ring }
  have hA := M.measuredEffect_of_branchOne_compression b hP rfl
  exact ⟨M, (M.idealTest_iff_projection b).mpr ⟨P, hP, rfl, rfl, hA⟩, rfl, rfl⟩

example : ∃ M : ComplexInstrument b, M.IsIdealTest b ∧
    M.branchOne = complexSandwich b 0 ∧ M.branchZero = complexSandwich b (1 - 0) :=
  projection_consumer b 0 (IsStarProjection.zero _)

example : ∃ M : ComplexInstrument b, M.IsIdealTest b ∧
    M.branchOne = complexSandwich b 1 ∧ M.branchZero = complexSandwich b (1 - 1) :=
  projection_consumer b 1 (IsStarProjection.one _)

end NativeConsumer

#print axioms positiveFunctional_ext_of_rankOne
#print axioms exists_positiveContraction_of_diagonal_bilinear
#print axioms exists_complex_effect_of_trace_dominated
#print axioms ComplexInstrument.exists_measuredEffect
#print axioms signedTrace_complexSandwich
#print axioms ComplexInstrument.measuredEffect_isProjection_of_sharp
#print axioms ComplexInstrument.idealTest_iff_projection
#print axioms branch_factors_through_complexSandwich
