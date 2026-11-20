module

import HilbertTraceQuaternionicIdeal

open AlbertSequential AlbertSequential.HilbertTrace

section NativeConsumer

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

example (M : QuaternionicInstrument b S) (hM : M.IsIdealTest b S) :
    ∃ P : S.toOperatorStructure.operatorAlgebra, IsStarProjection P ∧
      (∀ X : quaternionicSignedFiniteTrace b S,
        (M.branchOne X).val = P.val * X.val * P.val ∧
        (M.branchZero X).val = (1 - P.val) * X.val * (1 - P.val)) ∧
      (∀ X, quaternionicSignedTrace b S (M.branchOne X) = quaternionicTracePairing b S P X) := by
  obtain ⟨P, hP, h1, h0, hA⟩ := (M.idealTest_iff_projection b S).mp hM
  let Q := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have hp : star P.val = P.val := (hP.map S.toOperatorStructure.operatorValue).isSelfAdjoint.star_eq
  have hq : star Q.val = Q.val := (hQ.map S.toOperatorStructure.operatorValue).isSelfAdjoint.star_eq
  refine ⟨P, hP, ?_, hA⟩
  intro X
  rw [h1, h0]
  change P.val * X.val * star P.val = P.val * X.val * P.val ∧
    Q.val * X.val * star Q.val = Q.val * X.val * Q.val
  rw [hp, hq]
  exact ⟨rfl, rfl⟩

theorem quaternionic_projection_consumer (P : S.toOperatorStructure.operatorAlgebra) (hP : IsStarProjection P) :
    ∃ M : QuaternionicInstrument b S, M.IsIdealTest b S ∧
      M.branchOne = quaternionicSandwich b S P ∧ M.branchZero = quaternionicSandwich b S (1 - P) := by
  let Q := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  let M : QuaternionicInstrument b S :=
    { branchOne := quaternionicSandwich b S P
      branchZero := quaternionicSandwich b S Q
      one_positive := quaternionicSandwich_positive b S P
      zero_positive := quaternionicSandwich_positive b S Q
      trace_preserving := by
        intro X
        rw [map_add, signedTrace_quaternionicSandwich, signedTrace_quaternionicSandwich,
          hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
          hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
        change quaternionicTracePairing b S P X + quaternionicTracePairing b S (1 - P) X =
          quaternionicSignedTrace b S X
        rw [quaternionicTracePairing_complement_eq]
        ring }
  have hA := M.measuredEffect_of_branchOne_compression b S hP rfl
  exact ⟨M, (M.idealTest_iff_projection b S).mpr ⟨P, hP, rfl, rfl, hA⟩, rfl, rfl⟩

example : ∃ M : QuaternionicInstrument b S, M.IsIdealTest b S ∧
    M.branchOne = quaternionicSandwich b S 0 ∧ M.branchZero = quaternionicSandwich b S (1 - 0) :=
  quaternionic_projection_consumer b S 0 (IsStarProjection.zero _)

example : ∃ M : QuaternionicInstrument b S, M.IsIdealTest b S ∧
    M.branchOne = quaternionicSandwich b S 1 ∧ M.branchZero = quaternionicSandwich b S (1 - 1) :=
  quaternionic_projection_consumer b S 1 (IsStarProjection.one _)

end NativeConsumer

#print axioms quaternionicAverage_positive
#print axioms quaternionicAverage_trace
#print axioms exists_quaternionic_effect_of_trace_dominated
#print axioms quaternionicVectorDyad_pairing
#print axioms quaternionic_signedFiniteTrace_decomposition
#print axioms QuaternionicInstrument.exists_measuredEffect
#print axioms signedTrace_quaternionicSandwich
#print axioms branch_factors_through_quaternionicSandwich
#print axioms QuaternionicInstrument.idealTest_iff_projection
