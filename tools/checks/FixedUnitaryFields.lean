module

import FixedUnitaryPhysicalFields

noncomputable section

open AlbertSequential AlbertSequential.FixedUnitary AlbertSequential.HilbertTrace

variable {H I B E : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
variable [AddCommGroup E] [Module ℝ E]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)

example {A : Type*} [Ring A] (Y : A) (P : I → A) (a c : Outcome I) :
    preTestAmplitude Y P [a, c] = algebraicOutcome P c * (Y * (algebraicOutcome P a * Y)) := by
  change algebraicOutcome P c * (Y * (algebraicOutcome P a * (Y * 1))) = _
  rw [mul_one]

example {n d : ℕ} (Y : Matrix (Fin d) (Fin d) ℂ) (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (w : Word (Fin n)) : preTestAmplitude Y P w = interleaved Y P w := rfl

example (J : UnitalJordanProduct E) (p : I → E) (hp : ∀ i, J.product (p i) (p i) = p i)
    (s : E) (tr : E →ₗ[ℝ] ℝ) (Y : unitary (H →L[ℝ] H)) (P : I → H →L[ℝ] H)
    (hP : ∀ i, IsStarProjection (P i)) (X : signedFiniteTrace b) (hX : IsRealDensity b X)
    (hm : ∀ w, signedTrace b (realSandwich b (preTestAmplitude (Y : H →L[ℝ] H) P w) X) =
      tr (J.sequentialBranchState p s w)) :
    ∃ M : HilbertProjectiveData I ℝ H, M.operatorProjection = P ∧
      (∀ w, M.probability w = tr (J.sequentialBranchState p s w)) := by
  obtain ⟨hrot, hw⟩ := real_projective_of_fixedUnitary_jordanTable J b p hp s tr Y P hP X hX hm
  refine ⟨realTraceProjectiveModel b P hP _ hrot, ?_, hw⟩
  funext i
  exact (operatorValue ℝ H).apply_symm_apply (P i)

local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S

example (J : UnitalJordanProduct E) (p : I → E) (hp : ∀ i, J.product (p i) (p i) = p i)
    (s : E) (tr : E →ₗ[ℝ] ℝ) (Y : unitary Op) (P : I → Op)
    (hP : ∀ i, IsStarProjection (P i)) (X : Carrier) (hX : IsQuaternionicDensity b S X)
    (hm : ∀ w, quaternionicSignedTrace b S (quaternionicSandwich b S
      (preTestAmplitude (Y : Op) P w) X) = tr (J.sequentialBranchState p s w)) :
    ∃ M : QuaternionicProjectiveData I S.toOperatorStructure, M.projection = P ∧
      (∀ w, M.state (M.wordEffect w) = tr (J.sequentialBranchState p s w)) ∧
      S.IsRightLinear ((quaternionicSandwich b S (Y : Op) X).val) := by
  obtain ⟨hrot, hw⟩ := quaternionic_projective_of_fixedUnitary_jordanTable J b S
    p hp s tr Y P hP X hX hm
  refine ⟨quaternionicTraceProjectiveModel b S P hP _ hrot, rfl, hw, ?_⟩
  apply (mem_quaternionicSignedFiniteTrace_iff b S _).mp
    (quaternionicSandwich b S (Y : Op) X).property |>.2

#print axioms real_projective_of_fixedUnitary_noSwitch
#print axioms quaternionic_projective_of_fixedUnitary_noSwitch
#print axioms real_projective_of_fixedUnitary_jordanTable
#print axioms quaternionic_projective_of_fixedUnitary_jordanTable
