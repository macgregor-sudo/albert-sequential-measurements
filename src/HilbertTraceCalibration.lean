/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HilbertTraceCalibrationData
public import Robustness.RoundedTraceInstrument
public import Robustness.RealTraceProjectiveWords
public import Robustness.ComplexTraceProjectiveWords
public import Robustness.QuaternionicTraceProjectiveWords

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ContinuousFunctionalCalculus
open AlbertSequential.RealHilbertComplexification

namespace AlbertSequential.HilbertTrace

section Complex
variable {H ι I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H)

theorem ComplexInstrument.exists_roundedTraceInstrument (M : ComplexInstrument b)
    (A : H →L[ℂ] H) (hA : IsComplexEffect A)
    (hpair : ∀ X, M.massOne b X = signedTracePairing b A X)
    {ε : ℝ} (hdefect : ‖A - A * A‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ R : RoundedTraceInstrument (complexOperatorTraceData b) (spectralRoundingError ε),
      R.instrument = M.traceNormInstrument b ∧ R.projection = cfc halfThresholdCutoff A := by
  obtain ⟨P, hP, hcut, hplus, hminus⟩ := exists_complex_calibration_projection A hA.1 hA.2
    (by rwa [norm_sub_rev]) hε
  let D := complexOperatorTraceData b
  let F := M.traceNormInstrument b
  have hleak := D.calibration_leakage hP F (spectralRoundingError ε) hpair
    (fun X hX => (complex_signedTracePairing_nonneg_zero_iff b _ X hplus hX).1)
    (fun X hX => (complex_signedTracePairing_nonneg_zero_iff b _ X hminus hX).1)
  exact ⟨⟨F, P, hP, hleak⟩, rfl, hcut⟩

theorem complex_roundedTraceInstrument_word {τ : ℝ}
    (R : I → RoundedTraceInstrument (complexOperatorTraceData b) τ)
    (ρ : (complexSignedTraceMass b).WithNorm) (hρ : IsComplexDensity b ρ) :
    ∀ w, (complexTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ).probability w =
      RoundedTraceInstrument.roundedWord R ρ w := by
  intro w
  let P (i : I) := (R i).projection
  let F (a : Outcome I) := complexSandwich b (algebraicOutcome P a)
  let X : signedFiniteTrace b := ρ
  exact (complexTraceProjectiveModel_probability b P (fun i => (R i).isProjection) X hρ w).trans
    ((congrArg (signedTrace b) (SharpDisturbance.wordMap_eq_chronologicalState F w X)).trans
      (RoundedTraceInstrument.roundedWord_eq_sandwich R ρ w).symm)

end Complex

section Real
variable {H ι I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)

theorem RealInstrument.exists_roundedTraceInstrument (M : RealInstrument b)
    (A : H →L[ℝ] H) (hA : IsRealEffect A)
    (hpair : ∀ X, M.massOne b X = signedTracePairing b A X)
    {ε : ℝ} (hdefect : ‖A - A * A‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ R : RoundedTraceInstrument (realOperatorTraceData b) (spectralRoundingError ε),
      R.instrument = M.traceNormInstrument b ∧
      complexifyBoundedOperator R.projection = cfc halfThresholdCutoff (complexifyBoundedOperator A) := by
  obtain ⟨P, hP, hcut, _, hplus, hminus⟩ := exists_real_calibration_projection A hA.1 hA.2
    (by rwa [norm_sub_rev]) hε
  let D := realOperatorTraceData b
  let F := M.traceNormInstrument b
  have hleak := D.calibration_leakage hP F (spectralRoundingError ε) hpair
    (fun X hX => (real_signedTracePairing_nonneg_zero_iff b _ X hplus hX).1)
    (fun X hX => (real_signedTracePairing_nonneg_zero_iff b _ X hminus hX).1)
  exact ⟨⟨F, P, hP, hleak⟩, rfl, hcut⟩

theorem real_roundedTraceInstrument_word {τ : ℝ}
    (R : I → RoundedTraceInstrument (realOperatorTraceData b) τ)
    (ρ : (realSignedTraceMass b).WithNorm) (hρ : IsRealDensity b ρ) :
    ∀ w, (realTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ).probability w =
      RoundedTraceInstrument.roundedWord R ρ w := by
  intro w
  let P (i : I) := (R i).projection
  let F (a : Outcome I) := realSandwich b (algebraicOutcome P a)
  let X : signedFiniteTrace b := ρ
  exact (realTraceProjectiveModel_probability b P (fun i => (R i).isProjection) X hρ w).trans
    ((congrArg (signedTrace b) (SharpDisturbance.wordMap_eq_chronologicalState F w X)).trans
      (RoundedTraceInstrument.roundedWord_eq_sandwich R ρ w).symm)

variable (S : RightQuaternionicHilbertStructure H)

theorem QuaternionicInstrument.exists_roundedTraceInstrument (M : QuaternionicInstrument b S)
    (A : S.toOperatorStructure.operatorAlgebra) (hA : IsQuaternionicEffect S A)
    (hpair : ∀ X, M.massOne b S X = quaternionicTracePairing b S A X)
    {ε : ℝ} (hdefect : ‖A.val - A.val * A.val‖ ≤ ε) (hε : ε < 1 / 4) :
    ∃ R : RoundedTraceInstrument (quaternionicOperatorTraceData b S) (spectralRoundingError ε),
      R.instrument = M.traceNormInstrument b S ∧
      complexifyBoundedOperator R.projection.val = cfc halfThresholdCutoff (complexifyBoundedOperator A.val) := by
  obtain ⟨P, hP, hcut, hplus, hminus⟩ := S.exists_quaternionic_calibration_projection A hA.1 hA.2
    (by rwa [norm_sub_rev]) hε
  let D := quaternionicOperatorTraceData b S
  let F := M.traceNormInstrument b S
  let U : S.toOperatorStructure.operatorAlgebra := spectralRoundingError ε • 1 - (A - P)
  let V : S.toOperatorStructure.operatorAlgebra := spectralRoundingError ε • 1 - (P - A)
  have hleak := D.calibration_leakage hP F (spectralRoundingError ε) hpair
    (fun X hX => (quaternionic_pairing_nonneg_zero_iff b S U X hplus hX).1)
    (fun X hX => (quaternionic_pairing_nonneg_zero_iff b S V X hminus hX).1)
  exact ⟨⟨F, P, hP, hleak⟩, rfl, hcut⟩

theorem quaternionic_roundedTraceInstrument_word {τ : ℝ}
    (R : I → RoundedTraceInstrument (quaternionicOperatorTraceData b S) τ)
    (ρ : (quaternionicSignedTraceMass b S).WithNorm) (hρ : IsQuaternionicDensity b S ρ) :
    ∀ w, (quaternionicTraceProjectiveModel b S (fun i => (R i).projection) (fun i => (R i).isProjection)
      ρ hρ).toAlgebraic.probability w = RoundedTraceInstrument.roundedWord R ρ w := by
  intro w
  let P (i : I) := (R i).projection
  let F (a : Outcome I) := quaternionicSandwich b S (algebraicOutcome P a)
  let X : quaternionicSignedFiniteTrace b S := ρ
  let M := quaternionicTraceProjectiveModel b S P (fun i => (R i).isProjection) X hρ
  exact (M.toAlgebraic_probability w).trans
    ((quaternionicTraceProjectiveModel_probability b S P (fun i => (R i).isProjection) X hρ w).trans
      ((congrArg (quaternionicSignedTrace b S) (SharpDisturbance.wordMap_eq_chronologicalState F w X)).trans
        (RoundedTraceInstrument.roundedWord_eq_sandwich R ρ w).symm))

end Real
end AlbertSequential.HilbertTrace
