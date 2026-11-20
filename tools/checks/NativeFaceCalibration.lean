module

import HilbertTraceCalibrationWitness
import Robustness.ComplexSharpDisturbance

open AlbertSequential AlbertSequential.HilbertTrace
open scoped ContinuousFunctionalCalculus

example {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (M : ComplexInstrument b) (A : H →L[ℂ] H) (hA : IsComplexEffect A)
    (hpair : ∀ X, M.massOne b X = signedTracePairing b A X) {ε δ : ℝ}
    (hdef : ‖A - A * A‖ ≤ ε) (hε : ε < 1 / 4) (hδ : 0 ≤ δ) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧ P = cfc halfThresholdCutoff A ∧
      ((∀ σ : signedFiniteTrace b, IsComplexDensity b σ →
        (P * σ.val * P = σ.val → complexTraceNorm b (M.branchOne σ - σ) ≤ δ) ∧
        ((1 - P) * σ.val * (1 - P) = σ.val → complexTraceNorm b (M.branchZero σ - σ) ≤ δ)) →
       ∀ ρ : signedFiniteTrace b, IsComplexDensity b ρ →
        complexTraceNorm b (M.branchOne ρ - complexSandwich b P ρ) ≤
          min 2 (faceCalibrationError δ (spectralRoundingError ε)) ∧
        complexTraceNorm b (M.branchZero ρ - complexSandwich b (1 - P) ρ) ≤
          min 2 (faceCalibrationError δ (spectralRoundingError ε))) := by
  obtain ⟨R, hR, hcut⟩ := M.exists_roundedTraceInstrument b A hA hpair hdef hε
  refine ⟨R.projection, R.isProjection, hcut, fun hcal ρ hρ => ?_⟩
  have hcal' : R.FaceCalibrated δ := by
    apply (R.faceCalibrated_iff δ).mpr
    intro k σ hs ht hp
    let X : signedFiniteTrace b := σ
    cases k
    · have h := (hcal σ ⟨hs, ht⟩).2 hp
      rw [hR, complex_traceNorm_eq_trace_modulus]
      change complexTraceNorm b (M.branchZero X - X) ≤ δ
      exact h
    · have h := (hcal σ ⟨hs, ht⟩).1 hp
      rw [hR, complex_traceNorm_eq_trace_modulus]
      change complexTraceNorm b (M.branchOne X - X) ≤ δ
      exact h
  have hτ := spectralRoundingError_nonneg ((norm_nonneg _).trans hdef)
  have hyes := R.branch_error hδ hτ hcal' true hρ.1 hρ.2
  have hno := R.branch_error hδ hτ hcal' false hρ.1 hρ.2
  rw [hR, complex_traceNorm_eq_trace_modulus] at hyes hno
  exact ⟨hyes, hno⟩

#print axioms HilbertTrace.real_traceNorm_eq_trace_modulus
#print axioms HilbertTrace.complex_traceNorm_eq_trace_modulus
#print axioms HilbertTrace.quaternionic_traceNorm_eq_trace_modulus
#print axioms HilbertTrace.RealInstrument.exists_roundedTraceInstrument
#print axioms HilbertTrace.ComplexInstrument.exists_roundedTraceInstrument
#print axioms HilbertTrace.QuaternionicInstrument.exists_roundedTraceInstrument
#print axioms RoundedTraceInstrument.faceCalibrated_iff
#print axioms RoundedTraceInstrument.branch_error
#print axioms RoundedTraceInstrument.branch_eq_sandwich_of_zero_calibration
#print axioms RoundedTraceInstrument.word_error
#print axioms HilbertTrace.real_calibration_witness_bound
#print axioms HilbertTrace.complex_calibration_witness_bound
#print axioms HilbertTrace.quaternionic_calibration_witness_bound
#print axioms HilbertTrace.exists_hilbertTrace_calibration_sevenStep_margin
