/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.OperatorTraceCalibration
public import Robustness.WitnessTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    {T : TraceBaseNormData E}

structure RoundedTraceInstrument (D : OperatorTraceData (A := A) T) (τ : ℝ) where
  instrument : PositiveBinaryInstrument T
  projection : A
  isProjection : IsStarProjection projection
  leakage : ∀ b x, x ∈ T.positive →
    T.trace (instrument.branch b (blockBranch (D.positiveBlocks isProjection) (!b) x)) ≤
      τ * T.trace (blockBranch (D.positiveBlocks isProjection) (!b) x)

namespace RoundedTraceInstrument

variable {D : OperatorTraceData (A := A) T} {τ : ℝ}

def blocks (R : RoundedTraceInstrument D τ) : PositiveBlockDecomposition T :=
  D.positiveBlocks R.isProjection

def FaceCalibrated (R : RoundedTraceInstrument D τ) (δ : ℝ) : Prop :=
  ∀ b σ, σ ∈ T.positive → T.trace σ = 1 → blockBranch R.blocks b σ = σ →
    ‖R.instrument.branch b σ - σ‖ ≤ δ

theorem faceCalibrated_iff (R : RoundedTraceInstrument D τ) (δ : ℝ) :
    R.FaceCalibrated δ ↔ ∀ b σ, σ ∈ T.positive → T.trace σ = 1 →
      algebraicOutcome (fun _ : Unit => R.projection) ((), b) * D.val σ *
        algebraicOutcome (fun _ : Unit => R.projection) ((), b) = D.val σ →
      ‖R.instrument.branch b σ - σ‖ ≤ δ := by
  have h (b : Bool) (σ : E) : D.val (blockBranch R.blocks b σ) =
      algebraicOutcome (fun _ : Unit => R.projection) ((), b) * D.val σ *
        algebraicOutcome (fun _ : Unit => R.projection) ((), b) := by
    cases b
    · exact (D.val_sandwich (1 - R.projection) σ).trans (by
        simp [algebraicOutcome, R.isProjection.one_sub.isSelfAdjoint.star_eq])
    · exact (D.val_sandwich R.projection σ).trans (by
        simp [algebraicOutcome, R.isProjection.isSelfAdjoint.star_eq])
  constructor
  · intro hcal b σ hσ ht hh
    exact hcal b σ hσ ht (D.injective ((h b σ).trans hh))
  · intro hcal b σ hσ ht hh
    apply hcal b σ hσ ht
    exact (h b σ).symm.trans (congrArg D.val hh)

theorem branch_error (R : RoundedTraceInstrument D τ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : R.FaceCalibrated δ)
    (b : Bool) {ρ : E} (hρ : ρ ∈ T.positive) (htr : T.trace ρ = 1) :
    ‖R.instrument.branch b ρ - blockBranch R.blocks b ρ‖ ≤ min 2 (faceCalibrationError δ τ) :=
  calibrated_positive_instrument_error_le T R.blocks R.instrument hδ hτ R.leakage hcal b hρ htr

theorem branch_eq_sandwich_of_zero_calibration (R : RoundedTraceInstrument D 0)
    (hcal : R.FaceCalibrated 0) (b : Bool) {ρ : E} (hρ : ρ ∈ T.positive) (htr : T.trace ρ = 1) :
    R.instrument.branch b ρ = blockBranch R.blocks b ρ := by
  have h := R.branch_error le_rfl le_rfl hcal b hρ htr
  rw [faceCalibrationError_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

variable {I : Type*}

def measuredWord (R : I → RoundedTraceInstrument D τ) (ρ : E) (w : Word I) : ℝ :=
  T.trace (chronologicalState (fun a : Outcome I => (R a.1).instrument.branch a.2) ρ w)

def roundedWord (R : I → RoundedTraceInstrument D τ) (ρ : E) (w : Word I) : ℝ :=
  T.trace (chronologicalState (fun a : Outcome I => blockBranch (R a.1).blocks a.2) ρ w)

theorem roundedWord_eq_sandwich (R : I → RoundedTraceInstrument D τ) (ρ : E) (w : Word I) :
    roundedWord R ρ w = T.trace (chronologicalState
      (fun a => D.sandwich (algebraicOutcome (fun i => (R i).projection) a)) ρ w) := by
  have h : (fun a : Outcome I => blockBranch (R a.1).blocks a.2) =
      fun a => D.sandwich (algebraicOutcome (fun i => (R i).projection) a) := by
    funext a
    rcases a with ⟨i, k⟩
    cases k <;> rfl
  exact congrArg (fun F : Outcome I → (E →ₗ[ℝ] E) =>
    T.trace (chronologicalState (fun a => F a) ρ w)) h

theorem word_error (R : I → RoundedTraceInstrument D τ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : ∀ i, (R i).FaceCalibrated δ)
    {ρ : E} (hρ : ρ ∈ T.positive) (htr : T.trace ρ = 1) (w : Word I) :
    |measuredWord R ρ w - roundedWord R ρ w| ≤ (w.length : ℝ) * min 2 (faceCalibrationError δ τ) :=
  calibrated_positive_instrument_word_error_le T (fun i => (R i).blocks) (fun i => (R i).instrument)
    hδ hτ (fun i => (R i).leakage) hcal hρ htr w

theorem witness_bound {n : ℕ} (R : Fin n → RoundedTraceInstrument D τ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : ∀ i, (R i).FaceCalibrated δ)
    {ρ : E} (hρ : ρ ∈ T.positive) (htr : T.trace ρ = 1)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {η γ : ℝ} (hγ : 0 < γ)
    (hmodel : 0 ≤ c.evaluate (roundedWord R ρ)) (htarget : c.evaluate target ≤ -γ)
    (hobs : ∀ w ∈ c.coefficients.support, |measuredWord R ρ w - target w| ≤ η) :
    γ / c.coefficientNorm ≤ η + L * min 2 (faceCalibrationError δ τ) := by
  obtain ⟨_, w, hw, _⟩ :=
    c.positive_witness_margin_forces_some_word target (roundedWord R ρ) hγ hmodel htarget
  have hη : 0 ≤ η := (abs_nonneg _).trans (hobs w hw)
  have hβ : 0 ≤ min 2 (faceCalibrationError δ τ) := le_min (by norm_num) (by
    unfold faceCalibrationError
    positivity)
  refine (c.positive_witness_margin_normalized_error L hL target (measuredWord R ρ) (roundedWord R ρ)
    hη hβ hγ hobs ?_ hmodel htarget).2
  intro v _
  rw [abs_sub_comm]
  exact word_error R hδ hτ hcal hρ htr v

end RoundedTraceInstrument
end AlbertSequential
