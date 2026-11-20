/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HilbertTraceCalibration

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.HilbertTrace

open RoundedTraceInstrument

section Real
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)

theorem real_calibration_witness_bound {n : ℕ} {τ δ : ℝ}
    (R : Fin n → RoundedTraceInstrument (realOperatorTraceData b) τ)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : ∀ i, (R i).FaceCalibrated δ)
    (ρ : (realSignedTraceMass b).WithNorm) (hρ : IsRealDensity b ρ)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {η γ : ℝ} (hγ : 0 < γ)
    (hmodel : ∀ M : HilbertProjectiveData (Fin n) ℝ H, 0 ≤ c.evaluate M.probability)
    (htarget : c.evaluate target ≤ -γ)
    (hobs : ∀ w ∈ c.coefficients.support, |measuredWord R ρ w - target w| ≤ η) :
    γ / c.coefficientNorm ≤ η + L * min 2 (faceCalibrationError δ τ) := by
  let M := realTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
  have hm := hmodel M
  rw [show M.probability = roundedWord R ρ from funext (real_roundedTraceInstrument_word b R ρ hρ)] at hm
  exact witness_bound R hδ hτ hcal hρ.1 hρ.2 c L hL target hγ hm htarget hobs

variable (S : RightQuaternionicHilbertStructure H)

theorem quaternionic_calibration_witness_bound {n : ℕ} {τ δ : ℝ}
    (R : Fin n → RoundedTraceInstrument (quaternionicOperatorTraceData b S) τ)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : ∀ i, (R i).FaceCalibrated δ)
    (ρ : (quaternionicSignedTraceMass b S).WithNorm) (hρ : IsQuaternionicDensity b S ρ)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {η γ : ℝ} (hγ : 0 < γ)
    (hmodel : ∀ M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure,
      0 ≤ c.evaluate M.toAlgebraic.probability)
    (htarget : c.evaluate target ≤ -γ)
    (hobs : ∀ w ∈ c.coefficients.support, |measuredWord R ρ w - target w| ≤ η) :
    γ / c.coefficientNorm ≤ η + L * min 2 (faceCalibrationError δ τ) := by
  let M := quaternionicTraceProjectiveModel b S (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
  have hm := hmodel M
  rw [show M.toAlgebraic.probability = roundedWord R ρ from
    funext (quaternionic_roundedTraceInstrument_word b S R ρ hρ)] at hm
  exact witness_bound R hδ hτ hcal hρ.1 hρ.2 c L hL target hγ hm htarget hobs

end Real

section Complex
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H)

theorem complex_calibration_witness_bound {n : ℕ} {τ δ : ℝ}
    (R : Fin n → RoundedTraceInstrument (complexOperatorTraceData b) τ)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hcal : ∀ i, (R i).FaceCalibrated δ)
    (ρ : (complexSignedTraceMass b).WithNorm) (hρ : IsComplexDensity b ρ)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {η γ : ℝ} (hγ : 0 < γ)
    (hmodel : ∀ M : HilbertProjectiveData (Fin n) ℂ H, 0 ≤ c.evaluate M.probability)
    (htarget : c.evaluate target ≤ -γ)
    (hobs : ∀ w ∈ c.coefficients.support, |measuredWord R ρ w - target w| ≤ η) :
    γ / c.coefficientNorm ≤ η + L * min 2 (faceCalibrationError δ τ) := by
  let M := complexTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
  have hm := hmodel M
  rw [show M.probability = roundedWord R ρ from funext (complex_roundedTraceInstrument_word b R ρ hρ)] at hm
  exact witness_bound R hδ hτ hcal hρ.1 hρ.2 c L hL target hγ hm htarget hobs

end Complex

universe u v

/-- The same seven-step margin serves arbitrary real, complex and right-quaternionic carriers. -/
theorem exists_hilbertTrace_calibration_sevenStep_margin
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    ∃ margin > (0 : ℝ),
      (∀ (H : Type u) (ι : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (b : HilbertBasis ι ℝ H) (τ δ η : ℝ)
        (R : Fin 4 → RoundedTraceInstrument (realOperatorTraceData b) τ)
        (ρ : (realSignedTraceMass b).WithNorm), IsRealDensity b ρ → 0 ≤ δ → 0 ≤ τ →
        (∀ i, (R i).FaceCalibrated δ) →
        (∀ w ∈ Ends.wordsE3Seven,
          |measuredWord R ρ w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| ≤ η) →
        margin ≤ η + 7 * min 2 (faceCalibrationError δ τ)) ∧
      (∀ (H : Type u) (ι : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (b : HilbertBasis ι ℂ H) (τ δ η : ℝ)
        (R : Fin 4 → RoundedTraceInstrument (complexOperatorTraceData b) τ)
        (ρ : (complexSignedTraceMass b).WithNorm), IsComplexDensity b ρ → 0 ≤ δ → 0 ≤ τ →
        (∀ i, (R i).FaceCalibrated δ) →
        (∀ w ∈ Ends.wordsE3Seven,
          |measuredWord R ρ w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| ≤ η) →
        margin ≤ η + 7 * min 2 (faceCalibrationError δ τ)) ∧
      (∀ (H : Type u) (ι : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H) (τ δ η : ℝ)
        (R : Fin 4 → RoundedTraceInstrument (quaternionicOperatorTraceData b S) τ)
        (ρ : (quaternionicSignedTraceMass b S).WithNorm), IsQuaternionicDensity b S ρ → 0 ≤ δ → 0 ≤ τ →
        (∀ i, (R i).FaceCalibrated δ) →
        (∀ w ∈ Ends.wordsE3Seven,
          |measuredWord R ρ w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| ≤ η) →
        margin ≤ η + 7 * min 2 (faceCalibrationError δ τ)) := by
  obtain ⟨margin, hm, hmargin⟩ := sevenStepMargin_of_calibrated_instruments.{u} p hp hA
  refine ⟨margin, hm, ?_, ?_, ?_⟩
  · intro H ι _ _ _ b τ δ η R ρ hρ hδ hτ hcal hobs
    let M := realTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
    apply hmargin _ _ _ (fun i => (R i).blocks) (fun i => (R i).instrument) M.toAlgebraic ρ δ τ η
      hρ.1 hρ.2 hδ hτ (fun i => (R i).leakage) hcal _ hobs
    intro w
    rw [M.toAlgebraic_probability]
    exact real_roundedTraceInstrument_word b R ρ hρ w
  · intro H ι _ _ _ b τ δ η R ρ hρ hδ hτ hcal hobs
    let M := complexTraceProjectiveModel b (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
    apply hmargin _ _ _ (fun i => (R i).blocks) (fun i => (R i).instrument) M.toAlgebraic ρ δ τ η
      hρ.1 hρ.2 hδ hτ (fun i => (R i).leakage) hcal _ hobs
    intro w
    rw [M.toAlgebraic_probability]
    exact complex_roundedTraceInstrument_word b R ρ hρ w
  · intro H ι _ _ _ b S τ δ η R ρ hρ hδ hτ hcal hobs
    let M := quaternionicTraceProjectiveModel b S (fun i => (R i).projection) (fun i => (R i).isProjection) ρ hρ
    apply hmargin _ _ _ (fun i => (R i).blocks) (fun i => (R i).instrument) M.toAlgebraic ρ δ τ η
      hρ.1 hρ.2 hδ hτ (fun i => (R i).leakage) hcal _ hobs
    exact quaternionic_roundedTraceInstrument_word b S R ρ hρ

end AlbertSequential.HilbertTrace
