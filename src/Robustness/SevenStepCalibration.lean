/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Ends.UniformB
public import Robustness.PositiveInstrumentStability

@[expose] public section
noncomputable section
namespace AlbertSequential

/-- The uncapped branch error in the face-calibration estimate of core §6. -/
def faceCalibrationError (δ τ : ℝ) : ℝ :=
  (δ + τ + Real.sqrt ((δ - τ)^2 + 4*τ)) / 2

theorem faceCalibrationError_zero : faceCalibrationError 0 0 = 0 := by
  simp [faceCalibrationError]

theorem faceCalibrationError_le {δ τ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) :
    faceCalibrationError δ τ ≤ δ + τ + Real.sqrt τ := by
  have hs := Real.sq_sqrt hτ
  have hr : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have h : Real.sqrt ((δ - τ)^2 + 4*τ) ≤ δ + τ + 2 * Real.sqrt τ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [mul_nonneg hδ hτ, mul_nonneg hδ hr, mul_nonneg hτ hr]
  unfold faceCalibrationError
  linarith

/-- The common seven-step margin after uniform face calibration, for any trace-base
instrument whose rounded blocks have the supplied projective realization. -/
theorem sevenStepMargin_of_calibrated_instruments
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    : ∃ margin > (0 : ℝ), ∀ (E A : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [StarModule ℝ A] (T : TraceBaseNormData E)
      (B : Fin 4 → PositiveBlockDecomposition T) (F : Fin 4 → PositiveBinaryInstrument T)
      (M : AlgebraicProjectiveData (Fin 4) A) (ρ : E) (δ τ η : ℝ),
      ρ ∈ T.positive → T.trace ρ = 1 → 0 ≤ δ → 0 ≤ τ →
      (∀ i b x, x ∈ T.positive → T.trace ((F i).branch b (blockBranch (B i) (!b) x)) ≤
        τ * T.trace (blockBranch (B i) (!b) x)) →
      (∀ i b σ, σ ∈ T.positive → T.trace σ = 1 → blockBranch (B i) b σ = σ →
        ‖(F i).branch b σ - σ‖ ≤ δ) →
      (∀ w, M.probability w =
        T.trace (chronologicalState (fun a : Fin 4 × Bool => blockBranch (B a.1) a.2) ρ w)) →
      (∀ w ∈ Ends.wordsE3Seven,
        |T.trace (chronologicalState (fun a : Fin 4 × Bool => (F a.1).branch a.2) ρ w) -
          nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| ≤ η) →
      margin ≤ η + 7 * min 2 (faceCalibrationError δ τ) := by
  obtain ⟨g, hg, gap⟩ := Ends.uniform_b_algebraic p hp hA
  refine ⟨g, hg, ?_⟩
  intro E A _ _ _ _ _ _ _ _ T B F M ρ δ τ η hρ htr hδ hτ hleak hcal hmodel hobs
  obtain ⟨w, hlen, hhead, hw⟩ := gap A M
  let measured := T.trace (chronologicalState (fun a : Fin 4 × Bool => (F a.1).branch a.2) ρ w)
  have he : |M.probability w - measured| ≤ (w.length : ℝ) * min 2 (faceCalibrationError δ τ) := by
    rw [hmodel, abs_sub_comm]
    exact calibrated_positive_instrument_word_error_le T B F hδ hτ hleak hcal hρ htr w
  have ho := hobs w ⟨hlen, hhead⟩
  have hβ : 0 ≤ min 2 (faceCalibrationError δ τ) := le_min (by norm_num) (by
    unfold faceCalibrationError; positivity)
  have hn : (w.length : ℝ) ≤ 7 := by exact_mod_cast hlen
  calc
    g ≤ _ := hw
    _ ≤ |M.probability w - measured| + |measured - _| := abs_sub_le _ _ _
    _ ≤ (w.length : ℝ) * min 2 (faceCalibrationError δ τ) + η := add_le_add he ho
    _ ≤ η + 7 * min 2 (faceCalibrationError δ τ) := by linarith [mul_le_mul_of_nonneg_right hn hβ]

end AlbertSequential
