module

public import Robustness.FaceCalibration

/-! Both positive outcome branches and unconditional word stability under
uniform all-density face calibration. These are exact abstract trace-base
theorems; actual R/C/H trace-class and spectral bindings are not part of them.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure PositiveBinaryInstrument {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : TraceBaseNormData E) where
  branch : Bool → (E →ₗ[ℝ] E)
  positive : ∀ b x, x ∈ T.positive → branch b x ∈ T.positive
  normalized : ∀ x, T.trace (branch true x + branch false x) = T.trace x

def blockBranch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : TraceBaseNormData E} (B : PositiveBlockDecomposition T) (b : Bool) : E →ₗ[ℝ] E :=
  if b then B.first else B.second

theorem PositiveBinaryInstrument.branch_trace_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : TraceBaseNormData E}
    (F : PositiveBinaryInstrument T) (b : Bool) {x : E} (hx : x ∈ T.positive) :
    T.trace (F.branch b x) ≤ T.trace x := by
  have hs := F.normalized x
  rw [map_add] at hs
  have hyes := traceBase_trace_nonneg T (F.positive true x hx)
  have hno := traceBase_trace_nonneg T (F.positive false x hx)
  cases b <;> linarith

theorem blockBranch_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : TraceBaseNormData E} (B : PositiveBlockDecomposition T) (b : Bool)
    {x : E} (hx : x ∈ T.positive) : blockBranch B b x ∈ T.positive := by
  cases b
  · exact B.second_positive x hx
  · exact B.first_positive x hx

theorem blockBranch_trace_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : TraceBaseNormData E} (B : PositiveBlockDecomposition T) (b : Bool)
    {x : E} (hx : x ∈ T.positive) : T.trace (blockBranch B b x) ≤ T.trace x := by
  cases b
  · exact B.second_trace_le hx
  · exact B.first_trace_le hx

theorem calibrated_positive_instrument_error_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (B : PositiveBlockDecomposition T) (F : PositiveBinaryInstrument T)
    {delta tau : ℝ} (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hleakage : ∀ b x, x ∈ T.positive →
      T.trace (F.branch b (blockBranch B (!b) x)) ≤ tau * T.trace (blockBranch B (!b) x))
    (hcalibration : ∀ b sigma, sigma ∈ T.positive → T.trace sigma = 1 →
      blockBranch B b sigma = sigma → ‖F.branch b sigma - sigma‖ ≤ delta)
    (b : Bool) {rho : E} (hrho : rho ∈ T.positive) (htrace : T.trace rho = 1) :
    ‖F.branch b rho - blockBranch B b rho‖ ≤
      min 2 ((delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2) := by
  cases b
  · change ‖F.branch false rho - B.second rho‖ ≤ _
    simpa only [PositiveBlockDecomposition.swap] using
      calibrated_positive_branch_error_le T B.swap (F.branch false) (F.positive false)
        (fun x hx => F.branch_trace_le false hx) hdelta htau
        (fun x hx => hleakage false x hx) (fun sigma hs ht hf => hcalibration false sigma hs ht hf)
        hrho htrace
  · change ‖F.branch true rho - B.first rho‖ ≤ _
    exact
      calibrated_positive_branch_error_le T B (F.branch true) (F.positive true)
        (fun x hx => F.branch_trace_le true hx) hdelta htau
        (fun x hx => hleakage true x hx) (fun sigma hs ht hf => hcalibration true sigma hs ht hf)
        hrho htrace

theorem calibrated_positive_instrument_word_error_le {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (B : I → PositiveBlockDecomposition T) (F : I → PositiveBinaryInstrument T)
    {delta tau : ℝ} (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hleakage : ∀ i b x, x ∈ T.positive →
      T.trace ((F i).branch b (blockBranch (B i) (!b) x)) ≤
        tau * T.trace (blockBranch (B i) (!b) x))
    (hcalibration : ∀ i b sigma, sigma ∈ T.positive → T.trace sigma = 1 →
      blockBranch (B i) b sigma = sigma → ‖(F i).branch b sigma - sigma‖ ≤ delta)
    {rho : E} (hrho : rho ∈ T.positive) (htrace : T.trace rho = 1) (w : List (I × Bool)) :
    |T.trace (chronologicalState (fun a : I × Bool => (F a.1).branch a.2) rho w) -
        T.trace (chronologicalState (fun a : I × Bool => blockBranch (B a.1) a.2) rho w)| ≤
      (w.length : ℝ) * min 2 ((delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2) := by
  let beta : ℝ := min 2 ((delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2)
  have hbeta : 0 ≤ beta := le_min (by norm_num) (by positivity)
  have hstep : ∀ (a : I × Bool) x, x ∈ T.positive →
      ‖(F a.1).branch a.2 x - blockBranch (B a.1) a.2 x‖ ≤ beta * T.trace x := by
    intro a x hx
    let L : E →ₗ[ℝ] E := (F a.1).branch a.2 - blockBranch (B a.1) a.2
    have heval (y : E) : L y = (F a.1).branch a.2 y - blockBranch (B a.1) a.2 y := rfl
    have hcalL : ∀ sigma ∈ T.positive, T.trace sigma = 1 →
        (LinearMap.id : E →ₗ[ℝ] E) sigma = sigma →
        ‖L sigma‖ ≤ beta := by
      intro sigma hs ht _
      simpa only [heval] using calibrated_positive_instrument_error_le T (B a.1) (F a.1) hdelta htau
        (hleakage a.1) (hcalibration a.1) a.2 hs ht
    have hbound := homogeneous_bound_on_positive_face T L LinearMap.id hbeta hcalL hx rfl
    simpa only [heval] using hbound
  have hnorm := positive_instrument_word_state_error_le T
    (fun a : I × Bool => (F a.1).branch a.2) (fun a : I × Bool => blockBranch (B a.1) a.2)
    (fun a => (F a.1).positive a.2) (fun a x hx => blockBranch_positive (B a.1) a.2 hx)
    (fun a x hx => (F a.1).branch_trace_le a.2 hx)
    (fun a x hx => blockBranch_trace_le (B a.1) a.2 hx) hbeta hstep hrho htrace w
  have hprob := traceBase_abs_trace_le_norm T
    (chronologicalState (fun a : I × Bool => (F a.1).branch a.2) rho w -
      chronologicalState (fun a : I × Bool => blockBranch (B a.1) a.2) rho w)
  rw [map_sub] at hprob
  exact hprob.trans hnorm

end AlbertSequential
