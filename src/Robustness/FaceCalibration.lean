module

public import Robustness.TraceBaseNorm
public import Robustness.PositiveQuadraticCrossBound

/-! The noncomputational positive-map face-calibration engine. The explicit
trace-base and positive block interface is general; an actual arbitrary R/C/H
trace-class/spectral instance remains a separate native proof obligation.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem homogeneous_bound_on_positive_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (L B : E →ₗ[ℝ] E) {delta : ℝ} (_hdelta : 0 ≤ delta)
    (hcalibration : ∀ sigma ∈ T.positive, T.trace sigma = 1 → B sigma = sigma → ‖L sigma‖ ≤ delta)
    {x : E} (hx : x ∈ T.positive) (hface : B x = x) :
    ‖L x‖ ≤ delta * T.trace x := by
  let mass : ℝ := T.trace x
  have hmass : 0 ≤ mass := traceBase_trace_nonneg T hx
  by_cases hmzero : mass = 0
  · have hnormzero : ‖x‖ = 0 := by rw [← T.trace_eq_norm x hx]; exact hmzero
    have hxzero := norm_eq_zero.mp hnormzero
    subst x
    simp
  · let sigma : E := mass⁻¹ • x
    have hsigma : sigma ∈ T.positive := T.smul_positive _ (inv_nonneg.mpr hmass) x hx
    have hsigmatrace : T.trace sigma = 1 := by
      simp only [sigma, map_smul, smul_eq_mul]
      change mass⁻¹ * mass = 1
      exact inv_mul_cancel₀ hmzero
    have hsigmaface : B sigma = sigma := by
      simp only [sigma, map_smul, hface]
    have hreconstruct : mass • sigma = x := by
      simp only [sigma, smul_smul, mul_inv_cancel₀ hmzero, one_smul]
    have hbound := hcalibration sigma hsigma hsigmatrace hsigmaface
    calc
      ‖L x‖ = ‖L (mass • sigma)‖ := by rw [hreconstruct]
      _ = mass * ‖L sigma‖ := by rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmass]
      _ ≤ mass * delta := mul_le_mul_of_nonneg_left hbound hmass
      _ = delta * T.trace x := by ring

structure PositiveBlockDecomposition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : TraceBaseNormData E) where
  first : E →ₗ[ℝ] E
  second : E →ₗ[ℝ] E
  first_positive : ∀ x ∈ T.positive, first x ∈ T.positive
  second_positive : ∀ x ∈ T.positive, second x ∈ T.positive
  first_idempotent : ∀ x, first (first x) = first x
  second_idempotent : ∀ x, second (second x) = second x
  trace_split : ∀ x ∈ T.positive, T.trace (first x) + T.trace (second x) = T.trace x
  quadratic_positive : ∀ x ∈ T.positive, ∀ s t : ℝ,
    s ^ 2 • first x + (s * t) • (x - first x - second x) + t ^ 2 • second x ∈ T.positive

def PositiveBlockDecomposition.swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : TraceBaseNormData E} (B : PositiveBlockDecomposition T) : PositiveBlockDecomposition T where
  first := B.second
  second := B.first
  first_positive := B.second_positive
  second_positive := B.first_positive
  first_idempotent := B.second_idempotent
  second_idempotent := B.first_idempotent
  trace_split := fun x hx => by simpa only [add_comm] using B.trace_split x hx
  quadratic_positive := by
    intro x hx s t
    have hcross : x - B.second x - B.first x = x - B.first x - B.second x := by abel
    simpa only [hcross, mul_comm, add_comm, add_left_comm, add_assoc] using
      B.quadratic_positive x hx t s

theorem PositiveBlockDecomposition.first_trace_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : TraceBaseNormData E}
    (B : PositiveBlockDecomposition T) {x : E} (hx : x ∈ T.positive) :
    T.trace (B.first x) ≤ T.trace x := by
  have hnonneg := traceBase_trace_nonneg T (B.second_positive x hx)
  have hsplit := B.trace_split x hx
  linarith

theorem PositiveBlockDecomposition.second_trace_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : TraceBaseNormData E}
    (B : PositiveBlockDecomposition T) {x : E} (hx : x ∈ T.positive) :
    T.trace (B.second x) ≤ T.trace x := by
  have hnonneg := traceBase_trace_nonneg T (B.first_positive x hx)
  have hsplit := B.trace_split x hx
  linarith

theorem calibrated_positive_branch_error_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (B : PositiveBlockDecomposition T) (F : E →ₗ[ℝ] E)
    (hFpositive : ∀ x ∈ T.positive, F x ∈ T.positive)
    (hFtrace : ∀ x ∈ T.positive, T.trace (F x) ≤ T.trace x)
    {delta tau : ℝ} (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hleakage : ∀ x ∈ T.positive, T.trace (F (B.second x)) ≤ tau * T.trace (B.second x))
    (hcalibration : ∀ sigma ∈ T.positive, T.trace sigma = 1 → B.first sigma = sigma →
      ‖F sigma - sigma‖ ≤ delta)
    {rho : E} (hrho : rho ∈ T.positive) (htrace : T.trace rho = 1) :
    ‖F rho - B.first rho‖ ≤
      min 2 ((delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2) := by
  let p : ℝ := T.trace (B.first rho)
  let q : ℝ := T.trace (B.second rho)
  have hP := B.first_positive rho hrho
  have hQ := B.second_positive rho hrho
  have hp : 0 ≤ p := traceBase_trace_nonneg T hP
  have hq : 0 ≤ q := traceBase_trace_nonneg T hQ
  have hpq : p + q = 1 := (B.trace_split rho hrho).trans htrace
  have hpone : p ≤ 1 := by linarith
  have hFP := hFpositive (B.first rho) hP
  have hFQ := hFpositive (B.second rho) hQ
  have hFPzero := traceBase_trace_nonneg T hFP
  have hFQzero := traceBase_trace_nonneg T hFQ
  have hFPtrace : T.trace (F (B.first rho)) ≤ p := hFtrace _ hP
  have hFQtrace : T.trace (F (B.second rho)) ≤ tau * q := hleakage rho hrho
  have hcalP : ‖F (B.first rho) - B.first rho‖ ≤ delta * p := by
    let L : E →ₗ[ℝ] E := F - LinearMap.id
    have heval (x : E) : L x = F x - x := rfl
    have hcalL : ∀ sigma ∈ T.positive, T.trace sigma = 1 → B.first sigma = sigma →
        ‖L sigma‖ ≤ delta := by
      intro sigma hs ht hf
      simpa only [heval] using hcalibration sigma hs ht hf
    have hbound := homogeneous_bound_on_positive_face T L B.first hdelta hcalL hP
      (B.first_idempotent rho)
    simpa only [heval, p] using hbound
  have hquad : ∀ t : ℝ,
      t ^ 2 • F (B.first rho) + t • F (rho - B.first rho - B.second rho) +
        F (B.second rho) ∈ T.positive := by
    intro t
    have h := hFpositive _ (B.quadratic_positive rho hrho t 1)
    simpa only [map_add, map_smul, mul_one, one_pow, one_smul] using h
  have hcross := positive_quadratic_trace_norm_bound T.positive T.trace T.trace_eq_norm
    (F (B.first rho)) (F (B.second rho)) (F (rho - B.first rho - B.second rho)) hFP hFQ hquad
  have hcrossbound : ‖F (rho - B.first rho - B.second rho)‖ ≤ 2 * Real.sqrt (tau * p * q) := by
    have hm := mul_le_mul hFPtrace hFQtrace hFQzero hp
    have hs := Real.sqrt_le_sqrt hm
    have hreorder : p * (tau * q) = tau * p * q := by ring
    rw [hreorder] at hs
    exact hcross.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hQnorm : ‖F (B.second rho)‖ ≤ tau * q := by
    rw [← T.trace_eq_norm _ hFQ]
    exact hFQtrace
  have hdecomposition : F rho - B.first rho =
      (F (B.first rho) - B.first rho) + F (B.second rho) +
        F (rho - B.first rho - B.second rho) := by
    rw [map_sub, map_sub]
    abel
  have hmain : ‖F rho - B.first rho‖ ≤
      (delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2 := by
    rw [hdecomposition]
    calc
      _ ≤ ‖(F (B.first rho) - B.first rho) + F (B.second rho)‖ +
          ‖F (rho - B.first rho - B.second rho)‖ := norm_add_le _ _
      _ ≤ (‖F (B.first rho) - B.first rho‖ + ‖F (B.second rho)‖) +
          ‖F (rho - B.first rho - B.second rho)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ delta * p + tau * q + 2 * Real.sqrt (tau * p * q) :=
        add_le_add (add_le_add hcalP hQnorm) hcrossbound
      _ ≤ _ := calibration_quadratic_form_le hdelta htau hp hq hpq
  have hFwhole := hFpositive rho hrho
  have hFnorm : ‖F rho‖ ≤ 1 := by
    rw [← T.trace_eq_norm _ hFwhole]
    exact (hFtrace rho hrho).trans_eq htrace
  have hPnorm : ‖B.first rho‖ ≤ 1 := by
    rw [← T.trace_eq_norm _ hP]
    exact hpone
  have htwo : ‖F rho - B.first rho‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith)
  exact le_min htwo hmain

end AlbertSequential
