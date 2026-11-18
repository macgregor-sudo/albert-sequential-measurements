module

public import Robustness.WordContractions

/-! Explicit trace-base norm data and positive-map contraction. This models
the precise structural facts needed from self-adjoint trace-class operators;
constructing the actual arbitrary-dimensional R/C/H instances is separate.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure TraceBaseNormData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  positive : Set E
  trace : E →ₗ[ℝ] ℝ
  zero_positive : (0 : E) ∈ positive
  add_positive : ∀ x ∈ positive, ∀ y ∈ positive, x + y ∈ positive
  smul_positive : ∀ (c : ℝ), 0 ≤ c → ∀ x ∈ positive, c • x ∈ positive
  trace_eq_norm : ∀ x ∈ positive, trace x = ‖x‖
  decompose : ∀ x : E, ∃ p n : E,
    p ∈ positive ∧ n ∈ positive ∧ x = p - n ∧ ‖x‖ = trace p + trace n

theorem traceBase_trace_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : TraceBaseNormData E) {x : E} (hx : x ∈ T.positive) : 0 ≤ T.trace x := by
  rw [T.trace_eq_norm x hx]
  exact norm_nonneg x

theorem traceBase_abs_trace_le_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : TraceBaseNormData E) (x : E) : |T.trace x| ≤ ‖x‖ := by
  obtain ⟨p, n, hp, hn, hx, hnorm⟩ := T.decompose x
  have hp0 := traceBase_trace_nonneg T hp
  have hn0 := traceBase_trace_nonneg T hn
  have htrace : T.trace x = T.trace p - T.trace n := by rw [hx, map_sub]
  rw [htrace, hnorm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem positive_trace_nonincreasing_norm_contracts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (F : E →ₗ[ℝ] E) (hpositive : ∀ x ∈ T.positive, F x ∈ T.positive)
    (htrace : ∀ x ∈ T.positive, T.trace (F x) ≤ T.trace x) (x : E) :
    ‖F x‖ ≤ ‖x‖ := by
  obtain ⟨p, n, hp, hn, hx, hnorm⟩ := T.decompose x
  rw [hx, map_sub]
  calc
    ‖F p - F n‖ ≤ ‖F p‖ + ‖F n‖ := norm_sub_le _ _
    _ = T.trace (F p) + T.trace (F n) := by
      rw [T.trace_eq_norm (F p) (hpositive p hp), T.trace_eq_norm (F n) (hpositive n hn)]
    _ ≤ T.trace p + T.trace n := add_le_add (htrace p hp) (htrace n hn)
    _ = ‖p - n‖ := by simpa only [hx] using hnorm.symm

theorem positive_trace_nonincreasing_distance_contracts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (F : E →ₗ[ℝ] E) (hpositive : ∀ x ∈ T.positive, F x ∈ T.positive)
    (htrace : ∀ x ∈ T.positive, T.trace (F x) ≤ T.trace x) (x y : E) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  simpa only [map_sub] using positive_trace_nonincreasing_norm_contracts T F hpositive htrace (x - y)

theorem positive_instrument_word_state_error_le {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (F G : I → (E →ₗ[ℝ] E))
    (hFpos : ∀ i x, x ∈ T.positive → F i x ∈ T.positive)
    (hGpos : ∀ i x, x ∈ T.positive → G i x ∈ T.positive)
    (hFtrace : ∀ i x, x ∈ T.positive → T.trace (F i x) ≤ T.trace x)
    (hGtrace : ∀ i x, x ∈ T.positive → T.trace (G i x) ≤ T.trace x)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hstep : ∀ i x, x ∈ T.positive → ‖F i x - G i x‖ ≤ beta * T.trace x)
    {rho : E} (hrho : rho ∈ T.positive) (htrace : T.trace rho = 1) (w : List I) :
    ‖chronologicalState (fun i => F i) rho w - chronologicalState (fun i => G i) rho w‖ ≤
      (w.length : ℝ) * beta := by
  let C : Set E := {x | x ∈ T.positive ∧ T.trace x ≤ 1}
  apply norm_chronologicalState_sub_le C (fun i => F i) (fun i => G i)
    (fun i => positive_trace_nonincreasing_distance_contracts T (F i) (hFpos i) (hFtrace i))
    (fun i y hy => ⟨hGpos i y hy.1, (hGtrace i y hy.1).trans hy.2⟩) hbeta
  · intro i y hy
    exact (hstep i y hy.1).trans
      ((mul_le_mul_of_nonneg_left hy.2 hbeta).trans_eq (mul_one beta))
  · exact ⟨hrho, htrace.le⟩

theorem positive_instrument_word_probability_error_le {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : TraceBaseNormData E)
    (F G : I → (E →ₗ[ℝ] E))
    (hFpos : ∀ i x, x ∈ T.positive → F i x ∈ T.positive)
    (hGpos : ∀ i x, x ∈ T.positive → G i x ∈ T.positive)
    (hFtrace : ∀ i x, x ∈ T.positive → T.trace (F i x) ≤ T.trace x)
    (hGtrace : ∀ i x, x ∈ T.positive → T.trace (G i x) ≤ T.trace x)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hstep : ∀ i x, x ∈ T.positive → ‖F i x - G i x‖ ≤ beta * T.trace x)
    {rho : E} (hrho : rho ∈ T.positive) (htrace : T.trace rho = 1) (w : List I) :
    |T.trace (chronologicalState (fun i => F i) rho w) -
      T.trace (chronologicalState (fun i => G i) rho w)| ≤ (w.length : ℝ) * beta := by
  rw [← map_sub]
  exact (traceBase_abs_trace_le_norm T _).trans
    (positive_instrument_word_state_error_le T F G hFpos hGpos hFtrace hGtrace hbeta hstep hrho htrace w)

end AlbertSequential
