module

public import Robustness.QuadraticBounds
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! The positive-map cross-term estimate in an arbitrary real normed trace
space. Hahn–Banach replaces spectral support projections of the cross term.
Actual R/C/H self-adjoint trace-class bindings remain separate obligations.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem positive_quadratic_trace_norm_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : Set E) (trace : E →ₗ[ℝ] ℝ)
    (htrace : ∀ x ∈ C, trace x = ‖x‖)
    (U V H : E) (hU : U ∈ C) (hV : V ∈ C)
    (hquadratic : ∀ t : ℝ, t ^ 2 • U + t • H + V ∈ C) :
    ‖H‖ ≤ 2 * Real.sqrt (trace U * trace V) := by
  obtain ⟨f, hfnorm, hfH⟩ := exists_dual_vector'' ℝ H
  have hfHreal : f H = ‖H‖ := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hfH
  have hfbound (x : E) : |f x| ≤ ‖x‖ := by
    calc
      |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hfnorm (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  let fplus : E →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • (trace + f.toLinearMap)
  let fminus : E →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • (trace - f.toLinearMap)
  have hp (x : E) (hx : x ∈ C) : 0 ≤ fplus x := by
    have hb := (abs_le.mp (hfbound x)).1
    have ht := htrace x hx
    simp only [fplus, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul,
      ContinuousLinearMap.coe_coe]
    linarith
  have hm (x : E) (hx : x ∈ C) : 0 ≤ fminus x := by
    have hb := (abs_le.mp (hfbound x)).2
    have ht := htrace x hx
    simp only [fminus, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
      ContinuousLinearMap.coe_coe]
    linarith
  have hqp : ∀ t : ℝ, 0 ≤ t ^ 2 * fplus U + t * fplus H + fplus V := by
    intro t
    simpa only [map_add, map_smul, smul_eq_mul] using hp _ (hquadratic t)
  have hqm : ∀ t : ℝ, 0 ≤ t ^ 2 * fminus U + t * fminus H + fminus V := by
    intro t
    simpa only [map_add, map_smul, smul_eq_mul] using hm _ (hquadratic t)
  have hplus := positive_quadratic_cross_bound (hp U hU) (hp V hV) hqp
  have hminus := positive_quadratic_cross_bound (hm U hU) (hm V hV) hqm
  have hsplit (x : E) : fplus x + fminus x = trace x := by
    simp only [fplus, fminus, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    ring
  have hH : fplus H - fminus H = ‖H‖ := by
    simp only [fplus, fminus, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    rw [hfHreal]
    ring
  calc
    ‖H‖ = fplus H - fminus H := hH.symm
    _ ≤ |fplus H| + |fminus H| := by
      simpa only [sub_eq_add_neg] using add_le_add (le_abs_self (fplus H)) (neg_le_abs (fminus H))
    _ ≤ 2 * Real.sqrt (fplus U * fplus V) + 2 * Real.sqrt (fminus U * fminus V) :=
      add_le_add hplus hminus
    _ = 2 * (Real.sqrt (fplus U * fplus V) + Real.sqrt (fminus U * fminus V)) := by ring
    _ ≤ 2 * Real.sqrt ((fplus U + fminus U) * (fplus V + fminus V)) :=
      mul_le_mul_of_nonneg_left
        (two_term_sqrt_cauchy_schwarz (hp U hU) (hm U hU) (hp V hV) (hm V hV)) (by norm_num)
    _ = 2 * Real.sqrt (trace U * trace V) := by rw [hsplit U, hsplit V]

end AlbertSequential
