/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi

/-! Gaussian and radial integrals in the normalization needed by the rank-one
chart argument. These inputs are independent of the Albert algebra. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Real Set

/-- The product Gaussian integral with an arbitrary translated center.
The ordinary coordinate volume uses a rank `2k` real coordinate space. -/
theorem integral_exp_shifted_normSq (k : ℕ) (b : ℝ) (hb : 0 < b)
    (u : Fin (2 * k) → ℝ) :
    (∫ x : Fin (2 * k) → ℝ, exp (-b * ∑ i, (x i + u i)^2)) = (π / b)^k := by
  have hp (x : Fin (2 * k) → ℝ) : exp (-b * ∑ i, (x i + u i)^2) =
      ∏ i, exp (-b * (x i + u i)^2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  have hshift (a : ℝ) : (∫ x : ℝ, exp (-b * (x + a)^2)) = √(π / b) := by
    rw [integral_add_right_eq_self (fun x : ℝ => exp (-b * x^2)) a, integral_gaussian]
  simp_rw [hp]
  rw [integral_fintype_prod_volume_eq_prod (fun i a => exp (-b * (a + u i)^2))]
  simp_rw [hshift]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul,
    Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)]

/-- The remaining radial integral on the positive ray with a free
strictly positive exponent scale. -/
theorem integral_rankOne_radial (k b : ℝ) (hk : 0 < k) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), t ^ (k - 1) * exp (-b * t)) = b ^ (-k) * Gamma k := by
  have hq : -1 < k - 1 := by linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := k - 1) zero_lt_one hq hb
  simpa [Real.rpow_one] using h

/-- The iterated chart integral once the native trace exponent has been
completed into two squares. The first Gaussian center can depend on the
second integration variable. -/
theorem integral_rankOne_chart_kernel (k : ℕ) (hk : 0 < k) (b r s : ℝ)
    (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (uCenter : (Fin (2 * k) → ℝ) → (Fin (2 * k) → ℝ)) (wCenter : Fin (2 * k) → ℝ) :
    (∫ t in Ioi (0 : ℝ), t ^ (3 * (k : ℝ) - 1) *
      (∫ w : Fin (2 * k) → ℝ, ∫ u : Fin (2 * k) → ℝ,
        exp (-t * (b * ∑ i, (u i + uCenter w i)^2) +
          -(t * r) * (∑ i, (w i + wCenter i)^2) + -(t * s)))) =
      ((π / b)^k * (π / r)^k) * (s ^ (-(k : ℝ)) * Gamma k) := by
  have hku : 0 < (k : ℝ) := by exact_mod_cast hk
  let C := (π / b)^k * (π / r)^k
  calc
    _ = ∫ t in Ioi (0 : ℝ), C * (t ^ ((k : ℝ) - 1) * exp (-s * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht' : 0 < t := ht
      have hsplit (w u : Fin (2 * k) → ℝ) :
          exp (-t * (b * ∑ i, (u i + uCenter w i)^2) +
            -(t * r) * (∑ i, (w i + wCenter i)^2) + -(t * s)) =
          exp (-(t * b) * (∑ i, (u i + uCenter w i)^2)) *
            exp (-(t * r) * (∑ i, (w i + wCenter i)^2)) * exp (-(t * s)) := by
        rw [Real.exp_add, Real.exp_add]
        congr 2
        ring
      simp_rw [hsplit, integral_mul_const, integral_exp_shifted_normSq k (t * b) (mul_pos ht' hb)]
      rw [integral_const_mul, integral_exp_shifted_normSq k (t * r) (mul_pos ht' hr)]
      rw [show t * s = s * t by ring]
      have hscale (a : ℝ) : (π / (t * a))^k = (π / a)^k * (t ^ (k : ℝ))⁻¹ := by
        rw [Real.rpow_natCast, ← inv_pow, ← mul_pow]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [hscale b, hscale r, ← Real.rpow_neg ht'.le]
      have hpow : t ^ (3 * (k : ℝ) - 1) * t ^ (-(k : ℝ)) * t ^ (-(k : ℝ)) =
          t ^ ((k : ℝ) - 1) := by
        rw [← Real.rpow_add ht', ← Real.rpow_add ht']
        congr 1
        ring
      dsimp [C]
      rw [show -(s * t) = -s * t by ring]
      linear_combination (π / b)^k * (π / r)^k * exp (-s * t) * hpow
    _ = _ := by
      rw [integral_const_mul, integral_rankOne_radial (k : ℝ) s hku hs]

end AlbertSequential.WindowProbability
