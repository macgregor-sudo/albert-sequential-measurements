module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

/-! Degenerate-safe scalar ingredients for positive-instrument calibration.
The proofs use quadratic positivity and elementary two-variable inequalities.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem positive_quadratic_cross_bound {u v h : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hq : ∀ t : ℝ, 0 ≤ t ^ 2 * u + t * h + v) :
    |h| ≤ 2 * Real.sqrt (u * v) := by
  have hd := discrim_le_zero (a := u) (b := h) (c := v) (fun t => by
    simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using hq t)
  simp only [discrim] at hd
  apply abs_le_of_sq_le_sq _ (by positivity : 0 ≤ 2 * Real.sqrt (u * v))
  have hs := Real.sq_sqrt (mul_nonneg hu hv)
  nlinarith

theorem two_term_sqrt_cauchy_schwarz {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * c) + Real.sqrt (b * d) ≤ Real.sqrt ((a + b) * (c + d)) := by
  have hcross : Real.sqrt (a * c) * Real.sqrt (b * d) =
      Real.sqrt (a * d) * Real.sqrt (b * c) := by
    rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_mul ha, Real.sqrt_mul hb]
    ring
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  have h1 := Real.sq_sqrt (mul_nonneg ha hc)
  have h2 := Real.sq_sqrt (mul_nonneg hb hd)
  have h3 := Real.sq_sqrt (mul_nonneg ha hd)
  have h4 := Real.sq_sqrt (mul_nonneg hb hc)
  rw [Real.sq_sqrt (mul_nonneg (add_nonneg ha hb) (add_nonneg hc hd))]
  nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (b * c))]

theorem calibration_quadratic_form_le {delta tau p q : ℝ}
    (_hdelta : 0 ≤ delta) (htau : 0 ≤ tau) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) :
    delta * p + tau * q + 2 * Real.sqrt (tau * p * q) ≤
      (delta + tau + Real.sqrt ((delta - tau) ^ 2 + 4 * tau)) / 2 := by
  let rad : ℝ := (delta - tau) ^ 2 + 4 * tau
  let b : ℝ := (delta + tau + Real.sqrt rad) / 2
  have hrad : 0 ≤ rad := by dsimp [rad]; positivity
  have hs := Real.sq_sqrt hrad
  have hdiff : |delta - tau| ≤ Real.sqrt rad := by
    apply abs_le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    dsimp [rad] at hs
    nlinarith
  have hbd : 0 ≤ b - delta := by
    have hh := (abs_le.mp hdiff).2
    dsimp [b]
    linarith
  have hbt : 0 ≤ b - tau := by
    have hh := (abs_le.mp hdiff).1
    dsimp [b]
    linarith
  have hbprod : (b - delta) * (b - tau) = tau := by
    dsimp [b]
    dsimp [rad] at hs
    nlinarith
  have hleft := Real.sq_sqrt (mul_nonneg hbd hp)
  have hright := Real.sq_sqrt (mul_nonneg hbt hq)
  have hcross : Real.sqrt ((b - delta) * p) * Real.sqrt ((b - tau) * q) =
      Real.sqrt (tau * p * q) := by
    rw [← Real.sqrt_mul (mul_nonneg hbd hp)]
    congr 1
    calc
      ((b - delta) * p) * ((b - tau) * q) = (b - delta) * (b - tau) * p * q := by ring
      _ = tau * p * q := by rw [hbprod]
  have hmix : 2 * Real.sqrt (tau * p * q) ≤ (b - delta) * p + (b - tau) * q := by
    nlinarith [sq_nonneg (Real.sqrt ((b - delta) * p) - Real.sqrt ((b - tau) * q))]
  have hbmass : delta * p + tau * q + (b - delta) * p + (b - tau) * q = b := by
    calc
      _ = b * (p + q) := by ring
      _ = b := by rw [hpq, mul_one]
  change delta * p + tau * q + 2 * Real.sqrt (tau * p * q) ≤ b
  nlinarith

end AlbertSequential
