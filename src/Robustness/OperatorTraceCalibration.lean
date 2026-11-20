/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.SevenStepCalibration
public import Mathlib.Tactic.Module

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Ring A] [StarRing A] [Module ℝ A] (T : TraceBaseNormData E)

/-- A trace-norm operator carrier with its trace pairing and literal sandwiches. -/
structure OperatorTraceData where
  val : E →ₗ[ℝ] A
  injective : Function.Injective val
  sandwich : A → E →ₗ[ℝ] E
  val_sandwich : ∀ P x, val (sandwich P x) = P * val x * star P
  sandwich_positive : ∀ P x, x ∈ T.positive → sandwich P x ∈ T.positive
  pairing : E → A →ₗ[ℝ] ℝ
  trace_sandwich : ∀ P x, T.trace (sandwich P x) = pairing x (star P * P)

namespace OperatorTraceData

variable {T} (D : OperatorTraceData (A := A) T)

theorem sandwich_one (x : E) : D.sandwich 1 x = x := by
  apply D.injective
  rw [D.val_sandwich, star_one, one_mul, mul_one]

theorem pairing_one (x : E) : D.pairing x 1 = T.trace x := by
  have h := D.trace_sandwich 1 x
  rwa [D.sandwich_one, star_one, one_mul, eq_comm] at h

theorem trace_sandwich_projection {P : A} (hP : IsStarProjection P) (x : E) :
    T.trace (D.sandwich P x) = D.pairing x P := by
  rw [D.trace_sandwich, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem]

theorem sandwich_projection_idempotent {P : A} (hP : IsStarProjection P) (x : E) :
    D.sandwich P (D.sandwich P x) = D.sandwich P x := by
  apply D.injective
  simp only [D.val_sandwich, hP.isSelfAdjoint.star_eq]
  calc
    P * (P * D.val x * P) * P = (P * P) * D.val x * (P * P) := by noncomm_ring
    _ = P * D.val x * P := by rw [hP.isIdempotentElem]

theorem sandwich_projection_complement {P : A} (hP : IsStarProjection P) (x : E) :
    D.sandwich P (D.sandwich (1 - P) x) = 0 := by
  apply D.injective
  simp only [D.val_sandwich, map_zero, hP.isSelfAdjoint.star_eq, hP.one_sub.isSelfAdjoint.star_eq]
  calc
    P * ((1 - P) * D.val x * (1 - P)) * P =
      (P * (1 - P)) * D.val x * ((1 - P) * P) := by noncomm_ring
    _ = 0 := by rw [hP.mul_one_sub_self, zero_mul, zero_mul]

theorem pairing_projection_complement_zero {P : A} (hP : IsStarProjection P) (x : E) :
    D.pairing (D.sandwich (1 - P) x) P = 0 := by
  rw [← D.trace_sandwich_projection hP, D.sandwich_projection_complement hP, map_zero]

variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem sandwich_quadratic_projection {P : A} (hP : IsStarProjection P) (x : E) (s t : ℝ) :
    D.sandwich (s • P + t • (1 - P)) x = s ^ 2 • D.sandwich P x +
      (s * t) • (x - D.sandwich P x - D.sandwich (1 - P) x) +
      t ^ 2 • D.sandwich (1 - P) x := by
  let Q := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have he : D.val x = P * D.val x * P + P * D.val x * Q + Q * D.val x * P + Q * D.val x * Q := by
    dsimp only [Q]
    noncomm_ring
  apply D.injective
  change D.val (D.sandwich (s • P + t • Q) x) = D.val
    (s ^ 2 • D.sandwich P x + (s * t) • (x - D.sandwich P x - D.sandwich Q x) + t ^ 2 • D.sandwich Q x)
  simp only [map_add, map_sub, map_smul, D.val_sandwich, star_add, star_smul, star_trivial,
    hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
  have hd : D.val x - P * D.val x * P - Q * D.val x * Q = P * D.val x * Q + Q * D.val x * P := by
    conv_lhs => rw [sub_sub]
    exact sub_eq_iff_eq_add.mpr (he.trans (by abel))
  rw [hd]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, pow_two]
  module

def positiveBlocks {P : A} (hP : IsStarProjection P) : PositiveBlockDecomposition T where
  first := D.sandwich P
  second := D.sandwich (1 - P)
  first_positive := D.sandwich_positive P
  second_positive := D.sandwich_positive (1 - P)
  first_idempotent := D.sandwich_projection_idempotent hP
  second_idempotent := D.sandwich_projection_idempotent hP.one_sub
  trace_split x _ := by
    rw [D.trace_sandwich_projection hP, D.trace_sandwich_projection hP.one_sub, ← map_add,
      add_sub_cancel, D.pairing_one]
  quadratic_positive x hx s t := by
    rw [← D.sandwich_quadratic_projection hP]
    exact D.sandwich_positive _ _ hx

theorem calibration_leakage {P A₀ : A} (hP : IsStarProjection P) (F : PositiveBinaryInstrument T) (τ : ℝ)
    (hF : ∀ x, T.trace (F.branch true x) = D.pairing x A₀)
    (hplus : ∀ x ∈ T.positive, 0 ≤ D.pairing x (τ • 1 - (A₀ - P)))
    (hminus : ∀ x ∈ T.positive, 0 ≤ D.pairing x (τ • 1 - (P - A₀)))
    (b : Bool) (x : E) (hx : x ∈ T.positive) :
    T.trace (F.branch b (blockBranch (D.positiveBlocks hP) (!b) x)) ≤
      τ * T.trace (blockBranch (D.positiveBlocks hP) (!b) x) := by
  cases b
  · let y := D.sandwich P x
    change T.trace (F.branch false y) ≤ τ * T.trace y
    have hpos := hminus y (D.sandwich_positive P x hx)
    have hz := D.pairing_projection_complement_zero hP.one_sub x
    rw [sub_sub_cancel] at hz
    change D.pairing y (1 - P) = 0 at hz
    rw [map_sub, D.pairing_one] at hz
    rw [map_sub, map_sub, map_smul, D.pairing_one, smul_eq_mul] at hpos
    have htr := F.normalized y
    rw [map_add, hF] at htr
    linarith
  · let y := D.sandwich (1 - P) x
    change T.trace (F.branch true y) ≤ τ * T.trace y
    rw [hF]
    have hpos := hplus y (D.sandwich_positive (1 - P) x hx)
    have hz := D.pairing_projection_complement_zero hP x
    rw [map_sub, map_sub, map_smul, D.pairing_one, smul_eq_mul] at hpos
    linarith

end OperatorTraceData
end AlbertSequential
