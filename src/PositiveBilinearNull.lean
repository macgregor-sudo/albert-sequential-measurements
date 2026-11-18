/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
The null-vector consequence of Cauchy--Schwarz for a real symmetric positive
bilinear form. No algebra product, involution, finite dimension or norm is
needed. The proof is positivity of one real linear polynomial in t.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem positiveBilinear_null_pair
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x) (c : V) (hc : B c c = 0) (y : V) : B c y = 0 := by
  by_contra hne
  let t : ℝ := -(B y y + 1) / (2 * B c y)
  have ht : 2 * t * B c y + B y y = -1 := by
    dsimp only [t]
    field_simp
    ring
  have he : B (t • c + y) (t • c + y) =
      t ^ 2 * B c c + 2 * t * B c y + B y y := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsym y c]
    ring
  have hp := hpos (t • c + y)
  rw [he, hc, mul_zero, zero_add, ht] at hp
  norm_num at hp

end AlbertSequential
