module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NoncommRing

/-! A direct three-generator volume calculation with a local unit.
No ambient unit is assumed. -/

@[expose] public section
noncomputable section

namespace AlbertSequential

theorem localUnit_volume_eq_half_reverse
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (E x y z : A) (u v w : ℝ)
    (hEx : E * x = x) (hyE : y * E = y) (hEz : E * z = z)
    (hxy : x * y + y * x = (2 * u) • E)
    (hxz : x * z + z * x = (2 * v) • E)
    (hyz : y * z + z * y = (2 * w) • E) :
    x * y * z - w • x + v • y - u • z =
      (1 / 2 : ℝ) • (x * y * z - z * y * x) := by
  have hyx : y * x = (2 * u) • E - x * y := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hxy
  have hzx : z * x = (2 * v) • E - x * z := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hxz
  have hzy : z * y = (2 * w) • E - y * z := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hyz
  have hreverse : z * y * x =
      (2 * w) • x - (2 * v) • y + (2 * u) • z - x * y * z := by
    calc
      z * y * x = (2 * w) • x - y * (z * x) := by
        rw [hzy]
        simp only [sub_mul, smul_mul_assoc, hEx, mul_assoc]
      _ = (2 * w) • x - (2 * v) • y + (2 * u) • z - x * y * z := by
        rw [hzx]
        simp only [mul_sub, mul_smul_comm, hyE, ← mul_assoc, hyx,
          sub_mul, smul_mul_assoc, hEz]
        module
  rw [hreverse]
  module

theorem localUnit_volume_square
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (E x y z : A) (a b c u v w : ℝ)
    (hxE : x * E = x)
    (hEy : E * y = y) (hyE : y * E = y)
    (hEz : E * z = z)
    (hxx : x * x = a • E) (hyy : y * y = b • E)
    (hzz : z * z = c • E)
    (hxy : x * y + y * x = (2 * u) • E)
    (hxz : x * z + z * x = (2 * v) • E)
    (hyz : y * z + z * y = (2 * w) • E) :
    let Γ := x * y * z - w • x + v • y - u • z
    Γ * Γ = (-(a * b * c + 2 * u * w * v -
      a * w ^ 2 - b * v ^ 2 - c * u ^ 2)) • E := by
  have hyx : y * x = (2 * u) • E - x * y := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hxy
  have hzx : z * x = (2 * v) • E - x * z := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hxz
  have hzy : z * y = (2 * w) • E - y * z := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hyz
  have hxyzx : x * y * z * x =
      (2 * v) • (x * y) - (2 * u) • (x * z) + a • (y * z) := by
    calc
      x * y * z * x = x * (y * (z * x)) := by simp only [mul_assoc]
      _ = x * (y * ((2 * v) • E - x * z)) := by rw [hzx]
      _ = (2 * v) • (x * y) - (2 * u) • (x * z) + a • (y * z) := by
        simp only [mul_sub, mul_smul_comm, hyE, ← mul_assoc, hyx,
          sub_mul, smul_mul_assoc, hEz, hEy, hxx, mul_sub]
        module
  have hxyzy : x * y * z * y = (2 * w) • (x * y) - b • (x * z) := by
    calc
      x * y * z * y = x * (y * (z * y)) := by simp only [mul_assoc]
      _ = x * (y * ((2 * w) • E - y * z)) := by rw [hzy]
      _ = (2 * w) • (x * y) - b • (x * z) := by
        simp only [mul_sub, mul_smul_comm, hyE, ← mul_assoc, hyy,
          smul_mul_assoc, hEz]
  have hxyzz : x * y * z * z = c • (x * y) := by
    rw [mul_assoc (x * y), hzz, mul_smul_comm, mul_assoc, hyE]
  let Γ := x * y * z - w • x + v • y - u • z
  have hΓx : Γ * x = a • (y * z) - u • (x * z) + v • (x * y) - (a * w) • E := by
    dsimp [Γ]
    simp only [sub_mul, add_mul, smul_mul_assoc, hxyzx, hxx, hyx, hzx,
      smul_sub, smul_smul]
    module
  have hΓy : Γ * y = u • (y * z) - b • (x * z) + w • (x * y) +
      (b * v - 2 * u * w) • E := by
    dsimp [Γ]
    simp only [sub_mul, add_mul, smul_mul_assoc, hxyzy, hyy, hzy,
      smul_sub, smul_smul]
    module
  have hΓz : Γ * z = v • (y * z) - w • (x * z) + c • (x * y) - (c * u) • E := by
    dsimp [Γ]
    simp only [sub_mul, add_mul, smul_mul_assoc, hxyzz, hzz, smul_smul]
    module
  have hyzyz : (y * z) * (y * z) = (2 * w) • (y * z) - (b * c) • E := by
    calc
      (y * z) * (y * z) = y * (z * y) * z := by simp only [mul_assoc]
      _ = y * ((2 * w) • E - y * z) * z := by rw [hzy]
      _ = (2 * w) • (y * z) - (b * c) • E := by
        simp only [mul_sub, mul_smul_comm, hyE, sub_mul, smul_mul_assoc,
          ← mul_assoc, hyy, hEz, hzz, smul_smul]
  have hxzyz : (x * z) * (y * z) = (2 * w) • (x * z) - c • (x * y) := by
    calc
      (x * z) * (y * z) = x * (z * y) * z := by simp only [mul_assoc]
      _ = x * ((2 * w) • E - y * z) * z := by rw [hzy]
      _ = (2 * w) • (x * z) - c • (x * y) := by
        simp only [mul_sub, mul_smul_comm, hxE, sub_mul, smul_mul_assoc,
          mul_assoc, hzz, mul_smul_comm, hyE]
  have hxyyz : (x * y) * (y * z) = b • (x * z) := by
    simp only [mul_assoc, ← mul_assoc y y, hyy, smul_mul_assoc,
      hEz, mul_smul_comm]
  have hEyz : E * (y * z) = y * z := by rw [← mul_assoc, hEy]
  have hΓxyz : (Γ * x) * (y * z) =
      (a * w) • (y * z) + (b * v - 2 * u * w) • (x * z) +
      (c * u) • (x * y) - (a * b * c) • E := by
    rw [hΓx]
    simp only [sub_mul, add_mul, smul_mul_assoc, hyzyz, hxzyz, hxyyz,
      hEyz, smul_sub, smul_smul]
    module
  change Γ * Γ = _
  calc
    Γ * Γ = (Γ * x) * (y * z) - w • (Γ * x) + v • (Γ * y) - u • (Γ * z) := by
      dsimp only [Γ] at ⊢
      simp only [mul_sub, mul_add, mul_smul_comm, mul_assoc]
    _ = (-(a * b * c + 2 * u * w * v -
        a * w ^ 2 - b * v ^ 2 - c * u ^ 2)) • E := by
      rw [hΓxyz, hΓx, hΓy, hΓz]
      module

end AlbertSequential
