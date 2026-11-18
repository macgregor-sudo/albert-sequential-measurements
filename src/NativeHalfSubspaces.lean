/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativePeirceHalfOperators
public import NativeWordPositivity

/-! The actual native zero and half Peirce subspaces and their projection.
No spinor coordinate, orientation or positivity assertion is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def nativePeirceZero (p : Albert) : Submodule ℝ Albert := (nativeMultiplicationOperator p).ker

def nativePeirceHalf (p : Albert) : Submodule ℝ Albert :=
  (nativeMultiplicationOperator p - (1 / 2 : ℝ) • LinearMap.id).ker

@[simp] theorem mem_nativePeirceZero (p x : Albert) :
    x ∈ nativePeirceZero p ↔ jordanMul p x = 0 := Iff.rfl

@[simp] theorem mem_nativePeirceHalf (p h : Albert) :
    h ∈ nativePeirceHalf p ↔ jordanMul p h = (1 / 2 : ℝ) • h := by
  change jordanMul p h - (1 / 2 : ℝ) • h = 0 ↔ _
  exact sub_eq_zero

def nativeHalfProjection (p : Albert) : Module.End ℝ Albert :=
  LinearMap.id - quadraticMapLinear p - quadraticMapLinear (albertUnit - p)

theorem nativeHalfProjection_apply (p x : Albert) :
    nativeHalfProjection p x = x - quadraticMap p x - quadraticMap (albertUnit - p) x := rfl

theorem nativeHalfProjection_eq (p x : Albert) :
    nativeHalfProjection p x = (2 : ℝ) • (jordanMul p x - quadraticMap p x) := by
  rw [nativeHalfProjection_apply, quadraticMap_complement]
  module

theorem native_idempotent_quadratic_mem_one (p x : Albert) (hp : jordanMul p p = p) :
    jordanMul p (quadraticMap p x) = quadraticMap p x := by
  change quadraticMap p x ∈ {y | jordanMul p y = y}
  rw [← quadraticMap_idempotent_range p hp]
  exact ⟨x, rfl⟩

theorem native_complement_quadratic_mem_zero (p x : Albert) (hp : jordanMul p p = p) :
    jordanMul p (quadraticMap (albertUnit - p) x) = 0 := by
  have h := native_idempotent_quadratic_mem_one (albertUnit - p) x (complementary_idempotent p hp)
  rw [jordanMul_sub_left, jordanMul_albertUnit_left] at h
  linear_combination (norm := module) (-1 : ℝ) • h

theorem nativeHalfProjection_mem (p x : Albert) (hp : jordanMul p p = p) :
    nativeHalfProjection p x ∈ nativePeirceHalf p := by
  rw [mem_nativePeirceHalf]
  nth_rw 1 [nativeHalfProjection_apply]
  rw [jordanMul_sub_right, jordanMul_sub_right, native_idempotent_quadratic_mem_one p x hp,
    native_complement_quadratic_mem_zero p x hp, nativeHalfProjection_eq]
  module

theorem native_quadratic_zero_on_half (p h : Albert) (hp : jordanMul p p = p)
    (hh : h ∈ nativePeirceHalf p) : quadraticMap p h = 0 := by
  have hh := (mem_nativePeirceHalf p h).mp hh
  unfold quadraticMap
  rw [hp, hh, jordanMul_smul_right, hh]
  module

theorem native_complement_quadratic_zero_on_half (p h : Albert) (hp : jordanMul p p = p)
    (hh : h ∈ nativePeirceHalf p) : quadraticMap (albertUnit - p) h = 0 := by
  rw [quadraticMap_complement, native_quadratic_zero_on_half p h hp hh,
    (mem_nativePeirceHalf p h).mp hh]
  module

theorem nativeHalfProjection_fixed (p h : Albert) (hp : jordanMul p p = p)
    (hh : h ∈ nativePeirceHalf p) : nativeHalfProjection p h = h := by
  rw [nativeHalfProjection_apply, native_quadratic_zero_on_half p h hp hh,
    native_complement_quadratic_zero_on_half p h hp hh, sub_zero, sub_zero]

theorem nativeHalfProjection_idempotent (p x : Albert) (hp : jordanMul p p = p) :
    nativeHalfProjection p (nativeHalfProjection p x) = nativeHalfProjection p x :=
  nativeHalfProjection_fixed p _ hp (nativeHalfProjection_mem p x hp)

theorem nativeHalfProjection_self_adjoint (p x y : Albert) :
    tracePairing (nativeHalfProjection p x) y = tracePairing x (nativeHalfProjection p y) := by
  rw [nativeHalfProjection_apply, nativeHalfProjection_apply,
    tracePairing_sub_left, tracePairing_sub_left, tracePairing_sub_right,
    tracePairing_sub_right, quadraticMap_self_adjoint, quadraticMap_self_adjoint]

theorem native_quadratic_zero_on_zero (p x : Albert) (hp : jordanMul p p = p)
    (hx : x ∈ nativePeirceZero p) : quadraticMap p x = 0 := by
  have hx := (mem_nativePeirceZero p x).mp hx
  unfold quadraticMap
  rw [hp, hx, jordanMul_zero_right]
  simp

theorem native_complement_quadratic_fixed_zero (p x : Albert) (hp : jordanMul p p = p)
    (hx : x ∈ nativePeirceZero p) : quadraticMap (albertUnit - p) x = x := by
  rw [quadraticMap_complement, (mem_nativePeirceZero p x).mp hx,
    native_quadratic_zero_on_zero p x hp hx]
  simp

end AlbertSequential.NativeAnalysis
