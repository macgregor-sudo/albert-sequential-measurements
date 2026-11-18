/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfSubspaces

/-! The genuine Jordan representation of the zero corner on the half space.
The representation is 2L_x, on C_p only; it is not a representation of Albert.
No coordinates, trace constants or positive encoding are assumed here. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def nativeCornerProduct (p : Albert) (hp : jordanMul p p = p) :
    nativePeirceZero p →ₗ[ℝ] nativePeirceZero p →ₗ[ℝ] nativePeirceZero p where
  toFun x :=
    { toFun y := ⟨jordanMul x y, by
        rw [mem_nativePeirceZero, native_peirceZero_commute p x y hp x.property,
          (mem_nativePeirceZero p y).mp y.property, jordanMul_zero_right]⟩
      map_add' y z := Subtype.ext (jordanMul_add_right x y z)
      map_smul' r y := Subtype.ext (jordanMul_smul_right r x y) }
  map_add' x y := by
    ext z
    exact jordanMul_add_left x y z
  map_smul' r x := by
    ext y
    exact jordanMul_smul_left r x y

def nativeCornerUnit (p : Albert) (hp : jordanMul p p = p) : nativePeirceZero p :=
  ⟨albertUnit - p, by
    rw [mem_nativePeirceZero, jordanMul_sub_right, jordanMul_albertUnit_right, hp, sub_self]⟩

def nativeHalfRepresentation (p : Albert) (hp : jordanMul p p = p) :
    nativePeirceZero p →ₗ[ℝ] Module.End ℝ (nativePeirceHalf p) where
  toFun x :=
    { toFun h := ⟨(2 : ℝ) • jordanMul x h, (nativePeirceHalf p).smul_mem 2 (by
        rw [mem_nativePeirceHalf]
        exact native_peirceHalf_product p x h hp x.property
          ((mem_nativePeirceHalf p h).mp h.property))⟩
      map_add' h k := by
        apply Subtype.ext
        change (2 : ℝ) • jordanMul x ((h : Albert) + k) = _
        rw [jordanMul_add_right, smul_add]
        rfl
      map_smul' r h := by
        apply Subtype.ext
        change (2 : ℝ) • jordanMul x (r • (h : Albert)) = r • ((2 : ℝ) • jordanMul x h)
        rw [jordanMul_smul_right]
        module }
  map_add' x y := by
    ext h
    change (2 : ℝ) • jordanMul ((x : Albert) + y) h =
      (2 : ℝ) • jordanMul x h + (2 : ℝ) • jordanMul y h
    rw [jordanMul_add_left, smul_add]
  map_smul' r x := by
    ext h
    change (2 : ℝ) • jordanMul (r • (x : Albert)) h = r • ((2 : ℝ) • jordanMul x h)
    rw [jordanMul_smul_left]
    module

theorem nativeHalfRepresentation_apply (p : Albert) (hp : jordanMul p p = p)
    (x : nativePeirceZero p) (h : nativePeirceHalf p) :
    (nativeHalfRepresentation p hp x h : Albert) = (2 : ℝ) • jordanMul x h := rfl

theorem nativeHalfRepresentation_unit (p : Albert) (hp : jordanMul p p = p) :
    nativeHalfRepresentation p hp (nativeCornerUnit p hp) = 1 := by
  ext h
  change (2 : ℝ) • jordanMul (albertUnit - p) h = (h : Albert)
  rw [jordanMul_sub_left, jordanMul_albertUnit_left,
    (mem_nativePeirceHalf p h).mp h.property]
  module

theorem nativeHalfRepresentation_jordan (p : Albert) (hp : jordanMul p p = p)
    (x y : nativePeirceZero p) :
    nativeHalfRepresentation p hp (nativeCornerProduct p hp x y) =
      (1 / 2 : ℝ) • (nativeHalfRepresentation p hp x * nativeHalfRepresentation p hp y +
        nativeHalfRepresentation p hp y * nativeHalfRepresentation p hp x) := by
  ext h
  change (2 : ℝ) • jordanMul (jordanMul x y) h =
    (1 / 2 : ℝ) • ((2 : ℝ) • jordanMul x ((2 : ℝ) • jordanMul y h) +
      (2 : ℝ) • jordanMul y ((2 : ℝ) • jordanMul x h))
  rw [native_peirceHalf_jordan_action p x y h hp x.property y.property
    ((mem_nativePeirceHalf p h).mp h.property), jordanMul_smul_right, jordanMul_smul_right]
  module

theorem nativeHalfRepresentation_self_adjoint (p : Albert) (hp : jordanMul p p = p)
    (x : nativePeirceZero p) (h k : nativePeirceHalf p) :
    tracePairing (nativeHalfRepresentation p hp x h) k =
      tracePairing h (nativeHalfRepresentation p hp x k) := by
  rw [nativeHalfRepresentation_apply, nativeHalfRepresentation_apply,
    tracePairing_smul_left, tracePairing_smul_right,
    jordanMul_comm (x : Albert) h, tracePairing_associative]

theorem nativePolarizedQuadratic_half_factor (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (z : Albert) :
    nativePolarizedQuadratic p x z = (2 : ℝ) • jordanMul x (nativeHalfProjection p z) := by
  have hx : jordanMul p x = 0 := x.property
  have hxp : jordanMul (x : Albert) p = 0 := (jordanMul_comm _ _).trans hx
  have hzero : jordanMul (x : Albert) (quadraticMap p z) = 0 := by
    rw [quadraticMap_atom p z hp, jordanMul_smul_right, hxp, smul_zero]
  rw [nativePolarizedQuadratic_apply, hx, jordanMul_zero_left,
    native_peirceZero_commute p x z hp.1 hx, nativeHalfProjection_eq,
    jordanMul_smul_right, jordanMul_sub_right, hzero]
  module

end AlbertSequential.NativeAnalysis
