/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfMatrices

/-! The actual real matrix representation preserves the corner unit and Jordan
product. Its multiplicativity is asserted only in the Jordan sense. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis

theorem spinorInclusion_injective (p : Albert) (hp : IsAtom p) :
    Function.Injective (spinorInclusion p hp) := by
  intro v w h
  have h := congrArg (spinorReadout p hp) h
  simpa only [spinorReadout_inclusion] using h

theorem nativeHalfMatrix_unit (p : Albert) (hp : IsAtom p) :
    nativeHalfMatrix p hp (nativeCornerUnit p hp.1) = 1 := by
  apply Matrix.mulVec_injective
  funext v
  apply spinorInclusion_injective p hp
  rw [nativeHalfMatrix_inclusion, Matrix.one_mulVec]
  change (2 : ℝ) • jordanMul (albertUnit - p) (spinorInclusion p hp v) = _
  rw [jordanMul_sub_left, jordanMul_albertUnit_left,
    (mem_nativePeirceHalf p _).mp (spinorInclusion_mem p hp v)]
  module

theorem nativeHalfMatrix_jordan (p : Albert) (hp : IsAtom p)
    (x y : nativePeirceZero p) :
    nativeHalfMatrix p hp (nativeCornerProduct p hp.1 x y) =
      (1 / 2 : ℝ) • (nativeHalfMatrix p hp x * nativeHalfMatrix p hp y +
        nativeHalfMatrix p hp y * nativeHalfMatrix p hp x) := by
  apply Matrix.mulVec_injective
  funext v
  apply spinorInclusion_injective p hp
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    map_smul, map_add, nativeHalfMatrix_inclusion]
  change (2 : ℝ) • jordanMul (jordanMul x y) (spinorInclusion p hp v) = _
  rw [native_peirceHalf_jordan_action p x y _ hp.1 x.property y.property
    ((mem_nativePeirceHalf p _).mp (spinorInclusion_mem p hp v)),
    jordanMul_smul_right, jordanMul_smul_right]
  module

theorem nativeHalfMatrix_square (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) :
    nativeHalfMatrix p hp (nativeCornerProduct p hp.1 x x) =
      nativeHalfMatrix p hp x * nativeHalfMatrix p hp x := by
  rw [nativeHalfMatrix_jordan]
  module

end AlbertSequential.NativeAnalysis
