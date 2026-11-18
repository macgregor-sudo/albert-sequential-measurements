/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeFirstHalfTrace

/-! Exact trace normalization and positive native corner encoding into real
16 by 16 matrices. No affine encoding of the full Albert state space is asserted. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

theorem nativeHalfMatrix_eq_first (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) :
    nativeHalfMatrix p hp x = firstHalfMatrix ((chosenAtomNormalizer p hp).linearEquiv x) := by
  ext i j
  change octonionPairCoordinates (firstHalfReadout
    ((chosenAtomNormalizer p hp).linearEquiv ((2 : ℝ) • jordanMul x
      ((chosenAtomNormalizer p hp).linearEquiv.symm
        (firstHalfInclusion (octonionPairCoordinates.symm (Pi.single j 1))))))) i =
    octonionPairCoordinates (firstHalfReadout ((2 : ℝ) •
      jordanMul ((chosenAtomNormalizer p hp).linearEquiv x)
        (firstHalfInclusion (octonionPairCoordinates.symm (Pi.single j 1))))) i
  rw [map_smul, (chosenAtomNormalizer p hp).preserves_product,
    LinearEquiv.apply_symm_apply]

theorem native_normalized_corner_first_zero (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) : ((chosenAtomNormalizer p hp).linearEquiv x).1 0 = 0 := by
  have h : jordanMul (diagAtom 0) ((chosenAtomNormalizer p hp).linearEquiv x) = 0 := by
    rw [← atomNormalizer_first p hp, ← (chosenAtomNormalizer p hp).preserves_product]
    rw [(mem_nativePeirceZero p x).mp x.property, map_zero]
  have h := congrArg (fun z : Albert => z.1 0) h
  rw [first_atom_mul] at h
  exact h

theorem nativeHalfMatrix_trace (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    Matrix.trace (nativeHalfMatrix p hp x) = 8 * albertTrace x := by
  rw [nativeHalfMatrix_eq_first, firstHalfMatrix_trace,
    native_normalized_corner_first_zero]
  have ht := (chosenAtomNormalizer p hp).preserves_trace x
  change ∑ i : Fin 3, ((chosenAtomNormalizer p hp).linearEquiv x).1 i = albertTrace x at ht
  rw [Fin.sum_univ_three, native_normalized_corner_first_zero] at ht
  linarith

theorem nativeHalfMatrix_trace_product (p : Albert) (hp : IsAtom p)
    (x y : nativePeirceZero p) :
    Matrix.trace (nativeHalfMatrix p hp x * nativeHalfMatrix p hp y) = 8 * tracePairing x y := by
  have h := congrArg Matrix.trace (nativeHalfMatrix_jordan p hp x y)
  rw [nativeHalfMatrix_trace, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_mul_comm (nativeHalfMatrix p hp y)] at h
  change 8 * tracePairing x y = (1 / 2 : ℝ) •
    (Matrix.trace (nativeHalfMatrix p hp x * nativeHalfMatrix p hp y) +
      Matrix.trace (nativeHalfMatrix p hp x * nativeHalfMatrix p hp y)) at h
  simp only [smul_eq_mul] at h
  linarith

def nativeCornerEncoding (p : Albert) (hp : IsAtom p) :
    nativePeirceZero p →ₗ[ℝ] Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  (1 / 8 : ℝ) • nativeHalfMatrix p hp

theorem nativeCornerEncoding_trace (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    Matrix.trace (nativeCornerEncoding p hp x) = albertTrace x := by
  change Matrix.trace ((1 / 8 : ℝ) • nativeHalfMatrix p hp x) = _
  rw [Matrix.trace_smul, nativeHalfMatrix_trace]
  simp [smul_eq_mul]

theorem nativeCornerEncoding_positive (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (hx : IsPositive x) : (nativeCornerEncoding p hp x).PosSemidef :=
  (nativeHalfMatrix_positive p hp x hx).smul (by norm_num : (0 : ℝ) ≤ 1 / 8)

end AlbertSequential.NativeAnalysis
