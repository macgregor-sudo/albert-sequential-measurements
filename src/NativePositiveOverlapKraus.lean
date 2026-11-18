/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerEffects

/-! A literal real Kraus matrix when the atomic overlap is positive.
The zero-overlap case has no division and is constructed separately. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis

def nativePositiveOverlapKraus (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  (Real.sqrt (tracePairing p q))⁻¹ • nativeHalfExchangeMatrix p hp q hq

theorem sqrt_reciprocal_normalization (o : ℝ) (ho : 0 < o) :
    (Real.sqrt o)⁻¹ * (Real.sqrt o)⁻¹ * o = 1 := by
  have hs : Real.sqrt o ≠ 0 := (Real.sqrt_pos.mpr ho).ne'
  field_simp
  exact (Real.sq_sqrt ho.le).symm

theorem nativePositiveOverlapKraus_transpose (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) :
    (nativePositiveOverlapKraus p hp q hq).transpose = nativePositiveOverlapKraus q hq p hp := by
  simp only [nativePositiveOverlapKraus, Matrix.transpose_smul,
    nativeHalfExchangeMatrix_transpose, tracePairing_comm p q]

theorem nativePositiveOverlapKraus_intertwining (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) (ho : 0 < tracePairing p q) (x : nativePeirceZero p) :
    nativePositiveOverlapKraus p hp q hq * nativeHalfMatrix p hp x *
      (nativePositiveOverlapKraus p hp q hq).transpose =
    nativeHalfMatrix q hq (nativeCornerNoUpdate p q hq x) := by
  simp only [nativePositiveOverlapKraus, Matrix.transpose_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, nativeHalfExchangeMatrix_intertwining]
  have hs := sqrt_reciprocal_normalization (tracePairing p q) ho
  rw [← mul_assoc, hs, one_smul]

theorem nativePositiveOverlapKraus_encoding (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) (ho : 0 < tracePairing p q) (x : nativePeirceZero p) :
    nativePositiveOverlapKraus p hp q hq * nativeCornerEncoding p hp x *
      (nativePositiveOverlapKraus p hp q hq).transpose =
    nativeCornerEncoding q hq (nativeCornerNoUpdate p q hq x) := by
  simp only [nativeCornerEncoding_apply, mul_smul_comm, smul_mul_assoc,
    nativePositiveOverlapKraus_intertwining p hp q hq ho x]

theorem nativePositiveOverlapKraus_effect (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    (nativePositiveOverlapKraus p hp q hq).transpose * nativePositiveOverlapKraus p hp q hq =
      nativeCornerNoEffect p hp q := by
  have ho' : 0 < tracePairing q p := by rwa [tracePairing_comm]
  have h := nativePositiveOverlapKraus_intertwining q hq p hp ho' (nativeCornerUnit q hq.1)
  rw [nativeHalfMatrix_unit, Matrix.mul_one,
    ← nativePositiveOverlapKraus_transpose p hp q hq, Matrix.transpose_transpose] at h
  exact h

end AlbertSequential.NativeAnalysis
