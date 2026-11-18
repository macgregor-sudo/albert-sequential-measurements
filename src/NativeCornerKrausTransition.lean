/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativePositiveOverlapKraus
public import NativeOrthogonalCorner
public import PositiveMeasurePrepare

/-! Actual real no-branch Kraus maps between every pair of atomic zero corners.
The positive-overlap single-Kraus and orthogonal reset cases are both literal. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

theorem nativeOrthogonalRemainder_mem_right (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : nativeOrthogonalRemainder p q ∈ nativePeirceZero q := by
  have he : nativeOrthogonalRemainder p q = nativeOrthogonalRemainder q p := by
    unfold nativeOrthogonalRemainder
    abel
  rw [he]
  exact nativeOrthogonalRemainder_mem q p hq hp (by rwa [tracePairing_comm])

def nativeOrthogonalResetDensity (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  nativeCornerEncoding q hq
    ⟨nativeOrthogonalRemainder p q, nativeOrthogonalRemainder_mem_right p q hp hq ho⟩

theorem nativeOrthogonalResetDensity_positive (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : (nativeOrthogonalResetDensity p q hp hq ho).PosSemidef :=
  nativeCornerEncoding_positive q hq _
    (isPositive_idempotent _ (nativeOrthogonalRemainder_isAtom p q hp hq ho).1)

theorem nativeOrthogonalResetDensity_trace (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : Matrix.trace (nativeOrthogonalResetDensity p q hp hq ho) = 1 := by
  rw [nativeOrthogonalResetDensity, nativeCornerEncoding_trace]
  exact (nativeOrthogonalRemainder_isAtom p q hp hq ho).2

theorem nativeCornerNoEffect_weight (p : Albert) (hp : IsAtom p)
    (q : Albert) (x : nativePeirceZero p) :
    Matrix.trace (nativeCornerNoEffect p hp q * nativeCornerEncoding p hp x) =
      tracePairing (albertUnit - q) x :=
  nativeCornerYesEffect_weight p hp (albertUnit - q) x

theorem nativeCornerNoEffect_orthogonal_weight (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) (x : nativePeirceZero p) :
    Matrix.trace (nativeCornerNoEffect p hp q * nativeCornerEncoding p hp x) =
      tracePairing (nativeOrthogonalRemainder p q) x := by
  rw [nativeCornerNoEffect_weight]
  have hpx : tracePairing p x = 0 := by
    unfold tracePairing
    rw [(mem_nativePeirceZero p x).mp x.property, albertTrace_zero]
  simp only [nativeOrthogonalRemainder, tracePairing_sub_left, hpx]
  ring

def nativeOrthogonalNoKraus (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : List (Matrix SpinorCoordinate SpinorCoordinate ℝ) :=
  positiveMeasurePrepare (nativeOrthogonalResetDensity p q hp hq ho)
    (nativeOrthogonalResetDensity_positive p q hp hq ho)
    (nativeCornerNoEffect p hp q) (nativeCornerNoEffect_positive p hp q hq)

theorem nativeOrthogonalNoKraus_effect (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) :
    rectangularKrausEffect (nativeOrthogonalNoKraus p q hp hq ho) = nativeCornerNoEffect p hp q := by
  rw [nativeOrthogonalNoKraus, positiveMeasurePrepare_effect,
    nativeOrthogonalResetDensity_trace, one_smul]

theorem nativeOrthogonalNoKraus_encoding (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) (x : nativePeirceZero p) :
    rectangularKrausAction (nativeOrthogonalNoKraus p q hp hq ho) (nativeCornerEncoding p hp x) =
      nativeCornerEncoding q hq (nativeCornerNoUpdate p q hq x) := by
  rw [nativeOrthogonalNoKraus, positiveMeasurePrepare_action,
    nativeCornerNoEffect_orthogonal_weight p q hp hq ho x]
  unfold nativeOrthogonalResetDensity
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  exact (nativeOrthogonalNoUpdate p q hp hq ho x).symm

def nativeCornerNoKraus (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    List (Matrix SpinorCoordinate SpinorCoordinate ℝ) :=
  if ho : 0 < tracePairing p q then [nativePositiveOverlapKraus p hp q hq]
  else nativeOrthogonalNoKraus p q hp hq (le_antisymm (not_lt.mp ho)
    (tracePairing_positive_nonnegative p q (isPositive_idempotent p hp.1)
      (isPositive_idempotent q hq.1)))

theorem nativeCornerNoKraus_effect (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    rectangularKrausEffect (nativeCornerNoKraus p hp q hq) = nativeCornerNoEffect p hp q := by
  unfold nativeCornerNoKraus
  split_ifs with ho
  · simp only [rectangularKrausEffect_cons, rectangularKrausEffect_nil, add_zero,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact nativePositiveOverlapKraus_effect p hp q hq ho
  · exact nativeOrthogonalNoKraus_effect p q hp hq _

theorem nativeCornerNoKraus_encoding (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q)
    (x : nativePeirceZero p) :
    rectangularKrausAction (nativeCornerNoKraus p hp q hq) (nativeCornerEncoding p hp x) =
      nativeCornerEncoding q hq (nativeCornerNoUpdate p q hq x) := by
  unfold nativeCornerNoKraus
  split_ifs with ho
  · simp only [rectangularKrausAction_cons, rectangularKrausAction_nil, add_zero,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact nativePositiveOverlapKraus_encoding p hp q hq ho x
  · exact nativeOrthogonalNoKraus_encoding p q hp hq _ x

end AlbertSequential.NativeAnalysis
