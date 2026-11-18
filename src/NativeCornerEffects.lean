/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfExchangeMatrix

/-! Exact positive complementary real effects on an atomic zero-corner block.
Both effects and the trace weight are defined for every pair of atoms. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

def nativeCornerProjection (p : Albert) (hp : IsAtom p) : Albert →ₗ[ℝ] nativePeirceZero p where
  toFun x := ⟨quadraticMap (albertUnit - p) x,
    native_complement_quadratic_mem_zero p x hp.1⟩
  map_add' _ _ := Subtype.ext (quadraticMap_add_right _ _ _)
  map_smul' r _ := Subtype.ext (quadraticMap_smul_right r _ _)

theorem nativeCornerProjection_unit (p : Albert) (hp : IsAtom p) :
    nativeCornerProjection p hp albertUnit = nativeCornerUnit p hp.1 := by
  apply Subtype.ext
  exact (quadraticMap_unit_argument _).trans (complementary_idempotent p hp.1)

theorem nativeCornerProjection_fixed (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    nativeCornerProjection p hp x = x := by
  apply Subtype.ext
  exact native_complement_quadratic_fixed_zero p x hp.1 x.property

def nativeCornerYesEffect (p : Albert) (hp : IsAtom p) (q : Albert) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  nativeHalfMatrix p hp (nativeCornerProjection p hp q)

def nativeCornerNoEffect (p : Albert) (hp : IsAtom p) (q : Albert) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  nativeHalfMatrix p hp (nativeCornerProjection p hp (albertUnit - q))

theorem nativeCornerEffects_sum (p : Albert) (hp : IsAtom p) (q : Albert) :
    nativeCornerYesEffect p hp q + nativeCornerNoEffect p hp q = 1 := by
  unfold nativeCornerYesEffect nativeCornerNoEffect
  rw [← map_add, ← map_add]
  have he : q + (albertUnit - q) = albertUnit := by abel
  rw [he, nativeCornerProjection_unit, nativeHalfMatrix_unit]

theorem nativeCornerYesEffect_positive (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) : (nativeCornerYesEffect p hp q).PosSemidef :=
  nativeHalfMatrix_positive p hp _
    (isPositive_quadraticMap _ q (isPositive_idempotent q hq.1))

theorem nativeCornerNoEffect_positive (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) : (nativeCornerNoEffect p hp q).PosSemidef :=
  nativeHalfMatrix_positive p hp _ (isPositive_quadraticMap _ _
    (isPositive_idempotent _ (complementary_idempotent q hq.1)))

theorem nativeCornerEncoding_apply (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    nativeCornerEncoding p hp x = (1 / 8 : ℝ) • nativeHalfMatrix p hp x := rfl

theorem nativeCornerYesEffect_weight (p : Albert) (hp : IsAtom p)
    (q : Albert) (x : nativePeirceZero p) :
    Matrix.trace (nativeCornerYesEffect p hp q * nativeCornerEncoding p hp x) = tracePairing q x := by
  rw [nativeCornerEncoding_apply, mul_smul_comm, Matrix.trace_smul]
  unfold nativeCornerYesEffect
  rw [nativeHalfMatrix_trace_product]
  change (1 / 8 : ℝ) • (8 * tracePairing (quadraticMap (albertUnit - p) q) x) = _
  rw [quadraticMap_self_adjoint, native_complement_quadratic_fixed_zero p x hp.1 x.property]
  simp

end AlbertSequential.NativeAnalysis
