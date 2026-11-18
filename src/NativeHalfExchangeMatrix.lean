/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeAtomicExchange
public import NativeHalfTraceEncoding

/-! The exact real sixteen-dimensional intertwining identity. The projected
coordinate transfer is used; U_(p+q-e) need not map the entire half space into
the other half space. This identity includes zero overlap without division. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis

def nativeCornerNoUpdate (p q : Albert) (hq : IsAtom q) :
    nativePeirceZero p →ₗ[ℝ] nativePeirceZero q where
  toFun x := ⟨quadraticMap (albertUnit - q) x,
    native_complement_quadratic_mem_zero q x hq.1⟩
  map_add' _ _ := Subtype.ext (quadraticMap_add_right _ _ _)
  map_smul' r _ := Subtype.ext (quadraticMap_smul_right r _ _)

def nativeHalfExchangeMatrix (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  nativeHalfCoordinateMatrix q hq p hp (quadraticMapLinear (p + q - albertUnit))

theorem nativeHalfExchangeMatrix_transpose (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) :
    (nativeHalfExchangeMatrix p hp q hq).transpose = nativeHalfExchangeMatrix q hq p hp := by
  unfold nativeHalfExchangeMatrix
  rw [add_comm q p]
  exact nativeHalfCoordinateMatrix_transpose q hq p hp _ _
    (quadraticMap_self_adjoint (p + q - albertUnit))

theorem nativeHalfMatrix_readout_factor (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (z : Albert) :
    spinorInclusion p hp (nativeHalfMatrix p hp x *ᵥ spinorReadout p hp z) =
      nativePolarizedQuadratic p x z := by
  rw [nativeHalfMatrix_inclusion, spinorInclusion_readout,
    nativePolarizedQuadratic_half_factor p hp x z]

theorem nativeHalfExchangeMatrix_intertwining (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) (x : nativePeirceZero p) :
    nativeHalfExchangeMatrix p hp q hq * nativeHalfMatrix p hp x *
      (nativeHalfExchangeMatrix p hp q hq).transpose =
    tracePairing p q • nativeHalfMatrix q hq (nativeCornerNoUpdate p q hq x) := by
  apply Matrix.mulVec_injective
  funext v
  rw [nativeHalfExchangeMatrix_transpose]
  simp only [← Matrix.mulVec_mulVec, nativeHalfExchangeMatrix,
    nativeHalfCoordinateMatrix_mulVec, Matrix.smul_mulVec]
  rw [add_comm q p, nativeHalfMatrix_readout_factor]
  simp only [quadraticMapLinear_apply]
  rw [← nativePolarizedQuadratic_exchange p q hp hq x, map_smul]
  change tracePairing p q • spinorReadout q hq
    (nativePolarizedQuadratic q (nativeCornerNoUpdate p q hq x) (spinorInclusion q hq v)) = _
  rw [nativePolarizedQuadratic_half_factor q hq (nativeCornerNoUpdate p q hq x),
    nativeHalfProjection_fixed q _ hq.1 (spinorInclusion_mem q hq v)]
  rw [nativeHalfMatrix_mulVec]

end AlbertSequential.NativeAnalysis
