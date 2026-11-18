/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfCoordinates
public import MeasurePrepareKraus

/-! Literal real matrices in the matched atomic half-space coordinates.
Transpose is the native trace adjoint: the common factor two cancels. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace AlbertSequential.NativeAnalysis

def nativeHalfCoordinateMatrix (q : Albert) (hq : IsAtom q) (p : Albert) (hp : IsAtom p)
    (F : Module.End ℝ Albert) : Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  LinearMap.toMatrix' ((spinorReadout q hq).comp (F.comp (spinorInclusion p hp)))

theorem nativeHalfCoordinateMatrix_mulVec (q : Albert) (hq : IsAtom q)
    (p : Albert) (hp : IsAtom p) (F : Module.End ℝ Albert) (v : SpinorCoordinate → ℝ) :
    nativeHalfCoordinateMatrix q hq p hp F *ᵥ v =
      spinorReadout q hq (F (spinorInclusion p hp v)) :=
  LinearMap.toMatrix'_mulVec _ _

theorem nativeHalfCoordinateMatrix_apply (q : Albert) (hq : IsAtom q)
    (p : Albert) (hp : IsAtom p) (F : Module.End ℝ Albert) (i j : SpinorCoordinate) :
    nativeHalfCoordinateMatrix q hq p hp F i j =
      spinorReadout q hq (F (spinorInclusion p hp (Pi.single j 1))) i := rfl

theorem spinorInclusion_pairing_general (p : Albert) (hp : IsAtom p)
    (v : SpinorCoordinate → ℝ) (x : Albert) :
    tracePairing (spinorInclusion p hp v) x =
      2 * (v ⬝ᵥ spinorReadout p hp x) := by
  calc
    _ = tracePairing (nativeHalfProjection p (spinorInclusion p hp v)) x := by
      rw [nativeHalfProjection_fixed p _ hp.1 (spinorInclusion_mem p hp v)]
    _ = tracePairing (spinorInclusion p hp v) (nativeHalfProjection p x) :=
      nativeHalfProjection_self_adjoint p _ x
    _ = tracePairing (spinorInclusion p hp v)
        (spinorInclusion p hp (spinorReadout p hp x)) := by rw [spinorInclusion_readout]
    _ = _ := spinorInclusion_pairing p hp v _

theorem nativeHalfCoordinateMatrix_transpose (q : Albert) (hq : IsAtom q)
    (p : Albert) (hp : IsAtom p) (F G : Module.End ℝ Albert)
    (hFG : ∀ x y, tracePairing (F x) y = tracePairing x (G y)) :
    (nativeHalfCoordinateMatrix q hq p hp F).transpose =
      nativeHalfCoordinateMatrix p hp q hq G := by
  ext i j
  change nativeHalfCoordinateMatrix q hq p hp F j i = _
  have he : 2 * nativeHalfCoordinateMatrix q hq p hp F j i =
      2 * nativeHalfCoordinateMatrix p hp q hq G i j := by
    rw [nativeHalfCoordinateMatrix_apply, nativeHalfCoordinateMatrix_apply]
    have h := hFG (spinorInclusion p hp (Pi.single i 1))
      (spinorInclusion q hq (Pi.single j 1))
    rw [tracePairing_comm (F _), spinorInclusion_pairing_general,
      spinorInclusion_pairing_general] at h
    simpa only [single_one_dotProduct] using h
  linarith

def nativeHalfMatrix (p : Albert) (hp : IsAtom p) :
    nativePeirceZero p →ₗ[ℝ] Matrix SpinorCoordinate SpinorCoordinate ℝ where
  toFun x := nativeHalfCoordinateMatrix p hp p hp ((2 : ℝ) • nativeMultiplicationOperator x)
  map_add' x y := by
    ext i j
    simp only [Matrix.add_apply, nativeHalfCoordinateMatrix_apply, LinearMap.smul_apply,
      nativeMultiplicationOperator, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_add, jordanMul_add_left, smul_add, map_add, Pi.add_apply]
  map_smul' r x := by
    ext i j
    simp only [Matrix.smul_apply, nativeHalfCoordinateMatrix_apply, LinearMap.smul_apply,
      nativeMultiplicationOperator, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_smul, jordanMul_smul_left, map_smul,
      RingHom.id_apply, Pi.smul_apply]
    module

theorem nativeHalfMatrix_mulVec (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (v : SpinorCoordinate → ℝ) :
    nativeHalfMatrix p hp x *ᵥ v =
      spinorReadout p hp ((2 : ℝ) • jordanMul x (spinorInclusion p hp v)) :=
  nativeHalfCoordinateMatrix_mulVec p hp p hp _ v

theorem nativeHalfMatrix_inclusion (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (v : SpinorCoordinate → ℝ) :
    spinorInclusion p hp (nativeHalfMatrix p hp x *ᵥ v) =
      (2 : ℝ) • jordanMul x (spinorInclusion p hp v) := by
  rw [nativeHalfMatrix_mulVec, spinorInclusion_readout]
  apply nativeHalfProjection_fixed p _ hp.1
  exact (nativePeirceHalf p).smul_mem 2 (by
    rw [mem_nativePeirceHalf]
    exact native_peirceHalf_product p x _ hp.1 x.property
      ((mem_nativePeirceHalf p _).mp (spinorInclusion_mem p hp v)))

theorem nativeHalfMatrix_symmetric (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) : (nativeHalfMatrix p hp x).transpose = nativeHalfMatrix p hp x := by
  apply nativeHalfCoordinateMatrix_transpose
  intro h k
  change tracePairing ((2 : ℝ) • jordanMul x h) k =
    tracePairing h ((2 : ℝ) • jordanMul x k)
  rw [tracePairing_smul_left, tracePairing_smul_right,
    jordanMul_comm (x : Albert) h, tracePairing_associative]

theorem nativeHalfMatrix_positive (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (hx : IsPositive x) : (nativeHalfMatrix p hp x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (nativeHalfMatrix p hp x).conjTranspose = nativeHalfMatrix p hp x
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using nativeHalfMatrix_symmetric p hp x
  · intro v
    have h := (isPositive_iff_dual_squares x).mp hx (spinorInclusion p hp v)
    have he := spinorInclusion_pairing p hp v (nativeHalfMatrix p hp x *ᵥ v)
    rw [nativeHalfMatrix_inclusion, tracePairing_smul_right,
      ← tracePairing_associative, jordanMul_comm (spinorInclusion p hp v) (x : Albert),
      tracePairing_associative] at he
    change 0 ≤ v ⬝ᵥ (nativeHalfMatrix p hp x *ᵥ v)
    change 2 * tracePairing x (jordanMul (spinorInclusion p hp v) (spinorInclusion p hp v)) =
      2 * (v ⬝ᵥ (nativeHalfMatrix p hp x *ᵥ v)) at he
    linarith

end AlbertSequential.NativeAnalysis
