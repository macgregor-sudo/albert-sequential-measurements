/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfRepresentation
public import OctonionRealCoordinates

/-! Actual real sixteen-dimensional coordinates on every atomic half space.
Their metric is twice the ordinary coordinate dot product, uniformly in p. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def firstHalfInclusion : (Octonion × Octonion) →ₗ[ℝ] Albert where
  toFun x := (0, ![x.1, x.2, 0])
  map_add' x y := by
    apply Prod.ext
    · change (0 : Fin 3 → ℝ) = 0 + 0
      simp
    · funext i
      change ![x.1 + y.1, x.2 + y.2, 0] i = ![x.1, x.2, 0] i + ![y.1, y.2, 0] i
      fin_cases i <;> simp
  map_smul' r x := by
    apply Prod.ext
    · change (0 : Fin 3 → ℝ) = r • 0
      simp
    · funext i
      change ![r • x.1, r • x.2, 0] i = r • ![x.1, x.2, 0] i
      fin_cases i <;> simp

def firstHalfReadout : Albert →ₗ[ℝ] (Octonion × Octonion) where
  toFun x := (x.2 0, x.2 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstHalfReadout_inclusion (x : Octonion × Octonion) :
    firstHalfReadout (firstHalfInclusion x) = x := rfl

theorem first_atom_mul (x : Albert) :
    jordanMul (diagAtom 0) x =
      (![x.1 0, 0, 0], ![(1/2 : ℝ) • x.2 0, (1/2 : ℝ) • x.2 1, 0]) := by
  have he : diagAtom 0 = diagonalElement ![1,0,0] := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [diagAtom, diagonalElement]
    · rfl
  rw [he, jordanMul_diagonal]
  apply Prod.ext
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

theorem firstHalfInclusion_readout (x : Albert) :
    firstHalfInclusion (firstHalfReadout x) = nativeHalfProjection (diagAtom 0) x := by
  rw [nativeHalfProjection_eq, first_atom_mul, quadraticMap_diagAtom]
  apply Prod.ext
  · funext i
    change (0 : ℝ) = 2 * (![x.1 0,0,0] i - x.1 0 * (if i = 0 then 1 else 0))
    fin_cases i <;> simp
  · funext i
    change ![x.2 0,x.2 1,0] i = (2 : ℝ) •
      (![ (1/2 : ℝ) • x.2 0, (1/2 : ℝ) • x.2 1, 0] i - x.1 0 • (0 : Octonion))
    fin_cases i <;> simp [smul_smul]

theorem firstHalfInclusion_pairing (x y : Octonion × Octonion) :
    tracePairing (firstHalfInclusion x) (firstHalfInclusion y) =
      2 * (octDot x.1 y.1 + octDot x.2 y.2) := by
  rw [tracePairing_eq_coords]
  change (0 * 0 + 0 * 0 + 0 * 0) +
    2 * (octDot x.1 y.1 + octDot x.2 y.2 + octDot 0 0) = _
  simp [octDot_zero_left]

def spinorInclusion (p : Albert) (hp : IsAtom p) : (SpinorCoordinate → ℝ) →ₗ[ℝ] Albert :=
  (chosenAtomNormalizer p hp).linearEquiv.symm.toLinearMap.comp
    (firstHalfInclusion.comp octonionPairCoordinates.symm.toLinearMap)

def spinorReadout (p : Albert) (hp : IsAtom p) : Albert →ₗ[ℝ] (SpinorCoordinate → ℝ) :=
  octonionPairCoordinates.toLinearMap.comp
    (firstHalfReadout.comp (chosenAtomNormalizer p hp).linearEquiv.toLinearMap)

theorem atomNormalizer_first (p : Albert) (hp : IsAtom p) :
    (chosenAtomNormalizer p hp).linearEquiv p = diagAtom 0 :=
  Classical.choose_spec (nativeAtomNormalizer_first p hp)

theorem spinorReadout_inclusion (p : Albert) (hp : IsAtom p) (v : SpinorCoordinate → ℝ) :
    spinorReadout p hp (spinorInclusion p hp v) = v := by
  simp only [spinorReadout, spinorInclusion, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, firstHalfReadout_inclusion,
    LinearEquiv.apply_symm_apply]

theorem nativeHalfProjection_covariant (g : NativeAlbertAutomorphism) (p x : Albert) :
    g.linearEquiv (nativeHalfProjection p x) =
      nativeHalfProjection (g.linearEquiv p) (g.linearEquiv x) := by
  rw [nativeHalfProjection_apply, nativeHalfProjection_apply, map_sub, map_sub,
    nativeAutomorphism_quadraticMap, nativeAutomorphism_quadraticMap, map_sub,
    g.preserves_unit]

theorem spinorInclusion_readout (p : Albert) (hp : IsAtom p) (x : Albert) :
    spinorInclusion p hp (spinorReadout p hp x) = nativeHalfProjection p x := by
  apply (chosenAtomNormalizer p hp).linearEquiv.injective
  simp only [spinorInclusion, spinorReadout, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rw [firstHalfInclusion_readout, nativeHalfProjection_covariant, atomNormalizer_first]

theorem spinorInclusion_mem (p : Albert) (hp : IsAtom p) (v : SpinorCoordinate → ℝ) :
    spinorInclusion p hp v ∈ nativePeirceHalf p := by
  rw [← spinorReadout_inclusion p hp v]
  rw [spinorInclusion_readout]
  exact nativeHalfProjection_mem p _ hp.1

theorem spinorInclusion_pairing (p : Albert) (hp : IsAtom p)
    (v w : SpinorCoordinate → ℝ) :
    tracePairing (spinorInclusion p hp v) (spinorInclusion p hp w) =
      2 * ∑ i, v i * w i := by
  rw [← nativeAutomorphism_pairing (chosenAtomNormalizer p hp)]
  simp only [spinorInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [firstHalfInclusion_pairing, octonionPairCoordinates_pairing]
  simp only [LinearEquiv.apply_symm_apply]

end AlbertSequential.NativeAnalysis
