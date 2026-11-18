/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PositiveBilinearNull
public import NativeSquareCone
public import NativeMatrixTrace
public import NativePeirceIdentities

/-!
The literal native support lemma and certainty-state ideality for arbitrary
idempotents, including 0 and e. Positivity of the trace Jordan form replaces
the Peirce limiting proof; the native fundamental formula is not used.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

private def stateJordanForm (x : Albert) : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun y :=
    { toFun z := tracePairing x (jordanMul y z)
      map_add' z w := by rw [jordanMul_add_right, tracePairing_add_right]
      map_smul' r z := by simp only [jordanMul_smul_right, tracePairing_smul_right,
        RingHom.id_apply, smul_eq_mul] }
  map_add' y z := by
    apply LinearMap.ext
    intro w
    change tracePairing x (jordanMul (y + z) w) =
      tracePairing x (jordanMul y w) + tracePairing x (jordanMul z w)
    rw [jordanMul_add_left, tracePairing_add_right]
  map_smul' r y := by
    apply LinearMap.ext
    intro z
    change tracePairing x (jordanMul (r • y) z) = r * tracePairing x (jordanMul y z)
    rw [jordanMul_smul_left, tracePairing_smul_right]

theorem native_positive_zero_pairing_support (c x : Albert)
    (hc : jordanMul c c = c) (hx : IsPositive x) (hzero : tracePairing x c = 0) :
    jordanMul c x = 0 ∧ quadraticMap c x = 0 ∧ quadraticMap (albertUnit - c) x = x := by
  have hBsym : ∀ y z, stateJordanForm x y z = stateJordanForm x z y := by
    intro y z
    change tracePairing x (jordanMul y z) = tracePairing x (jordanMul z y)
    rw [jordanMul_comm y z]
  have hBpos : ∀ y, 0 ≤ stateJordanForm x y y := (isPositive_iff_dual_squares x).mp hx
  have hBc : stateJordanForm x c c = 0 := by
    change tracePairing x (jordanMul c c) = 0
    rw [hc, hzero]
  have hpair : tracePairing (jordanMul x c) (jordanMul x c) = 0 := by
    rw [tracePairing_associative]
    exact positiveBilinear_null_pair (stateJordanForm x) hBsym hBpos c hBc _
  have hcx : jordanMul c x = 0 := by
    rw [jordanMul_comm c x]
    exact (tracePairing_positive_definite _).2.mp hpair
  have hUc : quadraticMap c x = 0 := by
    unfold quadraticMap
    rw [hcx, jordanMul_zero_right, hc, hcx]
    simp only [nsmul_zero, sub_zero]
  refine ⟨hcx, hUc, ?_⟩
  rw [quadraticMap_complement, hcx, hUc, smul_zero, sub_zero, add_zero]

theorem native_idempotent_complement (p : Albert) (hp : jordanMul p p = p) :
    jordanMul (albertUnit - p) (albertUnit - p) = albertUnit - p := by
  simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
    jordanMul_albertUnit_right, hp]
  module

theorem native_idempotent_quadratic_unit (p : Albert) (hp : jordanMul p p = p) :
    quadraticMap p albertUnit = p := by
  unfold quadraticMap
  simp only [jordanMul_albertUnit_right, hp, two_smul]
  module

theorem native_idempotent_certainty_ideality (p ρ : Albert)
    (hp : jordanMul p p = p) (hρ : IsDensity ρ) (hcertainty : tracePairing ρ p = 1) :
    quadraticMap p ρ = ρ := by
  have hzero : tracePairing ρ (albertUnit - p) = 0 := by
    rw [tracePairing_sub_right, tracePairing_unit_right, hρ.2, hcertainty, sub_self]
  have h := (native_positive_zero_pairing_support (albertUnit - p) ρ
    (native_idempotent_complement p hp) hρ.1 hzero).2.2
  have he : albertUnit - (albertUnit - p) = p := by abel
  rwa [he] at h

theorem native_idempotent_instrument_trace (p z : Albert) (hp : jordanMul p p = p) :
    albertTrace (quadraticMap p z + quadraticMap (albertUnit - p) z) = albertTrace z := by
  calc
    albertTrace (quadraticMap p z + quadraticMap (albertUnit - p) z) =
        tracePairing (quadraticMap p z + quadraticMap (albertUnit - p) z) albertUnit :=
      (tracePairing_unit_right _).symm
    _ = tracePairing z (quadraticMap p albertUnit + quadraticMap (albertUnit - p) albertUnit) := by
      rw [tracePairing_add_left, tracePairing_add_right, quadraticMap_self_adjoint,
        quadraticMap_self_adjoint]
    _ = tracePairing z albertUnit := by
      rw [native_idempotent_quadratic_unit p hp,
        native_idempotent_quadratic_unit _ (native_idempotent_complement p hp)]
      congr 1
      abel
    _ = albertTrace z := tracePairing_unit_right z

end AlbertSequential
