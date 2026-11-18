/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerEffects
public import NativeSupport

/-! Orthogonal atoms leave an actual third atom. The no update on the first
zero corner is rank-one compression, with no positive-overlap division. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis

def nativeOrthogonalRemainder (p q : Albert) : Albert := albertUnit - p - q

theorem native_orthogonal_atoms_product (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : jordanMul p q = 0 := by
  apply (native_positive_zero_pairing_support p q hp.1
    (isPositive_idempotent q hq.1) _).1
  rwa [tracePairing_comm]

theorem nativeOrthogonalRemainder_isAtom (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : IsAtom (nativeOrthogonalRemainder p q) := by
  have hpq := native_orthogonal_atoms_product p q hp hq ho
  have hqp : jordanMul q p = 0 := (jordanMul_comm q p).trans hpq
  constructor
  · simp only [nativeOrthogonalRemainder, jordanMul_sub_left, jordanMul_sub_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, hp.1, hq.1, hpq, hqp]
    module
  · change albertTrace (albertUnit - p - q) = 1
    rw [albertTrace_sub, albertTrace_sub, hp.2, hq.2]
    have he : albertTrace albertUnit = 3 := by
      simp [albertTrace, albertUnit, Fin.sum_univ_three]
    rw [he]
    norm_num

theorem nativeOrthogonalRemainder_mem (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) : nativeOrthogonalRemainder p q ∈ nativePeirceZero p := by
  rw [mem_nativePeirceZero]
  simp only [nativeOrthogonalRemainder, jordanMul_sub_right,
    jordanMul_albertUnit_right, hp.1, native_orthogonal_atoms_product p q hp hq ho,
    sub_self, sub_zero]

theorem nativeOrthogonalNoUpdate (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) (x : nativePeirceZero p) :
    quadraticMap (albertUnit - q) x =
      tracePairing (nativeOrthogonalRemainder p q) x • nativeOrthogonalRemainder p q := by
  have he : albertUnit - q = p - (-nativeOrthogonalRemainder p q) := by
    unfold nativeOrthogonalRemainder
    abel
  rw [he, quadraticMap_exchange_on_zero p _ x hp.1 x.property]
  have hn (a z : Albert) : quadraticMap (-a) z = quadraticMap a z := by
    have h := quadraticMap_smul_left (-1 : ℝ) a z
    simpa using h
  rw [hn, quadraticMap_atom _ _ (nativeOrthogonalRemainder_isAtom p q hp hq ho)]

theorem nativeCornerNoEffect_orthogonal (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : tracePairing p q = 0) :
    nativeCornerNoEffect p hp q = nativeHalfMatrix p hp
      ⟨nativeOrthogonalRemainder p q, nativeOrthogonalRemainder_mem p q hp hq ho⟩ := by
  unfold nativeCornerNoEffect
  congr 1
  apply Subtype.ext
  change quadraticMap (albertUnit - p) (albertUnit - q) = nativeOrthogonalRemainder p q
  rw [quadraticMap_sub_argument, quadraticMap_unit_argument, complementary_idempotent p hp.1]
  have hqp : q ∈ nativePeirceZero p := native_orthogonal_atoms_product p q hp hq ho
  rw [native_complement_quadratic_fixed_zero p q hp.1 hqp]
  rfl

end AlbertSequential.NativeAnalysis
