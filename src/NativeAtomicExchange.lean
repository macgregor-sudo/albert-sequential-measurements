/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfRepresentation

/-! Exact atom exchange identities for a=p+q-e. These hold also at zero
overlap; the later positive-overlap Kraus normalization is kept separate. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem quadraticMap_idempotent_exchange (p q : Albert)
    (hp : jordanMul p p = p) (hq : jordanMul q q = q) :
    quadraticMap (p + q - albertUnit) p = quadraticMap q p := by
  simp only [quadraticMap, jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_add_left, jordanMul_add_right, jordanMul_albertUnit_left,
    jordanMul_albertUnit_right, hp, hq, jordanMul_comm q p,
    jordanMul_comm (jordanMul p q) p, two_smul]
  module

theorem quadraticMap_atom_exchange (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    quadraticMap (p + q - albertUnit) p = tracePairing p q • q := by
  rw [quadraticMap_idempotent_exchange p q hp.1 hq.1,
    quadraticMap_atom q p hq, tracePairing_comm q p]

theorem quadraticMap_exchange_on_zero (p b x : Albert)
    (hp : jordanMul p p = p) (hx : jordanMul p x = 0) :
    quadraticMap (p - b) x = quadraticMap b x := by
  have h : jordanMul p (jordanMul b x) = jordanMul (jordanMul p b) x := by
    rw [jordanMul_comm b x, native_peirceZero_commute p x b hp hx, jordanMul_comm x]
  simp only [quadraticMap, jordanMul_sub_left, jordanMul_sub_right, hp, hx,
    zero_sub, jordanMul_neg_right,
    h, jordanMul_comm b p, two_smul]
  module

theorem quadraticMap_atom_exchange_corner (p q : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) :
    quadraticMap (p + q - albertUnit) x = quadraticMap (albertUnit - q) x := by
  have he : p + q - albertUnit = p - (albertUnit - q) := by abel
  rw [he]
  exact quadraticMap_exchange_on_zero p _ x hp.1 x.property

theorem nativePolarizedQuadratic_smul_left (r : ℝ) (p x z : Albert) :
    nativePolarizedQuadratic (r • p) x z = r • nativePolarizedQuadratic p x z := by
  simp only [nativePolarizedQuadratic_apply, jordanMul_smul_left, jordanMul_smul_right]
  module

theorem nativePolarizedQuadratic_exchange (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (x : nativePeirceZero p) (z : Albert) :
    (tracePairing p q) •
      nativePolarizedQuadratic q (quadraticMap (albertUnit - q) x) z =
    quadraticMap (p + q - albertUnit)
      (nativePolarizedQuadratic p x (quadraticMap (p + q - albertUnit) z)) := by
  rw [← nativePolarizedQuadratic_smul_left,
    ← quadraticMap_atom_exchange p q hp hq,
    ← quadraticMap_atom_exchange_corner p q hp x]
  exact congrArg (fun f : Module.End ℝ Albert => f z)
    (nativePolarizedQuadratic_fundamental (p + q - albertUnit) p x)

end AlbertSequential.NativeAnalysis
