/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerYesKraus

/-! Finite real Kraus branches from a scalar tag representing one fixed
native density. This covers the initial ray and all atomic reset rays. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

def nativeScalarYesState (q z : Albert) : Matrix Unit Unit ℝ :=
  tracePairing q z • (1 : Matrix Unit Unit ℝ)

theorem nativeScalarYesState_positive (q z : Albert) (hq : IsAtom q) (hz : IsPositive z) :
    (nativeScalarYesState q z).PosSemidef :=
  Matrix.PosSemidef.one.smul
    (tracePairing_positive_nonnegative q z (isPositive_idempotent q hq.1) hz)

def nativeScalarNoState (q : Albert) (hq : IsAtom q) (z : Albert) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  nativeCornerEncoding q hq (nativeCornerProjection q hq z)

theorem nativeScalarNoState_positive (q : Albert) (hq : IsAtom q) (z : Albert)
    (hz : IsPositive z) : (nativeScalarNoState q hq z).PosSemidef :=
  nativeCornerEncoding_positive q hq _ (isPositive_quadraticMap _ z hz)

def nativeScalarYesKraus (q : Albert) (hq : IsAtom q) (z : Albert) (hz : IsPositive z) :
    List (Matrix Unit Unit ℝ) :=
  positiveMeasurePrepare (nativeScalarYesState q z) (nativeScalarYesState_positive q z hq hz)
    (1 : Matrix Unit Unit ℝ) Matrix.PosSemidef.one

def nativeScalarNoKraus (q : Albert) (hq : IsAtom q) (z : Albert) (hz : IsPositive z) :
    List (Matrix SpinorCoordinate Unit ℝ) :=
  positiveMeasurePrepare (nativeScalarNoState q hq z) (nativeScalarNoState_positive q hq z hz)
    (1 : Matrix Unit Unit ℝ) Matrix.PosSemidef.one

theorem nativeScalarYesKraus_action (q : Albert) (hq : IsAtom q) (z : Albert)
    (hz : IsPositive z) (r : ℝ) :
    rectangularKrausAction (nativeScalarYesKraus q hq z hz) (r • (1 : Matrix Unit Unit ℝ)) =
      (r * tracePairing q z) • (1 : Matrix Unit Unit ℝ) := by
  rw [nativeScalarYesKraus, positiveMeasurePrepare_action]
  simp [nativeScalarYesState, smul_smul]

theorem nativeScalarNoKraus_action (q : Albert) (hq : IsAtom q) (z : Albert)
    (hz : IsPositive z) (r : ℝ) :
    rectangularKrausAction (nativeScalarNoKraus q hq z hz) (r • (1 : Matrix Unit Unit ℝ)) =
      nativeCornerEncoding q hq (r • nativeCornerProjection q hq z) := by
  rw [nativeScalarNoKraus, positiveMeasurePrepare_action, map_smul]
  simp [nativeScalarNoState]

theorem nativeScalarKraus_normalized (q : Albert) (hq : IsAtom q) (z : Albert) (hz : IsDensity z) :
    rectangularKrausEffect (nativeScalarYesKraus q hq z hz.1) +
      rectangularKrausEffect (nativeScalarNoKraus q hq z hz.1) = 1 := by
  rw [nativeScalarYesKraus, nativeScalarNoKraus, positiveMeasurePrepare_effect,
    positiveMeasurePrepare_effect]
  have ht : tracePairing q z + albertTrace (quadraticMap (albertUnit - q) z) = 1 := by
    rw [albertTrace_quadraticMap, complementary_idempotent q hq.1,
      tracePairing_sub_left, tracePairing_comm albertUnit, tracePairing_unit_right, hz.2]
    ring
  rw [nativeScalarYesState, Matrix.trace_smul, nativeScalarNoState, nativeCornerEncoding_trace]
  have hu : Matrix.trace (1 : Matrix Unit Unit ℝ) = 1 := by simp
  rw [hu, smul_eq_mul, mul_one]
  change (tracePairing q z) • (1 : Matrix Unit Unit ℝ) +
    albertTrace (quadraticMap (albertUnit - q) z) • 1 = 1
  rw [← add_smul, ht, one_smul]

end AlbertSequential.NativeAnalysis
