/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerKrausTransition

/-! The complementary branch resets into a literal one-dimensional block.
No preparation or positivity assumption is needed for the encoded weight law. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

def nativeCornerYesKraus (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    List (Matrix Unit SpinorCoordinate ℝ) :=
  positiveMeasurePrepare (1 : Matrix Unit Unit ℝ) Matrix.PosSemidef.one
    (nativeCornerYesEffect p hp q) (nativeCornerYesEffect_positive p hp q hq)

theorem nativeCornerYesKraus_effect (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    rectangularKrausEffect (nativeCornerYesKraus p hp q hq) = nativeCornerYesEffect p hp q := by
  rw [nativeCornerYesKraus, positiveMeasurePrepare_effect]
  simp

theorem nativeCornerYesKraus_encoding (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q)
    (x : nativePeirceZero p) :
    rectangularKrausAction (nativeCornerYesKraus p hp q hq) (nativeCornerEncoding p hp x) =
      tracePairing q x • (1 : Matrix Unit Unit ℝ) := by
  rw [nativeCornerYesKraus, positiveMeasurePrepare_action, nativeCornerYesEffect_weight]

theorem nativeCornerKraus_normalized (p : Albert) (hp : IsAtom p) (q : Albert) (hq : IsAtom q) :
    rectangularKrausEffect (nativeCornerYesKraus p hp q hq) +
      rectangularKrausEffect (nativeCornerNoKraus p hp q hq) = 1 := by
  rw [nativeCornerYesKraus_effect, nativeCornerNoKraus_effect, nativeCornerEffects_sum]

end AlbertSequential.NativeAnalysis
