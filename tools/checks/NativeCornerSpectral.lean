module

import NativeCornerSpectralCoordinates

open AlbertSequential AlbertSequential.NativeAnalysis Polynomial

example (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    let a := (chosenAtomNormalizer p hp).linearEquiv (x : Albert)
    IsPositive (x : Albert) ↔
      Real.sqrt (((a.1 1 - a.1 2) / 2) ^ 2 + octNormSq (a.2 2)) ≤ (a.1 1 + a.1 2) / 2 :=
  nativeCorner_positive_iff_chartForwardCone p hp x

example (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    (nativeHalfMatrix p hp x).charpoly =
      (X - C (nativeCornerTime x + nativeCornerRadius p hp x))^8 *
      (X - C (nativeCornerTime x - nativeCornerRadius p hp x))^8 :=
  nativeHalfMatrix_corner_charpoly p hp x

#print axioms nativeCorner_traceless_square
#print axioms nativeCorner_time_radius_coordinates
#print axioms nativeCorner_spectralAtoms
#print axioms nativeCorner_positive_iff_chartForwardCone
#print axioms nativeHalfMatrix_corner_charpoly
