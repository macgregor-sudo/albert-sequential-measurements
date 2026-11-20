/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedCertaintySupport
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! The repeated-atom case of the corner spectrum in the spinor realization. -/

@[expose] public section
namespace AlbertSequential.NativeAnalysis

/-- When two labels test the same atom the sixteen-dimensional yes-effect is zero.
The two groups of eight eigenvalues coalesce, with total multiplicity sixteen. -/
theorem nativeCornerYesEffect_charpoly_of_eq (p q : Albert) (hp : IsAtom p) (h : q = p) :
    (nativeCornerYesEffect p hp q).charpoly = Polynomial.X ^ 16 := by
  rw [h, nativeCornerYesEffect_same_zero, Matrix.charpoly_zero, spinorCoordinate_card]

end AlbertSequential.NativeAnalysis
