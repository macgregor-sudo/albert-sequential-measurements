/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RectangularKrausFamilies
public import FiniteSpectralSupport

/-! An actual finite real/complex rectangular Kraus family for every positive
measure-and-prepare pair, valid on all matrices and including zero effects. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

def positiveMeasurePrepare (τ : Matrix m m 𝕜) (hτ : τ.PosSemidef)
    (E : Matrix n n 𝕜) (hE : E.PosSemidef) : List (Matrix m n 𝕜) :=
  rectangularMeasurePrepare (finiteSpectralSupport hτ).root (finiteSpectralSupport hE).root

theorem positiveMeasurePrepare_action (τ : Matrix m m 𝕜) (hτ : τ.PosSemidef)
    (E : Matrix n n 𝕜) (hE : E.PosSemidef) (Y : Matrix n n 𝕜) :
    rectangularKrausAction (positiveMeasurePrepare τ hτ E hE) Y =
      Matrix.trace (E * Y) • τ := by
  rw [positiveMeasurePrepare, rectangularMeasurePrepare_action,
    (finiteSpectralSupport hτ).root_hermitian, (finiteSpectralSupport hτ).root_sq,
    (finiteSpectralSupport hE).root_hermitian,
    Matrix.trace_mul_comm ((finiteSpectralSupport hE).root * Y),
    ← Matrix.mul_assoc, (finiteSpectralSupport hE).root_sq]

theorem positiveMeasurePrepare_effect (τ : Matrix m m 𝕜) (hτ : τ.PosSemidef)
    (E : Matrix n n 𝕜) (hE : E.PosSemidef) :
    rectangularKrausEffect (positiveMeasurePrepare τ hτ E hE) = Matrix.trace τ • E := by
  rw [positiveMeasurePrepare, rectangularMeasurePrepare_effect,
    (finiteSpectralSupport hτ).root_hermitian, (finiteSpectralSupport hτ).root_sq,
    (finiteSpectralSupport hE).root_hermitian, (finiteSpectralSupport hE).root_sq]

end AlbertSequential
