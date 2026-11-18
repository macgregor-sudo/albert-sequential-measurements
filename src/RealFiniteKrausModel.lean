/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RectangularKrausFamilies

/-! A finite real Kraus model indexed by any finite coordinate set. Conversion
to the public complex Fin-d interface is a separate literal transport. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
variable (I X : Type*) [Fintype I] [DecidableEq I]

structure RealFiniteKrausModel where
  initial : Matrix I I ℝ
  positive : initial.PosSemidef
  trace_one : Matrix.trace initial = 1
  kraus : X → Bool → List (Matrix I I ℝ)
  normalized : ∀ x, rectangularKrausEffect (kraus x true) + rectangularKrausEffect (kraus x false) = 1

def realFiniteKrausProbability (r : RealFiniteKrausModel I X) (w : Word X) : ℝ :=
  Matrix.trace (w.foldl (fun Y a => rectangularKrausAction (r.kraus a.1 a.2) Y) r.initial)

end AlbertSequential
