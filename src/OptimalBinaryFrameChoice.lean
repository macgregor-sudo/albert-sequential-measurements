/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BinarySpectralSupport
public import SharpDilationChannelFrame
public import RealMatrixComplexification
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section
set_option autoImplicit false

namespace AlbertSequential

open Matrix

/-- A single binary effect with both reduced branch frames on the same input
corner. A zero original effect has a globally zero outcome projection. -/
structure OptimalBinaryFrameChoice {d m : ℕ} (A : ComplexMatrix d) where
  spectral : BinarySpectralSupport A
  projection : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℂ
  hermitian : projectionᴴ = projection
  idempotent : projection * projection = projection
  compression : let J : Matrix (Fin d ⊕ Fin m) (Fin d) ℂ := fromRows 1 0
    Jᴴ * projection * J = A
  yesFrame : SharpDilationChannelFrame (fromRows 1 0) projection spectral.yes.root
  noFrame : SharpDilationChannelFrame (fromRows 1 0) (1 - projection) spectral.no.root
  zero_yes : A = 0 → projection = 0
  zero_no : 1 - A = 0 → 1 - projection = 0
  real_data : HasRealEntries A →
    (∀ i j, (projection i j).im = 0) ∧
    (∀ i j, (yesFrame.frame i j).im = 0) ∧ (∀ i j, (noFrame.frame i j).im = 0) ∧
    HasRealEntries spectral.yes.inverseRoot ∧ HasRealEntries spectral.no.inverseRoot ∧
    HasRealEntries spectral.yes.support ∧ HasRealEntries spectral.no.support

end AlbertSequential
