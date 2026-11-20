/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The rectangular frame identities used to transport a channel to one sharp outcome.
The index types may be arbitrary finite types, including a sum of source and ancillary indices. -/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential

open Matrix

/-- Data for an outcome projection `R` with input inclusion `J` and effect square root `S`.
The partial-isometry range is contained in `R`, and agrees with `R` on the included input space. -/
structure SharpDilationChannelFrame {input output : Type*} [Fintype input] [Fintype output]
    (J : Matrix output input ℂ) (R : Matrix output output ℂ) (S : Matrix input input ℂ) where
  frame : Matrix output input ℂ
  range_idempotent : (frame * frameᴴ) * (frame * frameᴴ) = frame * frameᴴ
  projection_frame : R * frame = frame
  frame_inclusion : frameᴴ * J = S
  projection_inclusion : R * J = frame * S

namespace SharpDilationChannelFrame

theorem residual_annihilates_inclusion {input output : Type*}
    [Fintype input] [Fintype output] {J : Matrix output input ℂ} {R : Matrix output output ℂ}
    {S : Matrix input input ℂ} (f : SharpDilationChannelFrame J R S) :
    (R - f.frame * f.frameᴴ) * J = 0 := by
  rw [Matrix.sub_mul, f.projection_inclusion, Matrix.mul_assoc f.frame f.frameᴴ J,
    f.frame_inclusion, sub_self]

end SharpDilationChannelFrame

end AlbertSequential
