/- SPDX-License-Identifier: Apache-2.0
Original owner-directed Lean from the frozen 2026-11-17 ProjectiveTableClasses return. -/
module
public import FieldExtensionFiniteDimension
public import QuaternionicClassIConstructor

/-! Actual class-(I) table sets at an arbitrary carrier universe. These are
existential models, not assumed realization theorems. The finite quaternionic
set uses the literal ordinary right scalar action's opposite module.
FieldExtensionFiniteDimension supplies that accepted module definition; this
file introduces no GNS or field-equality proof and no circular import. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
namespace AlbertSequential

/-- ALL word probabilities for one finite labelled menu and one fixed actual
Hilbert model, with arbitrary positive normalized real-linear SA state. -/
def hilbertProjectiveTables (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    Set (Word (Fin n) → ℝ) := {f |
  ∃ H : Type u, ∃ hN : NormedAddCommGroup H,
    letI := hN
    ∃ hI : InnerProductSpace 𝕜 H,
    letI := hI
    ∃ hC : CompleteSpace H,
    letI := hC
    ∃ M : HilbertProjectiveData (Fin n) 𝕜 H,
      ∀ w, M.toAlgebraic.probability w = f w}

/-- Finite ORIGINAL source-field dimension; no preset dimension bound or
normal/faithful state restriction is imposed. -/
def finiteHilbertProjectiveTables (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    Set (Word (Fin n) → ℝ) := {f |
  ∃ H : Type u, ∃ hN : NormedAddCommGroup H,
    letI := hN
    ∃ hI : InnerProductSpace 𝕜 H,
    letI := hI
    ∃ hC : CompleteSpace H,
    letI := hC
    FiniteDimensional 𝕜 H ∧
      ∃ M : HilbertProjectiveData (Fin n) 𝕜 H,
        ∀ w, M.toAlgebraic.probability w = f w}

/-- The carrier has an ACTUAL ordinary right-quaternionic Hilbert structure.
The accepted commutant/source correspondence identifies its full bounded
right-linear SA state and chronological probabilities exactly. -/
def quaternionicProjectiveTables (n : ℕ) : Set (Word (Fin n) → ℝ) := {f |
  ∃ H : Type u, ∃ hN : NormedAddCommGroup H,
    letI := hN
    ∃ hI : InnerProductSpace ℝ H,
    letI := hI
    ∃ hC : CompleteSpace H,
    letI := hC
    ∃ S : RightQuaternionicHilbertStructure H,
      ∃ M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure,
        ∀ w, M.toAlgebraic.probability w = f w}

/-- Finite dimension over the literal opposite quaternion module associated
to the ordinary RIGHT action, rather than an unrelated real-dimension premise. -/
def finiteQuaternionicProjectiveTables (n : ℕ) : Set (Word (Fin n) → ℝ) := {f |
  ∃ H : Type u, ∃ hN : NormedAddCommGroup H,
    letI := hN
    ∃ hI : InnerProductSpace ℝ H,
    letI := hI
    ∃ hC : CompleteSpace H,
    letI := hC
    ∃ S : RightQuaternionicHilbertStructure H,
      (letI := S.oppositeModule
       FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H) ∧
        ∃ M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure,
          ∀ w, M.toAlgebraic.probability w = f w}

end AlbertSequential
