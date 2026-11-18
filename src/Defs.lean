module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Matrix.Basic

/-!
# Compact Albert algebra: a nonunital associative-target obstruction

DEFINITIONS ONLY: no theorem and no axiom is imported.
Source: core `thm:tet:albert` (appendix `sec:tet`). This is one endpoint, not
the whole paper.

The concrete definitions below follow the Cayley–Dickson and Hermitian-matrix
construction.
Pair multiplication is NOT the octonion multiplication. All nonassociative
products below use `octonionMul` explicitly.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-- Compact real octonions, as pairs of ordinary real quaternions. -/
def Octonion := Quaternion ℝ × Quaternion ℝ

instance : AddCommGroup Octonion :=
  inferInstanceAs (AddCommGroup (Quaternion ℝ × Quaternion ℝ))
instance : Module ℝ Octonion :=
  inferInstanceAs (Module ℝ (Quaternion ℝ × Quaternion ℝ))

/-- Compact Cayley–Dickson convention, parameter minus one. -/
def octonionMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

def octonionConj (x : Octonion) : Octonion := (star x.1, -x.2)

def octonionScalar (r : ℝ) : Octonion := (⟨r, 0, 0, 0⟩, 0)

def octonionReal (x : Octonion) : ℝ := x.1.re

/-- Three diagonal reals and upper entries 01, 02, 12, in that order.
Paper coordinates (ξ; x₁,x₂,x₃) become (ξ; x₃, conjugate x₂, x₁).
Only additive/module instances are exposed; use `jordanMul` explicitly.
No coordinatewise multiplication, unit, star or norm is exported. -/
def Albert := (Fin 3 → ℝ) × (Fin 3 → Octonion)

instance : AddCommGroup Albert :=
  inferInstanceAs (AddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
instance : Module ℝ Albert :=
  inferInstanceAs (Module ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

def albertMatrix (x : Albert) : Fin 3 → Fin 3 → Octonion :=
  fun i j => match i.val, j.val with
    | 0, 0 => octonionScalar (x.1 0)
    | 1, 1 => octonionScalar (x.1 1)
    | 2, 2 => octonionScalar (x.1 2)
    | 0, 1 => x.2 0
    | 0, 2 => x.2 1
    | 1, 2 => x.2 2
    | 1, 0 => octonionConj (x.2 0)
    | 2, 0 => octonionConj (x.2 1)
    | 2, 1 => octonionConj (x.2 2)
    | _, _ => 0

/-- This is a binary matrix product; no associativity is asserted. -/
def octonionMatrixMul (x y : Fin 3 → Fin 3 → Octonion) :
    Fin 3 → Fin 3 → Octonion :=
  fun i j => ∑ k : Fin 3, octonionMul (x i k) (y k j)

def albertCoordinates (m : Fin 3 → Fin 3 → Octonion) : Albert :=
  (fun i => octonionReal (m i i), ![m 0 1, m 0 2, m 1 2])

/-- Native Jordan product, the coordinates of (xy + yx)/2. -/
def jordanMul (x y : Albert) : Albert :=
  (1 / 2 : ℝ) • albertCoordinates
    (octonionMatrixMul (albertMatrix x) (albertMatrix y) +
      octonionMatrixMul (albertMatrix y) (albertMatrix x))

def albertUnit : Albert := (fun _ => 1, fun _ => 0)

/-- Raw matrix trace; the unit has trace three, not one. -/
def albertTrace (x : Albert) : ℝ := ∑ i : Fin 3, x.1 i

def tracePairing (x y : Albert) : ℝ := albertTrace (jordanMul x y)

def quadraticMap (x y : Albert) : Albert :=
  2 • jordanMul x (jordanMul x y) - jordanMul (jordanMul x x) y

/-- The square cone. Its order properties (for instance convexity, `convex_positive_set`) are
proved separately; they are not part of the definition. -/
def IsPositive (x : Albert) : Prop := ∃ y : Albert, x = jordanMul y y

/-- Trace-one idempotent. These are exactly the primitive idempotents
(`NativeAnalysis.isAtom_iff_primitive`, in `Bridge.Atoms`). -/
def IsAtom (p : Albert) : Prop := jordanMul p p = p ∧ albertTrace p = 1

def IsDensity (ρ : Albert) : Prop := IsPositive ρ ∧ albertTrace ρ = 1

/-- A real-linear Jordan homomorphism, with no unit-preserving condition. -/
def IsJordanHom {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) : Prop :=
  ∀ x y, η (jordanMul x y) = (1 / 2 : ℝ) • (η x * η y + η y * η x)

end AlbertSequential
