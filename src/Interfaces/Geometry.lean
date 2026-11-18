module

public import Interfaces.WordsAndCertificates
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.Complex.Order

/-! Native subalgebras and the strong C3 triple statement. This file gives
definitions and statement types, not an embedding, classification or geometric theorem.
All Albert products are `jordanMul`, never inherited coordinate multiplication.
The 52-term invariant, all-degeneracy normal forms, quaternionic windows and
measure laws are not stated here. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential

structure NativeJordanSubalgebra where
  carrier : Submodule ℝ Albert
  unit_mem : albertUnit ∈ carrier
  product_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, jordanMul x y ∈ carrier

/-- Actual generated algebra membership by intersection of all unital Jordan
subalgebras containing the tests. This is not an unconstrained generation flag. -/
def InGeneratedAlgebra {ι : Type*} (p : ι → Albert) (x : Albert) : Prop :=
  ∀ B : NativeJordanSubalgebra, (∀ i, p i ∈ B.carrier) → x ∈ B.carrier

def GeneratesAlbert {ι : Type*} (p : ι → Albert) : Prop :=
  ∀ x, InGeneratedAlgebra p x

structure NativeJordanFrame where
  atom : Fin 3 → Albert
  atoms : ∀ i, IsAtom (atom i)
  orthogonal : ∀ i j, i ≠ j → jordanMul (atom i) (atom j) = 0
  sum_unit : ∑ i, atom i = albertUnit

/-- Concrete native automorphism, no Lie-group transitivity silently assumed. -/
structure NativeAlbertAutomorphism where
  linearEquiv : Albert ≃ₗ[ℝ] Albert
  preserves_product : ∀ x y,
    linearEquiv (jordanMul x y) = jordanMul (linearEquiv x) (linearEquiv y)
  preserves_unit : linearEquiv albertUnit = albertUnit
  preserves_trace : ∀ x, albertTrace (linearEquiv x) = albertTrace x

abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Hermitian3 := selfAdjoint ComplexMatrix3

/-- An actual complex Hermitian embedding. Product preservation is written
using the ambient matrix expression; the variable z is the Hermitian product.
Hermitian closure is separately explicit, so this clause cannot be vacuous. -/
structure ComplexWindow where
  embedding : Hermitian3 →ₗ[ℝ] Albert
  injective : Function.Injective embedding
  unit : embedding 1 = albertUnit
  product_closed : ∀ x y : Hermitian3, ∃ z : Hermitian3,
    (z : ComplexMatrix3) = (1 / 2 : ℝ) •
      ((x : ComplexMatrix3) * (y : ComplexMatrix3) +
        (y : ComplexMatrix3) * (x : ComplexMatrix3))
  preserves_product : ∀ x y z : Hermitian3,
    (z : ComplexMatrix3) = (1 / 2 : ℝ) •
      ((x : ComplexMatrix3) * (y : ComplexMatrix3) +
        (y : ComplexMatrix3) * (x : ComplexMatrix3)) →
      embedding z = jordanMul (embedding x) (embedding y)
  preserves_trace : ∀ x : Hermitian3,
    albertTrace (embedding x) = (Matrix.trace (x : ComplexMatrix3)).re

def ComplexWindow.Contains (W : ComplexWindow) (p : Albert) : Prop :=
  ∃ x : Hermitian3, W.embedding x = p

/-- Exact rank-one form with normalized vector; no rank-two C6 substitute. -/
def IsComplexRankOneProjection (P : ComplexMatrix3) : Prop :=
  ∃ v : Fin 3 → ℂ, (∑ i, star (v i) * v i) = 1 ∧
    ∀ i j, P i j = v i * star (v j)

def IsComplexDensity3 (σ : ComplexMatrix3) : Prop :=
  σ.PosSemidef ∧ Matrix.trace σ = 1

def complexWordProbability3 {ι : Type*} (P : ι → ComplexMatrix3)
    (σ : ComplexMatrix3) (w : Word ι) : ℝ :=
  (Matrix.trace (σ * wordOperator P w)).re

/-- prop:three, including repeated and orthogonal triples, arbitrary native
initial density, rank-one C3 projections and ALL chronological words.
Proved as `complexTripleContract_holds` (`ThreeAtomAndFourPoint`). -/
structure ComplexTripleContract : Prop where
  common_window : ∀ p : Fin 3 → Albert, (∀ i, IsAtom (p i)) →
    ∃ W : ComplexWindow, ∀ i, W.Contains (p i)
  rank_one_statistics : ∀ (p : Fin 3 → Albert) (ρ : Albert),
    (∀ i, IsAtom (p i)) → IsDensity ρ →
    ∃ P : Fin 3 → ComplexMatrix3, ∃ σ : ComplexMatrix3,
      (∀ i, IsComplexRankOneProjection (P i)) ∧ IsComplexDensity3 σ ∧
      ∀ w, complexWordProbability3 P σ w = nativeWordProbability p ρ w

/-- Restriction through a supplied complex window, not existence of that
window. The output state is not presumed equal to an unnormalized trace image. -/
structure ComplexRestrictionContract : Prop where
  common_density_transport : ∀ (W : ComplexWindow) (ρ : Albert), IsDensity ρ →
    ∃ σ : ComplexMatrix3, IsComplexDensity3 σ ∧
      (∀ x : Hermitian3,
        (Matrix.trace (σ * (x : ComplexMatrix3))).re = tracePairing ρ (W.embedding x)) ∧
      ∀ (ι : Type*) (p : ι → Albert) (P : ι → Hermitian3),
        (∀ i, IsAtom (p i)) → (∀ i, W.embedding (P i) = p i) →
        (∀ i, IsComplexRankOneProjection (P i : ComplexMatrix3)) ∧
        ∀ w, complexWordProbability3 (fun i => (P i : ComplexMatrix3)) σ w =
          nativeWordProbability p ρ w

/-- Interface consumer only: generation genuinely forces membership in any
supplied unital subalgebra containing the generators. -/
example {ι : Type*} (p : ι → Albert) (h : GeneratesAlbert p)
    (B : NativeJordanSubalgebra) (hp : ∀ i, p i ∈ B.carrier) (x : Albert) :
    x ∈ B.carrier := h x B hp

end AlbertSequential
