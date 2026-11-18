/- SPDX-License-Identifier: Apache-2.0
Actual supplied associative positive form; no canonical
trace normalization, classification, CP or trace-class theorem
is assumed. -/
module
public import EuclideanJordanQuadraticPositive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential.PositiveInstruments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

def trace (x : E) : ℝ := inner ℝ x P.unit

def IsDensity (x : E) : Prop := x ∈ P.squareCone ∧ trace P x = 1

def IsEffect (a : E) : Prop := a ∈ P.squareCone ∧ P.unit - a ∈ P.squareCone

structure PositiveBinaryInstrument where
  yes : E →ₗ[ℝ] E
  no : E →ₗ[ℝ] E
  yes_positive : ∀ x ∈ P.squareCone, yes x ∈ P.squareCone
  no_positive : ∀ x ∈ P.squareCone, no x ∈ P.squareCone
  normalized : ∀ x, trace P (yes x + no x) = trace P x

def measuredEffect (T : PositiveBinaryInstrument P) : E :=
  LinearMap.adjoint T.yes P.unit

def IsIdeal (T : PositiveBinaryInstrument P) : Prop :=
  (∀ ρ, IsDensity P ρ → inner ℝ ρ (measuredEffect P T) = 1 → T.yes ρ = ρ) ∧
  (∀ ρ, IsDensity P ρ → inner ℝ ρ (measuredEffect P T) = 0 → T.no ρ = ρ)

def IsSharpEffect (a : E) : Prop :=
  ¬ ∃ σ f, IsDensity P σ ∧ IsEffect P f ∧ inner ℝ σ f = 1 ∧
    ∀ ρ, IsDensity P ρ → (inner ℝ ρ a = 0 ∨ inner ℝ ρ a = 1) → inner ℝ ρ f = 0

def IsSharp (T : PositiveBinaryInstrument P) : Prop := IsSharpEffect P (measuredEffect P T)

def IsIdealTest (T : PositiveBinaryInstrument P) : Prop := IsIdeal P T ∧ IsSharp P T

omit [FiniteDimensional ℝ E] in
@[simp] theorem trace_add (x y : E) : trace P (x+y) = trace P x + trace P y :=
  inner_add_left _ _ _
omit [FiniteDimensional ℝ E] in
@[simp] theorem trace_smul (t : ℝ) (x : E) : trace P (t • x) = t * trace P x :=
  real_inner_smul_left _ _ _
omit [FiniteDimensional ℝ E] in
@[simp] theorem trace_zero : trace P (0 : E) = 0 := inner_zero_left P.unit

theorem measuredEffect_pairing (T : PositiveBinaryInstrument P) (x : E) :
    inner ℝ x (measuredEffect P T) = trace P (T.yes x) := by
  exact LinearMap.adjoint_inner_right T.yes x P.unit

theorem measuredEffect_isEffect
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (T : PositiveBinaryInstrument P) : IsEffect P (measuredEffect P T) := by
  constructor
  · apply (P.squareCone_self_dual hinner _).mpr
    intro x hx
    rw [real_inner_comm, measuredEffect_pairing]
    exact P.squareCone_unitPairing_nonnegative hinner _ (T.yes_positive x hx)
  · apply (P.squareCone_self_dual hinner _).mpr
    intro x hx
    have hn := T.normalized x
    rw [trace_add] at hn
    have hp := P.squareCone_unitPairing_nonnegative hinner _ (T.no_positive x hx)
    change 0 ≤ trace P (T.no x) at hp
    rw [inner_sub_left]
    have he : inner ℝ P.unit x = trace P x := real_inner_comm _ _
    have ha : inner ℝ (measuredEffect P T) x = trace P (T.yes x) :=
      (real_inner_comm _ _).trans (measuredEffect_pairing P T x)
    rw [he,ha]
    linarith

omit [FiniteDimensional ℝ E] in
theorem complementary_idempotent (p : E) (hp : P.product p p = p) :
    P.product (P.unit-p) (P.unit-p) = P.unit-p := by
  have hunit (x : E) : P.product x P.unit = x := by rw [P.commutative, P.unit_left]
  simp only [map_sub, LinearMap.sub_apply, P.unit_left, hunit, hp]
  abel

omit [FiniteDimensional ℝ E] in
theorem idempotent_isEffect (p : E) (hp : P.product p p = p) : IsEffect P p :=
  ⟨⟨p,hp.symm⟩, ⟨P.unit-p,(complementary_idempotent P p hp).symm⟩⟩

/- The quadratic coefficient is the opposite compression; no Peirce grading
or topological limiting argument is hidden in this identity. -/
omit [FiniteDimensional ℝ E] in
theorem quadratic_filter_interpolation (p x : E) (hp : P.product p p = p) (t : ℝ) :
    P.quadraticRepresentation (p+t • (P.unit-p)) x =
      P.quadraticRepresentation p x + t •
        (x-P.quadraticRepresentation p x-P.quadraticRepresentation (P.unit-p) x) +
      (t*t) • P.quadraticRepresentation (P.unit-p) x := by
  have hunit (y : E) : P.product y P.unit = y := by rw [P.commutative,P.unit_left]
  simp only [P.quadraticRepresentation_apply, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    P.unit_left, hunit, hp]
  module

/-- A whole real affine line in the actual pointed self-dual cone has zero
slope. The scalar argument works even when its base point is zero. -/
theorem affine_line_in_squareCone_slope_zero
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (b z : E) (h : ∀ t : ℝ, b+t • z ∈ P.squareCone) : z=0 := by
  have hpair (y : E) (hy : y∈P.squareCone) : inner ℝ z y=0 := by
    have hall (t : ℝ) : 0 ≤ inner ℝ b y + t * inner ℝ z y := by
      simpa only [inner_add_left, real_inner_smul_left] using
        P.squareCone_inner_nonnegative hinner _ y (h t) hy
    by_contra hn
    have hc := hall (-(inner ℝ b y+1) / inner ℝ z y)
    rw [div_mul_cancel₀ _ hn] at hc
    linarith
  have hz : z∈P.squareCone := (P.squareCone_self_dual hinner z).mpr (by
    intro y hy
    rw [hpair y hy])
  have hnz : -z∈P.squareCone := (P.squareCone_self_dual hinner (-z)).mpr (by
    intro y hy
    rw [inner_neg_left,hpair y hy,neg_zero])
  exact P.squareCone_pointed hinner z hz hnz

omit [FiniteDimensional ℝ E] in
theorem trace_quadratic_idempotent
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p x : E) (hp : P.product p p=p) :
    trace P (P.quadraticRepresentation p x) = inner ℝ x p := by
  exact (P.quadraticRepresentation_inner hinner p x P.unit).trans (by
    rw [P.quadraticRepresentation_unit,hp])

end AlbertSequential.PositiveInstruments
