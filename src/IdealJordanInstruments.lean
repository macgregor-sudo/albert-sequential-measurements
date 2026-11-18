/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SharpJordanEffects

/-! The full ideal-test equivalence for finite Jordan algebras with their
actual supplied positive associative form. Positivity is sufficient; CP,
classification and canonical primitive trace normalization are not assumed.
Arbitrary-dimensional R/C/H trace-class instruments are a separate theorem. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential.PositiveInstruments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)
  (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
include hinner

theorem idealTest_iff_quadraticRepresentation (T : PositiveBinaryInstrument P) :
    (IsIdeal P T ∧ IsSharpEffect P (measuredEffect P T)) ↔
      ∃ p : E, P.product p p=p ∧ T.yes=P.quadraticRepresentation p ∧
        T.no=P.quadraticRepresentation (P.unit-p) := by
  constructor
  · rintro ⟨hid,hsharp⟩
    let p := measuredEffect P T
    have hp : P.product p p=p :=
      sharpEffect_isIdempotent P hinner p (measuredEffect_isEffect P hinner T) hsharp
    have hy : T.yes=P.quadraticRepresentation p :=
      positiveMap_eq_quadraticRepresentation P hinner T.yes p hp T.yes_positive
        (fun x => (measuredEffect_pairing P T x).symm) hid.1
    have hntrace (x : E) : trace P (T.no x)=inner ℝ x (P.unit-p) := by
      have ht := T.normalized x
      rw [trace_add] at ht
      have hytrace := measuredEffect_pairing P T x
      rw [inner_sub_right]
      change trace P (T.no x)=trace P x-inner ℝ x p
      linarith
    have hnfix (ρ : E) (hρ : IsDensity P ρ) (hpair : inner ℝ ρ (P.unit-p)=1) : T.no ρ=ρ := by
      rw [inner_sub_right] at hpair
      change trace P ρ-inner ℝ ρ p=1 at hpair
      have hp0 : inner ℝ ρ p=0 := by linarith [hρ.2]
      exact hid.2 ρ hρ hp0
    have hn : T.no=P.quadraticRepresentation (P.unit-p) :=
      positiveMap_eq_quadraticRepresentation P hinner T.no (P.unit-p)
        (complementary_idempotent P p hp) T.no_positive hntrace hnfix
    exact ⟨p,hp,hy,hn⟩
  · rintro ⟨p,hp,hy,hn⟩
    have hm : measuredEffect P T=p :=
      measuredEffect_eq_of_quadraticRepresentation P hinner T p hp hy
    constructor
    · constructor
      · intro ρ hρ hpair
        rw [hm] at hpair
        rw [hy]
        exact quadraticRepresentation_fixes_density P hinner p hp ρ hρ hpair
      · intro ρ hρ hpair
        rw [hm] at hpair
        rw [hn]
        apply quadraticRepresentation_fixes_density P hinner _
          (complementary_idempotent P p hp) ρ hρ
        rw [inner_sub_right]
        change trace P ρ-inner ℝ ρ p=1
        rw [hρ.2,hpair,sub_zero]
    · rw [hm]
      exact idempotent_isSharpEffect P hinner p hp

/-- An actual instrument is constructed, rather than leaving the existence of
an admissible pair on the right-hand side as an unproved premise. -/
theorem quadraticInstrument_isIdealTest (p : E) (hp : P.product p p=p) :
    IsIdeal P (quadraticInstrument P hinner p hp) ∧
      IsSharpEffect P (measuredEffect P (quadraticInstrument P hinner p hp)) :=
  (idealTest_iff_quadraticRepresentation P hinner _).mpr ⟨p,hp,rfl,rfl⟩

end AlbertSequential.PositiveInstruments
