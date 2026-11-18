/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.AlgebraicReconstruction
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! Null-subspace and left-ideal calculus for an arbitrary positive real,
star-symmetric functional. No normalization, trace, faithfulness or boundedness
is used. This does not declare a two-sided algebra quotient. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

section PositiveFunctional
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ) (hstar : ∀ x, φ (star x) = φ x)

include hstar in
omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem positiveForm_symmetric (x y : A) :
    φ (star x * y) = φ (star y * x) := by
  calc
    φ (star x * y) = φ (star (star y * x)) := by rw [star_mul, star_star]
    _ = φ (star y * x) := hstar _

include hstar in
theorem positiveForm_expansion (x y : A) (t : ℝ) :
    φ (star (t • x + y) * (t • x + y)) =
      t ^ 2 * φ (star x * x) + 2 * t * φ (star x * y) + φ (star y * y) := by
  simp only [star_add, star_smul, star_trivial, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul]
  rw [positiveForm_symmetric φ hstar y x]
  ring

variable (hpos : ∀ x, 0 ≤ φ (star x * x))

include hstar hpos in
theorem nullFor_pair_zero (x : A) (hx : NullFor φ x) (y : A) :
    φ (star x * y) = 0 := by
  by_contra hne
  let t : ℝ := -(φ (star y * y) + 1) / (2 * φ (star x * y))
  have hvalue : 2 * t * φ (star x * y) + φ (star y * y) = -1 := by
    dsimp only [t]
    field_simp
    ring
  have hp := hpos (t • x + y)
  change φ (star x * x) = 0 at hx
  rw [positiveForm_expansion φ hstar, hx, mul_zero, zero_add, hvalue] at hp
  norm_num at hp

theorem nullFor_zero : NullFor φ 0 := by simp only [NullFor, star_zero, mul_zero, map_zero]

include hstar hpos in
theorem nullFor_add (x y : A) (hx : NullFor φ x) (hy : NullFor φ y) :
    NullFor φ (x + y) := by
  have hp := nullFor_pair_zero φ hstar hpos x hx y
  have he := positiveForm_expansion φ hstar x y 1
  change φ (star x * x) = 0 at hx
  change φ (star y * y) = 0 at hy
  change φ (star (x + y) * (x + y)) = 0
  simpa only [one_smul, one_pow, one_mul, hx, hy, hp, mul_zero, add_zero] using he

theorem nullFor_smul (r : ℝ) (x : A) (hx : NullFor φ x) :
    NullFor φ (r • x) := by
  change φ (star x * x) = 0 at hx
  simp only [NullFor, star_smul, star_trivial, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_smul, hx, smul_zero]

include hstar hpos in
theorem nullFor_left_invariant : NullLeftInvariant φ := by
  intro a x hx
  have hp := nullFor_pair_zero φ hstar hpos x hx (star a * a * x)
  simpa only [NullFor, star_mul, mul_assoc] using hp

/-- The null set is a real submodule; no right-ideal property is asserted. -/
def positiveFunctionalNullSubmodule : Submodule ℝ A where
  carrier := {x | NullFor φ x}
  zero_mem' := nullFor_zero φ
  add_mem' := fun hx hy => nullFor_add φ hstar hpos _ _ hx hy
  smul_mem' := fun r x hx => nullFor_smul φ r x hx

theorem mem_positiveFunctionalNullSubmodule (x : A) :
    x ∈ positiveFunctionalNullSubmodule φ hstar hpos ↔ NullFor φ x := Iff.rfl

include hstar hpos in
theorem nullFor_on_wordSpan {ι : Type*} (P : ι → A) (Z : A)
    (hZ : ∀ w, NullFor φ (Z * wordAmplitude P w))
    (x : A) (hx : x ∈ WordVectorSpan P) : NullFor φ (Z * x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨w, rfl⟩
      exact hZ w
  | zero => simpa only [mul_zero] using nullFor_zero φ
  | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact nullFor_add φ hstar hpos _ _ ihx ihy
  | smul r x hx ih =>
      rw [mul_smul_comm]
      exact nullFor_smul φ r _ ih

end PositiveFunctional

theorem allHistoryNullContract
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) : AllHistoryNullContract M where
  left_invariant := nullFor_left_invariant M.state M.state_star M.state_positive
  extend_to_span := fun Z hZ x hx =>
    nullFor_on_wordSpan M.state M.state_star M.state_positive M.projection Z hZ x hx

end AlbertSequential
