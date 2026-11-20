/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanProductQuadratic

/-! Reflection in an actual idempotent of a unital real Jordan algebra.
The fundamental formula is supplied by the existing concrete Jordan API. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- The quadratic reflection associated with a test idempotent. -/
def idempotentReflection (p : E) : E →ₗ[ℝ] E :=
  P.quadraticRepresentation ((2 : ℝ) • p - P.unit)

theorem idempotentReflection_apply (p x : E) :
    P.idempotentReflection p x = (2 : ℝ) •
      (P.quadraticRepresentation p x + P.quadraticRepresentation (P.unit - p) x) - x := by
  have hu (x : E) : P.product x P.unit = x := (P.commutative x P.unit).trans (P.unit_left x)
  simp only [idempotentReflection, quadraticRepresentation_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, P.unit_left, hu]
  module

theorem idempotentReflection_unit (p : E) (hp : P.product p p = p) :
    P.idempotentReflection p P.unit = P.unit := by
  have hu (x : E) : P.product x P.unit = x := (P.commutative x P.unit).trans (P.unit_left x)
  simp only [idempotentReflection, quadraticRepresentation_unit, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, P.unit_left, hu, hp]
  module

private theorem quadraticRepresentation_of_unit (x : E) : P.quadraticRepresentation P.unit x = x := by
  simp only [quadraticRepresentation_apply, P.unit_left, two_smul, add_sub_cancel_left]

theorem idempotentReflection_involutive (p : E) (hp : P.product p p = p) (x : E) :
    P.idempotentReflection p (P.idempotentReflection p x) = x := by
  have h := P.quadraticRepresentation_fundamental ((2 : ℝ) • p - P.unit) P.unit x
  change P.quadraticRepresentation (P.idempotentReflection p P.unit) x =
    P.idempotentReflection p (P.quadraticRepresentation P.unit (P.idempotentReflection p x)) at h
  rwa [P.idempotentReflection_unit p hp, P.quadraticRepresentation_of_unit,
    P.quadraticRepresentation_of_unit, eq_comm] at h

theorem idempotentReflection_quadratic (p a x : E) :
    P.quadraticRepresentation (P.idempotentReflection p a) x =
      P.idempotentReflection p (P.quadraticRepresentation a (P.idempotentReflection p x)) :=
  P.quadraticRepresentation_fundamental ((2 : ℝ) • p - P.unit) a x

theorem idempotentReflection_complement (p : E) (hp : P.product p p = p) (x : E) :
    P.idempotentReflection p (P.unit - x) = P.unit - P.idempotentReflection p x := by
  rw [map_sub, P.idempotentReflection_unit p hp]

theorem idempotentReflection_product (p : E) (hp : P.product p p = p) (x y : E) :
    P.idempotentReflection p (P.product x y) =
      P.product (P.idempotentReflection p x) (P.idempotentReflection p y) := by
  have hsq (z : E) : P.product (P.idempotentReflection p z) (P.idempotentReflection p z) =
      P.idempotentReflection p (P.product z z) := by
    have h := P.idempotentReflection_quadratic p z P.unit
    rwa [quadraticRepresentation_unit, P.idempotentReflection_unit p hp,
      quadraticRepresentation_unit] at h
  have hxy := hsq (x + y)
  simp only [map_add, LinearMap.add_apply, P.commutative (P.idempotentReflection p y) (P.idempotentReflection p x),
    P.commutative y x, hsq] at hxy
  linear_combination (norm := module) (-1 / 2 : ℝ) • hxy

theorem idempotentReflection_idempotent (p : E) (hp : P.product p p = p) {q : E}
    (hq : P.product q q = q) :
    P.product (P.idempotentReflection p q) (P.idempotentReflection p q) = P.idempotentReflection p q := by
  rw [← P.idempotentReflection_product p hp, hq]

theorem idempotentReflection_primitive (p : E) (hp : P.product p p = p) {q : E}
    (hq : P.IsPrimitive q) : P.IsPrimitive (P.idempotentReflection p q) := by
  let R := P.idempotentReflection p
  have hinv (x : E) : R (R x) = x := P.idempotentReflection_involutive p hp x
  have hzero {x : E} (hx : R x = 0) : x = 0 := by rw [← hinv x, hx, map_zero]
  refine ⟨P.idempotentReflection_idempotent p hp hq.1, fun h => hq.2.1 (hzero h), ?_⟩
  intro r s hr hs hrs hsum
  have hrs' : P.product (R r) (R s) = 0 := by
    rw [← P.idempotentReflection_product p hp, hrs, map_zero]
  have hsum' : R r + R s = q := by rw [← map_add, hsum, hinv]
  exact (hq.2.2 (R r) (R s) (P.idempotentReflection_idempotent p hp hr)
    (P.idempotentReflection_idempotent p hp hs) hrs' hsum').imp hzero hzero

end AlbertSequential.UnitalJordanProduct
