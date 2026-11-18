/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealJordanPeirce

/-! Algebraic Peirce-zero/half identities from the ordinary Jordan laws.
This module is independent of Albert coordinates, positivity and geometry.
The half-space action of the zero corner is an actual Jordan representation. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsCommJordan E]

omit [SMulCommClass ℝ E E] in
theorem idempotent_mul_zero_commute (p x z : E) (hp : p * p = p) (hpx : p * x = 0) :
    p * (x * z) = x * (p * z) := by
  have hxp : x * p = 0 := (mul_comm x p).trans hpx
  have h := cyclic_mulLeft_commutator p p x z
  simp only [hp, hpx, hxp, mul_zero, zero_mul, sub_self, zero_add, add_zero] at h
  exact (sub_eq_zero.mp h).symm

omit [SMulCommClass ℝ E E] in
theorem peirceZero_product (p x y : E) (hp : p * p = p)
    (hx : p * x = 0) (hy : p * y = 0) : p * (x * y) = 0 := by
  rw [idempotent_mul_zero_commute p x y hp hx, hy, mul_zero]

theorem peirceHalf_product (p x h : E) (hp : p * p = p)
    (hx : p * x = 0) (hh : p * h = (1 / 2 : ℝ) • h) :
    p * (x * h) = (1 / 2 : ℝ) • (x * h) := by
  rw [idempotent_mul_zero_commute p x h hp hx, hh, mul_smul_comm]

theorem peirceHalf_square_action (p x h : E) (hp : p * p = p)
    (hx : p * x = 0) (hh : p * h = (1 / 2 : ℝ) • h) :
    (x * x) * h = (2 : ℝ) • (x * (x * h)) := by
  have hxp : x * p = 0 := (mul_comm x p).trans hx
  have hsquare : (x * x) * p = 0 := by
    rw [mul_comm (x * x) p]
    exact peirceZero_product p x x hp hx hx
  have hxhp : (x * h) * p = (1 / 2 : ℝ) • (x * h) := by
    rw [mul_comm (x * h) p]
    exact peirceHalf_product p x h hp hx hh
  have hhp : h * p = (1 / 2 : ℝ) • h := (mul_comm h p).trans hh
  have hhxp : (h * x) * p = (1 / 2 : ℝ) • (x * h) := by
    rw [mul_comm h x]
    exact hxhp
  have h := cyclic_mulLeft_commutator x x h p
  simp only [hxp, hsquare, hxhp, hhxp, hhp, mul_zero, sub_zero,
    zero_sub, mul_smul_comm] at h
  linear_combination (norm := module) (-2 : ℝ) • h

theorem peirceHalf_jordan_action (p x y h : E) (hp : p * p = p)
    (hx : p * x = 0) (hy : p * y = 0) (hh : p * h = (1 / 2 : ℝ) • h) :
    (x * y) * h = x * (y * h) + y * (x * h) := by
  have hxy : p * (x + y) = 0 := by rw [mul_add, hx, hy, add_zero]
  have hs := peirceHalf_square_action p (x + y) h hp hxy hh
  have hxx := peirceHalf_square_action p x h hp hx hh
  have hyy := peirceHalf_square_action p y h hp hy hh
  simp only [mul_add, add_mul, smul_add, mul_comm y x] at hs
  linear_combination (norm := module) (1 / 2 : ℝ) • hs - (1 / 2 : ℝ) • hxx - (1 / 2 : ℝ) • hyy

def polarizedQuadratic (a b : E) : Module.End ℝ E :=
  quadraticRepresentation (a + b) - quadraticRepresentation a - quadraticRepresentation b

omit [IsCommJordan E] in
theorem polarizedQuadratic_apply (a b x : E) :
    polarizedQuadratic a b x =
      (2 : ℝ) • (a * (b * x) + b * (a * x) - (a * b) * x) := by
  simp only [polarizedQuadratic, LinearMap.sub_apply, quadRep_apply, mul_add, add_mul,
    smul_add, mul_comm b a]
  module

theorem polarizedQuadratic_zero_on_peirceZero (p b x : E)
    (hp : p * p = p) (hx : p * x = 0) : polarizedQuadratic p b x = 0 := by
  rw [polarizedQuadratic_apply, hx, mul_zero]
  have h := idempotent_mul_zero_commute p x b hp hx
  rw [mul_comm x b] at h
  rw [h, mul_comm x (p * b), add_zero, sub_self, smul_zero]

theorem polarizedQuadratic_fundamental (a b c : E) :
    polarizedQuadratic (quadraticRepresentation a b) (quadraticRepresentation a c) =
      (quadraticRepresentation a).comp
        ((polarizedQuadratic b c).comp (quadraticRepresentation a)) := by
  ext z
  change quadraticRepresentation (quadraticRepresentation a b + quadraticRepresentation a c) z -
      quadraticRepresentation (quadraticRepresentation a b) z -
      quadraticRepresentation (quadraticRepresentation a c) z =
    quadraticRepresentation a (polarizedQuadratic b c (quadraticRepresentation a z))
  rw [← map_add, quadraticRepresentation_fundamental_apply,
    quadraticRepresentation_fundamental_apply, quadraticRepresentation_fundamental_apply]
  simp only [polarizedQuadratic, LinearMap.sub_apply, map_sub]

end AlbertSequential.RealJordan
