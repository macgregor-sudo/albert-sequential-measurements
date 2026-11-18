/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE (the Apache-2.0 text, identical to Physlib's LICENSE).
Authors: Tom Ole Diem

Adapted from Physlib, https://github.com/leanprover-community/physlib, commit
08a6c1b5b8e6db340547142c3f7047635128c786 (the revision recorded for this development's Physlib
sources), files PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Operator.lean and
PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Quadratic/Triple.lean.
Adapted declarations: mulLeft, mulLeft_apply, quadRep, quadRep_apply, innerDerivation,
innerDerivation_apply, innerDerivation_swap (Operator.lean); jordanTriple, jordanTriple_outer_comm,
jordanTriple_diag (Quadratic/Triple.lean).
Modifications: `mulLeft` and `quadRep` are renamed leftMultiplication and quadraticRepresentation;
`a * a` replaces the power `a ^[2]`; the ambient class is NonUnitalNonAssocCommRing; the `_apply`
lemmas are proved by `rfl`; smul_mul_real and the quadraticRepresentation_{zero, smul, one,
apply_one} lemmas are added. No Physlib import remains. Licence: Apache-2.0. See
THIRD_PARTY_NOTICES.
Thanks to Tom Ole Diem and the Physlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to
Robert Hooke, 1676.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

/-! Explicit quadratic and triple operators for a real commutative Jordan algebra.
No unit, order, finite dimension, trace, or fundamental-formula axiom is assumed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [Module ℝ E] [SMulCommClass ℝ E E]

def leftMultiplication (a : E) : E →ₗ[ℝ] E where
  toFun := fun x => a * x
  map_add' := mul_add a
  map_smul' := fun r x => mul_smul_comm r a x

@[simp] theorem mulLeft_apply (a x : E) : leftMultiplication a x = a*x := rfl

/-- The product is real linear in its first argument as well, by commutativity. -/
theorem smul_mul_real (r : ℝ) (a b : E) : (r • a)*b = r • (a*b) := by
  rw [mul_comm (r • a) b, mul_smul_comm, mul_comm b a]

def quadraticRepresentation (a : E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • ((leftMultiplication a).comp (leftMultiplication a)) -
    leftMultiplication (a*a)

@[simp] theorem quadRep_apply (a x : E) :
    quadraticRepresentation a x = (2 : ℝ) • (a*(a*x)) - (a*a)*x := rfl

def innerDerivation (a b : E) : E →ₗ[ℝ] E :=
  (leftMultiplication a).comp (leftMultiplication b) -
    (leftMultiplication b).comp (leftMultiplication a)

@[simp] theorem innerDerivation_apply (a b x : E) :
    innerDerivation a b x = a*(b*x)-b*(a*x) := rfl

theorem innerDerivation_swap (a b : E) :
    innerDerivation a b = -innerDerivation b a := by
  ext x
  simp only [innerDerivation_apply, LinearMap.neg_apply]
  abel

def jordanTriple (a b c : E) : E := a*(b*c)+c*(b*a)-(a*c)*b

omit [Module ℝ E] [SMulCommClass ℝ E E] in
theorem jordanTriple_outer_comm (a b c : E) :
    jordanTriple a b c = jordanTriple c b a := by
  rw [jordanTriple, jordanTriple, mul_comm a c]
  abel

theorem jordanTriple_diag (a b : E) :
    jordanTriple a b a = quadraticRepresentation a b := by
  rw [jordanTriple, quadRep_apply, mul_comm b a]
  module

@[simp] theorem quadraticRepresentation_zero :
    quadraticRepresentation (0 : E)=0 := by
  ext x
  simp only [quadRep_apply, zero_mul, smul_zero, sub_zero, LinearMap.zero_apply]

theorem quadraticRepresentation_smul (r : ℝ) (a : E) :
    quadraticRepresentation (r • a)=(r*r) • quadraticRepresentation a := by
  ext x
  simp only [quadRep_apply, smul_mul_real, mul_smul_comm, smul_smul,
    LinearMap.smul_apply, smul_sub]
  module

section Unit
variable {F : Type*} [NonAssocCommRing F] [Module ℝ F] [SMulCommClass ℝ F F]

@[simp] theorem quadraticRepresentation_one :
    quadraticRepresentation (1 : F)=LinearMap.id := by
  ext x
  simp only [quadRep_apply, one_mul, LinearMap.id_apply, two_smul]
  abel

@[simp] theorem quadraticRepresentation_apply_one (a : F) :
    quadraticRepresentation a (1 : F)=a*a := by
  simp only [quadRep_apply, mul_one, two_smul]
  abel

end Unit

end AlbertSequential.RealJordan
