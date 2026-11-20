/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

@[expose] public section

namespace AlbertSequential.FiveTest

structure AffinePlane (E : Type*) where
  constant : E
  x : E
  y : E

structure QuadraticPlane (E : Type*) where
  constant : E
  x : E
  y : E
  xx : E
  xy : E
  yy : E

namespace AffinePlane

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def eval (a : AffinePlane E) (x y : ℝ) : E :=
  a.constant + x • a.x + y • a.y

def scale (w : ℝ) (a : AffinePlane E) : AffinePlane E :=
  ⟨w • a.constant, w • a.x, w • a.y⟩

def add (a b : AffinePlane E) : AffinePlane E :=
  ⟨a.constant + b.constant, a.x + b.x, a.y + b.y⟩

theorem eval_scale (w : ℝ) (a : AffinePlane E) (x y : ℝ) :
    (a.scale w).eval x y = w • a.eval x y := by
  simp only [eval, scale]
  module

theorem eval_add (a b : AffinePlane E) (x y : ℝ) :
    (a.add b).eval x y = a.eval x y + b.eval x y := by
  simp only [eval, add]
  module

end AffinePlane

namespace QuadraticPlane

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]

def eval (a : QuadraticPlane E) (x y : ℝ) : E :=
  a.constant + x • a.x + y • a.y + x^2 • a.xx + (x*y) • a.xy + y^2 • a.yy

def sub (a b : QuadraticPlane E) : QuadraticPlane E :=
  ⟨a.constant - b.constant, a.x - b.x, a.y - b.y, a.xx - b.xx, a.xy - b.xy, a.yy - b.yy⟩

theorem eval_sub (a b : QuadraticPlane E) (x y : ℝ) :
    (a.sub b).eval x y = a.eval x y - b.eval x y := by
  simp only [eval, sub]
  module

def bind (R : E →ₗ[ℝ] F →ₗ[ℝ] G) (a : AffinePlane E) (b : AffinePlane F) : QuadraticPlane G :=
  ⟨R a.constant b.constant, R a.x b.constant + R a.constant b.x,
    R a.y b.constant + R a.constant b.y, R a.x b.x, R a.x b.y + R a.y b.x, R a.y b.y⟩

theorem eval_bind (R : E →ₗ[ℝ] F →ₗ[ℝ] G) (a : AffinePlane E) (b : AffinePlane F) (x y : ℝ) :
    (bind R a b).eval x y = R (a.eval x y) (b.eval x y) := by
  simp only [eval, bind, AffinePlane.eval, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

def sumAndScaleFirst (a b : AffinePlane E) : QuadraticPlane E :=
  ⟨a.constant, a.x + b.constant, a.y, b.x, b.y, 0⟩

theorem eval_sumAndScaleFirst (a b : AffinePlane E) (x y : ℝ) :
    (sumAndScaleFirst a b).eval x y = a.eval x y + x • b.eval x y := by
  simp only [eval, sumAndScaleFirst, AffinePlane.eval]
  module

theorem zero_on_circle (a : QuadraticPlane E)
    (p1 : a.eval 1 0 = 0) (p2 : a.eval (-1) 0 = 0)
    (p3 : a.eval 0 1 = 0) (p4 : a.eval 0 (-1) = 0)
    (p5 : a.eval (3/5) (4/5) = 0) (x y : ℝ) (hxy : x^2 + y^2 = 1) :
    a.eval x y = 0 := by
  have h1 : a.constant + a.x + a.xx = 0 := by simpa [eval] using p1
  have h2 : a.constant + (-a.x) + a.xx = 0 := by norm_num [eval] at p2 ⊢; exact p2
  have h3 : a.constant + a.y + a.yy = 0 := by simpa [eval] using p3
  have h4 : a.constant + (-a.y) + a.yy = 0 := by norm_num [eval] at p4 ⊢; exact p4
  have hx0 : a.x = 0 := by
    calc
      a.x = (1/2 : ℝ) • ((a.constant + a.x + a.xx) - (a.constant + (-a.x) + a.xx)) := by module
      _ = 0 := by rw [h1,h2,sub_zero,smul_zero]
  have hy0 : a.y = 0 := by
    calc
      a.y = (1/2 : ℝ) • ((a.constant + a.y + a.yy) - (a.constant + (-a.y) + a.yy)) := by module
      _ = 0 := by rw [h3,h4,sub_zero,smul_zero]
  have hxx : a.xx = -a.constant := by
    rw [hx0, add_zero] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hyy : a.yy = -a.constant := by
    rw [hy0, add_zero] at h3
    exact eq_neg_of_add_eq_zero_right h3
  have hxy0 : a.xy = 0 := by
    calc
      a.xy = (25/12 : ℝ) • a.eval (3/5) (4/5) := by
        simp only [eval, hx0, hy0, hxx, hyy]
        module
      _ = 0 := by rw [p5, smul_zero]
  calc
    a.eval x y = (1 - x^2 - y^2) • a.constant := by
      simp only [eval,hx0,hy0,hxx,hyy,hxy0]
      module
    _ = 0 := by rw [show (1 : ℝ) - x^2 - y^2 = 0 by linarith, zero_smul]

end QuadraticPlane

end AlbertSequential.FiveTest
