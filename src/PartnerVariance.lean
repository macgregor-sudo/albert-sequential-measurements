/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

@[expose] public section
namespace AlbertSequential.PartnerVariance

/-- Exact real coordinates a+b√2 for the two quaternionic partners of M. -/
abbrev R := QuadraticAlgebra ℚ 2 0
abbrev Q := Quaternion R
abbrev V := Fin 3 → Q

def c (a b : ℚ) : R := ⟨a,b⟩
def ii : Q := ⟨0,1,0,0⟩
def jj : Q := ⟨0,0,1,0⟩
def base : V := ![1,0,0]
def col (s : Bool) (x : Fin 3) : V :=
  ![(![1,(c 0 1 : Q),0] : V), ![1,ii,1],
    ![1,jj,(if s then (c 0 (1/2) : Q) else (c 0 (-1/2) : Q)) * (ii+jj)]] x

/-- Quaternionic column projection v(v* u)/3. All three columns have squared norm three. -/
def proj (s : Bool) (x : Fin 3) (u : V) : V :=
  let v := col s x
  let a := star (v 0)*u 0 + star (v 1)*u 1 + star (v 2)*u 2
  fun i => (c (1/3) 0 : Q) * (v i * a)

def signed (f : Fin 3 → Fin 3 → Fin 3 → V) : V :=
  f 0 1 2 + f 1 2 0 + f 2 0 1 - f 0 2 1 - f 2 1 0 - f 1 0 2

def phi (s : Bool) : V :=
  let H x y z := proj s z (proj s y (proj s x base))
  let C x y z := (![H x y z 0,0,0] : V)
  let T x y z := proj s x (H x y z)
  4 • signed C + 10 • signed T - 9 • signed H

def squaredNorm (u : V) : R := Quaternion.normSq (u 0) + Quaternion.normSq (u 1) + Quaternion.normSq (u 2)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem partner_phi_squaredNorm (s : Bool) : squaredNorm (phi s) = c (788/729) 0 := by
  cases s <;> decide +kernel

end AlbertSequential.PartnerVariance
