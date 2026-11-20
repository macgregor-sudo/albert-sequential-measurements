/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetAssociators
public import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic.Abel

/-! The degree-three octonionic coefficient convolution and its degree-by-degree associator. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

/-- Four octonion coefficients, with degrees zero through three in order. -/
abbrev OctonionJetCoefficients := Fin 4 → Octonion

/-- The coefficient convolution modulo the fourth power of the formal parameter. -/
def octonionJetProduct (x y : OctonionJetCoefficients) : OctonionJetCoefficients :=
  ![octonionMul (x 0) (y 0),
    octonionMul (x 0) (y 1) + octonionMul (x 1) (y 0),
    octonionMul (x 0) (y 2) + octonionMul (x 1) (y 1) + octonionMul (x 2) (y 0),
    octonionMul (x 0) (y 3) + octonionMul (x 1) (y 2) + octonionMul (x 2) (y 1) +
      octonionMul (x 3) (y 0)]

def octonionJetAssociator (x y z : OctonionJetCoefficients) : OctonionJetCoefficients :=
  octonionJetProduct (octonionJetProduct x y) z - octonionJetProduct x (octonionJetProduct y z)

theorem octonionJetAssociator_degreeZero (x y z : OctonionJetCoefficients) :
    octonionJetAssociator x y z 0 = octAssociator (x 0) (y 0) (z 0) := rfl

theorem octonionJetAssociator_degreeOne (x y z : OctonionJetCoefficients) :
    octonionJetAssociator x y z 1 =
      octAssociator (x 0) (y 0) (z 1) + octAssociator (x 0) (y 1) (z 0) +
      octAssociator (x 1) (y 0) (z 0) := by
  simp [octonionJetAssociator, octonionJetProduct, octAssociator, octonionMul_add_left,
    octonionMul_add_right]
  abel

theorem octonionJetAssociator_degreeTwo (x y z : OctonionJetCoefficients) :
    octonionJetAssociator x y z 2 =
      octAssociator (x 0) (y 0) (z 2) + octAssociator (x 0) (y 1) (z 1) +
      octAssociator (x 0) (y 2) (z 0) + octAssociator (x 1) (y 0) (z 1) +
      octAssociator (x 1) (y 1) (z 0) + octAssociator (x 2) (y 0) (z 0) := by
  simp [octonionJetAssociator, octonionJetProduct, octAssociator, octonionMul_add_left,
    octonionMul_add_right]
  abel

theorem octonionJetAssociator_degreeThree (x y z : OctonionJetCoefficients) :
    octonionJetAssociator x y z 3 =
      octAssociator (x 0) (y 0) (z 3) + octAssociator (x 0) (y 1) (z 2) +
      octAssociator (x 0) (y 2) (z 1) + octAssociator (x 0) (y 3) (z 0) +
      octAssociator (x 1) (y 0) (z 2) + octAssociator (x 1) (y 1) (z 1) +
      octAssociator (x 1) (y 2) (z 0) + octAssociator (x 2) (y 0) (z 1) +
      octAssociator (x 2) (y 1) (z 0) + octAssociator (x 3) (y 0) (z 0) := by
  simp [octonionJetAssociator, octonionJetProduct, octAssociator, octonionMul_add_left,
    octonionMul_add_right]
  abel

/-- With real constant coefficients, degree three is the first possible associator term. -/
theorem octonionJetAssociator_realBase (x y z : OctonionJetCoefficients) (a b c : ℝ)
    (hx : x 0 = octonionScalar a) (hy : y 0 = octonionScalar b) (hz : z 0 = octonionScalar c) :
    octonionJetAssociator x y z 0 = 0 ∧ octonionJetAssociator x y z 1 = 0 ∧
      octonionJetAssociator x y z 2 = 0 ∧
      octonionJetAssociator x y z 3 = octAssociator (x 1) (y 1) (z 1) := by
  simp only [octonionJetAssociator_degreeZero, octonionJetAssociator_degreeOne,
    octonionJetAssociator_degreeTwo, octonionJetAssociator_degreeThree, hx, hy, hz,
    octAssociator_scalar_left, octAssociator_scalar_mid, octAssociator_scalar_right,
    zero_add, add_zero, and_self]

/-- With quaternionic constant coefficients, degree zero is associative, and degree one
is exactly the sum of the three placements of the first-order input. -/
theorem octonionJetAssociator_quaternionicBase (x y z : OctonionJetCoefficients)
    (a b c : Quaternion ℝ) (hx : x 0 = (a, 0)) (hy : y 0 = (b, 0)) (hz : z 0 = (c, 0)) :
    octonionJetAssociator x y z 0 = 0 ∧
      octonionJetAssociator x y z 1 ∈ quaternionicAssociatorSpace := by
  rw [octonionJetAssociator_degreeZero, octonionJetAssociator_degreeOne, hx, hy, hz]
  exact ⟨octAssociator_standard_quaternionic a b c, Submodule.add_mem _
    (Submodule.add_mem _ (octAssociator_of_two_quaternionic a b (z 1)).1
      (octAssociator_of_two_quaternionic a c (y 1)).2.1)
    (octAssociator_of_two_quaternionic b c (x 1)).2.2⟩

end AlbertSequential.AppF
