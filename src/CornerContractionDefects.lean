/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Basic.Real.Basic

/-! Denominator-free exact corner contractions with every R1--R3 error retained.
There is no ambient unit, involution, dimension, positivity or zero-error input. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
section RawDefects
variable {A : Type*} [NonUnitalRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

def pairDefectElement (X Y : A) (a : ℝ) : A := X * Y * X - a • X
def triangleDefectElement (X Y Z : A) (r : ℝ) : A :=
  X * (Y * Z + Z * Y) * X - (2 * r) • X
def tripleDefectElement (J K L M : A) (q : ℝ) : A :=
  J * (K * L * M + M * L * K) * J - (2 * q) • J

theorem reverseProduct_defect_expansion (J K L : A) (hJJ : J * J = J) (a t b : ℝ) :
    (J * L * K * J) * (J * K * L * J) - (a * t * b) • J =
      J * L * pairDefectElement K J a * L * J +
        a • (J * pairDefectElement L K t * J) + (a * t) • pairDefectElement J L b := by
  have hJx (x : A) : J * (J * x) = J * x := by rw [← mul_assoc, hJJ]
  simp only [pairDefectElement, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, mul_assoc, hJx]
  module

theorem mixedProduct_defect_expansion (J K L M : A) (hJJ : J * J = J) (b q : ℝ) :
    (J * K * L * J) * (J * L * M * J) + (J * M * L * J) * (J * L * K * J) -
        (2 * b * q) • J =
      J * K * pairDefectElement L J b * M * J +
        J * M * pairDefectElement L J b * K * J + b • tripleDefectElement J K L M q := by
  have hJx (x : A) : J * (J * x) = J * x := by rw [← mul_assoc, hJJ]
  simp only [pairDefectElement, tripleDefectElement, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, mul_assoc, hJx]
  module

theorem farFace_defect_expansion (J K L M : A) (hJJ : J * J = J) (a b c r : ℝ) :
    (J * K * L * J) * (J * L * M * J) * (J * M * K * J) +
        (J * K * M * J) * (J * M * L * J) * (J * L * K * J) - (2 * a * b * c * r) • J =
      J * K * L * J * L * pairDefectElement M J c * K * J +
        c • (J * K * pairDefectElement L J b * M * K * J) +
        J * K * M * J * M * pairDefectElement L J b * K * J +
        b • (J * K * pairDefectElement M J c * L * K * J) +
        (b * c) • (J * triangleDefectElement K L M r * J) +
        (2 * b * c * r) • pairDefectElement J K a := by
  have hJx (x : A) : J * (J * x) = J * x := by rw [← mul_assoc, hJJ]
  simp only [pairDefectElement, triangleDefectElement, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, mul_assoc, hJx]
  module

omit [SMulCommClass ℝ A A] in
theorem pairDefect_right_support (X Y : A) (hXX : X * X = X) (a : ℝ) :
    pairDefectElement X Y a * X = pairDefectElement X Y a := by
  simp only [pairDefectElement, sub_mul, smul_mul_assoc, mul_assoc, hXX]

omit [SMulCommClass ℝ A A] in
theorem triangleDefect_right_support (K L M : A) (hKK : K * K = K) (r : ℝ) :
    triangleDefectElement K L M r * K = triangleDefectElement K L M r := by
  simp only [triangleDefectElement, sub_mul, smul_mul_assoc, mul_assoc, hKK]

omit [SMulCommClass ℝ A A] in
theorem tripleDefect_right_support (J K L M : A) (hJJ : J * J = J) (q : ℝ) :
    tripleDefectElement J K L M q * J = tripleDefectElement J K L M q := by
  simp only [tripleDefectElement, sub_mul, smul_mul_assoc, mul_assoc, hJJ]

end RawDefects
end AlbertSequential
