/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertOperatorAlgebra
public import Mathlib.Algebra.Star.Subalgebra

/-! The concrete real operator algebra commuting with two actual right
quaternion scalar operators. Full right-Hilbert correspondence is separate. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

/-- I and J encode right multiplication by i and j. Composition is in reverse
scalar order: right multiplication by k is J*I, not I*J. -/
structure QuaternionicOperatorStructure where
  rightI : H →L[ℝ] H
  rightJ : H →L[ℝ] H
  rightI_sq : rightI * rightI = -1
  rightJ_sq : rightJ * rightJ = -1
  anticommute : rightI * rightJ = -(rightJ * rightI)
  star_rightI : star rightI = -rightI
  star_rightJ : star rightJ = -rightJ

namespace QuaternionicOperatorStructure
variable {H}

def rightK (Q : QuaternionicOperatorStructure H) : H →L[ℝ] H := Q.rightJ * Q.rightI

theorem rightI_mul_rightJ (Q : QuaternionicOperatorStructure H) :
    Q.rightI * Q.rightJ = -Q.rightK := Q.anticommute

theorem rightJ_mul_rightI (Q : QuaternionicOperatorStructure H) :
    Q.rightJ * Q.rightI = Q.rightK := rfl

theorem star_rightK (Q : QuaternionicOperatorStructure H) :
    star Q.rightK = -Q.rightK := by
  simp only [rightK, star_mul, Q.star_rightI, Q.star_rightJ, neg_mul_neg]
  exact Q.anticommute

theorem rightI_star_mul (Q : QuaternionicOperatorStructure H) :
    star Q.rightI * Q.rightI = 1 := by
  rw [Q.star_rightI, neg_mul, Q.rightI_sq, neg_neg]

theorem rightJ_star_mul (Q : QuaternionicOperatorStructure H) :
    star Q.rightJ * Q.rightJ = 1 := by
  rw [Q.star_rightJ, neg_mul, Q.rightJ_sq, neg_neg]

/-- The star centralizer includes adjoints by construction. For these skew
generators membership is exactly ordinary commutation with I and J. -/
def operatorAlgebra (Q : QuaternionicOperatorStructure H) :
    StarSubalgebra ℝ (H →L[ℝ] H) :=
  StarSubalgebra.centralizer ℝ {Q.rightI, Q.rightJ}

theorem mem_operatorAlgebra_iff (Q : QuaternionicOperatorStructure H)
    (T : H →L[ℝ] H) :
    T ∈ Q.operatorAlgebra ↔
      Q.rightI * T = T * Q.rightI ∧ Q.rightJ * T = T * Q.rightJ := by
  rw [operatorAlgebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h Q.rightI (by simp)).1, (h Q.rightJ (by simp)).1⟩
  · rintro ⟨hI, hJ⟩ S hS
    rcases (show S = Q.rightI ∨ S = Q.rightJ by simpa using hS) with rfl | rfl
    · exact ⟨hI, by simpa only [Q.star_rightI, neg_mul, mul_neg] using congrArg Neg.neg hI⟩
    · exact ⟨hJ, by simpa only [Q.star_rightJ, neg_mul, mul_neg] using congrArg Neg.neg hJ⟩

def operatorValue (Q : QuaternionicOperatorStructure H) :
    Q.operatorAlgebra →⋆ₐ[ℝ] (H →L[ℝ] H) := Q.operatorAlgebra.subtype

theorem operatorValue_injective (Q : QuaternionicOperatorStructure H) :
    Function.Injective Q.operatorValue := Subtype.val_injective

theorem operatorValue_mul_apply (Q : QuaternionicOperatorStructure H)
    (S T : Q.operatorAlgebra) (x : H) :
    Q.operatorValue (S * T) x = Q.operatorValue S (Q.operatorValue T x) := rfl

theorem operatorValue_one_apply (Q : QuaternionicOperatorStructure H) (x : H) :
    Q.operatorValue 1 x = x := rfl

theorem operatorValue_star (Q : QuaternionicOperatorStructure H)
    (T : Q.operatorAlgebra) :
    Q.operatorValue (star T) = ContinuousLinearMap.adjoint (Q.operatorValue T) := rfl

theorem operatorValue_real_smul (Q : QuaternionicOperatorStructure H)
    (r : ℝ) (T : Q.operatorAlgebra) :
    Q.operatorValue (r • T) = r • Q.operatorValue T := rfl

theorem operatorValue_star_mul_positive (Q : QuaternionicOperatorStructure H)
    (T : Q.operatorAlgebra) : (Q.operatorValue (star T * T)).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self (Q.operatorValue T)

end QuaternionicOperatorStructure
end AlbertSequential
