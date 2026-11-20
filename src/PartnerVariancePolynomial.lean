/- SPDX-License-Identifier: Apache-2.0 -/
module
public import PartnerVariance
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace AlbertSequential.PartnerVariance

/-- The three affine entries correspond to xyz, xzy and yxz in the CC row.
The other three entries are obtained by the paper's reversal identities. -/
def signedCCRow (x y z a b c : ℝ) : ℝ :=
  a - (2*y^2 - a) - b + (2*y*z - b) - c + (2*x*y - c)

def quadraticCCRow (x y z : ℝ) : ℝ := -2*y^2 + 2*y*z + 2*x*y

theorem signedCCRow_split (x y z a b c : ℝ) :
    signedCCRow x y z a b c = 2*(a-b-c) + quadraticCCRow x y z := by
  unfold signedCCRow quadraticCCRow
  ring

def quadraticCC (x y z : ℝ) : ℝ :=
  quadraticCCRow x y z + quadraticCCRow x z y + quadraticCCRow y x z +
  quadraticCCRow y z x + quadraticCCRow z x y + quadraticCCRow z y x

theorem quadraticCC_eq (x y z : ℝ) :
    quadraticCC x y z = 4*(x+y+z)^2 - 8*(x^2+y^2+z^2) := by
  unfold quadraticCC quadraticCCRow
  ring

theorem quadraticCC_variance (x y z : ℝ) :
    4/3*(x+y+z)^2 - quadraticCC x y z =
      8/3*((x-y)^2 + (y-z)^2 + (z-x)^2) := by
  rw [quadraticCC_eq]
  ring

theorem quadraticCC_le (x y z : ℝ) : quadraticCC x y z ≤ 4/3*(x+y+z)^2 := by
  have h := quadraticCC_variance x y z
  nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]

theorem quadraticCC_eq_max_iff (x y z : ℝ) :
    quadraticCC x y z = 4/3*(x+y+z)^2 ↔ x = y ∧ y = z := by
  constructor
  · intro h
    have e := quadraticCC_variance x y z
    rw [h,sub_self] at e
    constructor <;> nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
  · rintro ⟨rfl,rfl⟩
    rw [quadraticCC_eq]
    ring

theorem printed_partner_variance :
    quadraticCC (1/27) (1/27) (1/27) = 12/729 ∧
    quadraticCC (1/27) 0 (2/27) = -4/729 ∧
    quadraticCC (1/27) (2/27) 0 = -4/729 ∧
    (-4/27 : ℝ) + (16-2*36) * ((-4/729) - 12/729) = 788/729 := by
  norm_num [quadraticCC_eq]

end AlbertSequential.PartnerVariance
