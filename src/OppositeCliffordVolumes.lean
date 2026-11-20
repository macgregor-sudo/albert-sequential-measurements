/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

public section
noncomputable section

namespace AlbertSequential

abbrev QuaternionCliffordSectors := Quaternion ℝ × Quaternion ℝ

def oppositeCliffordGenerator (i : Fin 3) : QuaternionCliffordSectors :=
  ![ (⟨0, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩), (⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 0⟩),
    (⟨0, 0, 0, 1⟩, ⟨0, 0, 0, -1⟩) ] i

theorem oppositeCliffordGenerator_square (i : Fin 3) :
    oppositeCliffordGenerator i * oppositeCliffordGenerator i = -1 := by
  fin_cases i <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [oppositeCliffordGenerator, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

theorem oppositeCliffordGenerator_skew (i : Fin 3) :
    star (oppositeCliffordGenerator i) = -oppositeCliffordGenerator i := by
  fin_cases i <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [oppositeCliffordGenerator]

theorem oppositeCliffordGenerator_anti {i j : Fin 3} (h : i ≠ j) :
    oppositeCliffordGenerator i * oppositeCliffordGenerator j =
      -(oppositeCliffordGenerator j * oppositeCliffordGenerator i) := by
  fin_cases i <;> fin_cases j
  all_goals try exact (h rfl).elim
  all_goals apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [oppositeCliffordGenerator, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

theorem oppositeCliffordGenerator_unitary (i : Fin 3) :
    star (oppositeCliffordGenerator i) * oppositeCliffordGenerator i = 1 ∧
      oppositeCliffordGenerator i * star (oppositeCliffordGenerator i) = 1 := by
  rw [oppositeCliffordGenerator_skew, neg_mul, mul_neg, oppositeCliffordGenerator_square, neg_neg]
  exact ⟨rfl, rfl⟩

theorem oppositeCliffordGenerator_volume :
    oppositeCliffordGenerator 0 * oppositeCliffordGenerator 1 * oppositeCliffordGenerator 2 =
      ((-1 : Quaternion ℝ), 1) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [oppositeCliffordGenerator, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Left action on the direct sum of two quaternionic real vector spaces. -/
def oppositeCliffordAction (i : Fin 3) : Module.End ℝ QuaternionCliffordSectors where
  toFun x := oppositeCliffordGenerator i * x
  map_add' x y := mul_add _ x y
  map_smul' r x := mul_smul_comm r _ x

theorem oppositeCliffordAction_square (i : Fin 3) :
    oppositeCliffordAction i * oppositeCliffordAction i = -1 := by
  apply LinearMap.ext
  intro x
  change oppositeCliffordGenerator i * (oppositeCliffordGenerator i * x) = -x
  rw [← mul_assoc, oppositeCliffordGenerator_square, neg_one_mul]

theorem oppositeCliffordAction_anti {i j : Fin 3} (h : i ≠ j) :
    oppositeCliffordAction i * oppositeCliffordAction j =
      -(oppositeCliffordAction j * oppositeCliffordAction i) := by
  apply LinearMap.ext
  intro x
  change oppositeCliffordGenerator i * (oppositeCliffordGenerator j * x) =
    -(oppositeCliffordGenerator j * (oppositeCliffordGenerator i * x))
  rw [← mul_assoc, oppositeCliffordGenerator_anti h, neg_mul, mul_assoc]

theorem oppositeCliffordAction_nonScalar (r : ℝ) :
    oppositeCliffordAction 0 * oppositeCliffordAction 1 * oppositeCliffordAction 2 ≠
      r • (1 : Module.End ℝ QuaternionCliffordSectors) := by
  intro h
  have hOne := LinearMap.congr_fun h (1 : QuaternionCliffordSectors)
  change oppositeCliffordGenerator 0 * (oppositeCliffordGenerator 1 *
    (oppositeCliffordGenerator 2 * 1)) = r • (1 : QuaternionCliffordSectors) at hOne
  rw [mul_one, ← mul_assoc, oppositeCliffordGenerator_volume] at hOne
  have hPlus := congrArg (fun x : QuaternionCliffordSectors => x.1.re) hOne
  have hMinus := congrArg (fun x : QuaternionCliffordSectors => x.2.re) hOne
  change -1 = r * 1 at hPlus
  change 1 = r * 1 at hMinus
  rw [← hMinus] at hPlus
  norm_num at hPlus

end AlbertSequential
