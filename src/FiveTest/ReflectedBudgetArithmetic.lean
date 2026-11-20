/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.SignedReflectionTransfer
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace AlbertSequential.FiveTest

variable {ι : Type*}

private def coefficientWeight (terms : List (ℤ × Word ι)) : ℕ :=
  (terms.map fun t => t.1.natAbs).sum

private theorem coefficientWeight_append (u v : List (ℤ × Word ι)) :
    coefficientWeight (u ++ v) = coefficientWeight u + coefficientWeight v := by
  simp [coefficientWeight]

private theorem coefficientWeight_prefix (a : Outcome ι) (u : List (ℤ × Word ι)) :
    coefficientWeight (prefixReflectionTerms a u) = coefficientWeight u := by
  simp [coefficientWeight, prefixReflectionTerms, List.map_map, Function.comp_def]

private theorem coefficientWeight_scale (a : ℤ) (u : List (ℤ × Word ι)) :
    coefficientWeight (scaleReflectionTerms a u) = a.natAbs * coefficientWeight u := by
  induction u with
  | nil => simp [coefficientWeight, scaleReflectionTerms]
  | cons t u ih =>
    simpa [coefficientWeight, scaleReflectionTerms, Int.natAbs_mul, Nat.mul_add] using
      congrArg (a.natAbs * t.1.natAbs + ·) ih

private theorem coefficientWeight_expansion (c : ι) (steps : List (Option (Outcome ι))) :
    coefficientWeight (signedReflectionExpansion c steps) = 5 ^ (steps.countP Option.isNone) := by
  induction steps with
  | nil => rfl
  | cons a steps ih =>
    cases a with
    | some a =>
      simp only [signedReflectionExpansion, coefficientWeight_prefix, List.countP_cons,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ih]
    | none =>
      simp only [signedReflectionExpansion, coefficientWeight_append, coefficientWeight_scale,
        coefficientWeight_prefix, List.countP_cons, Option.isNone_none, ↓reduceIte, ih]
      norm_num [pow_succ]
      ring

/-- The absolute coefficient sum of the literal signed expansion, before merging words. -/
theorem signedReflectionTerms_sumNatAbs (c : ι) (w : MarkedWord ι) :
    ((signedReflectionTerms c w).map fun t => t.1.natAbs).sum = 5 ^ reflectionSwitchCount false w := by
  change coefficientWeight (signedReflectionExpansion c (reflectionSteps false w)) = _
  rw [coefficientWeight_expansion, reflectionSteps_count]

private theorem reflectionSwitchCount_le_length (prev : Bool) (w : MarkedWord ι) :
    reflectionSwitchCount prev w ≤ w.length := by
  induction w generalizing prev with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨⟨i, mark⟩, b⟩
    have h := ih mark
    simp only [reflectionSwitchCount, List.length_cons]
    split <;> omega

theorem signedReflectionTerms_sumNatAbs_budget (c : ι) (w : MarkedWord ι)
    (h : w.length + reflectionSwitchCount false w ≤ 10) :
    ((signedReflectionTerms c w).map fun t => t.1.natAbs).sum ≤ 5^5 := by
  rw [signedReflectionTerms_sumNatAbs]
  apply Nat.pow_le_pow_right (by decide)
  have hc := reflectionSwitchCount_le_length false w
  omega

/-- The scalar upper bound obtained from the two printed worst-entry counters. -/
theorem reflected_companion_coefficient_budget :
    let T : ℚ := (713 / 9)^2 * (17 / 2)
    let Y : ℚ := (713 / 9)^2 * (97 / 2)
    T + 11 / 3888 + (2 * 1944 / 11) * Y^2 < 32750000000000 := by
  norm_num

/-- The printed robust threshold after applying the signed reflection cost. -/
theorem reflected_companion_margin_arithmetic :
    (9 / 10^21 : ℚ) < (11 / 11664) / (5^5 * 32750000000000) := by
  norm_num

end AlbertSequential.FiveTest
