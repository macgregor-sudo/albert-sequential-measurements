/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! The scalar degree-four Newton step in the printed quaternionic Schur proof. -/
@[expose] public section

open scoped BigOperators

namespace AlbertSequential.MatchingModels

/-- The fourth elementary coefficient as a polynomial in the four power sums. -/
noncomputable def schurNewtonFourth (p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  (p₁ ^ 4 - 6 * p₁ ^ 2 * p₂ + 3 * p₂ ^ 2 + 8 * p₁ * p₃ - 6 * p₄) / 24

/-- The fourth Newton power-sum recurrence in the convention of Appendix C.
The extra term compared with the cubic trace identity is `-4 e₄`. -/
theorem schurNewtonFourth_powerSum (u : Fin 4 → ℝ) :
    let p₁ := ∑ i, u i
    let p₂ := ∑ i, u i ^ 2
    let p₃ := ∑ i, u i ^ 3
    let p₄ := ∑ i, u i ^ 4
    let e₂ := (p₁ ^ 2 - p₂) / 2
    let e₃ := (p₁ ^ 3 - 3 * p₁ * p₂ + 2 * p₃) / 6
    let e₄ := ∏ i, u i
    p₄ = p₁ * p₃ - e₂ * p₂ + e₃ * p₁ - 4 * e₄ := by
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_zero]
  ring

/-- The top coefficient is the product of the four spectral values, with no
assumption of strict positivity or distinctness. -/
theorem schurNewtonFourth_eq_product (u : Fin 4 → ℝ) :
    schurNewtonFourth (∑ i, u i) (∑ i, u i ^ 2) (∑ i, u i ^ 3) (∑ i, u i ^ 4) =
      ∏ i, u i := by
  unfold schurNewtonFourth
  rw [schurNewtonFourth_powerSum u]
  ring

end AlbertSequential.MatchingModels
