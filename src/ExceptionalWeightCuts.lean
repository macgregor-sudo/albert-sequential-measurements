/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Linarith

/-! Total and maximum weight cuts for states on direct sums.

The weight of a state in a summand is its evaluation on the central unit of
that summand. The total exceptional weight sums these linear evaluations.
When two summands exhaust the unit, their weights are nonnegative and sum to
one. States supported in the two individual summands give the two endpoints
of the weight simplex. -/

set_option autoImplicit false

@[expose] public section
namespace AlbertSequential

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The total-weight cut of a convex state set is convex. -/
theorem convex_totalWeightCut {ι : Type*} [Fintype ι] {states : Set E}
    (hstates : Convex ℝ states) (weight : ι → E →ₗ[ℝ] ℝ) (ε : ℝ) :
    Convex ℝ {ρ ∈ states | ε ≤ ∑ i, weight i ρ} := by
  let total : E →ₗ[ℝ] ℝ := ∑ i, weight i
  have halfSpace := convex_halfSpace_ge total.isLinear ε
  simpa only [total, LinearMap.sum_apply, Set.inter_ofPred_eq_sep] using hstates.inter halfSpace

/-- The maximum-weight cut for two summands. -/
def twoSummandMaxWeightCut (states : Set E) (left right : E →ₗ[ℝ] ℝ)
    (ε : ℝ) : Set E :=
  {ρ ∈ states | ε ≤ max (left ρ) (right ρ)}

/-- At or below one half, two weights summing to one always pass the cut. -/
theorem twoSummandMaxWeightCut_eq_states {states : Set E} {left right : E →ₗ[ℝ] ℝ}
    (hnormalized : ∀ ρ ∈ states, left ρ + right ρ = 1) {ε : ℝ} (hε : ε ≤ 1 / 2) :
    twoSummandMaxWeightCut states left right ε = states := by
  refine Set.Subset.antisymm (fun _ h => h.1) (fun ρ hρ => ⟨hρ, ?_⟩)
  have hleft := le_max_left (left ρ) (right ρ)
  have hright := le_max_right (left ρ) (right ρ)
  linarith [hnormalized ρ hρ]

/-- Above one, no pair of nonnegative normalized weights passes the cut. -/
theorem twoSummandMaxWeightCut_eq_empty {states : Set E} {left right : E →ₗ[ℝ] ℝ}
    (hnormalized : ∀ ρ ∈ states, left ρ + right ρ = 1)
    (hnonneg : ∀ ρ ∈ states, 0 ≤ left ρ ∧ 0 ≤ right ρ) {ε : ℝ} (hε : 1 < ε) :
    twoSummandMaxWeightCut states left right ε = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have ⟨hstate, hcut⟩ := hρ
  have ⟨hleft, hright⟩ := hnonneg ρ hstate
  have hmax : max (left ρ) (right ρ) ≤ 1 :=
    max_le (by linarith [hnormalized ρ hstate]) (by linarith [hnormalized ρ hstate])
  exact (not_le_of_gt hε) (hcut.trans hmax)

/-- Between one half and one, states supported in the two separate summands
pass the cut and their midpoint fails it. -/
theorem not_convex_twoSummandMaxWeightCut {states : Set E} {left right : E →ₗ[ℝ] ℝ}
    (hnormalized : ∀ ρ ∈ states, left ρ + right ρ = 1)
    {ρ₁ ρ₂ : E} (hρ₁ : ρ₁ ∈ states) (hρ₂ : ρ₂ ∈ states)
    (hleft : left ρ₁ = 1) (hright : right ρ₂ = 1)
    {ε : ℝ} (hhalf : 1 / 2 < ε) (hone : ε ≤ 1) :
    ¬ Convex ℝ (twoSummandMaxWeightCut states left right ε) := by
  intro hconvex
  have h₁ : ρ₁ ∈ twoSummandMaxWeightCut states left right ε :=
    ⟨hρ₁, (hone.trans_eq hleft.symm).trans (le_max_left _ _)⟩
  have h₂ : ρ₂ ∈ twoSummandMaxWeightCut states left right ε :=
    ⟨hρ₂, (hone.trans_eq hright.symm).trans (le_max_right _ _)⟩
  have hmid := hconvex h₁ h₂ (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  have hright₁ : right ρ₁ = 0 := by linarith [hnormalized ρ₁ hρ₁]
  have hleft₂ : left ρ₂ = 0 := by linarith [hnormalized ρ₂ hρ₂]
  have hcut := hmid.2
  simp only [map_add, map_smul, hleft, hleft₂, hright₁, hright, smul_eq_mul,
    mul_one, mul_zero, add_zero, zero_add, max_self] at hcut
  exact (not_le_of_gt hhalf) hcut

/-- The normalized positive states on the real two-summand algebra, expressed
in coordinates with canonical trace `ρ.1 + ρ.2`. Their central-unit weights
are their two coordinates. -/
def twoSummandWeightStates : Set (ℝ × ℝ) :=
  {ρ | 0 ≤ ρ.1 ∧ 0 ≤ ρ.2 ∧ ρ.1 + ρ.2 = 1}

theorem convex_twoSummandWeightStates : Convex ℝ twoSummandWeightStates := by
  let left := LinearMap.fst ℝ ℝ ℝ
  let right := LinearMap.snd ℝ ℝ ℝ
  exact (convex_halfSpace_ge left.isLinear 0).inter
    ((convex_halfSpace_ge right.isLinear 0).inter (convex_hyperplane (left + right).isLinear 1))

/-- The maximum-weight cut on two normalized state weights is convex exactly
when it is the entire state space or empty. -/
theorem convex_twoSummandWeightStates_max_iff (ε : ℝ) :
    Convex ℝ (twoSummandMaxWeightCut twoSummandWeightStates
      (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ) ε) ↔
      ε ≤ 1 / 2 ∨ 1 < ε := by
  have hnormalized :
      ∀ ρ ∈ twoSummandWeightStates, (LinearMap.fst ℝ ℝ ℝ) ρ + (LinearMap.snd ℝ ℝ ℝ) ρ = 1 :=
    fun _ h => h.2.2
  constructor
  · intro hconvex
    by_cases hhalf : ε ≤ 1 / 2
    · exact Or.inl hhalf
    · right
      by_contra hone
      have h₁ : ((1, 0) : ℝ × ℝ) ∈ twoSummandWeightStates := by
        norm_num [twoSummandWeightStates]
      have h₂ : ((0, 1) : ℝ × ℝ) ∈ twoSummandWeightStates := by
        norm_num [twoSummandWeightStates]
      exact not_convex_twoSummandMaxWeightCut hnormalized h₁ h₂ rfl rfl
        (lt_of_not_ge hhalf) (le_of_not_gt hone) hconvex
  · rintro (hhalf | hone)
    · rw [twoSummandMaxWeightCut_eq_states hnormalized hhalf]
      exact convex_twoSummandWeightStates
    · have hnonneg :
          ∀ ρ ∈ twoSummandWeightStates, 0 ≤ (LinearMap.fst ℝ ℝ ℝ) ρ ∧
            0 ≤ (LinearMap.snd ℝ ℝ ℝ) ρ :=
        fun _ h => ⟨h.1, h.2.1⟩
      rw [twoSummandMaxWeightCut_eq_empty hnormalized hnonneg hone]
      exact convex_empty

end AlbertSequential
