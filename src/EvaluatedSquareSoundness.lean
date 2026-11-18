/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectiveWordProbabilities

/-! Soundness of the existing evaluated finite square identity. The actual
identity is a supplied field at this comparator, not a parsed universal identity
or an assertion that any concrete certificate/ancillary file is available. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace AlgebraicProjectiveData
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData ι A)

theorem evaluatedSquareIdentity_sound (c : RationalWordFunctional ι)
    (h : EvaluatedSquareIdentity M.projection c) : 0 ≤ c.evaluate M.probability := by
  have heval := congrArg M.state h.identity
  simp only [map_list_sum, List.map_map, Function.comp_def, map_smul, smul_eq_mul] at heval
  change c.evaluate M.probability =
      (h.squares.map (fun t => (t.1 : ℝ) * M.squareMass t.2)).sum at heval
  rw [heval]
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  exact mul_nonneg (by exact_mod_cast (le_of_lt (h.positive_coefficients t ht)))
    (M.squareMass_nonneg _)

theorem rationalWordFunctional_square_identity_evaluation
    (c : RationalWordFunctional ι) (h : EvaluatedSquareIdentity M.projection c) :
    c.evaluate M.probability =
      (h.squares.map (fun t => (t.1 : ℝ) * M.squareMass t.2)).sum := by
  have heval := congrArg M.state h.identity
  simpa only [map_list_sum, List.map_map, Function.comp_def, map_smul, smul_eq_mul,
    RationalWordFunctional.evaluate, AlgebraicProjectiveData.probability, squareMass] using heval

end AlgebraicProjectiveData
end AlbertSequential
