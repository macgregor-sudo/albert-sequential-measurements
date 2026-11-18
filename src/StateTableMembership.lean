/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SelfAdjointFiniteModel
public import CanonicalGramTables

/-! Exact membership in the complete finite-real table set for the stated
algebraic and self-adjoint state interfaces. No concrete R/C/H operator
instance is supplied by these abstract real-star-algebra corollaries. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem algebraicData_table_mem {n : ℕ} (M : AlgebraicProjectiveData (Fin n) A) (L : ℕ) :
    (fun u : ReducedGramIndex n L => M.probability u.val) ∈
      finiteRealProjectiveTables n L := by
  obtain ⟨d, R, hR⟩ := algebraicData_finiteRealModel M L
  refine ⟨d, R, fun u => ?_⟩
  obtain ⟨hlen, hred⟩ := (mem_reducedWordsUpTo L u.val).mp u.property
  exact hR u.val hlen hred

theorem selfAdjointState_table_mem {n : ℕ}
    (P : Fin n → A) (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (ψ : selfAdjoint A →ₗ[ℝ] ℝ) (hunit : ψ 1 = 1)
    (hpositive : ∀ x : A, 0 ≤ ψ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩) (L : ℕ) :
    (fun u : ReducedGramIndex n L => selfAdjointWordProbability P ψ u.val) ∈
      finiteRealProjectiveTables n L := by
  obtain ⟨d, R, hR⟩ := selfAdjointState_finiteRealModel P hP hstar ψ hunit hpositive L
  refine ⟨d, R, fun u => ?_⟩
  obtain ⟨hlen, hred⟩ := (mem_reducedWordsUpTo L u.val).mp u.property
  exact hR u.val hlen hred

end AlbertSequential
