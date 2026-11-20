/- SPDX-License-Identifier: Apache-2.0 -/
module
public import PaperResidualVectors

@[expose] public section
noncomputable section
namespace AlbertSequential
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The corner may have a different unit from the ambient operator algebra. -/
theorem tracialCorner_annihilates_orbitClosure (ξ : H) (C : Set (H →L[ℝ] H))
    (hstar : ∀ T ∈ C, star T ∈ C) (hmul : ∀ S ∈ C, ∀ T ∈ C, S*T ∈ C)
    (htr : ∀ S ∈ C, ∀ T ∈ C, residualVectorFunctional ξ (S*T) = residualVectorFunctional ξ (T*S))
    {Z : H →L[ℝ] H} (hZ : Z ∈ C) (hz : Z ξ = 0) :
    (Submodule.span ℝ ((fun T : H →L[ℝ] H => T ξ) '' C)).topologicalClosure ≤ Z.ker := by
  have vanish (T : H →L[ℝ] H) (ht : T ∈ C) (hn : T ξ = 0) : (star T) ξ = 0 := by
    have eq := htr T ht (star T) (hstar T ht)
    conv_lhs at eq => rw [← star_star T]
    rw [residualVectorFunctional_starMul,residualVectorFunctional_starMul,hn] at eq
    simpa only [star_star,inner_zero_left,inner_self_eq_zero] using eq
  apply Submodule.topologicalClosure_minimal _ _ Z.isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨T,ht,rfl⟩
  have hst : star (Z*T) ξ = 0 := by
    rw [star_mul]
    change (star T) ((star Z) ξ) = 0
    rw [vanish Z hZ hz,map_zero]
  change (Z*T) ξ = 0
  simpa only [star_star] using vanish _ (hstar _ (hmul _ hZ _ ht)) hst

/-- A faithful vector functional on the generated algebra has zero nullspace. -/
theorem faithfulCorner_annihilator_zero (ξ : H) (C : Set (H →L[ℝ] H))
    (hf : ∀ T ∈ C, residualVectorFunctional ξ (star T*T) = 0 → T = 0)
    {Z : H →L[ℝ] H} (hZ : Z ∈ C) (hz : Z ξ = 0) : Z = 0 := by
  apply hf Z hZ
  simp [residualVectorFunctional_starMul,hz]

end AlbertSequential
