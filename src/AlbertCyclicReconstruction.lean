/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneratedCyclicReconstruction

/-!
The full-Albert specialization of the actual generated-subalgebra reconstruction.
No positivity, faithfulness, trace, rank or dimension hypothesis is added.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

def generatedOfGenerates {ι : Type*} (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : GeneratesAlbert p) : Albert →ₗ[ℝ] GeneratedAlbert p hp where
  toFun x := ⟨x, by rw [nativeOrbitSpan_eq_top_of_generates p hp hg]; trivial⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem exists_albertCyclicJordanMap
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : GeneratesAlbert p) (ρ : Albert) (hmatch : M.Matches p ρ) :
    ∃ η : Albert →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M),
      IsJordanHom η ∧ η albertUnit = 1 ∧
      ∀ x, cyclicExpectation M (η x (cyclicVector M)) = tracePairing ρ x := by
  obtain ⟨ηB, hjordan, hunit, hexpectation⟩ := exists_generatedCyclicJordanMap M p hp ρ hmatch
  let inclusion := generatedOfGenerates p hp hg
  let η := ηB.comp inclusion
  refine ⟨η, ?_, hunit, ?_⟩
  · intro x y
    exact hjordan (inclusion x) (inclusion y)
  · intro x
    exact hexpectation (inclusion x)

end AlbertSequential
