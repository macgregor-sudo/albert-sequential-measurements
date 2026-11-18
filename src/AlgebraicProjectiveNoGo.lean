/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertCyclicReconstruction
public import AlbertExceptionality

/-!
The generating-Albert all-word obstruction at the exact shared algebraic
comparator boundary. The native initial element is arbitrary; positivity is
required only of the comparator functional. Arbitrary-Hilbert R/C/H binding
and the common finite separator remain separate theorems.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem algebraicProjective_not_matches_generating_atoms
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : GeneratesAlbert p) (ρ : Albert) : ¬ M.Matches p ρ := by
  intro hmatch
  obtain ⟨η, hjordan, hunit, hexpectation⟩ := exists_albertCyclicJordanMap M p hp hg ρ hmatch
  have hzero := albertJordanHom_eq_zero (Module.End ℝ (CyclicWordSpace M)) η hjordan
  apply cyclic_endomorphism_unit_ne_zero M
  simpa only [hzero, LinearMap.zero_apply] using hunit.symm

theorem algebraicProjective_word_disagreement
    {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : GeneratesAlbert p) (ρ : Albert) :
    ∃ w, M.probability w ≠ nativeWordProbability p ρ w := by
  have h := algebraicProjective_not_matches_generating_atoms M p hp hg ρ
  change ¬ ∀ w, M.probability w = nativeWordProbability p ρ w at h
  exact not_forall.mp h

end AlbertSequential
