/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AlgebraicSeparationAssembly
public import AlgebraicProjectiveNoGo

/-! One finite inequality for all states of a generating native Albert atom
menu, at the algebraic projective comparison boundary. The native no-go is a
proved imported theorem, not an assumed reconstruction contract. Concrete
real/complex/quaternionic operator bindings remain separate. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
universe u

theorem noMomentMatch_generating_atoms {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) (states : Set Albert) :
    NoMomentMatch p states := by
  apply (noMomentMatch_iff_noUniversalProjectionMatch p states).mpr
  intro M ρ _
  exact algebraicProjective_not_matches_generating_atoms M p hp hg ρ

theorem uniformMomentSeparator_generating_atoms {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    UniformMomentSeparator p nativeDensitySet :=
  uniformDensitySeparator_of_noMomentMatch p
    (noMomentMatch_generating_atoms p hp hg nativeDensitySet)

/-- The all-state statement `AlbertUniformSeparationContract`, proved with its original
generation and trace-one density hypotheses. -/
def albertUniformSeparation (n : ℕ) : AlbertUniformSeparationContract n where
  all_states p hp hg := uniformMomentSeparator_generating_atoms p hp hg

/-- The same finite coefficients and strict margin work for every algebraic
projective model and every native density. No state-dependent selection occurs. -/
theorem uniformAlgebraicSeparator_generating_atoms {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    ∃ L : ℕ, ∃ c : FiniteRealWordFunctional n, ∃ γ : ℝ,
      0 < γ ∧ c.HasHorizon L ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A), 0 ≤ c.evaluate M.probability) ∧
      (∀ ρ ∈ nativeDensitySet, c.evaluate (nativeWordProbability p ρ) ≤ -γ) :=
  (uniformMomentSeparator_generating_atoms p hp hg).algebraic

end AlbertSequential
