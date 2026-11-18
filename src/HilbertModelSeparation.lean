/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertUniformSeparation
public import HilbertClassIConstructor
public import QuaternionicClassIConstructor

/-! The common native finite separator acts on actual arbitrary-Hilbert
real/complex/right-quaternionic projective models, with their original states.
The SAME coefficients precede all three independent carrier universes. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertModelSeparation

universe uR uC uQ

theorem hilbert_not_matches_generating_atoms
    {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData ι 𝕜 H) (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) (ρ : Albert) :
    ¬ M.Matches p ρ := by
  intro h
  exact algebraicProjective_not_matches_generating_atoms M.toAlgebraic p hp hg ρ
    ((M.toAlgebraic_matches_iff p ρ).mpr h)

theorem rightQuaternionic_not_matches_generating_atoms
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData ι S.toOperatorStructure) (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) (ρ : Albert) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability p ρ w) := by
  intro h
  exact algebraicProjective_not_matches_generating_atoms M.toAlgebraic p hp hg ρ
    ((M.toAlgebraic_matches_iff p ρ).mpr h)

theorem hilbertFunctional_nonnegative
    {n : ℕ} (c : FiniteRealWordFunctional n)
    (hc : ∀ m, AdmissibleProjectionMoments n m →
      0 ≤ c.evaluate (momentWordProbability m))
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin n) 𝕜 H) :
    0 ≤ c.evaluate (fun w => M.state (M.wordEffect w)) := by
  have h := wordFunctional_nonnegative_on_algebraic_models c hc M.toAlgebraic
  have heq : M.toAlgebraic.probability = (fun w => M.state (M.wordEffect w)) := by
    funext w
    exact M.toAlgebraic_probability w
  simpa only [heq] using h

theorem rightQuaternionicFunctional_nonnegative
    {n : ℕ} (c : FiniteRealWordFunctional n)
    (hc : ∀ m, AdmissibleProjectionMoments n m →
      0 ≤ c.evaluate (momentWordProbability m))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure) :
    0 ≤ c.evaluate (fun w => M.state (M.wordEffect w)) := by
  have h := wordFunctional_nonnegative_on_algebraic_models c hc M.toAlgebraic
  have heq : M.toAlgebraic.probability = (fun w => M.state (M.wordEffect w)) := by
    funext w
    exact M.toAlgebraic_probability w
  simpa only [heq] using h

/-- All carrier universes and models occur AFTER the one native choice of
L,c,γ. Only the native side is restricted to trace-one positive densities. -/
theorem uniformHilbertSeparator_generating_atoms {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    ∃ L : ℕ, ∃ c : FiniteRealWordFunctional n, ∃ γ : ℝ,
      0 < γ ∧ c.HasHorizon L ∧
      (∀ (H : Type uR) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℝ H),
        0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uC) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℂ H),
        0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uQ) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicHilbertStructure H)
        (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure),
        0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ ρ ∈ nativeDensitySet, c.evaluate (nativeWordProbability p ρ) ≤ -γ) := by
  obtain ⟨L,c,γ,hγ,hL,hc,hnative⟩ := uniformMomentSeparator_generating_atoms p hp hg
  refine ⟨L,c,γ,hγ,hL,?_,?_,?_,hnative⟩
  · intro H _ _ _ M
    exact hilbertFunctional_nonnegative c hc M
  · intro H _ _ _ M
    exact hilbertFunctional_nonnegative c hc M
  · intro H _ _ _ S M
    exact rightQuaternionicFunctional_nonnegative c hc S M

end AlbertSequential.HilbertModelSeparation
