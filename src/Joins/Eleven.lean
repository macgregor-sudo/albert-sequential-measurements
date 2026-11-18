/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenTheorem
public import MatchingModels.QuatPair

/-!
# thm:eleven with its side assertion

Core `thm:eleven` states, for four atoms with `𝒜 > 0`, that "all six transition probabilities lie
in `(0,1)`", then (a)–(c). `BlockB.thm_eleven_full` proves the list facts and (a)–(c);
`MatchingModels.overlap_pos_lt_one_of_fourPoint_pos` proves the side assertion. This module states
the conjunction.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential.BlockB

universe u v w

open AlbertSequential
open AlbertSequential.NativeAnalysis
open AlbertSequential.Ends.Eleven

attribute [local irreducible] fourPointInvariant tracePairing albertTrace

/-- **thm:eleven, with the side assertion.** The conjunction of `thm_eleven_full` (list sizes,
ledger identity, (a), (b), (c)) and the statement that every transition probability
`o_{ij} = ⟨p_i, p_j⟩`, `i ≠ j`, lies in `(0, 1)`. -/
theorem thm_eleven_with_overlaps (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    (∀ i j : Fin 4, i ≠ j → 0 < fpOverlap p i j ∧ fpOverlap p i j < 1) ∧
      elevenBase.card = 2041 ∧
      elevenLedgerWords = elevenBase ∧
      elevenUnion.card = 8164 ∧
      (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
          [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
          (M : AlgebraicProjectiveData (Fin 4) A),
          (∀ wd ∈ elevenBase,
            M.probability wd = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
          [InnerProductSpace 𝕜 H] [CompleteSpace H]
          (M : HilbertProjectiveData (Fin 4) 𝕜 H),
          (∀ wd ∈ elevenBase,
            M.probability wd = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          {Q : QuaternionicOperatorStructure H}
          (M : QuaternionicProjectiveData (Fin 4) Q),
          (∀ wd ∈ elevenBase,
            M.state (M.wordEffect wd) =
              nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ (ρ : Albert), IsDensity ρ →
        (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
            [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
            (M : AlgebraicProjectiveData (Fin 4) A),
            (∀ wd ∈ elevenUnion, M.probability wd = nativeWordProbability p ρ wd) → False) ∧
        (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
            [InnerProductSpace 𝕜 H] [CompleteSpace H]
            (M : HilbertProjectiveData (Fin 4) 𝕜 H),
            (∀ wd ∈ elevenUnion, M.probability wd = nativeWordProbability p ρ wd) → False) ∧
        (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            {Q : QuaternionicOperatorStructure H}
            (M : QuaternionicProjectiveData (Fin 4) Q),
            (∀ wd ∈ elevenUnion,
              M.state (M.wordEffect wd) = nativeWordProbability p ρ wd) → False)) ∧
      (∃ Λ : FiniteRealWordFunctional 4, ∃ γ : ℝ, 0 < γ ∧
        (∀ wd ∈ Λ.coefficients.support, (wd = [] ∨ wd ∈ elevenUnion) ∧ IsReducedWord wd) ∧
        Λ.HasHorizon 11 ∧
        (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
            [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
            (M : AlgebraicProjectiveData (Fin 4) A), 0 ≤ Λ.evaluate M.probability) ∧
        (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
            [InnerProductSpace 𝕜 H] [CompleteSpace H]
            (M : HilbertProjectiveData (Fin 4) 𝕜 H), 0 ≤ Λ.evaluate M.probability) ∧
        (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            {Q : QuaternionicOperatorStructure H}
            (M : QuaternionicProjectiveData (Fin 4) Q),
            0 ≤ Λ.evaluate (fun wd => M.state (M.wordEffect wd))) ∧
        (∀ ρ : Albert, IsDensity ρ → Λ.evaluate (nativeWordProbability p ρ) ≤ -γ)) :=
  ⟨fun _ _ hij => MatchingModels.overlap_pos_lt_one_of_fourPoint_pos p hp hA hij,
    thm_eleven_full.{u, v, w} p hp hA⟩

end AlbertSequential.BlockB
