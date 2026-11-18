/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Ends.Margin
public import FiveTest.Main

/-! # prop:five:short (b), existence form only

Paper (companion `prop:five:short` (b)): every sequential projective representation of
the five tests differs from the statistics of `F` from `e/3` by MORE THAN `9 × 10⁻²¹` on some word of
length at most eleven that begins with "yes" on `p_0`.

Lean proves only the EXISTENCE of some `δ_F > 0` with "at least `δ_F`" (equivalently, by halving,
"more than" some positive constant); the explicit constant `9 × 10⁻²¹` is NOT proved here.
Proof: prop:five:short (a) (`five_short_e3`) on the universal projection algebra,
then `Ends.moment_margin_of_noMatch`. -/

@[expose] public section

namespace AlbertSequential.Ends

open AlbertSequential AlbertSequential.FiveTest

/-- **prop:five:short (b), existence form**, all three model classes with one `δ_F` and one finite
witness set of five-test words of length at most eleven beginning with "yes" on `p_0`. -/
theorem five_short_b_exists :
    ∃ (F : Finset (Word (Fin 5))) (δ : ℝ),
      (∀ w ∈ F, w.length ≤ 11 ∧ w.head? = some (0, true)) ∧ 0 < δ ∧
      (∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 5) A),
        ∃ w ∈ F, δ < |M.probability w - nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w|) ∧
      (∀ (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
        [CompleteSpace H] (M : HilbertProjectiveData (Fin 5) 𝕜 H),
        ∃ w ∈ F, δ < |M.probability w - nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w|) ∧
      (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData (Fin 5) Q),
        ∃ w ∈ F, δ < |M.state (M.wordEffect w) -
          nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w|) := by
  obtain ⟨F, δ, hFS, hδ, h⟩ := moment_margin_of_noMatch
    {w : Word (Fin 5) | w.length ≤ 11 ∧ w.head? = some (0, true)}
    (nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit))
    (fun M hM => five_short_e3 M fun w hw h0 => hM w ⟨hw, h0⟩)
  refine ⟨F, δ / 2, hFS, half_pos hδ, fun A _ _ _ _ _ _ M => ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M
    exact ⟨w, hw, lt_of_lt_of_le (half_lt_self hδ) hgap⟩
  · intro 𝕜 H _ _ _ _ M
    obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M.toAlgebraic
    rw [M.toAlgebraic_probability] at hgap
    exact ⟨w, hw, lt_of_lt_of_le (half_lt_self hδ) hgap⟩
  · intro H _ _ _ Q M
    obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M.toAlgebraic
    rw [M.toAlgebraic_probability] at hgap
    exact ⟨w, hw, lt_of_lt_of_le (half_lt_self hδ) hgap⟩

/-- The `p_0` form (first half of prop:five:short (a)) also has a margin: words of length ≤ 10. -/
theorem five_short_b_p0_exists :
    ∃ (F : Finset (Word (Fin 5))) (δ : ℝ), (∀ w ∈ F, w.length ≤ 10) ∧ 0 < δ ∧
      ∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 5) A),
        ∃ w ∈ F, δ ≤ |M.probability w - nativeWordProbability pentadF (pentadF 0) w| :=
  algebraic_margin_of_noMatch {w | w.length ≤ 10} (nativeWordProbability pentadF (pentadF 0))
    (fun M hM => five_short_p0 M fun w hw => hM w hw)

end AlbertSequential.Ends

#print axioms AlbertSequential.Ends.five_short_b_exists
#print axioms AlbertSequential.Ends.five_short_b_p0_exists
