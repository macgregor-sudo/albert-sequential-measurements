/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Ends.Margin
public import Uniform.Main

/-! # thm:cer:uniform (b): a positive margin exists (existence only)

Paper (core `thm:cer:uniform` (b)): for atoms `p_A, …, p_D` of `J` with `𝒜 > 0`
there is `δ > 0`, depending on the quadruple, such that every sequential projective representation
differs from the octonionic table from `e/3` by at least `δ` on some word of length at most seven
that begins with "yes" on `A`.

Lean: one `δ` (and one finite witness set `F` of such words) serves every algebraic projective
model over any star ring, every real or complex Hilbert model and every quaternionic model.
Proof: thm:cer:uniform (a) (`uniform_lengthSeven_e3_algebraic`) applied on
the universal projection algebra, then `Ends.algebraic_margin_of_noMatch` (compactness of the
admissible moment domain). No explicit value of `δ` is given. -/

@[expose] public section

namespace AlbertSequential.Ends

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.Uniform

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

/-- The word set of thm:cer:uniform (a), first sentence, and of (b): words of length at most seven
beginning with "yes" on `A` (all such words, reduced or not). -/
def wordsE3Seven : Set (Word Letter) := {w | w.length ≤ 7 ∧ w.head? = some (0, true)}

/-- **thm:cer:uniform (b)** (existence of the margin), all three model classes at once. -/
theorem uniform_b (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (F : Finset (Word Letter)) (δ : ℝ), (∀ w ∈ F, w.length ≤ 7 ∧ w.head? = some (0, true)) ∧
      0 < δ ∧
      (∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData Letter A),
        ∃ w ∈ F, δ ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) ∧
      (∀ (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
        [CompleteSpace H] (M : HilbertProjectiveData Letter 𝕜 H),
        ∃ w ∈ F, δ ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) ∧
      (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData Letter Q),
        ∃ w ∈ F, δ ≤ |M.state (M.wordEffect w) -
          nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) := by
  obtain ⟨F, δ, hFS, hδ, h⟩ := moment_margin_of_noMatch wordsE3Seven
    (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit))
    (fun M hM => uniform_lengthSeven_e3_algebraic p hp hA M fun w hw h0 => hM w ⟨hw, h0⟩)
  refine ⟨F, δ, hFS, hδ, fun A _ _ _ _ _ _ M => algebraic_gap_of_moment h M, ?_, ?_⟩
  · intro 𝕜 H _ _ _ _ M
    obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M.toAlgebraic
    exact ⟨w, hw, by rwa [M.toAlgebraic_probability] at hgap⟩
  · intro H _ _ _ Q M
    obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M.toAlgebraic
    exact ⟨w, hw, by rwa [M.toAlgebraic_probability] at hgap⟩

/-- **thm:cer:uniform (b)**, the printed form for the algebraic class: there is `δ > 0` such that
every model differs from the octonionic table from `e/3` by at least `δ` on some word of length at
most seven beginning with "yes" on `A`. -/
theorem uniform_b_algebraic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData Letter A),
        ∃ w : Word Letter, w.length ≤ 7 ∧ w.head? = some (0, true) ∧
          δ ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| := by
  obtain ⟨F, δ, hFS, hδ, h⟩ := moment_margin_of_noMatch wordsE3Seven
    (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit))
    (fun M hM => uniform_lengthSeven_e3_algebraic p hp hA M fun w hw h0 => hM w ⟨hw, h0⟩)
  refine ⟨δ, hδ, fun A _ _ _ _ _ _ M => ?_⟩
  obtain ⟨w, hw, hgap⟩ := algebraic_gap_of_moment h M
  exact ⟨w, (hFS w hw).1, (hFS w hw).2, hgap⟩

/-- The `p_A` form (second sentence of (a)) also has a margin: words of length at most six. -/
theorem uniform_b_pA (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (F : Finset (Word Letter)) (δ : ℝ), (∀ w ∈ F, w.length ≤ 6) ∧ 0 < δ ∧
      ∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData Letter A),
        ∃ w ∈ F, δ ≤ |M.probability w - nativeWordProbability p (p 0) w| :=
  algebraic_margin_of_noMatch {w | w.length ≤ 6} (nativeWordProbability p (p 0))
    (fun M hM => uniform_lengthSix_pA_algebraic p hp hA M fun u hu => hM u hu)

end AlbertSequential.Ends

#print axioms AlbertSequential.Ends.moment_margin_of_noMatch
#print axioms AlbertSequential.Ends.algebraic_margin_of_noMatch
#print axioms AlbertSequential.Ends.uniform_b
#print axioms AlbertSequential.Ends.uniform_b_algebraic
#print axioms AlbertSequential.Ends.uniform_b_pA
