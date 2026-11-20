/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenTheorem
public import FixedSConstructedWitness

@[expose] public section
noncomputable section

namespace AlbertSequential

open BlockB ConstructorCalibration NativeAnalysis
open scoped BigOperators

attribute [local irreducible] fourPointInvariant

private theorem fixedS_invariant_pos : 0 < fourPointInvariant fixedS := by
  rw [fourPointInvariant_fixedS]
  norm_num

theorem fixedS_atomCorner_discriminant : (atomCornerData fixedS).scalarParameters.discriminant = 1 / 12 := by
  rw [atomCorner_discriminant_eq fixedS fixedS_isAtom fixedS_invariant_pos, fourPointInvariant_fixedS]
  change (1 / 5832 : ℝ) /
    (nativeOverlaps fixedS 0 1 * nativeOverlaps fixedS 0 2 * nativeOverlaps fixedS 0 3 *
      nativeOverlaps fixedS 1 2 * nativeOverlaps fixedS 2 3 * nativeOverlaps fixedS 3 1) = _
  norm_num [nativeOverlaps_fixedS_eq]

/-- The base order of the four printed word families. -/
abbrev fixedSPrintedMenu (j : Fin 4) : Fin 4 → Albert := fixedS ∘ swapBase j

/-- Occurrences retain repetitions and the left polynomial associated to each residual. -/
def fixedSPrintedOccurrences : List (ResidualTelescopeOccurrence 4) :=
  combinedCornerOccurrences
    (fun j => atomCornerData (fixedSPrintedMenu j))
    (fun j => atomCornerScalar (fixedSPrintedMenu j))
    (fun j a => swapBase j a) (fun _ => 1)

/-- The fixed-S separator with the base transpositions of the printed list. -/
def fixedSPrintedWitness : FiniteRealWordFunctional 4 :=
  combinedCornerWitness
    (fun j => atomCornerData (fixedSPrintedMenu j))
    (fun j => atomCornerScalar (fixedSPrintedMenu j))
    (fun j a => swapBase j a) (fun _ => 1) (7 / 414)

theorem fixedSPrinted_occurrence_calibrated (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ fixedSPrintedOccurrences) :
    o.leaf.outcome.2 = true ∧ o.leaf.constant =
      nativeWordProbability fixedS (fixedS o.leaf.outcome.1) o.leaf.suffix := by
  unfold fixedSPrintedOccurrences combinedCornerOccurrences ResidualOccurrenceExpression.combine
    ResidualOccurrenceExpression.scale ResidualOccurrenceExpression.relabel at ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  have h := cornerResidualTelescope_calibrated _ _ v hv
  refine ⟨h.1, ?_⟩
  change v.leaf.constant = nativeWordProbability fixedS (fixedS (swapBase j v.leaf.outcome.1))
    (relabelWord (swapBase j) v.leaf.suffix)
  rw [nativeWordProbability_relabel]
  exact h.2

theorem fixedSPrinted_occurrence_words (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ fixedSPrintedOccurrences) :
    ∃ j : Fin 4, ∀ t ∈ o.leaf.wordFunctional.terms,
      t.2 ∈ elevenFamily j ∧ IsReducedWord t.2 := by
  unfold fixedSPrintedOccurrences combinedCornerOccurrences ResidualOccurrenceExpression.combine
    ResidualOccurrenceExpression.scale ResidualOccurrenceExpression.relabel at ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  refine ⟨j, fun t ht => ?_⟩
  change t ∈ (SupportedPurityLeaf.relabel (fun a => swapBase j a) v.leaf).wordFunctional.terms at ht
  rw [SupportedPurityLeaf.wordFunctional_relabel] at ht
  rcases List.mem_map.mp ht with ⟨x, hx, rfl⟩
  have hm := cornerResidualTelescope_words_mem_elevenBase _ _ v hv x hx
  exact ⟨relabelWord_mem_elevenFamily j hm.1, isReducedWord_relabel (swapBase j).injective hm.2⟩

theorem fixedSPrinted_coefficientBudget :
    residualCoefficientBudget fixedSPrintedOccurrences =
      (fixedSPrintedOccurrences.map (fun o => ((o.leftTerms.terms.map (fun t => |t.1|)).sum) ^ 2)).sum :=
  rfl

theorem fixedSPrintedWitness_evaluate (f : Word (Fin 4) → ℝ) :
    fixedSPrintedWitness.evaluate f =
      (207 * (residualCoefficientBudget fixedSPrintedOccurrences + 1) / 7) *
        (fixedSPrintedOccurrences.map (fun o =>
          f o.leaf.longWord - 2 * o.leaf.constant * f o.leaf.middleWord +
            o.leaf.constant ^ 2 * f o.leaf.shortWord)).sum -
      (1 / 12) * (∑ j : Fin 4, f [(j, true)]) + (7 / 828) * f [] := by
  have hbase :
      (combinedCornerBase (fun j => atomCornerData (fixedSPrintedMenu j))
        (fun j a => swapBase j a) (fun _ => 1)).evaluate f =
        (1 / 12) * ∑ j : Fin 4, f [(j, true)] := by
    rw [← fixedS_atomCorner_discriminant]
    exact atomCornerWitness_combinedBase_evaluate fixedS fixedS_isAtom fixedS_invariant_pos f
  unfold fixedSPrintedWitness combinedCornerWitness
  rw [constructiveResidualSeparator_evaluate, hbase]
  change residualPenaltyParameter fixedSPrintedOccurrences (7 / 414) *
    (fixedSPrintedOccurrences.map (fun o => o.leaf.wordFunctional.evaluate f)).sum - _ + _ = _
  simp only [SupportedPurityLeaf.wordFunctional_evaluate]
  unfold residualPenaltyParameter
  ring

set_option maxRecDepth 2500 in
theorem fixedSPrintedWitness_support :
    (∀ t ∈ fixedSPrintedWitness.terms, (t.2 = [] ∨ t.2 ∈ elevenUnion) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ fixedSPrintedWitness.coefficients.support, (w = [] ∨ w ∈ elevenUnion) ∧ IsReducedWord w) := by
  unfold fixedSPrintedWitness
  exact combinedCornerWitness_swapBase_support
    (fun j => atomCornerData (fixedSPrintedMenu j))
    (fun j => atomCornerScalar (fixedSPrintedMenu j)) (fun _ => 1) (7 / 414)

theorem fixedSPrintedWitness_horizon : fixedSPrintedWitness.HasHorizon 11 :=
  atomCornerWitness_horizon fixedS (7 / 414)

section Models

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem fixedSPrinted_telescope (M : AlgebraicProjectiveData (Fin 4) A) :
    (1 / 12 : ℝ) * (∑ j : Fin 4, M.probability [(j, true)]) =
      (fixedSPrintedOccurrences.map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum := by
  rw [← fixedS_atomCorner_discriminant,
    ← atomCornerWitness_combinedBase_evaluate fixedS fixedS_isAtom fixedS_invariant_pos]
  exact combinedCornerTelescope_identity
    (fun j => atomCornerData (fixedSPrintedMenu j)) (fun j => atomCornerScalar (fixedSPrintedMenu j))
    (fun j a => swapBase j a) (fun _ => 1)
    (fun j => atomCorner_conditions (fixedSPrintedMenu j)
      (fun i => fixedS_isAtom (swapBase j i)) (fourPointInvariant_swapBase fixedS j fixedS_invariant_pos)) M

theorem fixedSPrintedWitness_model_nonneg (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ fixedSPrintedWitness.evaluate M.probability :=
  atomCornerWitness_model_nonnegative fixedS fixedS_isAtom fixedS_invariant_pos M (7 / 414) (by norm_num)

end Models

theorem fixedSPrinted_occurrence_native_zero (ρ : Albert) (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ fixedSPrintedOccurrences) :
    o.leaf.wordFunctional.evaluate (nativeWordProbability fixedS ρ) = 0 :=
  atomCorner_combined_leaves_native_zero fixedS fixedS_isAtom ρ o ho

theorem fixedSPrintedWitness_native_le (ρ : Albert) (hρ : IsDensity ρ) :
    fixedSPrintedWitness.evaluate (nativeWordProbability fixedS ρ) ≤ -(7 / 828) := by
  have hmass := fixedSAtomSum_density_mass ρ hρ
  simp only [fixedSAtomSum, Fin.sum_univ_four] at hmass
  have hm : (7 / 414 : ℝ) ≤ (atomCornerData fixedS).scalarParameters.discriminant *
      tracePairing ρ (fixedS 0 + fixedS 1 + fixedS 2 + fixedS 3) := by
    rw [fixedS_atomCorner_discriminant]
    linarith only [hmass]
  have h := atomCornerWitness_native_le fixedS fixedS_isAtom fixedS_invariant_pos ρ hρ (7 / 414) (by norm_num) hm
  rw [show (7 / 414 : ℝ) / 2 = 7 / 828 by norm_num] at h
  exact h

theorem fixedSPrintedWitness_forces_error
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (ρ : Albert) (hρ : IsDensity ρ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ w, w.length ≤ 11 → |M.probability w - nativeWordProbability fixedS ρ w| ≤ ε) :
    (7 / 828 : ℝ) ≤ fixedSPrintedWitness.coefficientNorm * ε :=
  fixedSPrintedWitness.separation_forces_error M.probability (nativeWordProbability fixedS ρ)
    ε (7 / 828) hε
    (fun w hw => herr w (fixedSPrintedWitness.coefficient_support_hasHorizon 11
      fixedSPrintedWitness_horizon w hw))
    (fixedSPrintedWitness_model_nonneg M) (fixedSPrintedWitness_native_le ρ hρ)

end AlbertSequential
