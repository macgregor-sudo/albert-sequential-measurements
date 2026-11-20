/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSPrintedWitness
public import Ends.PrintedElevenList

@[expose] public section
namespace AlbertSequential

open BlockB Ends.Eleven
open Ends.Eleven.Printed

/-- The concatenations of the deposited Appendix A.5 prefix and tail codes. -/
def depositedElevenBase (w : Word (Fin 4)) : Prop :=
  ((∃ u, Ends.Eleven.code u ∈ prefix012Codes ∧ ∃ v, Ends.Eleven.code v ∈ tailBCodes ∧ u ++ v = w) ∨
   (∃ u, Ends.Eleven.code u ∈ prefix01Codes ∧ ∃ v, Ends.Eleven.code v ∈ tailDCodes ∧ u ++ v = w)) ∨
  Ends.Eleven.code w ∈ farFaceCodes

/-- Membership in an individual deposited family after the specified base swap. -/
def depositedElevenFamily (j : Fin 4) (w : Word (Fin 4)) : Prop :=
  ∃ u, depositedElevenBase u ∧ relabelWord (swapBase j) u = w

theorem mem_elevenFamily_iff_deposited (j : Fin 4) (w : Word (Fin 4)) :
    w ∈ elevenFamily j ↔ depositedElevenFamily j w := by
  have h (u : Word (Fin 4)) : u ∈ elevenBase ↔ depositedElevenBase u := by
    rw [← elevenLedgerWords_eq_elevenBase]
    exact ledger_mem_iff_deposited u
  classical
  simp only [elevenFamily, depositedElevenFamily, Finset.mem_image, h]

theorem mem_elevenUnion_iff_deposited (w : Word (Fin 4)) :
    w ∈ elevenUnion ↔ ∃ j : Fin 4, depositedElevenFamily j w := by
  classical
  simp only [elevenUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_elevenFamily_iff_deposited]

theorem fixedSPrinted_occurrence_words_deposited (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ fixedSPrintedOccurrences) :
    ∃ j : Fin 4, (depositedElevenFamily j o.leaf.shortWord ∧
      depositedElevenFamily j o.leaf.middleWord ∧ depositedElevenFamily j o.leaf.longWord) := by
  obtain ⟨j, hj⟩ := fixedSPrinted_occurrence_words o ho
  refine ⟨j, ?_, ?_, ?_⟩
  · exact (mem_elevenFamily_iff_deposited j _).mp
      (hj (o.leaf.constant ^ 2, o.leaf.shortWord) (by simp [SupportedPurityLeaf.wordFunctional])).1
  · exact (mem_elevenFamily_iff_deposited j _).mp
      (hj (-2 * o.leaf.constant, o.leaf.middleWord) (by simp [SupportedPurityLeaf.wordFunctional])).1
  · exact (mem_elevenFamily_iff_deposited j _).mp
      (hj (1, o.leaf.longWord) (by simp [SupportedPurityLeaf.wordFunctional])).1

theorem fixedSPrintedWitness_support_deposited :
    (∀ t ∈ fixedSPrintedWitness.terms,
      (t.2 = [] ∨ ∃ j : Fin 4, depositedElevenFamily j t.2) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ fixedSPrintedWitness.coefficients.support,
      (w = [] ∨ ∃ j : Fin 4, depositedElevenFamily j w) ∧ IsReducedWord w) := by
  simpa only [mem_elevenUnion_iff_deposited] using fixedSPrintedWitness_support

end AlbertSequential
