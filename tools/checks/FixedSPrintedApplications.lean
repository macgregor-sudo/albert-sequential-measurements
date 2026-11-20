module

import FixedSPrintedWitnessSupport
import FixedSPrintedApplicationLedger

open AlbertSequential AlbertSequential.BlockB
open scoped BigOperators

set_option maxRecDepth 2500
set_option maxHeartbeats 1000000

example (f : Word (Fin 4) → ℝ) :
    fixedSPrintedWitness.evaluate f =
      (207 * (residualCoefficientBudget fixedSPrintedOccurrences + 1) / 7) *
        (fixedSPrintedOccurrences.map (fun o =>
          f o.leaf.longWord - 2 * o.leaf.constant * f o.leaf.middleWord +
            o.leaf.constant ^ 2 * f o.leaf.shortWord)).sum -
      (1 / 12) * (∑ j : Fin 4, f [(j, true)]) + (7 / 828) * f [] :=
  fixedSPrintedWitness_evaluate f

example (o : ResidualTelescopeOccurrence 4) (ho : o ∈ fixedSPrintedOccurrences) :
    (o.leaf.outcome.2 = true ∧ o.leaf.constant =
      nativeWordProbability fixedS (fixedS o.leaf.outcome.1) o.leaf.suffix) ∧
    ∃ j : Fin 4, depositedElevenFamily j o.leaf.shortWord ∧
      depositedElevenFamily j o.leaf.middleWord ∧ depositedElevenFamily j o.leaf.longWord :=
  ⟨fixedSPrinted_occurrence_calibrated o ho, fixedSPrinted_occurrence_words_deposited o ho⟩

example (ρ : Albert) (hρ : IsDensity ρ) (w : Word (Fin 4))
    (hw : w ∈ fixedSPrintedWitness.coefficients.support) :
    (w = [] ∨ ∃ j : Fin 4, depositedElevenFamily j w) ∧
      fixedSPrintedWitness.evaluate (nativeWordProbability fixedS ρ) ≤ -(7 / 828) :=
  ⟨(fixedSPrintedWitness_support_deposited.2 w hw).1, fixedSPrintedWitness_native_le ρ hρ⟩

example {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ fixedSPrintedWitness.evaluate M.probability ∧
      (1 / 12 : ℝ) * (∑ j : Fin 4, M.probability [(j, true)]) =
        (fixedSPrintedOccurrences.map (fun o => M.state
          (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum :=
  ⟨fixedSPrintedWitness_model_nonneg M, fixedSPrinted_telescope M⟩

example (o : ResidualTelescopeOccurrence 4) (ho : o ∈ fixedSPrintedOccurrences) :
    ∃ (j : Fin 4) (t : Word (Fin 4)) (q : Outcome (Fin 4)) (v : Word (Fin 4)),
      (t, q, v) ∈ ledgerApplications ∧
      o.leaf.outcome = relabelOutcome (Equiv.swap 0 j) q ∧
      o.leaf.suffix = relabelWord (Equiv.swap 0 j) v ∧
      reduceWord (relabelWord (Equiv.swap 0 j) t ++ [o.leaf.outcome]) = some o.leaf.shortWord :=
  fixedSPrinted_occurrence_has_ledger_application o ho

#print axioms fixedSPrinted_baseOccurrence_has_ledger_application
#print axioms fixedSPrinted_occurrence_has_ledger_application
#print axioms fixedS_atomCorner_discriminant
#print axioms fixedSPrinted_coefficientBudget
#print axioms fixedSPrintedWitness_evaluate
#print axioms fixedSPrinted_telescope
#print axioms fixedSPrinted_occurrence_calibrated
#print axioms fixedSPrinted_occurrence_native_zero
#print axioms fixedSPrinted_occurrence_words_deposited
#print axioms fixedSPrintedWitness_support_deposited
#print axioms fixedSPrintedWitness_horizon
#print axioms fixedSPrintedWitness_model_nonneg
#print axioms fixedSPrintedWitness_native_le
#print axioms fixedSPrintedWitness_forces_error
