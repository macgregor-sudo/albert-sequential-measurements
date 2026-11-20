module

import PaperRobustSourceCorrespondence

noncomputable section

open AlbertSequential AlbertSequential.BlockB AlbertSequential.LengthSeven
open AlbertSequential.LengthSeven.Robust

example (w : Word Letter) :
    robustFunctionalM.coefficients w =
      (((pairsM.map fun p =>
          (p.2.tabs.map fun m => if addYesA m.2.toWord = w then p.1 * m.1 else 0).sum +
          (p.2.defs.map fun d => sourceDefectCoefficient tableM thetaM p.1 d w).sum).sum : ℚ) : ℝ) :=
  robust_coefficient_recorded_formula tableM thetaM pairsM w

example (w : Word Letter) :
    robustFunctionalS.coefficients w =
      (((pairsS.map fun p =>
          (p.2.tabs.map fun m => if addYesA m.2.toWord = w then p.1 * m.1 else 0).sum +
          (p.2.defs.map fun d => sourceDefectCoefficient tableS thetaS p.1 d w).sum).sum : ℚ) : ℝ) :=
  robust_coefficient_recorded_formula tableS thetaS pairsS w

example :
    (eM_301.defs.drop 3).map (fun d => (d.α, d.q)) =
      List.replicate 3 ([3, 2, 1, 3].map lt, lt 3) ∧
    eM_301_literalAlpha.ok = true ∧
    piQ tableM ([3, 2, 1, 3].map lt) = 1 / 81 ∧
    piQ tableM ([3, 2, 1].map lt) = 1 / 27 :=
  ⟨residual301_retains_D, residual301_removal_keeps_gram_identity,
    residual301_removal_changes_probability_bucket⟩

#print axioms robust_coefficient_recorded_formula
#print axioms residual301_retains_D
#print axioms residual301_removal_keeps_gram_identity
#print axioms residual301_removal_changes_probability_bucket
#print axioms residual41_transposed_valid
#print axioms residual41_transposed_counters
#print axioms residual41_transposed_distinct_coefficient
