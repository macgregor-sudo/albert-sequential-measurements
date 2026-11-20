module

import CompanionReadoutBudgets

open AlbertSequential AlbertSequential.BlockB

example (ε : ℝ) (hε : 0 ≤ ε) (hm : ε ≤ 12 / 10^26) :
    ¬ maximizerRobustRatio ≤ 14 * Real.sqrt (spectralRoundingError ε) :=
  not_le_of_gt (maximizer_printed_exact_defect_budget hε hm)

example (ε : ℝ) (hε : 0 ≤ ε) (hs : ε ≤ 3 / 10^27) :
    ¬ fixedSRobustRatio ≤ 14 * Real.sqrt (spectralRoundingError ε) :=
  not_le_of_gt (fixedS_printed_exact_defect_budget hε hs)

#print axioms maximizerRobustRatio_gt_printed_floor
#print axioms fixedSRobustRatio_gt_printed_floor
#print axioms maximizer_printed_exact_defect_budget
#print axioms fixedS_printed_exact_defect_budget
#print axioms maximizer_printed_projective_readout_budget
#print axioms fixedS_printed_projective_readout_budget
#print axioms maximizer_printed_calibration_budget
#print axioms fixedS_printed_calibration_budget
#print axioms no_common_readout_of_budget
