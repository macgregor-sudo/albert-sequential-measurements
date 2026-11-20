/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenSupport
public import Mathlib.Data.List.Nodup

/-! Occurrences in the purity application ledger of companion Appendix A.4. -/

@[expose] public section
namespace AlbertSequential.BlockB

/-- The prefix A, base A and suffix D occur together more than once. -/
theorem repeated_purity_application :
    2 ≤ ledgerApplications.count ([(0, true)], (0, true), [(3, true)]) := by
  decide +kernel

/-- The 1,673 entries count applications with repetition. -/
theorem ledgerApplications_occurrences :
    ledgerApplications.length = 1673 ∧ ¬ ledgerApplications.Nodup := by
  refine ⟨ledgerApplications_length, ?_⟩
  intro h
  have bound := List.nodup_iff_count_le_one.mp h ([(0, true)], (0, true), [(3, true)])
  exact (by decide : ¬ (2 ≤ 1)) (repeated_purity_application.trans bound)

end AlbertSequential.BlockB
