/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenSupport
import Std.Data.TreeSet.Lemmas

/-! Distinct raw `(t, q, v)` keys of the purity applications in companion Appendix A.4. -/

@[expose] public section
namespace AlbertSequential.BlockB

attribute [local instance] lexOrd

private def distinctApplications : Std.TreeSet PurityApplication :=
  Std.TreeSet.ofList ledgerApplications

private theorem distinctApplications_toFinset :
    distinctApplications.toList.toFinset = ledgerApplications.toFinset := by
  ext app
  simp [distinctApplications]

private theorem distinctApplications_nodup : distinctApplications.toList.Nodup := by
  refine (Std.TreeSet.distinct_toList (t := distinctApplications)).imp ?_
  rintro a b h rfl
  exact h Std.compare_self

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- The application ledger has 1,118 distinct raw triples before word reduction. -/
theorem ledgerApplications_distinct_card : ledgerApplications.toFinset.card = 1118 := by
  rw [← distinctApplications_toFinset,
    List.toFinset_card_of_nodup distinctApplications_nodup, Std.TreeSet.length_toList]
  decide +kernel

end AlbertSequential.BlockB
