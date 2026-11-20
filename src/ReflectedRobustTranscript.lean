/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RobustCert.Assembly
public import LengthSeven.LemmaA.Main

/-! Exact trace data and checks for the reflected four-test residual transcript. -/

set_option autoImplicit false
@[expose] public section

namespace AlbertSequential.FiveTest

open LengthSeven LengthSeven.LemmaA LengthSeven.Robust

/-- The six overlaps, four triangles and three middle-letter traces in the
frozen companion's reflected quadruple. -/
def reflectedTraceTable : TraceTable :=
  ⟨1/2, 5/18, 5/18, 5/18, 5/18, 1/2, 5/36, 5/36, 5/36, 5/36, 41/648, 5/72, 5/72⟩

/-- Budget after absorbing a leading yes on (A) into the anchor. -/
def reflectedSupportCheck (w : Word Letter) : Bool :=
  decide (budgetCost (dropYesA w) ≤ 10)

/-- Check every table term, each residual's exact native constant, and all its
penalty words before merging occurrences. -/
def reflectedEntryCheck (e : Entry) : Bool :=
  e.ok &&
  e.tabs.all (fun m => (fvalQ reflectedTraceTable m.2).isSome && reflectedSupportCheck m.2.toWord) &&
  e.defs.all (fun d =>
    (fvalQ reflectedTraceTable (.yes d.α)).isSome && d.xok reflectedTraceTable &&
    decide (0 ≤ d.c ∧ d.c ≤ 1) &&
    reflectedSupportCheck (yesWord d.α) && reflectedSupportCheck d.long &&
    reflectedSupportCheck d.mid && reflectedSupportCheck d.short) &&
  decide (l1 (e.tabs.map fun m => (m.1,m.2.toWord)) ≤ (17/2 : ℚ)) &&
  decide ((e.defs.map fun d => |d.y|).sum ≤ (97/2 : ℚ))

/-- Unmerged absolute defect weight of the assembled Gram expression. -/
def reflectedDefectWeight (pairs : List (ℚ × Entry)) : ℚ :=
  (pairs.map fun p => (p.2.defs.map fun d => |p.1 * d.y|).sum).sum

end AlbertSequential.FiveTest
