/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ThirteenTracesAndAform

/-! Coefficient support of the expanded thirteen-trace invariant, core Appendix A. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

/-- Each sorted list is the multiset of trace-variable indices of one monomial. -/
def expandedTraceTerms : List (ℤ × List (Fin 13)) := [
  (1, [0, 1, 2, 3, 4, 5]),
  (-1, [0, 1, 2, 9, 9]),
  (-1, [0, 3, 4, 8, 8]),
  (-1, [0, 5, 10, 10]),
  (2, [0, 5, 10, 11]),
  (2, [0, 5, 10, 12]),
  (-1, [0, 5, 11, 11]),
  (-2, [0, 5, 11, 12]),
  (-1, [0, 5, 12, 12]),
  (-2, [0, 8, 9, 10]),
  (2, [0, 8, 9, 11]),
  (2, [0, 8, 9, 12]),
  (-1, [1, 3, 5, 7, 7]),
  (-1, [1, 4, 10, 10]),
  (2, [1, 4, 10, 11]),
  (-2, [1, 4, 10, 12]),
  (-1, [1, 4, 11, 11]),
  (2, [1, 4, 11, 12]),
  (-1, [1, 4, 12, 12]),
  (2, [1, 7, 9, 10]),
  (-2, [1, 7, 9, 11]),
  (2, [1, 7, 9, 12]),
  (-1, [2, 3, 10, 10]),
  (-2, [2, 3, 10, 11]),
  (2, [2, 3, 10, 12]),
  (-1, [2, 3, 11, 11]),
  (2, [2, 3, 11, 12]),
  (-1, [2, 3, 12, 12]),
  (-1, [2, 4, 5, 6, 6]),
  (2, [2, 6, 9, 10]),
  (2, [2, 6, 9, 11]),
  (-2, [2, 6, 9, 12]),
  (2, [3, 7, 8, 10]),
  (2, [3, 7, 8, 11]),
  (-2, [3, 7, 8, 12]),
  (2, [4, 6, 8, 10]),
  (-2, [4, 6, 8, 11]),
  (2, [4, 6, 8, 12]),
  (-2, [5, 6, 7, 10]),
  (2, [5, 6, 7, 11]),
  (2, [5, 6, 7, 12]),
  (-4, [6, 7, 8, 9]),
  (2, [10, 10, 10]),
  (-2, [10, 10, 11]),
  (-2, [10, 10, 12]),
  (-2, [10, 11, 11]),
  (4, [10, 11, 12]),
  (-2, [10, 12, 12]),
  (2, [11, 11, 11]),
  (-2, [11, 11, 12]),
  (-2, [11, 12, 12]),
  (2, [12, 12, 12])
]

def traceMonomialShape (m : List (Fin 13)) : Nat × Nat × Nat :=
  (m.countP (fun i => i < 6), m.countP (fun i => 6 ≤ i && i < 10), m.countP (fun i => 10 ≤ i))

theorem expandedTraceTerms_support :
    expandedTraceTerms.length = 52 ∧ (expandedTraceTerms.map Prod.snd).Nodup ∧
    (∀ t ∈ expandedTraceTerms, t.1 ≠ 0 ∧ t.2.Pairwise (· ≤ ·)) ∧
    ([(6,0,0),(3,2,0),(0,4,0),(2,0,2),(1,2,1),(0,0,3)] : List (Nat × Nat × Nat)).map
      (fun shape => expandedTraceTerms.countP (fun t => traceMonomialShape t.2 == shape)) =
        [1,4,1,18,18,10] := by decide +kernel

theorem expandedTraceTerms_eval (x : Fin 13 → ℝ) :
    ((expandedTraceTerms.map (fun t => (t.1 : ℝ) * (t.2.map x).prod)).sum) =
      fourPointTracePoly (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) := by
  simp [expandedTraceTerms, fourPointTracePoly, fourPointOmegaPoly]
  ring

/-- All four native arguments are simultaneously homogeneous of degree three. -/
theorem fourPointInvariant_multihomogeneous (p : Fin 4 → Albert) (s : Fin 4 → ℝ) :
    fourPointInvariant (fun i => s i • p i) =
      ((s 0 * s 1 * s 2 * s 3)^3) * fourPointInvariant p := by
  simp only [fourPointInvariant, fourPointOmegaPoly, fpOmega1, fpOmega2, fpOmega3,
    fpDoublePair1, fpDoublePair2, fpDoublePair3, fpTriangle, fpOverlap,
    jordanMul_smul_left, jordanMul_smul_right, tracePairing_smul_left, tracePairing_smul_right]
  ring

/-- Coordinates in the coefficient-list order. -/
def expandedTraceCoordinates (q : Fin 4 → Albert) : Fin 13 → ℝ :=
  ![fpOverlap q 0 1, fpOverlap q 0 2, fpOverlap q 0 3,
    fpOverlap q 1 2, fpOverlap q 1 3, fpOverlap q 2 3,
    fpTriangle q 0 1 2, fpTriangle q 0 1 3, fpTriangle q 0 2 3, fpTriangle q 1 2 3,
    fpDoublePair1 q, fpDoublePair2 q, fpDoublePair3 q]

theorem expandedTraceTerms_native (q : Fin 4 → Albert) :
    (expandedTraceTerms.map (fun t => (t.1 : ℝ) * (t.2.map (expandedTraceCoordinates q)).prod)).sum =
      fourPointInvariant q := by
  rw [expandedTraceTerms_eval]
  unfold fourPointInvariant fourPointTracePoly fpOmega1 fpOmega2 fpOmega3
  congr 1

end AlbertSequential
