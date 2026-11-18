/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSCornerScalars
public import Mathlib.Tactic.Positivity

/-! The constructor's scalar-only conditions for every literal fixed-S base.
Pair/triple numbers are reused, not recomputed in coordinates. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis

theorem fixedSCorner_overlap_native (j a b : Fin 4) :
    nativeOverlaps (fixedSCornerMenu j) a b =
      nativeOverlaps fixedS (fixedSCornerRelabelling j a) (fixedSCornerRelabelling j b) := rfl

theorem fixedSCorner_triangle_native (j a b c : Fin 4) :
    nativeTriangles (fixedSCornerMenu j) a b c =
      nativeTriangles fixedS (fixedSCornerRelabelling j a)
        (fixedSCornerRelabelling j b) (fixedSCornerRelabelling j c) := rfl

theorem fixedSCorner_overlap_table (j a b : Fin 4) :
    nativeOverlaps (fixedSCornerMenu j) a b = (fixedSCornerData j).overlap a b := by
  rw [fixedSCorner_overlap_native, nativeOverlaps_fixedS_eq]
  simp only [fixedSCornerRelabelling_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [fixedSCornerOrder, fixedSCornerData, fixedSABCornerData, fixedSCDCornerData,
      CornerNumericalData.overlap]

theorem fixedSCorner_triangle_values (j : Fin 4) :
    nativeTriangles (fixedSCornerMenu j) 0 1 2 = (fixedSCornerData j).r012 ∧
    nativeTriangles (fixedSCornerMenu j) 0 2 3 = (fixedSCornerData j).r023 ∧
    nativeTriangles (fixedSCornerMenu j) 0 3 1 = (fixedSCornerData j).r031 ∧
    nativeTriangles (fixedSCornerMenu j) 1 2 3 = (fixedSCornerData j).r123 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [fixedSCorner_triangle_native, nativeTriangles_fixedS_eq]
  all_goals simp only [fixedSCornerRelabelling_apply]
  all_goals fin_cases j <;> norm_num [fixedSCornerOrder, fixedSCornerData,
    fixedSABCornerData, fixedSCDCornerData, fixedSTriangleVal]

theorem signedAccessScalar_value {ι : Type*} (c : Word ι → ℝ) (b d : ι) :
    weightedWordScalar c (accessWordTerms b [(d, true)]) =
      c [(d, true)] + c [(b, true), (d, true)] - c [(b, false), (d, true)] := by
  simp only [weightedWordScalar, accessWordTerms, signedAccessChoices, accessPrefix,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, neg_one_mul, add_zero]
  ring

theorem jordanTriple_eq_access (x y z : Albert) :
    jordanTriple x y z = jordanMul x (jordanMul y z) +
      jordanMul z (jordanMul x y) - jordanMul y (jordanMul x z) := by
  rw [jordanTriple, jordanMul_comm (jordanMul x y) z,
    jordanMul_comm (jordanMul z y) x, jordanMul_comm (jordanMul x z) y,
    jordanMul_comm z y]
  module

theorem fixedSCorner_pair_access (j a b : Fin 4) :
    fixedSCornerScalar j a [(b, true)] = nativeOverlaps (fixedSCornerMenu j) a b := by
  rw [fixedSCornerScalar, nativeWordProbability_eq_pairing,
    nativeWordEffect_singleton (fixedSCornerMenu j) (fun i => (fixedSCorner_isAtom j i).1)]
  rfl

theorem fixedSCorner_triangle_access (j a b c : Fin 4) :
    fixedSCornerScalar j a [(c, true)] + fixedSCornerScalar j a [(b, true), (c, true)] -
      fixedSCornerScalar j a [(b, false), (c, true)] =
        2 * nativeTriangles (fixedSCornerMenu j) a b c := by
  rw [← signedAccessScalar_value]
  exact native_scalar_triangle_access (fixedSCornerMenu j)
    (fun i => (fixedSCorner_isAtom j i).1) (fixedSCornerMenu j a) b c

theorem fixedSCorner_triple_access (j a b c d : Fin 4) :
    weightedWordScalar (fixedSCornerScalar j a) (polarizedTripleWordTerms b c d) =
      4 * tracePairing (fixedSCornerMenu j a)
        (jordanTriple (fixedSCornerMenu j b) (fixedSCornerMenu j c) (fixedSCornerMenu j d)) := by
  rw [jordanTriple_eq_access]
  exact native_scalar_polarizedTriple_access (fixedSCornerMenu j)
    (fun i => (fixedSCorner_isAtom j i).1) (fixedSCornerMenu j a) b c d

theorem fixedSCorner_normalizers_nonzero (j : Fin 4) :
    ∀ i, (fixedSCornerData j).normalizer i ≠ 0 := by
  have h18 : Real.sqrt (1 / 18 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h27 : Real.sqrt (1 / 27 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  intro i
  fin_cases j <;> fin_cases i <;>
    first | exact h18 | exact h27

theorem fixedSCorner_normalizers_square (j : Fin 4) :
    ∀ i, (fixedSCornerData j).normalizer i ^ 2 = (fixedSCornerData j).normalizerSquare i := by
  have h18 : Real.sqrt (1 / 18 : ℝ) ^ 2 = 1 / 18 := Real.sq_sqrt (by norm_num)
  have h27 : Real.sqrt (1 / 27 : ℝ) ^ 2 = 1 / 27 := Real.sq_sqrt (by norm_num)
  intro i
  fin_cases j <;> fin_cases i <;>
    norm_num [fixedSCornerData, fixedSABCornerData, fixedSCDCornerData,
      CornerNumericalData.normalizer, CornerNumericalData.normalizerSquare, h18, h27]

theorem fixedSCorner_conditions (j : Fin 4) :
    CornerScalarConditions (fixedSCornerData j) (fixedSCornerScalar j) := by
  refine ⟨fixedSCorner_normalizers_nonzero j, fixedSCorner_normalizers_square j,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b _hab
    rw [fixedSCorner_pair_access, fixedSCorner_overlap_table]
  · rw [fixedSCorner_triangle_access, (fixedSCorner_triangle_values j).1]
  · rw [fixedSCorner_triangle_access, (fixedSCorner_triangle_values j).2.1]
  · rw [fixedSCorner_triangle_access, (fixedSCorner_triangle_values j).2.2.1]
  · rw [fixedSCorner_triangle_access, (fixedSCorner_triangle_values j).2.2.2]
  · rw [fixedSCorner_triple_access]
    have h := congrFun (fixedSCorner_Q j) 0
    change tracePairing (fixedSCornerMenu j 0)
      (jordanTriple (fixedSCornerMenu j 1) (fixedSCornerMenu j 2) (fixedSCornerMenu j 3)) = 1 / 18 at h
    rw [h]
    fin_cases j <;> rfl
  · rw [fixedSCorner_triple_access]
    have h := congrFun (fixedSCorner_Q j) 1
    change tracePairing (fixedSCornerMenu j 0)
      (jordanTriple (fixedSCornerMenu j 2) (fixedSCornerMenu j 3) (fixedSCornerMenu j 1)) = 1 / 18 at h
    rw [h]
    fin_cases j <;> rfl
  · rw [fixedSCorner_triple_access]
    have h := congrFun (fixedSCorner_Q j) 2
    change tracePairing (fixedSCornerMenu j 0)
      (jordanTriple (fixedSCornerMenu j 3) (fixedSCornerMenu j 1) (fixedSCornerMenu j 2)) = 1 / 18 at h
    rw [h]
    fin_cases j <;> rfl

end AlbertSequential
