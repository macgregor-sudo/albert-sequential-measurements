/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetHermitianDimensions
public import SubalgebraCoordsAndLine
public import DiagPeirceAnchor
import Mathlib.Tactic.Linarith

/-! The coefficient kernel is the stated native trace-orthogonal complement in the top degree. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF
open HigherJetCoefficients

def HigherJetBase.nativeLevel : HigherJetBase → CDLevel
  | .real => .R
  | .quaternionic => .H

theorem HigherJetBase.project_fixed_iff (b : HigherJetBase) (u : Octonion) :
    b.project u = u ↔ u ∈ (octSubalgebraOfLevel b.nativeLevel).carrier := by
  cases b
  · change octonionScalar (octonionReal u) = u ↔
      u.1.imI = 0 ∧ u.1.imJ = 0 ∧ u.1.imK = 0 ∧ u.2 = 0
    refine ⟨fun h => ?_, fun ⟨hi, hj, hk, hs⟩ => ?_⟩
    · exact ⟨(congrArg (fun v : Octonion => v.1.imI) h).symm,
        (congrArg (fun v : Octonion => v.1.imJ) h).symm,
        (congrArg (fun v : Octonion => v.1.imK) h).symm,
        (congrArg (fun v : Octonion => v.2) h).symm⟩
    · apply Prod.ext
      · apply Quaternion.ext <;> simp [octonionScalar, octonionReal, hi, hj, hk]
      · exact hs.symm
  · change ((u.1, 0) : Octonion) = u ↔ u.2 = 0
    exact ⟨fun h => (congrArg (fun v : Octonion => v.2) h).symm, fun h => Prod.ext rfl h.symm⟩

section LeadingOctonionCoordinates
set_option allowUnsafeReducibility true in
attribute [local reducible] Octonion

theorem HigherJetBase.mem_leadingSpace_iff_octDot (b : HigherJetBase) (u : Octonion) :
    u ∈ b.leadingSpace ↔
      ∀ v : Octonion, b.project v = v → octDot v u = 0 := by
  cases b
  · change octonionReal u = 0 ↔ ∀ v : Octonion, HigherJetBase.real.project v = v → octDot v u = 0
    constructor
    · intro hu v hv
      change octonionScalar (octonionReal v) = v at hv
      rw [← hv, octDot_eq_coords]
      change u.1.re = 0 at hu
      simp [octonionScalar, hu]
    · intro h
      have hv := h (octonionScalar 1) rfl
      rw [octDot_eq_coords] at hv
      simpa [octonionScalar, octonionReal] using hv
  · change u.1 = 0 ↔ ∀ v : Octonion, HigherJetBase.quaternionic.project v = v → octDot v u = 0
    constructor
    · intro hu v hv
      change ((v.1, 0) : Octonion) = v at hv
      rw [← hv, octDot_eq_coords]
      simp [hu]
    · intro h
      have hv := h ((u.1, 0) : Octonion) rfl
      rw [octDot_eq_coords] at hv
      simp only [Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero,
        Quaternion.imK_zero, zero_mul, add_zero] at hv
      apply Quaternion.ext <;>
        simp only [Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
      all_goals
        apply mul_self_eq_zero.mp
        nlinarith [sq_nonneg u.1.re, sq_nonneg u.1.imI, sq_nonneg u.1.imJ, sq_nonneg u.1.imK]

end LeadingOctonionCoordinates

private theorem leadingCoordinates_iff_tracePairing (b : HigherJetBase) (v : Albert) :
    ((∀ i, v.1 i = 0) ∧ ∀ i, v.2 i ∈ b.leadingSpace) ↔
      ∀ w : Albert, w ∈ (H3Subalgebra b.nativeLevel).carrier → tracePairing w v = 0 := by
  constructor
  · rintro ⟨hd, ho⟩ w hw
    have h (i : Fin 3) : octDot (w.2 i) (v.2 i) = 0 := by
      apply (b.mem_leadingSpace_iff_octDot _).mp (ho i)
      apply (b.project_fixed_iff _).mpr
      fin_cases i
      · exact hw.1
      · exact hw.2.1
      · exact hw.2.2
    simp [tracePairing_eq_coords, hd, h]
  · intro h
    refine ⟨fun i => ?_, fun i => (b.mem_leadingSpace_iff_octDot _).mpr fun u hu => ?_⟩
    · simpa only [tracePairing_diagAtom] using h (diagAtom i) (diagAtom_mem_H3Subalgebra _ i)
    · let w : Albert := (0, fun j => if j = i then u else 0)
      have hb : u ∈ (octSubalgebraOfLevel b.nativeLevel).carrier := (b.project_fixed_iff u).mp hu
      have hw : w ∈ (H3Subalgebra b.nativeLevel).carrier := by
        have hmem (j : Fin 3) : w.2 j ∈ (octSubalgebraOfLevel b.nativeLevel).carrier := by
          by_cases hj : j = i
          · simpa [w, hj] using hb
          · simp [w, hj]
        exact ⟨hmem 0, hmem 1, hmem 2⟩
      have hv := h w hw
      rw [tracePairing_eq_coords] at hv
      fin_cases i <;> simpa [w, octDot_zero_left] using hv

private theorem octonionConj_fixed_eq_scalar (u : Octonion) (h : octonionConj u = u) :
    octonionScalar (octonionReal u) = u := by
  have hi := congrArg (fun v : Octonion => v.1.imI) h
  have hj := congrArg (fun v : Octonion => v.1.imJ) h
  have hk := congrArg (fun v : Octonion => v.1.imK) h
  have hq : -u.2 = u.2 := congrArg (fun v : Octonion => v.2) h
  apply Prod.ext
  · apply Quaternion.ext
    · rfl
    · simp [octonionConj] at hi
      change 0 = u.1.imI
      linarith
    · simp [octonionConj] at hj
      change 0 = u.1.imJ
      linarith
    · simp [octonionConj] at hk
      change 0 = u.1.imK
      linarith
  · apply Quaternion.ext
    · have hr := congrArg (fun q : Quaternion ℝ => q.re) hq
      simp at hr
      change 0 = u.2.re
      linarith
    · have hr := congrArg (fun q : Quaternion ℝ => q.imI) hq
      simp at hr
      change 0 = u.2.imI
      linarith
    · have hr := congrArg (fun q : Quaternion ℝ => q.imJ) hq
      simp at hr
      change 0 = u.2.imJ
      linarith
    · have hr := congrArg (fun q : Quaternion ℝ => q.imK) hq
      simp at hr
      change 0 = u.2.imK
      linarith

/-- Each matrix coefficient in the original native Albert coordinates. -/
def higherJetAlbertCoefficient {b : HigherJetBase} {m : Fin 4}
    (M : HigherJetHermitian b m) (n : Fin 4) : Albert :=
  (fun i => octonionReal ((M.val i i).val n),
    ![(M.val 0 1).val n, (M.val 0 2).val n, (M.val 1 2).val n])

theorem albertMatrix_higherJetAlbertCoefficient {b : HigherJetBase} {m : Fin 4}
    (M : HigherJetHermitian b m) (n : Fin 4) (i j : Fin 3) :
    albertMatrix (higherJetAlbertCoefficient M n) i j = (M.val i j).val n := by
  have hs (i j : Fin 3) : octonionConj ((M.val j i).val n) = (M.val i j).val n :=
    congrArg (fun x : HigherJetCoefficients b m => x.val n) (M.property i j)
  have hd (i : Fin 3) : octonionScalar (octonionReal ((M.val i i).val n)) = (M.val i i).val n :=
    octonionConj_fixed_eq_scalar _ (hs i i)
  fin_cases i <;> fin_cases j <;> simp [higherJetAlbertCoefficient, albertMatrix, hs, hd]

private theorem albertZero_diag (i : Fin 3) : (0 : Albert).1 i = 0 := rfl
private theorem albertZero_offDiag (i : Fin 3) : (0 : Albert).2 i = 0 := rfl
private theorem octScalar_zero : octonionScalar 0 = 0 := rfl

/-- The printed `t^m H₃(B)ᗮ` description, using the repository's native trace pairing. -/
theorem higherJetHermitianKernel_iff_top_orthogonal (b : HigherJetBase)
    (M : HigherJetHermitian b b.threshold) :
    M ∈ higherJetHermitianKernel b ↔
      (∀ n, n ≠ b.threshold → higherJetAlbertCoefficient M n = 0) ∧
      ∀ w : Albert, w ∈ (H3Subalgebra b.nativeLevel).carrier →
        tracePairing w (higherJetAlbertCoefficient M b.threshold) = 0 := by
  change (∀ i j, M.val i j ∈ leadingIdeal b) ↔ _
  constructor
  · intro h
    refine ⟨fun n hn => ?_, (leadingCoordinates_iff_tracePairing b _).mp ⟨?_, ?_⟩⟩
    · have hz (i j : Fin 3) : (M.val i j).val n = 0 :=
        ((mem_leadingIdeal b _).mp (h i j)).1 n hn
      apply Prod.ext
      · funext i
        change octonionReal ((M.val i i).val n) = 0
        rw [hz, octonionReal_zero]
      · funext i
        fin_cases i <;> simp [higherJetAlbertCoefficient, hz, albertZero_offDiag]
    · intro i
      exact b.leadingSpace_real_zero _ (((mem_leadingIdeal b _).mp (h i i)).2)
    · intro i
      fin_cases i
      · exact ((mem_leadingIdeal b _).mp (h 0 1)).2
      · exact ((mem_leadingIdeal b _).mp (h 0 2)).2
      · exact ((mem_leadingIdeal b _).mp (h 1 2)).2
  · rintro ⟨hlow, htop⟩ i j
    obtain ⟨hd, ho⟩ := (leadingCoordinates_iff_tracePairing b _).mpr htop
    apply (mem_leadingIdeal b _).mpr
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [← albertMatrix_higherJetAlbertCoefficient M n, hlow n hn]
      fin_cases i <;> fin_cases j <;>
        simp [albertMatrix, albertZero_diag, albertZero_offDiag, octonionConj_zero, octScalar_zero]
    · rw [← albertMatrix_higherJetAlbertCoefficient M b.threshold]
      fin_cases i <;> fin_cases j <;> simp only [albertMatrix]
      all_goals
        first
        | exact ho _
        | exact b.leadingSpace_conj _ (ho _)
        | rw [hd _]; exact b.leadingSpace.zero_mem

end AlbertSequential.AppF
