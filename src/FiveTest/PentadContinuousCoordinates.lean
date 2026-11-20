/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Quad
public import WindowProbabilityChart
public import MatchingModels.FiveTestClifford
import BlockB.StateSupport
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open NativeAnalysis WindowProbability

/-- The actual family in companion Appendix A.7. Only the fifth atom varies. -/
def continuousPentad (u : Octonion) (i : Fin 5) : Albert :=
  if i = 4 then (1/2 : ℝ) • chartDyad u 0 else pentadF i

theorem continuousPentad_isAtom (u : Octonion) (hunit : octNormSq u = 1) (i : Fin 5) :
    IsAtom (continuousPentad u i) := by
  by_cases hi : i = 4
  · have htr : albertTrace (chartDyad u 0) = 2 := by
      rw [chartDyad_trace, hunit, (octNormSq_eq_zero _).mpr rfl]
      norm_num
    have ha := chartDyad_normalize_isAtom u 0
    rw [htr, ← one_div] at ha
    simpa [continuousPentad, hi] using ha
  · simpa [continuousPentad, hi] using pentadF_isAtom i

theorem continuousPentad_at_octL : continuousPentad octL = pentadF := by
  funext i
  fin_cases i <;> rfl

theorem entrywiseAuto_dyad (α : OctonionAutomorphism) (v : Fin 3 → Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (octDyad v) =
      octDyad (fun i => α.equiv (v i)) := by
  apply Prod.ext <;> funext i
  · change octNormSq (v i) = octNormSq (α.equiv (v i))
    exact (α.map_normSq _).symm
  · fin_cases i
    · change α.equiv (octonionMul (v 0) (octonionConj (v 1))) =
        octonionMul (α.equiv (v 0)) (octonionConj (α.equiv (v 1)))
      rw [α.map_mul, α.map_conj]
    · change α.equiv (octonionMul (v 0) (octonionConj (v 2))) =
        octonionMul (α.equiv (v 0)) (octonionConj (α.equiv (v 2)))
      rw [α.map_mul, α.map_conj]
    · change α.equiv (octonionMul (v 1) (octonionConj (v 2))) =
        octonionMul (α.equiv (v 1)) (octonionConj (α.equiv (v 2)))
      rw [α.map_mul, α.map_conj]

theorem entrywiseAuto_continuousPentad (α : OctonionAutomorphism)
    (hI : α.equiv octI = octI) (hJ : α.equiv octJ = octJ) (u : Octonion) (i : Fin 5) :
    (octAutoToAlbertAuto α).linearEquiv (continuousPentad u i) = continuousPentad (α.equiv u) i := by
  have hmap (a b c : Octonion) : (fun j => α.equiv (![a,b,c] j)) =
      ![α.equiv a, α.equiv b, α.equiv c] := by
    funext j
    fin_cases j <;> rfl
  fin_cases i
  · exact octAutoToAlbertAuto_diagAtom α 0
  · change (octAutoToAlbertAuto α).linearEquiv ((1/2 : ℝ) • octDyad ![octOne,octOne,0]) = _
    rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, map_zero]
    rfl
  · change (octAutoToAlbertAuto α).linearEquiv ((1/3 : ℝ) • octDyad ![octOne,octI,octOne]) = _
    rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, hI]
    rfl
  · change (octAutoToAlbertAuto α).linearEquiv ((1/2 : ℝ) • octDyad ![octOne,octJ,0]) = _
    rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, hJ, map_zero]
    rfl
  · change (octAutoToAlbertAuto α).linearEquiv ((1/2 : ℝ) • octDyad ![octOne,u,0]) = _
    rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, map_zero]
    rfl

/-- Reduce an arbitrary allowed axis to the exact two-coordinate family by a
single native automorphism fixing the first four atoms. -/
theorem exists_rotate_continuousPentad (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0) :
    ∃ (g : NativeAlbertAutomorphism) (d : ℝ), 0 ≤ d ∧ (octDot u octK)^2 + d^2 = 1 ∧
      ∀ i, g.linearEquiv (continuousPentad u i) =
        continuousPentad (octDot u octK • octK + d • octL) i := by
  obtain ⟨α, hαI, hαJ, hαK, a, b, c, k, d, hd, he⟩ := exists_octAuto_fix_IJ_to_IJL u
  have ha : a = 0 := by
    have h := α.map_real u
    rw [he, hre] at h
    simp [octonionReal_add, octonionReal_smul, octonionReal_one,
      show octonionReal octI = 0 from rfl, show octonionReal octJ = 0 from rfl,
      show octonionReal octK = 0 from rfl, show octonionReal octL = 0 from rfl] at h
    exact h
  have hcoords (r s t e : ℝ) :
      (r • octI + s • octJ + t • octK + e • octL).1 = ⟨0,r,s,t⟩ ∧
      (r • octI + s • octJ + t • octK + e • octL).2 = ⟨e,0,0,0⟩ := by
    have hsmul₁ (a : ℝ) (x : Octonion) : (a • x).1 = a • x.1 := rfl
    have hsmul₂ (a : ℝ) (x : Octonion) : (a • x).2 = a • x.2 := rfl
    have hadd₁ (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
    have hadd₂ (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
    constructor
    · simp only [hadd₁, hsmul₁]
      apply Quaternion.ext <;> simp [octI, octJ, octK, octL]
    · simp only [hadd₂, hsmul₂]
      apply Quaternion.ext <;> simp [octI, octJ, octK, octL]
  rw [ha, zero_smul, zero_add] at he
  obtain ⟨hfst, hsnd⟩ := hcoords b c k d
  have hb : b = 0 := by
    have h := α.map_dot u octI
    rw [hαI, he, hI, octDot_eq_coords, hfst, hsnd] at h
    simpa [octI] using h
  have hc : c = 0 := by
    have h := α.map_dot u octJ
    rw [hαJ, he, hJ, octDot_eq_coords, hfst, hsnd] at h
    simpa [octJ] using h
  have hk : k = octDot u octK := by
    have h := α.map_dot u octK
    rw [hαK, he, octDot_eq_coords, hfst, hsnd] at h
    simpa [octK, octDot_eq_coords] using h
  have hn := α.map_normSq u
  rw [he, hu, octNormSq_eq_coords, hfst, hsnd, hb, hc, hk] at hn
  have he' : α.equiv u = octDot u octK • octK + d • octL := by
    simpa [hb, hc, hk] using he
  refine ⟨octAutoToAlbertAuto α, d, hd, ?_, fun i => ?_⟩
  · simpa using hn
  · rw [entrywiseAuto_continuousPentad α hαI hαJ, he']

/-- The complement update block X = (no 2, no 1, no 3, no 2). -/
def continuousPentadPrefixState : Albert :=
  quadraticMap (albertUnit - pentadF 2)
    (quadraticMap (albertUnit - pentadF 3)
      (quadraticMap (albertUnit - pentadF 1)
        (quadraticMap (albertUnit - pentadF 2) (pentadF 0))))

private def qPrefixState : QA :=
  let q (i : Fin 5) := QA.unit.sub (qpent i)
  (q 2).U ((q 3).U ((q 1).U ((q 2).U (qpent 0))))

private def qPrefixStateCoordinates : QA :=
  (⟨53,17,50, QO.mk8 (-6) 10 21 (-18) 0 0 0 0,
    QO.mk8 (-43) 6 18 21 0 0 0 0, QO.mk8 6 (-7) 21 (-18) 0 0 0 0⟩ : QA).smul (1/648)

private theorem continuousPentadPrefixState_eq :
    continuousPentadPrefixState = castA qPrefixStateCoordinates := by
  have h : qPrefixState = qPrefixStateCoordinates := by decide +kernel
  rw [← h]
  simp only [qPrefixState, castA_U, castA_sub, castA_unit, ← pentadF_eq_cast]
  rfl

private theorem chartDyad_line (u : Octonion) (hre : octonionReal u = 0)
    (hu : octNormSq u = 1) : chartDyad u 0 = (![1,1,0], ![-u,0,0]) := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · exact octNormSq_one
  · exact hu
  · exact (octNormSq_eq_zero _).mpr rfl
  · change octonionMul octOne (octonionConj u) = -u
    rw [octonionMul_one_left, octonionConj_eq_neg_of_real_zero hre]
  · change octonionMul octOne (octonionConj 0) = 0
    rw [octonionMul_one_left, octonionConj_zero]
  · change octonionMul u (octonionConj 0) = 0
    rw [octonionConj_zero, octonionMul_zero_right]

/-- The literal printed five-letter probability 35/648 + ⟨u,ij⟩/36 for every allowed axis. -/
theorem continuousPentad_shortWord_probability (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0) :
    nativeWordProbability (continuousPentad u) (pentadF 0)
      [(2,false),(1,false),(3,false),(2,false),(4,true)] =
      (35/648 : ℝ) + octDot u octK / 36 := by
  change albertTrace (quadraticMap (continuousPentad u 4) continuousPentadPrefixState) = _
  rw [albertTrace_quadraticMap, (continuousPentad_isAtom u hu 4).1]
  change tracePairing ((1/2 : ℝ) • chartDyad u 0) continuousPentadPrefixState = _
  rw [continuousPentadPrefixState_eq, tracePairing_smul_left, tracePairing_eq_coords,
    chartDyad_line u hre hu]
  let x := castA qPrefixStateCoordinates
  change (1/2 : ℝ) * ((1 * x.1 0 + 1 * x.1 1 + 0 * x.1 2) +
    2 * (octDot (-u) (x.2 0) + octDot 0 (x.2 1) + octDot 0 (x.2 2))) = _
  have h0 : u.1.re = 0 := hre
  have h1 : u.1.imI = 0 := by
    rw [octDot_eq_coords] at hI
    simpa [octI] using hI
  have h2 : u.1.imJ = 0 := by
    rw [octDot_eq_coords] at hJ
    simpa [octJ] using hJ
  rw [octDot_neg_left, octDot_zero_left, octDot_zero_left]
  simp only [octDot_eq_coords]
  norm_num [x, castA, castO, castQ, qPrefixStateCoordinates, QA.smul, QO.smul, QQ.smul, QO.mk8,
    octK, h0, h1, h2]
  ring

/-- The full ten-letter return word is the square of the printed affine probability. -/
theorem continuousPentad_returnWord_probability (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0) :
    nativeWordProbability (continuousPentad u) (pentadF 0) MatchingModels.pentadSepWord10 =
      ((35/648 : ℝ) + octDot u octK / 36)^2 := by
  let F := continuousPentad u
  let q (i : Fin 5) := albertUnit - F i
  let X := continuousPentadPrefixState
  let R (x : Albert) :=
    quadraticMap (q 2) (quadraticMap (q 1) (quadraticMap (q 3) (quadraticMap (q 2) x)))
  have hf : tracePairing (F 4) X = (35/648 : ℝ) + octDot u octK / 36 := by
    have h := continuousPentad_shortWord_probability u hu hre hI hJ
    change albertTrace (quadraticMap (F 4) X) = _ at h
    rwa [albertTrace_quadraticMap, (continuousPentad_isAtom u hu 4).1] at h
  have hr : tracePairing (F 0) (R (F 4)) = tracePairing (F 4) X := by
    dsimp only [R]
    rw [← quadraticMap_self_adjoint, ← quadraticMap_self_adjoint,
      ← quadraticMap_self_adjoint, ← quadraticMap_self_adjoint, tracePairing_comm]
    rfl
  change albertTrace (quadraticMap (F 0) (R (quadraticMap (F 4) X))) = _
  rw [quadraticMap_atom (F 4) X (continuousPentad_isAtom u hu 4)]
  dsimp only [R]
  have ha0 : jordanMul (F 0) (F 0) = F 0 := (continuousPentad_isAtom u hu 0).1
  simp only [quadraticMap_smul_right, albertTrace_smul, albertTrace_quadraticMap, ha0]
  change tracePairing (F 4) X * tracePairing (F 0) (R (F 4)) = _
  rw [hr, hf, pow_two]

theorem continuousPentad_returnWord_mixed_probability (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0) :
    nativeWordProbability (continuousPentad u) ((1/3 : ℝ) • albertUnit)
      MatchingModels.pentadSepWord11 = (1/3 : ℝ) * ((35/648 : ℝ) + octDot u octK / 36)^2 := by
  rw [MatchingModels.pentadSepWord11,
    BlockB.nativeWordProbability_cons_yes_e3 _ _ (continuousPentad_isAtom u hu 0)]
  exact congrArg (fun r : ℝ => (1/3 : ℝ) * r)
    (continuousPentad_returnWord_probability u hu hre hI hJ)

end AlbertSequential.FiveTest
