/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.PentadContinuousCoordinates
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open NativeAnalysis

private def swapJL : OctonionAutomorphism :=
  octAutoOfBasicTriple octI octL octJ rfl rfl rfl
    (by rw [octNormSq_eq_coords]; norm_num [octI]) (by rw [octNormSq_eq_coords]; norm_num [octL])
    (by rw [octNormSq_eq_coords]; norm_num [octJ])
    (by rw [octDot_eq_coords]; norm_num [octI, octL])
    (by rw [octDot_eq_coords]; norm_num [octI, octJ])
    (by rw [octDot_eq_coords]; norm_num [octL, octJ])
    (by rw [octDot_eq_coords]; norm_num [octI, octL, octJ, octonionMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul])

theorem exists_reflectedQuad_interchange :
    ∃ α : OctonionAutomorphism,
      α.equiv octI = octI ∧ α.equiv octJ = octL ∧ α.equiv octL = octJ ∧
      (∀ i, (octAutoToAlbertAuto α).linearEquiv (pentadF i) =
        pentadF ((Equiv.swap (3 : Fin 5) 4) i)) ∧
      (∀ i, (octAutoToAlbertAuto α).linearEquiv (reflQuad i) =
        reflQuad ((Equiv.swap (2 : Fin 4) 3) i)) := by
  let α := swapJL
  have hI : α.equiv octI = octI := by dsimp only [α, swapJL]; exact octAutoOfBasicTriple_I ..
  have hJ : α.equiv octJ = octL := by dsimp only [α, swapJL]; exact octAutoOfBasicTriple_J ..
  have hL : α.equiv octL = octJ := by dsimp only [α, swapJL]; exact octAutoOfBasicTriple_L ..
  let g := octAutoToAlbertAuto α
  have hmap (a b c : Octonion) : (fun j => α.equiv (![a,b,c] j)) =
      ![α.equiv a, α.equiv b, α.equiv c] := by
    funext j
    fin_cases j <;> rfl
  have hp (i : Fin 5) : g.linearEquiv (pentadF i) = pentadF ((Equiv.swap (3 : Fin 5) 4) i) := by
    fin_cases i
    · exact octAutoToAlbertAuto_diagAtom α 0
    · change g.linearEquiv ((1/2 : ℝ) • octDyad ![octOne,octOne,0]) = _
      rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, map_zero]
      rfl
    · change g.linearEquiv ((1/3 : ℝ) • octDyad ![octOne,octI,octOne]) = _
      rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, hI]
      rfl
    · change g.linearEquiv ((1/2 : ℝ) • octDyad ![octOne,octJ,0]) = _
      rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, hJ, map_zero]
      rfl
    · change g.linearEquiv ((1/2 : ℝ) • octDyad ![octOne,octL,0]) = _
      rw [map_smul, entrywiseAuto_dyad, hmap, α.map_one, hL, map_zero]
      rfl
  have hp2 : g.linearEquiv (pentadF 2) = pentadF 2 := hp 2
  have hr : g.linearEquiv reflR = reflR := by rw [reflR, map_sub, map_smul, hp2, g.preserves_unit]
  refine ⟨α, hI, hJ, hL, hp, fun i => ?_⟩
  fin_cases i
  · exact hp 0
  · exact hp 1
  · change g.linearEquiv (quadraticMap reflR (pentadF 3)) = quadraticMap reflR (pentadF 4)
    rw [g.map_quadraticMap, hr]
    exact congrArg (quadraticMap reflR) (hp 3)
  · change g.linearEquiv (quadraticMap reflR (pentadF 4)) = quadraticMap reflR (pentadF 3)
    rw [g.map_quadraticMap, hr]
    exact congrArg (quadraticMap reflR) (hp 4)

end AlbertSequential.FiveTest
