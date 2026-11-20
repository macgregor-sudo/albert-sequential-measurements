module

import Ends.UniformSevenMargin

open AlbertSequential AlbertSequential.Ends
open scoped Matrix

universe u

attribute [local irreducible] fourPointInvariant

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    0 < uniformSevenMargin p ∧
      IsLeast (uniformSevenError p '' hilbertProjectiveTables.{u} ℝ 4) (uniformSevenMargin p) ∧
      IsLeast (uniformSevenError p '' hilbertProjectiveTables.{u} ℂ 4) (uniformSevenMargin p) ∧
      IsLeast (uniformSevenError p '' quaternionicProjectiveTables.{u} 4) (uniformSevenMargin p) :=
  ⟨uniformSevenMargin_pos p hp hA, uniformSevenMargin_physical_minima.{u} p⟩

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∀ δ : ℝ, (∃ F : Finset (Word (Fin 4)), (∀ w ∈ F, w.length ≤ 7 ∧ w.head? = some (0,true)) ∧
      ∀ g ∈ hilbertProjectiveTables.{u} ℝ 4, ∃ w ∈ F,
        δ ≤ |g w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) ↔ δ ≤ uniformSevenMargin p :=
  exists_finiteWitnessGap_iff_le_uniformSevenMargin.{u} p hp

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    IsLeast ((fun (g : Word (Fin 4) → ℝ) => |g [(0,true)] -
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) [(0,true)]|) ''
      hilbertProjectiveTables.{u} ℂ 4) 0 := by
  let W : Finset (Word (Fin 4)) := {[(0,true)]}
  have hwne : W.Nonempty := Finset.singleton_nonempty _
  have hwShort (w : Word (Fin 4)) (hw : w ∈ W) : w.length ≤ 6 := by
    rw [Finset.mem_singleton.mp hw]
    decide
  have h := (uniformSixError_physical_minima.{u} p hp hA W hwne hwShort).2.1
  simpa only [W, finiteWordError, Finset.sup'_singleton] using h

#check @uniformSevenMargin_physical_witness
#print axioms mem_reducedSevenAYesWords
#print axioms sevenAYesWordError_eq_reduced
#print axioms uniformSevenMargin_moment_minimum
#print axioms uniformSevenMargin_pos
#print axioms hilbertProjectiveTables_real_eq_moment_image
#print axioms uniformSevenMargin_physical_minima
#print axioms exists_finiteWitnessGap_iff_le_uniformSevenMargin
#print axioms uniformSixError_physical_minima
#print axioms uniformSevenMargin_physical_witness
