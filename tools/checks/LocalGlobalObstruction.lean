module

import CompanionLocalGlobal

open AlbertSequential

example : (fun i : Fin 5 => fourPointInvariant (i.removeNth companionCConfig)) =
    ![0, 0, 0, 0, 1 / 5832] := companionCConfig_facetValues

example : orderedTupleCoboundary fourPointAtomCochain companionCAtoms ≠ 0 := by
  rw [companionCConfig_coboundary]
  norm_num

example {G : Type*} [AddCommGroup G] (v n : ℕ) (c : FullSimplex v (n + 1) → G)
    (h : ∀ s, fullSimplexCoboundary c s = 0) :
    ∃ b : FullSimplex v n → G, ∀ s, fullSimplexCoboundary b s = c s :=
  (fullSimplex_positiveCocycle_iff_coboundary c).mp h

example {G : Type*} [AddCommGroup G] (c : FullSimplex 4 0 → G) :
    (∀ s, fullSimplexCoboundary c s = 0) ↔ ∃ x, ∀ s, c s = x :=
  fullSimplex_zeroCocycle_iff_constant c

#print axioms companionCConfig_facetValues
#print axioms companionCConfig_coboundary
#print axioms fourPointAtomCochain_not_cocycle
#print axioms containingQuaternionicWindows_univ_nonempty
#print axioms fullSimplexCoboundary_squared
#print axioms fullSimplex_contraction
#print axioms fullSimplex_positiveCocycle_iff_coboundary
#print axioms fullSimplex_zeroCocycle_iff_constant

#print axioms fullSimplex_realization_contractible
