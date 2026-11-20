/- SPDX-License-Identifier: Apache-2.0 -/
module

import EvenHyperplaneReflections

open Submodule

example (g : EuclideanSpace ℝ (Fin 9) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 9))
    (hg : LinearMap.det g.toLinearMap = 1) :
    ∃ N : List (EuclideanSpace ℝ (Fin 9)), (∀ v ∈ N, ‖v‖ = 1) ∧ Even N.length ∧
      N.length ≤ 8 ∧ g = (N.map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod := by
  obtain ⟨N,hN,he,hl,hgN⟩ := AlbertSequential.exists_even_unit_reflections g hg
  have h9 : N.length ≤ 9 := by simpa using hl
  obtain ⟨k,hk⟩ := he
  exact ⟨N,hN,⟨k,hk⟩,by omega,hgN⟩

#print axioms AlbertSequential.exists_even_unit_reflections
