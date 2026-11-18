/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OrbitLinearDescent

/-!
Expectation preservation for the reconstructed linear map. This is a genuine
statement about the cyclic vector and the original normalized positive
functional; no faithful state or trace-cyclic identity is introduced.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Expectation
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem cyclicOrbitLinearMap_expectation
    (M : AlgebraicProjectiveData ι A) (θ : Word ι → J) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (he : HasSequentialEffectLift M.projection θ 1 e)
    (hq : ∀ i, HasSequentialEffectLift M.projection θ (Q i : A) (q i))
    (η : J →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M))
    (hgraph : ∀ x, (x, η x) ∈ unitAndAtomRelation e q 1
      (fun i => cyclicRepresentation M (Q i))) (x : J) :
    cyclicExpectation M (η x (cyclicVector M)) = ω x := by
  have hmap : (x, η x) ∈ unitAndAtomRelation e q
      ((cyclicRepresentation M).toLinearMap (1 : wordSubalgebra M.projection))
      (fun i => (cyclicRepresentation M).toLinearMap (Q i)) := by
    simpa only [AlgHom.toLinearMap_apply, map_one] using hgraph x
  obtain ⟨Z, hZ, hη⟩ := unitAndAtomRelation_map_lift e q 1 Q
    (cyclicRepresentation M).toLinearMap hmap
  change cyclicRepresentation M Z = η x at hη
  have hZa := unitAndAtomRelation_map e q 1 Q
    (wordSubalgebra M.projection).val.toLinearMap hZ
  change (x, (Z : A)) ∈ unitAndAtomRelation e q 1 (fun i => (Q i : A)) at hZa
  have hlift := unitAndAtomRelation_lift M.projection θ e q (fun i => (Q i : A)) he hq hZa
  calc
    cyclicExpectation M (η x (cyclicVector M)) =
        cyclicExpectation M (cyclicRepresentation M Z (cyclicVector M)) := by rw [hη]
    _ = M.state (Z : A) := cyclicExpectation_action_vector M Z
    _ = ω x := sequentialEffectLift_expectation M.projection θ M.state ω hmatch hlift

end Expectation
end AlbertSequential
