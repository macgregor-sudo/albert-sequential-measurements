/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanSquareLifts

/-!
The linear well-definedness step of reconstruction, with actual all-history
matching and finite square lifts. Native orbit generators and their cross-term
lifts are explicit inputs. The output is a unital linear map; to make it a Jordan
homomorphism, native purity and reflection intertwining are also required.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Descent
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem cyclicOrbitRelation_zero
    (M : AlgebraicProjectiveData ι A)
    (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w)) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hstar : ∀ i, star (Q i : A) = Q i)
    (hcross : ∀ i j : Option κ, HasSequentialEffectLift M.projection θ
      (associativeJordanProduct
        (unitAndAtomLabels (1 : A) (fun i => (Q i : A)) i)
        (unitAndAtomLabels (1 : A) (fun i => (Q i : A)) j))
      (jmul (unitAndAtomLabels e q i) (unitAndAtomLabels e q j))) :
    ∀ Y, (0, Y) ∈ unitAndAtomRelation e q (1 : Module.End ℝ (CyclicWordSpace M))
      (fun i => cyclicRepresentation M (Q i)) → Y = 0 := by
  intro Y hY
  have hmap : (0, Y) ∈ unitAndAtomRelation e q
      ((cyclicRepresentation M).toLinearMap (1 : wordSubalgebra M.projection))
      (fun i => (cyclicRepresentation M).toLinearMap (Q i)) := by
    simpa only [AlgHom.toLinearMap_apply, map_one] using hY
  obtain ⟨Z, hZ, he⟩ := unitAndAtomRelation_map_lift e q 1 Q
    (cyclicRepresentation M).toLinearMap hmap
  have hZa := unitAndAtomRelation_map e q 1 Q
    (wordSubalgebra M.projection).val.toLinearMap hZ
  change (0, (Z : A)) ∈ unitAndAtomRelation e q 1 (fun i => (Q i : A)) at hZa
  have hself := unitAndAtomRelation_selfAdjoint e q (fun i => (Q i : A)) hstar hZa
  have hsq := unitAndAtomRelation_square_lift M.projection θ e q
    (fun i => (Q i : A)) jmul hcross hZa
  have hz := cyclicRepresentation_eq_zero_of_square_lift M θ U hθ ω hmatch Z hself hsq
  exact he.symm.trans hz

theorem exists_cyclicOrbitLinearMap
    (M : AlgebraicProjectiveData ι A)
    (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w)) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hspan : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤)
    (hstar : ∀ i, star (Q i : A) = Q i)
    (hcross : ∀ i j : Option κ, HasSequentialEffectLift M.projection θ
      (associativeJordanProduct
        (unitAndAtomLabels (1 : A) (fun i => (Q i : A)) i)
        (unitAndAtomLabels (1 : A) (fun i => (Q i : A)) j))
      (jmul (unitAndAtomLabels e q i) (unitAndAtomLabels e q j))) :
    ∃ η : J →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M),
      η e = 1 ∧ (∀ i, η (q i) = cyclicRepresentation M (Q i)) ∧
      (∀ x, (x, η x) ∈ unitAndAtomRelation e q 1
        (fun i => cyclicRepresentation M (Q i))) := by
  let R := unitAndAtomRelation e q (1 : Module.End ℝ (CyclicWordSpace M))
    (fun i => cyclicRepresentation M (Q i))
  have htotal := unitAndAtomRelation_total e q (1 : Module.End ℝ (CyclicWordSpace M))
    (fun i => cyclicRepresentation M (Q i)) hspan
  have hzero := cyclicOrbitRelation_zero M θ U hθ ω hmatch e q Q jmul hstar hcross
  let η := descendedLinearMap R htotal hzero
  refine ⟨η, ?_, ?_, ?_⟩
  · exact descendedLinearMap_eq_of_mem R htotal hzero
      (unitAndAtomRelation_generator e q 1 (fun i => cyclicRepresentation M (Q i)) none)
  · intro i
    exact descendedLinearMap_eq_of_mem R htotal hzero
      (unitAndAtomRelation_generator e q 1 (fun i => cyclicRepresentation M (Q i)) (some i))
  · intro x
    exact descendedLinearMap_graph R htotal hzero x

end Descent
end AlbertSequential
