/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneratedAlbertOperations
public import CyclicOrbitReconstruction

/-!
The native-Albert atom-menu instance of Proposition prop:bri:eta,
including proper generated subalgebras. Native
word effects and reflection orbits are restricted to their actual generated
Jordan algebra, which may be proper. No all-Albert generation is assumed.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

section GeneratedReconstruction
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem exists_generatedCyclicJordanMap (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hmatch : M.Matches p ρ) :
    ∃ η : GeneratedAlbert p hp →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M),
      (∀ x y, η (generatedJordanProduct p hp x y) = associativeJordanProduct (η x) (η y)) ∧
      η (generatedUnit p hp) = 1 ∧
      ∀ x, cyclicExpectation M (η x (cyclicVector M)) = tracePairing ρ (x : Albert) := by
  let e := generatedUnit p hp
  let q := generatedOrbitPoint p hp
  let Q := cyclicOrbitProjection M
  let θ := generatedWordEffect p hp
  let H := (nativeOrbitSpan p hp).subtype
  let weight := generatedOrbitWeight p hp
  let R := generatedReflectionUpdate p hp
  have hθ : ∀ a w, θ (a :: w) = generatedOutcomeUpdate p hp a (θ w) := fun _ _ => rfl
  have hm : ∀ w, M.probability w = generatedExpectation p hp ρ (θ w) := by
    intro w
    exact (hmatch w).trans (nativeWordProbability_eq_pairing p ρ w)
  have he : HasSequentialEffectLift M.projection θ 1 e := by
    have hnil : θ [] = e := rfl
    simpa only [wordOperator_nil, hnil] using hasSequentialEffectLift_word M.projection θ []
  have hq : ∀ α, HasSequentialEffectLift M.projection θ (Q α : A) (q α) := by
    intro α
    apply sequentialEffectLift_of_injective_native M.projection θ H (nativeOrbitSpan p hp).injective_subtype
    exact nativeOrbitProjection_has_lift M p hp α
  have hQ : ∀ α, (Q α : A) * Q α = Q α :=
    fun α => orbitProjection_idempotent M.projection M.idempotent M.selfAdjoint α.1 α.2
  have hQstar : ∀ α, star (Q α : A) = Q α :=
    fun α => orbitProjection_star M.projection M.selfAdjoint α.1 α.2
  have hQlabel : ∀ α β, Q (reflectedOrbitLabel α β) =
      ((2 : ℝ) • Q α - 1) * Q β * ((2 : ℝ) • Q α - 1) := by
    intro α β
    exact Subtype.ext (orbitProjection_reflected_label M.projection M.idempotent M.selfAdjoint α β)
  have hcorner : ∀ α {Z x}, HasSequentialEffectLift M.projection θ Z x →
      HasSequentialEffectLift M.projection θ ((Q α : A) * Z * Q α) (weight α x • q α) := by
    intro α Z x hZ
    apply sequentialEffectLift_of_injective_native M.projection θ H (nativeOrbitSpan p hp).injective_subtype
    have hraw := sequentialEffectLift_map_native M.projection θ H hZ
    have h := hasSequentialEffectLift_orbit_corner M.projection (nativeWordEffect p)
      (nativeOutcomeUpdate p) M.selfAdjoint (fun _ _ => rfl) α.1 α.2 hraw
    rw [orbitCornerUpdate_native p hp,
      quadraticMap_atom _ _ (nativeOrbitPoint_isAtom p hp α)] at h
    exact h
  have hreflect : ∀ α {Z x}, HasSequentialEffectLift M.projection θ Z x →
      HasSequentialEffectLift M.projection θ
        (((2 : ℝ) • (Q α : A) - 1) * Z * ((2 : ℝ) • (Q α : A) - 1)) (R α x) := by
    intro α Z x hZ
    apply sequentialEffectLift_of_injective_native M.projection θ H (nativeOrbitSpan p hp).injective_subtype
    have hraw := sequentialEffectLift_map_native M.projection θ H hZ
    have h := hasSequentialEffectLift_orbit_reflection M.projection (nativeWordEffect p)
      (nativeOutcomeUpdate p) M.idempotent M.selfAdjoint (fun _ _ => rfl) α.1 α.2 hraw
    rw [orbitReflectionUpdate_native p hp] at h
    exact h
  obtain ⟨η, hjordan, hunit, hηq, hexp⟩ := exists_cyclicOrbitJordanMap M θ
    (generatedOutcomeUpdate p hp) hθ (generatedExpectation p hp ρ) hm e q Q
    (generatedJordanProduct p hp) (generatedJordanProduct_unit p hp) (generatedOrbitPoints_span p hp)
    weight R (generatedOrbitWeight_unit p hp) (generatedOrbitWeight_symmetric p hp)
    (generatedPeirce_identity p hp) reflectedOrbitLabel (generatedReflection_unit p hp)
    (generatedReflection_label p hp) he hq hQ hQstar hQlabel hcorner hreflect
  exact ⟨η, hjordan, hunit, hexp⟩

end GeneratedReconstruction
end AlbertSequential
