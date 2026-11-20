/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneratedOrbitUpdates
public import CyclicOrbitReconstruction

/-! The algebraic cyclic reconstruction for a full menu of primitive tests in its own EJA. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace AlbertSequential.UnitalJordanProduct
variable {E I A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : UnitalJordanProduct E) (q : I → E)
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem primitive_orbit_labels_span (hinner : ∀ x y z, inner ℝ (P.product x y) z =
    inner ℝ x (P.product y z)) (hp : ∀ i, P.IsPrimitive (q i)) (hg : P.GeneratesMenu q) :
    Submodule.span ℝ (Set.range (unitAndAtomLabels P.unit
      (fun α : ReflectionOrbitLabel I => P.reflectedMenuPoint q α.1 α.2))) = ⊤ := by
  rw [← P.reflectedMenuSpan_eq_top q hinner hp hg]
  unfold reflectedMenuSpan
  congr 1
  ext x
  constructor
  · rintro ⟨_ | a, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨a,rfl⟩
  · rintro (rfl | ⟨a,rfl⟩)
    · exact ⟨none,rfl⟩
    · exact ⟨some a,rfl⟩

theorem primitive_orbit_cyclic_reconstruction (M : AlgebraicProjectiveData I A)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hp : ∀ i, P.IsPrimitive (q i)) (hg : P.GeneratesMenu q)
    (ω : E →ₗ[ℝ] ℝ) (hm : ∀ w, M.probability w = ω (P.sequentialWordEffect q w)) :
    ∃ η : E →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M),
      (∀ x y, η (P.product x y) = associativeJordanProduct (η x) (η y)) ∧ η P.unit = 1 ∧
      (∀ α : ReflectionOrbitLabel I, η (P.reflectedMenuPoint q α.1 α.2) =
        cyclicRepresentation M (cyclicOrbitProjection M α)) ∧
      ∀ x, cyclicExpectation M (η x (cyclicVector M)) = ω x := by
  let hfr := P.formallyReal_of_associative_inner hinner
  let a := fun α : ReflectionOrbitLabel I => P.reflectedMenuPoint q α.1 α.2
  let Q := cyclicOrbitProjection M
  let θ := P.sequentialWordEffect q
  let U := P.menuOutcomeUpdate q
  have hθ : ∀ o w, θ (o::w) = U o (θ w) := fun _ _ => rfl
  have hap (α) : P.IsPrimitive (a α) := P.reflectedMenuPoint_primitive q hp _ _
  let W := fun α => P.canonicalPairingFunctional hfr (a α)
  let R := fun α => P.idempotentReflection (a α)
  have hweight (α x) : P.quadraticRepresentation (a α) x = W α x • a α :=
    P.canonicalTraceOfFormallyReal_primitive_compression hfr _ _ (hap α)
  refine exists_cyclicOrbitJordanMap M θ U hθ ω hm P.unit a Q P.product P.unit_left
    (P.primitive_orbit_labels_span q hinner hp hg) W R ?_ ?_ ?_ reflectedOrbitLabel ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro α
    exact (P.canonicalTraceFormOfFormallyReal_unit hfr (a α)).trans
      (P.canonicalTraceOfFormallyReal_primitive hfr _ (hap α))
  · intro α β
    exact P.canonicalTraceFormOfFormallyReal_symmetric hfr _ _
  · intro α x
    rw [← hweight, ← P.peirce_product_reflection _ _ (hap α).1]
  · intro α; exact P.idempotentReflection_unit _ (hap α).1
  · intro α β; exact (P.reflectedMenuPoint_conjugate q hp α β).symm
  · simpa only [wordOperator_nil, show θ [] = P.unit from rfl] using hasSequentialEffectLift_word M.projection θ []
  · intro α
    have hi := hasSequentialEffectLift_word M.projection θ [(α.2,true)]
    have h := hasSequentialEffectLift_reflection_word M.projection θ U M.selfAdjoint hθ α.1 hi
    have hsingle : θ [(α.2,true)] = q α.2 := by
      change P.quadraticRepresentation (q α.2) P.unit = q α.2
      rw [P.quadraticRepresentation_unit, (hp _).1]
    simpa only [wordOperator_singleton M.projection M.idempotent M.selfAdjoint,
      algebraicOutcome, ↓reduceIte, hsingle, U, P.menuAction_point, Q, a, cyclicOrbitProjection, orbitProjection] using h
  · intro α; exact orbitProjection_idempotent M.projection M.idempotent M.selfAdjoint _ _
  · intro α; exact orbitProjection_star M.projection M.selfAdjoint _ _
  · intro α β; exact Subtype.ext (orbitProjection_reflected_label M.projection M.idempotent M.selfAdjoint α β)
  · intro α Z x hh
    have h := hasSequentialEffectLift_orbit_corner M.projection θ U M.selfAdjoint hθ α.1 α.2 hh
    rwa [show orbitCornerUpdate U α.1 α.2 x = _ from P.menuOrbit_corner q α.1 α.2 x, hweight] at h
  · intro α Z x hh
    have h := hasSequentialEffectLift_orbit_reflection M.projection θ U M.idempotent M.selfAdjoint hθ α.1 α.2 hh
    rwa [show orbitReflectionUpdate U α.1 α.2 x = R α x from P.menuOrbit_reflection q hp α.1 α.2 x] at h

end AlbertSequential.UnitalJordanProduct
