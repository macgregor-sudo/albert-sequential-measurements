module

import GeneratedCyclicHilbertMap

open AlbertSequential
open scoped InnerProductSpace

universe u v w

example {E : Type u} {I : Type v} {A : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : UnitalJordanProduct E) (p : I → E) (M : AlgebraicProjectiveData I A)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hprim : ∀ i, (P.generatedMenuProduct p).IsPrimitive (P.generatedMenuTest p i))
    (ρ : E) (hm : ∀ w, M.probability w =
      P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
        (P.sequentialBranchState p ρ w)) :
    let B := P.generatedMenuProduct p
    let H := CyclicHilbert M →L[ℝ] CyclicHilbert M
    ‖cyclicHilbertVector M‖ = 1 ∧
    ∃ η : P.generatedMenuCarrier p →ₗ[ℝ] selfAdjoint H,
      η B.unit = 1 ∧
      (∀ x y, (η (B.product x y) : H) =
        (1 / 2 : ℝ) • ((η x : H) * (η y : H) + (η y : H) * (η x : H))) ∧
      (∀ α : ReflectionOrbitLabel I, (η (B.reflectedMenuPoint (P.generatedMenuTest p) α.1 α.2) : H) =
        cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm (cyclicOrbitProjection M α))) ∧
      ∀ x, inner ℝ (cyclicHilbertVector M) ((η x : H) (cyclicHilbertVector M)) =
        P.canonicalTraceFormOfFormallyReal (P.formallyReal_of_associative_inner hinner) ρ x.val := by
  obtain ⟨η, hmul, hunit, horbit, hstate⟩ :=
    P.generated_cyclicHilbertJordanMap p M hinner hprim ρ hm
  exact ⟨cyclicHilbertVector_norm M, η, Subtype.ext hunit, hmul, horbit, hstate⟩

#print axioms UnitalJordanProduct.generated_cyclicHilbertJordanMap
#print axioms UnitalJordanProduct.primitive_orbit_cyclic_reconstruction
#print axioms exists_cyclicHilbertJordanMap_of_orbits
