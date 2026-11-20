module

import GeneralEJAFrameMatrixSurjective

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 3 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let hfr := P.formallyReal_of_associative_inner hinner
    ∃ C : P.PeirceTriangleCoordinates hfr c 0 1 2,
      ∃ F : P.FaithfulPeirceHermitianMatrixMap hfr c C,
        ∀ Y, P.PeirceCoefficientHermitian hfr c C Y → ∃ x, F.map x = Y := by
  obtain ⟨C, ⟨F⟩⟩ := P.exists_peirceHermitianMatrixEquivalence_of_simple c hc hor hunit hinner hsimple
    (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) < 2) (by decide)
  exact ⟨C, F.toFaithfulPeirceHermitianMatrixMap, F.onto⟩

#print axioms UnitalJordanProduct.peirceCoefficient_eq_scalar_of_conjugate_fixed
#print axioms UnitalJordanProduct.peirceFrameMatrix_surjective_hermitian
#print axioms UnitalJordanProduct.exists_peirceHermitianMatrixEquivalence_of_simple
