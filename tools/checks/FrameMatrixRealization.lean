module

import GeneralEJAFrameMatrixRealization

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 3 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let hfr := P.formallyReal_of_associative_inner hinner
    ∃ C : P.PeirceTriangleCoordinates hfr c 0 1 2,
      Nonempty (P.FaithfulPeirceHermitianMatrixMap hfr c C) :=
  P.exists_faithfulPeirceHermitianMatrixMap_of_simple c hc hor hunit hinner hsimple
    (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) < 2) (by decide)

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 5 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let hfr := P.formallyReal_of_associative_inner hinner
    ∃ C : P.PeirceTriangleCoordinates hfr c 0 1 2,
      Nonempty (P.FaithfulPeirceHermitianMatrixMap hfr c C) ∧
      ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  obtain ⟨C, hAssoc⟩ := P.exists_associative_peirceTriangleCoordinates_of_simple_four c hc hor hunit hinner
    hsimple (by decide : (0 : Fin 5) ≠ 1) (by decide : (0 : Fin 5) ≠ 2) (by decide : (0 : Fin 5) ≠ 3)
    (by decide : (1 : Fin 5) ≠ 2) (by decide : (1 : Fin 5) ≠ 3) (by decide : (2 : Fin 5) ≠ 3)
  have hconnected (i j : Fin 5) (hij : i < j) : P.frameOffDiagonalSpace c i j ≠ ⊥ :=
    P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j (ne_of_lt hij)
  obtain ⟨C', hp, _, D, hform⟩ := P.exists_peirceIncreasingFrameChart_normalized hfr c C hc hor hunit
    (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2) (by decide) hconnected
  refine ⟨C', P.exists_faithfulPeirceHermitianMatrixMap hfr c C' hc hor hunit hinner
    (by decide) (by decide) D hform, ?_⟩
  rw [hp]
  exact hAssoc

#print axioms UnitalJordanProduct.peirceCoefficientConjugate_product
#print axioms UnitalJordanProduct.peirceCoefficientMatrixMul_single
#print axioms UnitalJordanProduct.peirceCoefficientMatrixJordan_same_edge
#print axioms UnitalJordanProduct.peirceFrameMatrix_product
#print axioms UnitalJordanProduct.exists_faithfulPeirceHermitianMatrixMap
#print axioms UnitalJordanProduct.exists_faithfulPeirceHermitianMatrixMap_of_simple
