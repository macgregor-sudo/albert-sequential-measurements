module

import GeneralEJAFrameGlobalChart

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 5 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let hfr := P.formallyReal_of_associative_inner hinner
    ∃ C : P.PeirceTriangleCoordinates hfr c 0 1 2,
      Nonempty (P.PeirceIncreasingFrameChart hfr c C hc hunit
        (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2)) ∧
      ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  obtain ⟨C, hAssoc⟩ := P.exists_associative_peirceTriangleCoordinates_of_simple_four c hc hor hunit hinner
    hsimple (by decide : (0 : Fin 5) ≠ 1) (by decide : (0 : Fin 5) ≠ 2) (by decide : (0 : Fin 5) ≠ 3)
    (by decide : (1 : Fin 5) ≠ 2) (by decide : (1 : Fin 5) ≠ 3) (by decide : (2 : Fin 5) ≠ 3)
  refine ⟨C, P.exists_peirceIncreasingFrameChart hfr c C hc hunit
    (by decide : (0 : Fin 5) < 1) (by decide : (1 : Fin 5) < 2) hor (by decide) ?_, hAssoc⟩
  intro i j hij
  exact P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j (ne_of_lt hij)

#print axioms UnitalJordanProduct.exists_peirceFrameColumns
#print axioms UnitalJordanProduct.exists_peirceFrameEdges
#print axioms UnitalJordanProduct.peirceFrameEdges_product_of_increasing
#print axioms UnitalJordanProduct.exists_peirceIncreasingFrameChart
