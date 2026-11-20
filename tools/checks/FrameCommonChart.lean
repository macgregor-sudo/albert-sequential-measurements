module

import GeneralEJAFrameCommonChart

open AlbertSequential

example {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (c : Fin 4 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (C : P.PeirceTriangleCoordinates hfr c 0 1 2)
    (t : P.frameOffDiagonalSpace c 2 3)
    (ht : P.canonicalTraceOfFormallyReal hfr (P.product t.val t.val) = 2) :
    Nonempty (P.PeirceFourCharts c hfr C hc hunit
      (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)) :=
  P.exists_peirceFourCharts c hfr C hc hor hunit
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t ht

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 4 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let hfr := P.formallyReal_of_associative_inner hinner
    ∃ C : P.PeirceTriangleCoordinates hfr c 0 1 2,
      Nonempty (P.PeirceFourCharts c hfr C hc hunit
        (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
        (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)) ∧
      ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  obtain ⟨C, hAssoc⟩ := P.exists_associative_peirceTriangleCoordinates_of_simple_four c hc hor hunit hinner
    hsimple (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
    (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)
  obtain ⟨t, ht⟩ := P.exists_frameOffDiagonal_traceUnit hfr c
    (P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple 2 3 (by decide))
  exact ⟨C, P.exists_peirceFourCharts c hfr C hc hor hunit
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t ht, hAssoc⟩

#print axioms UnitalJordanProduct.exists_frameOffDiagonal_scaledLeftEquiv
#print axioms UnitalJordanProduct.exists_frameOffDiagonal_scaledRightEquiv
#print axioms UnitalJordanProduct.exists_peirceFourCharts
