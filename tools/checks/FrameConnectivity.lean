module

import GeneralEJAFrameConnectivity

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 3 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    ∃ x : P.frameJointSpace c (UnitalJordanProduct.frameOffDiagonalPattern 0 1),
      P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner) (P.product x.val x.val) = 2 :=
  P.exists_frameOffDiagonal_traceUnit (P.formallyReal_of_associative_inner hinner) c
    (P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple 0 1 (by decide))

#print axioms UnitalJordanProduct.frameOffDiagonal_ne_bot_of_simple
