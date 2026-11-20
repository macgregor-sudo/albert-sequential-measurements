module

import GeneralEJAFrameCoherence

open AlbertSequential

example {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E) (c : Fin 4 → E)
    (hc : ∀ r, P.product (c r) (c r) = c r) (hunit : ∑ r, c r = P.unit)
    {x y z : E}
    (hx : x ∈ P.frameOffDiagonalSpace c 0 1)
    (hy : y ∈ P.frameOffDiagonalSpace c 1 2)
    (hz : z ∈ P.frameOffDiagonalSpace c 2 3) :
    P.product (P.product x y) z = P.product x (P.product y z) :=
  P.frameOffDiagonal_product_associative_of_chain c hc hunit
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx hy hz

#print axioms UnitalJordanProduct.frameOffDiagonal_product_associative_of_chain
#print axioms UnitalJordanProduct.frameOffDiagonal_scaled_product_associative_of_chain
#print axioms UnitalJordanProduct.frameOffDiagonal_scaled_left_injective
