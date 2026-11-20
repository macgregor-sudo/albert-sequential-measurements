module

import AlbertGeneratingOrbitTangent

open AlbertSequential

example (D : AlbertDerivation) (x y : Albert) :
    D.val (jordanMul x y) = jordanMul (D.val x) y + jordanMul x (D.val y) :=
  albertDerivation_mul D x y

example : Module.finrank ℝ AlbertDerivation = 52 := finrank_albertDerivation

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) :
    Module.finrank ℝ (((i : Fin 4) → albertAtomTangent (p i)) ⧸ (derivationMenuTangent p hp).range) = 12 :=
  finrank_albertGeneratingLinearizedQuotient p hp hgen

#print axioms albertDerivationFrameCoords_surjective
#print axioms albertDerivationFrameCoords_zero_iff
#print axioms albertFrameFixedSlotAction_skew
#print axioms albertFrameFixedSlotAction_triality
#print axioms albertFrameFixed_zero_of_firstSlot_zero
#print axioms albertFrameFixedSkewCoords_injective
#print axioms albertFrameFixedSkewCoords_surjective
#print axioms finrank_albertFrameFixedDerivation
#print axioms finrank_albertDerivation
#print axioms finrank_albertAtomTangent
#print axioms albertAtomTangent_trace_zero
#print axioms derivationMenuTangent_injective
#print axioms finrank_albertGeneratingLinearizedQuotient
