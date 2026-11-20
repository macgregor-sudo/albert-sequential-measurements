module

import RealPairJordanBlock

open AlbertSequential

noncomputable section

example (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) (hne : p ≠ q)
    (hpos : 0 < tracePairing p q) :
    ∃ g : NativeAlbertAutomorphism,
      ∀ x : Albert, x ∈ (generatedSubalgebra ({p,q} : Set Albert)).carrier ↔
        g.linearEquiv x ∈ realPairBlock.carrier :=
  realPairBlock_original_generated p q hp hq hne hpos

example (x y : RealPairCoordinates) :
    (realPairProductEquiv (realPairBlockProduct x y)).1 =
      (realPairProductEquiv x).1 * (realPairProductEquiv y).1 ∧
    (realPairProductEquiv (realPairBlockProduct x y)).2.1 =
      (1 / 2 : ℝ) • ((realPairProductEquiv x).2.1 * (realPairProductEquiv y).2.1 +
        (realPairProductEquiv y).2.1 * (realPairProductEquiv x).2.1) :=
  realPairProductEquiv_product x y

#print axioms realPairBlock_product
#print axioms realPairProductEquiv_product
#print axioms realPairBlock_standard_generated
#print axioms realPairBlock_normal_generated
#print axioms realPairBlock_original_generated
