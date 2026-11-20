module

import CyclicCornerSevenTraceModel

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.CornerHolonomy
open AlbertSequential.CornerResidualBuilder AlbertSequential.MatchingModels

attribute [local irreducible] fourPointInvariant

section

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
variable (M : AlgebraicProjectiveData (Fin 4) A)

example (h : CyclicAnchorStateTracial M) (T S : CyclicBoundedOperator M)
    (hT : InCyclicAnchorCorner M T) (hS : InCyclicAnchorCorner M S)
    (hzero : T (cyclicHilbertProjection M 0 (cyclicHilbertVector M)) = 0) :
    T (S (cyclicHilbertProjection M 0 (cyclicHilbertVector M))) = 0 :=
  cyclicAnchor_null_right_of_tracial M h T S hT hS hzero

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ρ w)
    (hstate : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M)
    (v : CyclicHilbert M) (hv : v ∈ closure (CyclicAnchorOrbit M)) :
    let P := cyclicHilbertProjection M
    let d := BlockB.atomCornerData p
    let h := normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2
    (∀ i, hermitianDefect (P 0) (h i) (d.hermitianConstants i) v = 0 ∧
      leftUnitarityDefect (P 0) (h i) v = 0 ∧ rightUnitarityDefect (P 0) (h i) v = 0) ∧
    (∀ i, pairProductDefect (P 0) (h i) (h (nextHolonomy i)) (mixedConstant d i) v = 0) ∧
    cornerCubicDefect (P 0) h d.cubicConstant v = 0 :=
  cyclic_seven_corner_defects_on_closed_orbit M p hp hA ρ hM hstate v hv

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (hs : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M) :
    ¬ (∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :=
  cyclic_anchoredSeven_e3_not_match_of_faithful_or_tracial M p hp hA hs

end

example (b d : ℝ) (hd : d ^ 2 = 1 / 2) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ w : Word (Fin 4), w.length ≤ 7 ∧ w.head? = some (0, true) ∧
      (horizonC12Model b d hd).probability w ≠ nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  horizonC12Model_fails_anchoredSeven b d hd p hp hA

#print axioms inCyclicAnchorCorner_iff_compression
#print axioms cyclicAnchor_null_on_closed_orbit
#print axioms cyclicAnchorStateTracial_of_source_trace
#print axioms cyclicSupportedLeaf_norm_sq
#print axioms cyclic_seven_corner_defects
#print axioms cyclic_seven_corner_defects_on_closed_orbit
#print axioms cyclic_anchoredSeven_corner_discriminant
#print axioms cyclic_anchoredSeven_e3_not_match_of_faithful_or_tracial
#print axioms horizonC12AlgebraicTraceModel_anchorTracial
#print axioms horizonC12Model_fails_anchoredSeven
#print axioms horizon_M_matrix_fails_at_anchoredSeven
#print axioms horizon_S_matrix_fails_at_anchoredSeven
