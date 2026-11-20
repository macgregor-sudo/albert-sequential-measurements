module

import CyclicRangeCompletion

open AlbertSequential
open scoped InnerProductSpace

universe u v w t

example {I : Type u} {A : Type v} {J : Type w} {κ : Type t}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] [AddCommGroup J] [Module ℝ J]
    (M : AlgebraicProjectiveData I A)
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hs : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤)
    (hQ : ∀ i, star (Q i : A) = Q i)
    (η : J →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M))
    (hj : ∀ x y, η (jmul x y) = associativeJordanProduct (η x) (η y))
    (he : η e = 1) (hg : ∀ i, η (q i) = cyclicRepresentation M (Q i))
    (ω : J →ₗ[ℝ] ℝ)
    (hω : ∀ x, cyclicExpectation M (η x (cyclicVector M)) = ω x) :
    let H := CyclicHilbert M →L[ℝ] CyclicHilbert M
    ∃ F : J →ₗ[ℝ] selfAdjoint H,
      F e = 1 ∧
      (∀ x y, (F (jmul x y) : H) =
        (1 / 2 : ℝ) • ((F x : H) * (F y : H) + (F y : H) * (F x : H))) ∧
      (∀ i, (F (q i) : H) = cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm (Q i))) ∧
      ∀ x, inner ℝ (cyclicHilbertVector M) ((F x : H) (cyclicHilbertVector M)) = ω x := by
  obtain ⟨F, hFj, hFe, hFg, hFω⟩ :=
    exists_cyclicHilbertJordanMap_of_orbits M e q Q jmul hs hQ η hj he hg ω hω
  exact ⟨F, Subtype.ext hFe, hFj, hFg, hFω⟩

#print axioms cyclicHilbert_eq_of_cyclic_eq
#print axioms exists_cyclic_range_completion
#print axioms exists_cyclicHilbertJordanMap_of_orbits
