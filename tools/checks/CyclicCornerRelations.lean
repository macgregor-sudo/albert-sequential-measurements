module

import CyclicNativeCornerRelations

open AlbertSequential

universe u

example {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (p : Fin 4 → Albert) (ρ : Albert)
    (hp : ∀ i, IsAtom (p i)) (h : ∀ w, M.probability w = nativeWordProbability p ρ w)
    (a b c d : Fin 4) :
    let P := cyclicHilbertProjection M
    P a * P b * P a = nativeOverlaps p a b • P a ∧
    P a * (P b * P c + P c * P b) * P a = (2 * nativeTriangles p a b c) • P a ∧
    P a * (P b * P c * P d + P d * P c * P b) * P a =
      (2 * tracePairing (p a) (jordanTriple (p b) (p c) (p d))) • P a := by
  obtain ⟨h₁, h₂, h₃⟩ := cyclic_native_corner_relations M p ρ hp h
  exact ⟨h₁ a b, h₂ a b c, h₃ a b c d⟩

#print axioms cyclic_nativePurityElement_eq_zero
#print axioms cyclic_native_corner_relations
#print axioms cyclic_native_corner_relations_at_order
