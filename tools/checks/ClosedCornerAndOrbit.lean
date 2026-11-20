module

import FiveTest.DenseOrbit
import TracialCornerKernel

open AlbertSequential

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ξ : H) (C : Set (H →L[ℝ] H)) (hs : ∀ T ∈ C, star T ∈ C)
    (hm : ∀ S ∈ C, ∀ T ∈ C, S*T ∈ C)
    (ht : ∀ S ∈ C, ∀ T ∈ C, residualVectorFunctional ξ (S*T) = residualVectorFunctional ξ (T*S))
    {Z : H →L[ℝ] H} (hz : Z ∈ C) (h : Z ξ = 0) (T : H →L[ℝ] H) (hT : T ∈ C) :
    Z (T ξ) = 0 := by
  apply tracialCorner_annihilates_orbitClosure ξ C hs hm ht hz h
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨T,hT,rfl⟩

#print axioms faithfulCorner_annihilator_zero
#print axioms tracialCorner_annihilates_orbitClosure
#print axioms exists_positive_reflection_quad_of_dense
