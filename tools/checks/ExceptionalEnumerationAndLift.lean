module

import QuaternionicDensityLift
import ExceptionalIdealEnumeration

set_option warningAsError true
open scoped InnerProductSpace Matrix ComplexOrder

open AlbertSequential AlbertSequential.NativeAnalysis AlbertSequential.WindowProbability

example (M : ComplexMatrix3) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank ≤ 2) :
    ∃ Z : Matrix (Fin 3) (Fin 2) ℂ, Z * Zᴴ = M ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      quaternionicDyadFromTwoColumns Z ∈ standardQuaternionicWindow.subalgebra.carrier ∧
      projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = M := by
  obtain ⟨Z, hz, _, ha, hQ, hP⟩ := complexDensity_rank_le_two_quaternionicLift M hM ht hr
  exact ⟨Z, hz, ha, hQ, hP⟩

example (M : ComplexMatrix3) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank ≤ 1) :
    ∃ Z : Matrix (Fin 3) (Fin 2) ℂ, (∀ i, Z i 1 = 0) ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = M := by
  obtain ⟨Z, hv, _, _, ha, _, hP⟩ := complexDensity_rank_le_one_quaternionicLift M hM ht hr
  exact ⟨Z, hv, ha, hP⟩

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    ∃ (k : ℕ) (I : Fin k → P.AlbertIdeal),
      (∀ i j, i ≠ j → (I i).carrier ≤ (I j).carrierᗮ) ∧
      (∀ J : P.AlbertIdeal, ∃ i, (I i).carrier = J.carrier) :=
  P.exists_complete_exceptional_ideal_family hinner

#print axioms exists_rectangularComplexGram
#print axioms quaternionOfComplexPair_eq_add_mul_j
#print axioms twoColumnComplexGram_eq_dyads
#print axioms complexDensity_rank_le_two_quaternionicMatrixLift
#print axioms complexDensity_rank_le_two_quaternionicLift
#print axioms complexDensity_rank_le_one_quaternionicLift
#print axioms UnitalJordanProduct.exists_complete_exceptional_ideal_family
