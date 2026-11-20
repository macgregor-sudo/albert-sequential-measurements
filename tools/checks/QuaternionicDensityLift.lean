module

import QuaternionicDensityLift

open AlbertSequential AlbertSequential.WindowProbability
open scoped Matrix ComplexOrder

example (M : Matrix (Fin 5) (Fin 5) ℂ) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank ≤ 2) :
    ∃ Z : Matrix (Fin 5) (Fin 2) ℂ, Z * Zᴴ = M ∧
      let u := fun i : Fin 5 => quaternionOfComplexPair (Z i 0) (Z i 1)
      let Q := Matrix.vecMulVec u (star u)
      (∑ i, quatNormSq (u i)) = 1 ∧ Q.IsHermitian ∧ Q * Q = Q ∧
      (∀ i j, (⟨(Q i j).re, (Q i j).imI⟩ : ℂ) = M i j) ∧
      Set.range Q.mulVec = Set.range (fun a : Quaternion ℝ => fun i => u i * a) :=
  complexDensity_rank_le_two_quaternionicMatrixLift M hM ht hr

example (M : ComplexMatrix3) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank ≤ 2) :
    ∃ q : Albert, IsAtom q ∧ q ∈ standardQuaternionicWindow.subalgebra.carrier ∧ projectedMatrix standardComplexWindow q = M := by
  obtain ⟨Z, _, _, ha, hm, hp⟩ := complexDensity_rank_le_two_quaternionicLift M hM ht hr
  exact ⟨quaternionicDyadFromTwoColumns Z, ha, hm, hp⟩

example (M : ComplexMatrix3) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank = 1) :
    ∃ Z : Matrix (Fin 3) (Fin 2) ℂ, (∀ i, Z i 1 = 0) ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = M := by
  obtain ⟨Z, hy, _, _, ha, _, hp⟩ := complexDensity_rank_le_one_quaternionicLift M hM ht hr.le
  exact ⟨Z, hy, ha, hp⟩

#print axioms exists_rectangularComplexGram
#print axioms twoColumnComplexGram_eq_dyads
#print axioms quaternionOfComplexPair_eq_add_mul_j
#print axioms complexDensity_rank_le_two_quaternionicMatrixLift
#print axioms complexDensity_rank_le_two_quaternionicLift
#print axioms complexDensity_rank_le_one_quaternionicLift
