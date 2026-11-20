module

import QuaternionicSchurNewton
open AlbertSequential.MatchingModels
open scoped BigOperators
example (μ : Fin 4 → ℝ) :
    schurNewtonFourth (∑ i, μ i) (∑ i, μ i ^ 2) (∑ i, μ i ^ 3) (∑ i, μ i ^ 4) = ∏ i, μ i :=
  schurNewtonFourth_eq_product μ
#print axioms schurNewtonFourth_powerSum
#print axioms schurNewtonFourth_eq_product
