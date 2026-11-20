module

import ClassifiedJordanFoil

open AlbertSequential
example (n : ℕ) : finiteJordanTables.{0} n =
    convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) :=
  finiteJordanTables_eq_convexHull n

#print axioms allSimpleFactorsAlbertOrHermitian_native
#print axioms finiteJordanTables_eq_convexHull
#print axioms finiteJordan_linear_inequality_iff
#print axioms UnitalJordanProduct.exceptionalWeight_no_uniform_margin
