module

import SpinFactorTables
open AlbertSequential
example : spinSeparationQutritTable ∈ finiteHilbertProjectiveTables.{0} ℂ 3 :=
  spinSeparationQutritTable_mem_finiteComplex
example (i : Fin 3) : spinSeparationQutritTable [(i,true)] = 1/3 := spinSeparationQutritTable_yes i
#print axioms spinSeparationQutritTable_not_mem_spinFactor
#print axioms spinSeparationQutritTable_mem_finiteComplex
#print axioms UnitalJordanProduct.exists_projectiveRepresentation_of_zero_complement_weight
