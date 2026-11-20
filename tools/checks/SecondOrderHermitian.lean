module

import AppF.SecondOrderHermitian

open AlbertSequential AlbertSequential.AppF

example : Module.finrank ℝ secondOrderCoefficientIdeal = 6 :=
  secondOrderCoefficientIdeal_finrank

theorem coefficientInvolution_product_check (d e : Dq) : star (d * e) = star e * star d := star_mul _ _

example (x : J3) : (redq x).IsHermitian := redq_isHermitian x

theorem reducedEntries_conj_check (x : J3) (i j : Fin 3) :
    star (redq x j i) = redq x i j := congrFun (congrFun (redq_isHermitian x) i) j

#print axioms secondOrderCoefficientIdeal_finrank
#print axioms coefficientInvolution_product_check
#print axioms redq_isHermitian
#print axioms reducedEntries_conj_check
