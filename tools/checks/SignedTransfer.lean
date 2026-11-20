module

import FiveTest.SignedReflectionTransfer

open AlbertSequential AlbertSequential.FiveTest

#check @reflectionSwitchCount_eq_nu
#check @signedReflectionTerms_count
#check @signedReflectionTerms_support
#check @signedReflectionTransfer_jordan
#check @signedReflectionTransfer_operator
#check @signedReflectionTransfer_probability
#print axioms reflectionSwitchCount_eq_nu
#print axioms signedReflectionTerms_count
#print axioms signedReflectionTerms_support
#print axioms signedReflectionTransfer_jordan
#print axioms signedReflectionTransfer_operator
#print axioms signedReflectionTransfer_probability

example : (signedReflectionTerms (0 : Fin 2) [((1, true), true), ((0, false), false),
    ((1, true), false)]).length = 27 := by decide

example : signedReflectionTerms (0 : Fin 2) [((1, true), false)] =
    [(2, [(0, true), (1, false)]), (2, [(0, false), (1, false)]), (-1, [(1, false)])] := by decide

#check @signedReflectionTransfer_hilbert
#check @signedReflectionTransfer_quaternionic
#print axioms signedReflectionTransfer_hilbert
#print axioms signedReflectionTransfer_quaternionic
