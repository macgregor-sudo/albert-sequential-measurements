module

import PaperNormalFormGram
import PaperNormalFormPolynomial

noncomputable section

namespace AlbertSequential
open NormalFormPolynomial

example : (tracePolynomial : MvPolynomial (Fin 23) ℚ) = associatorPolynomial :=
  normalFormPolynomial_eq

example (v : Fin 23 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) v tracePolynomial =
      fourPointInvariant (sparseFourConfigOct (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
        (⟨v 7, v 8, v 9, v 10⟩, ⟨v 11, v 12, v 13, v 14⟩)
        (⟨v 15, v 16, v 17, v 18⟩, ⟨v 19, v 20, v 21, v 22⟩)) :=
  eval_tracePolynomial v

example (v : Fin 23 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) v associatorPolynomial =
      (1 / 4 : ℝ) * (v 0)^2 * (v 1)^4 * (v 2)^2 * (v 4)^2 * (v 5)^2 * (v 6)^2 *
        octNormSq (octAssociator octI
          (⟨v 7, v 8, v 9, v 10⟩, ⟨v 11, v 12, v 13, v 14⟩)
          (⟨v 15, v 16, v 17, v 18⟩, ⟨v 19, v 20, v 21, v 22⟩)) :=
  eval_associatorPolynomial v

example (g₁ g₂ g₃ : Octonion) :
    fpGramTriplePoly (octonionReal g₁) (octonionReal g₂) (octonionReal g₃)
      (octonionReal (octonionMul g₁ (octonionConj g₂)))
      (octonionReal (octonionMul g₁ g₃))
      (octonionReal (octonionMul g₂ (octonionConj g₃)))
      (octonionReal (octonionMul (octonionMul g₁ g₃) (octonionConj g₂))) =
    octDot (octCross (octIm g₁) (octIm g₃)) (octIm g₂) :=
  fpGramTriplePoly_eq_octonion_cross g₁ g₂ g₃

#print axioms sparseFourConfigOct_signedGram
#print axioms normalFormPolynomial_eq
#print axioms eval_tracePolynomial
#print axioms eval_associatorPolynomial
#print axioms fpGramMatrixPoly_eq_octonion_gram
#print axioms fpGramTriplePoly_eq_octonion_cross
#print axioms sparseFourConfigOct_fourPointInvariant

end AlbertSequential
