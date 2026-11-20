module

import RealPairJordanSpan
import RealPairQutrit

open AlbertSequential

example (p : Albert) (hp : IsAtom p) :
    (generatedSubalgebra ({p} : Set Albert)).carrier =
      Submodule.span ℝ ({p, albertUnit - p} : Set Albert) :=
  generatedSingleAtom_eq_span p hp

example (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    (generatedSubalgebra ({p,q} : Set Albert)).carrier =
      Submodule.span ℝ ({albertUnit,p,q,jordanMul p q} : Set Albert) :=
  generatedPair_eq_span p q hp hq

example (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    ∃ P : Fin 2 → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i, (P i).transpose = P i ∧ P i * P i = P i ∧ (P i).rank = 1) ∧
      (P 0 * P 1).trace = tracePairing p q ∧
      ∀ ρ : Albert, IsDensity ρ → ∃ τ : Matrix (Fin 3) (Fin 3) ℝ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ∀ w : Word (Fin 2), (τ * wordOperator P w).trace = nativeWordProbability ![p,q] ρ w :=
  realPair_qutrit_word_model p q hp hq

#print axioms realPairBlock_original_generated
#print axioms realPairProductEquiv_product
#print axioms generatedSingleAtom_eq_span
#print axioms generatedPair_eq_span
#print axioms realPair_qutrit_word_model
