module

import FiveTest.PentadContinuousWords
import FiveTest.ReflectedInterchange

set_option warningAsError true

open AlbertSequential AlbertSequential.FiveTest AlbertSequential.MatchingModels

example (L : List (Fin 5)) :
    ∃ p : Polynomial ℚ,
      (∀ a : Fin 5, a ≠ 2 → p.natDegree ≤ L.count a) ∧
      2 * p.natDegree ≤ L.count (2 : Fin 5) ∧ 6 * p.natDegree ≤ L.length ∧
      (∀ u : Octonion, octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        albertTrace (pentadChain (continuousPentad u) L) = parameterEval (octDot u octK) p) :=
  continuousPentad_connectedTrace_degree_bounds L

example (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 1 ∧
      ∀ (u : Octonion), octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        nativeWordProbability (continuousPentad u) (pentadF 0) w = parameterEval (octDot u octK) p :=
  continuousPentad_p0_word_affine w hw

example (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 1 ∧
      ∀ (u : Octonion), octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        nativeWordProbability (continuousPentad u) ((1/3 : ℝ) • albertUnit) w =
          parameterEval (octDot u octK) p :=
  continuousPentad_e3_word_affine w hw

#print axioms QuadraticPlane.zero_on_circle
#print axioms zPentadProbe_xpos
#print axioms zPentadProbe_xneg
#print axioms zPentadProbe_ypos
#print axioms zPentadProbe_yneg
#print axioms zPentadProbe_mixed
#print axioms parameterizedPeirce_action
#print axioms pentadChainPolynomial_coeff_grade
#print axioms pentadConnectedTracePolynomial_coeff_frequency
#print axioms pentadConnectedTracePolynomial_coeff_length
#print axioms continuousPentad_connectedTrace
#print axioms continuousPentad_connectedTrace_degree_bounds
#print axioms continuousPentad_connectedWord
#print axioms continuousPentad_p0_word_affine
#print axioms continuousPentad_e3_word_affine
