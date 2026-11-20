module

import TableModel.WalkUpsilon

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.TableModel

attribute [local irreducible] fourPointInvariant

example (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    AlgebraicWalkHypotheses (comparisonWalkSpace τ hB hC hD) τ :=
  comparison_hypotheses τ hB hC hD

example (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    LemmaB.Q (comparisonParams τ) (LemmaB.uhat (comparisonParams τ) [0, 1, 1, 3])
      (LemmaB.uhat (comparisonParams τ) [2, 0, 3, 3]) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ)
        (walkUpsilon [0, 1, 1, 3, 3, 3, 0, 2]) :=
  comparisonGram_eq_upsilon τ hB hC hD [0, 1, 1, 3] [2, 0, 3, 3] (by decide) (by decide)

example {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (S : Set (Word Letter)) (h : Gram28Hyp W (nativeTraceData p) S)
    (hrep : W.Reproduces S (nativeWordProbability p (p 0))) :
    W.form (W.pathVec [0, 1, 1, 3]) (W.pathVec [2, 0, 3, 3]) =
      LemmaB.Q (comparisonParams (nativeTraceData p))
        (LemmaB.uhat (comparisonParams (nativeTraceData p)) [0, 1, 1, 3])
        (LemmaB.uhat (comparisonParams (nativeTraceData p)) [2, 0, 3, 3]) :=
  native_gram_eq_comparison_of_gram28Hyp W p hp hA S h hrep [0, 1, 1, 3] [2, 0, 3, 3] (by decide) (by decide)

#print axioms comparisonWalkSpace
#print axioms comparison_R1
#print axioms comparison_hypotheses
#print axioms comparisonGram_eq_upsilon
#print axioms WalkForm.gram_eq_upsilon_of_gram28Hyp
#print axioms native_gram_eq_comparison_of_gram28Hyp
