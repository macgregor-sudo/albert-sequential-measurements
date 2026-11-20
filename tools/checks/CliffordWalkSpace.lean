module

import TableModel.CliffordWalkSpace

open LemmaB AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.TableModel

noncomputable section
attribute [local irreducible] fourPointInvariant
set_option maxHeartbeats 1200000

example (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q) :
    let W : AlgebraicWalkSpace (CliffordFrames (nativeCliffordParams q)) := nativeCliffordWalkSpace q hq hA
    AlgebraicWalkHypotheses W (nativeTraceData q) ∧
      (∀ F G, W.form F G = cliffordComparisonForm (nativeCliffordParams q) F G) ∧
      (∀ i F, W.P i F = cliffordComparisonProjection (nativeCliffordParams q) i F) ∧
      W.ξ = Pi.single 0 1 ∧
      ∀ w, W.pathVec w = cliffordComparisonPath (nativeCliffordParams q) w :=
  ⟨native_cliffordComparison_hypotheses q hq hA,
    fun F G => cliffordComparisonWalkSpace_form _ _ _ _ F G,
    fun i F => cliffordComparisonWalkSpace_projection _ _ _ _ i F,
    cliffordComparisonWalkSpace_anchor _ _ _ _,
    fun w => cliffordComparisonWalkSpace_pathVec _ _ _ _ w⟩

example (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (x y : Letter) (hxy : x ≠ y) (F : CliffordFrames (comparisonParams τ)) :
    let W := cliffordComparisonWalkSpace τ hB hC hD
    W.P x (W.P y (W.P x F)) = τ.o x y • W.P x F :=
  cliffordComparison_R1 τ hB hC hD x y hxy F

example (τ : TraceData) (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    cliffordComparisonForm (comparisonParams τ) (cliffordComparisonPath (comparisonParams τ) u)
      (cliffordComparisonPath (comparisonParams τ) v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) :=
  cliffordComparisonGram_eq_upsilon τ hB hC hD u v hu hv

example {E : Type*} [AddCommGroup E] [Module ℝ E] (W : WalkForm E)
    (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q)
    (S : Set (Word Letter)) (h : Gram28Hyp W (nativeTraceData q) S)
    (hrep : W.Reproduces S (nativeWordProbability q (q 0)))
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) =
      cliffordComparisonForm (nativeCliffordParams q) (cliffordComparisonPath (nativeCliffordParams q) u)
        (cliffordComparisonPath (nativeCliffordParams q) v) :=
  native_gram_eq_cliffordComparison_of_gram28Hyp W q hq hA S h hrep u v hu hv

#print axioms printedCliffordBasis_apply
#print axioms cliffordPairing_ghostMate
#print axioms cliffordReflection_selfAdjoint
#print axioms cliffordReflection_involutive
#print axioms cliffordComparisonWalkSpace
#print axioms cliffordComparisonWalkSpace_form
#print axioms cliffordComparisonWalkSpace_projection
#print axioms cliffordComparisonWalkSpace_anchor
#print axioms cliffordComparisonWalkSpace_pathVec
#print axioms cliffordComparison_R1
#print axioms cliffordComparison_hypotheses
#print axioms cliffordComparisonGram_eq_upsilon
#print axioms native_cliffordComparison_hypotheses
#print axioms native_gram_eq_cliffordComparison_of_gram28Hyp
#print axioms native_cliffordComparisonGram_eq_upsilon
