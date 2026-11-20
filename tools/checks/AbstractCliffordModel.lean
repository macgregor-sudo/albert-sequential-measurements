module

import TableModel.CliffordComparison
import TableModel.CliffordNativeGram
import TableModel.CliffordVolumeCoordinates
import TableModel.CliffordVolumeDet
import TableModel.WalkUpsilon

open LemmaB AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.TableModel

noncomputable section
attribute [local irreducible] fourPointInvariant

set_option maxHeartbeats 500000 in
example (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q) :
    ∃ (Λ : Matrix (Fin 3) (Fin 3) ℝ)
      (E : ComparisonClifford (nativeCliffordParams q) ≃ₐ[ℝ] StandardComparisonClifford),
      comparisonMatrix (nativeCliffordParams q) = Λ * Λ.transpose ∧ IsUnit Λ.det ∧
      (∀ i : Fin 3, E (cliffordGenerator (nativeCliffordParams q) i) =
        ∑ j, Λ i j • standardComparisonGenerator j) ∧
      E (cliffordVolume (nativeCliffordParams q)) = Λ.det •
        (standardComparisonGenerator 0 * standardComparisonGenerator 1 * standardComparisonGenerator 2) := by
  obtain ⟨Λ, hΛ, hd⟩ := native_comparison_gram_factor q hq hA
  exact ⟨Λ, cliffordGramFactorEquiv _ Λ hΛ hd, hΛ, hd, cliffordGramFactorEquiv_generator _ _ hΛ hd,
    cliffordGramFactorEquiv_volume _ _ hΛ hd⟩

example (p : Params ℝ) (F : CliffordFrames p) (x : Fin 4) :
    cliffordFrameEquiv p (cliffordComparisonProjection p x F) =
      P p x (cliffordFrameEquiv p F) := by
  simp only [cliffordFrameEquiv_apply, cliffordCoordinates_projection]

set_option maxHeartbeats 500000 in
example {E : Type*} [AddCommGroup E] [Module ℝ E] (W : WalkForm E)
    (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q)
    (S : Set (Word Letter)) (h : Gram28Hyp W (nativeTraceData q) S)
    (hrep : W.Reproduces S (nativeWordProbability q (q 0)))
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) =
      cliffordComparisonForm (nativeCliffordParams q) (cliffordComparisonPath (nativeCliffordParams q) u)
        (cliffordComparisonPath (nativeCliffordParams q) v) := by
  rw [cliffordComparisonPath_gram]
  exact native_gram_eq_comparison_of_gram28Hyp W q hq hA S h hrep u v hu hv

#print axioms comparisonClifford_finrank
#print axioms cliffordCoordinateEquiv
#print axioms cliffordCoordinates_basisWords
#print axioms cliffordPairing_eq_W
#print axioms cliffordComparisonForm_eq_Q
#print axioms cliffordCoordinates_projection
#print axioms cliffordComparisonPath_gram
#print axioms standardComparisonGenerator_sq
#print axioms standardComparisonGenerator_anti
#print axioms cliffordGramFactorEquiv_generator
#print axioms comparisonMatrix_native_normalization
#print axioms native_comparison_gram_factor
#print axioms cliffordVolume_eq_half_reverse
#print axioms cliffordVolume_square
#print axioms cliffordConjugate_volume
#print axioms cliffordPairing_ghost
#print axioms cliffordVolume_central
#print axioms cliffordGramFactorEquiv_volume
