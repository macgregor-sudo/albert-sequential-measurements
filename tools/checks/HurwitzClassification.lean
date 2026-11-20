module

import HurwitzRankThreeClassification

noncomputable section

open AlbertSequential

namespace HurwitzPeer

private def toNative (a : CompositionAlgebra.CD (Quaternion ℝ)) : AlbertSequential.Octonion :=
  (a.fst, a.snd)

private theorem star_eq (x : Quaternion ℝ) : CompositionAlgebra.cstar x = star x := by
  ext <;> simp [Quaternion.cstar_eq]

example (a b : CompositionAlgebra.CD (Quaternion ℝ)) :
    toNative (a * b) = octonionMul (toNative a) (toNative b) := by
  apply Prod.ext
  · change a.fst * b.fst - CompositionAlgebra.cstar b.snd * a.snd =
      a.fst * b.fst - star b.snd * a.snd
    rw [star_eq]
  · change b.snd * a.fst + a.snd * CompositionAlgebra.cstar b.fst =
      b.snd * a.fst + a.snd * star b.fst
    rw [star_eq]

example (a : CompositionAlgebra.CD (Quaternion ℝ)) :
    toNative (CompositionAlgebra.cstar a) = octonionConj (toNative a) := by
  unfold toNative octonionConj
  rw [CompositionAlgebra.CD.cstar_eq, star_eq]
  rfl

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (c : Fin 3 → E)
    {r s t : Fin 3} (C : P.PeirceTriangleCoordinates hfr c r s t)
    (f : P.PeirceCoefficientNativeOctonionIso hfr c C)
    (H : P.PeirceHermitianMatrixEquivalence hfr c C) :
    ∃ g : E ≃ₗ[ℝ] Albert, g P.unit = albertUnit ∧
      ∀ x y, g (P.product x y) = jordanMul (g x) (g y) := by
  obtain ⟨g⟩ := P.exists_nativeAlbertJordanIso_of_coefficients hfr c C f H
  exact ⟨g.map, g.unit, g.product⟩

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    P.SimpleFactorsAlbertOrHermitian hinner :=
  P.simpleFactorsAlbertOrHermitian_native hinner

#print axioms CompositionAlgebra.finrank_eq_one_or_two_or_four_or_eight
#print axioms CompositionAlgebra.hurwitz_classification
#print axioms CompositionAlgebra.cdQuaternionEquiv_isCompIso
#print axioms UnitalJordanProduct.peirceCoefficient_associative_or_nativeOctonion
#print axioms UnitalJordanProduct.exists_nativeAlbertJordanIso_of_coefficients
#print axioms UnitalJordanProduct.nativeAlbert_or_faithfulHermitian_of_simple_rank_three
#print axioms UnitalJordanProduct.rankThreeSimpleFactorsAlbertOrHermitian_native
#print axioms UnitalJordanProduct.simpleFactorsAlbertOrHermitian_native

end HurwitzPeer
