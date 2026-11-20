/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HurwitzNativeAlbert
public import GeneralEJARankFourClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)

theorem nativeAlbert_or_faithfulHermitian_of_simple_rank_three
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan)
    (hrank : P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner) P.unit = 3) :
    Nonempty P.NativeAlbertJordanIso ∨ ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  obtain ⟨n, _, c, hc, hor, hunit, _⟩ := P.primitive_spectral_resolution_of_formallyReal hfr 0
  have hlen := P.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hunit
  have hn : n = 3 := by exact_mod_cast hlen.symm.trans hrank
  subst n
  obtain ⟨C, ⟨H⟩⟩ := P.exists_peirceHermitianMatrixEquivalence_of_simple c hc hor hunit hinner hsimple
    (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) < 2) (by decide)
  rcases P.peirceCoefficient_associative_or_nativeOctonion hfr c C with h | h
  · exact Or.inr (P.exists_faithfulHermitianJordanEmbedding_of_peirceAssociative hfr c C
      H.toFaithfulPeirceHermitianMatrixMap h)
  · obtain ⟨f⟩ := h
    exact Or.inl (P.exists_nativeAlbertJordanIso_of_coefficients hfr c C f H)

theorem rankThreeSimpleFactorsAlbertOrHermitian_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    P.RankThreeSimpleFactorsAlbertOrHermitian hinner := by
  intro I hI
  let Q := P.orthogonalIdealProduct hinner I hI.1
  have hform := P.orthogonalIdealProduct_inner hinner I hI.1
  change Q.canonicalTraceOfFormallyReal (Q.formallyReal_of_associative_inner hform) Q.unit = 3 → _
  intro hrank
  have hsimple := (P.simple_ideal_iff_restricted_simple hinner I hI.1).mp hI
  rcases Q.nativeAlbert_or_faithfulHermitian_of_simple_rank_three hform hsimple hrank with h | h
  · obtain ⟨iso⟩ := h
    exact Or.inl ⟨{
      carrier := I
      isIdeal := hI.1
      identify := iso.map
      product := iso.product
      unit := iso.unit }, rfl⟩
  · exact Or.inr h

theorem simpleFactorsAlbertOrHermitian_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    P.SimpleFactorsAlbertOrHermitian hinner :=
  (P.simpleFactorsAlbertOrHermitian_iff_rankThree hinner).mpr
    (P.rankThreeSimpleFactorsAlbertOrHermitian_native hinner)

end AlbertSequential.UnitalJordanProduct
