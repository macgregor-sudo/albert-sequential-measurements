/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameRegularRepresentation
public import GeneralEJAHigherRankReduction

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)

theorem exists_faithfulHermitianJordanEmbedding_of_simple_rank_ge_four
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan)
    (hrank : 4 ≤ P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner) P.unit) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  obtain ⟨n, _, c, hc, hor, hunit, _⟩ := P.primitive_spectral_resolution_of_formallyReal hfr 0
  have hlen := P.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hunit
  have hnR : (4 : ℝ) ≤ n := by
    rw [← hlen]
    exact hrank
  have hn : 4 ≤ n := by exact_mod_cast hnR
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let d : Fin n := ⟨2, by omega⟩
  let e : Fin n := ⟨3, by omega⟩
  have hab : a < b := by change 0 < 1; decide
  have hbd : b < d := by change 1 < 2; decide
  have hde : d < e := by change 2 < 3; decide
  have hfirst (i : Fin n) (ha : i ≠ a) (hb : i ≠ b) (hd : i ≠ d) : d < i := by
    have h0 : i.val ≠ 0 := fun h => ha (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hb (Fin.ext h)
    have h2 : i.val ≠ 2 := fun h => hd (Fin.ext h)
    change 2 < i.val
    omega
  exact P.exists_faithfulHermitianJordanEmbedding_of_simple_four_frame c hc hor hunit hinner hsimple
    hab hbd hde hfirst

theorem simple_factor_has_hermitian_embedding_of_rank_ge_four
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsSimpleJordanIdeal I)
    (hrank : let Q := P.orthogonalIdealProduct hinner I hI.1
      let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
      4 ≤ Q.canonicalTraceOfFormallyReal hfr Q.unit) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (P.orthogonalIdealProduct hinner I hI.1) d) :=
  (P.orthogonalIdealProduct hinner I hI.1).exists_faithfulHermitianJordanEmbedding_of_simple_rank_ge_four
    (P.orthogonalIdealProduct_inner hinner I hI.1)
    ((P.simple_ideal_iff_restricted_simple hinner I hI.1).mp hI) hrank

/-- The actual remaining factor classification after the rank-one, rank-two,
and rank-at-least-four Hermitian embeddings. -/
def RankThreeSimpleFactorsAlbertOrHermitian
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) : Prop :=
  ∀ (I : Submodule ℝ E) (hI : P.IsSimpleJordanIdeal I),
    let Q := P.orthogonalIdealProduct hinner I hI.1
    let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
    Q.canonicalTraceOfFormallyReal hfr Q.unit = 3 →
      (∃ J : P.AlbertIdeal, J.carrier = I) ∨
        ∃ d, Nonempty (FaithfulHermitianJordanEmbedding Q d)

theorem simpleFactorsAlbertOrHermitian_iff_rankThree
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    P.SimpleFactorsAlbertOrHermitian hinner ↔ P.RankThreeSimpleFactorsAlbertOrHermitian hinner := by
  constructor
  · intro h I hI
    exact fun _ => h I hI
  · intro h
    apply (P.simpleFactorsAlbertOrHermitian_iff_higherRank hinner).mpr
    intro I hI
    let Q := P.orthogonalIdealProduct hinner I hI.1
    let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
    change 3 ≤ Q.canonicalTraceOfFormallyReal hfr Q.unit → _
    intro hge
    by_cases h4 : 4 ≤ Q.canonicalTraceOfFormallyReal hfr Q.unit
    · exact Or.inr (P.simple_factor_has_hermitian_embedding_of_rank_ge_four hinner I hI h4)
    obtain ⟨n, _, c, hc, _, hunit, _⟩ := Q.primitive_spectral_resolution_of_formallyReal hfr 0
    have hlen := Q.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hunit
    rw [hlen] at hge h4
    have hnlo : 3 ≤ n := by exact_mod_cast hge
    have hnhi : n < 4 := by exact_mod_cast lt_of_not_ge h4
    have hn : n = 3 := by omega
    apply h I hI
    change Q.canonicalTraceOfFormallyReal hfr Q.unit = 3
    rw [hlen, hn]
    norm_num

end AlbertSequential.UnitalJordanProduct
