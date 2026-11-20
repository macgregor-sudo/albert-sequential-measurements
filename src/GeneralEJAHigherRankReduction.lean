/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJALowRankClassification
public import GeneralEJASpecialFactors
public import JordanIdealRestriction

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- Classification of the actual simple restricted factors whose primitive frames have at least
three idempotents. -/
def HigherRankSimpleFactorsAlbertOrHermitian
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) : Prop :=
  ∀ (I : Submodule ℝ E) (hI : P.IsSimpleJordanIdeal I),
    let Q := P.orthogonalIdealProduct hinner I hI.1
    let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
    3 ≤ Q.canonicalTraceOfFormallyReal hfr Q.unit →
      (∃ J : P.AlbertIdeal, J.carrier = I) ∨
        ∃ d, Nonempty (FaithfulHermitianJordanEmbedding Q d)

theorem simpleFactorsAlbertOrHermitian_iff_higherRank
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    P.SimpleFactorsAlbertOrHermitian hinner ↔ P.HigherRankSimpleFactorsAlbertOrHermitian hinner := by
  constructor
  · intro h I hI
    exact fun _ => h I hI
  · intro h I hI
    let Q := P.orthogonalIdealProduct hinner I hI.1
    let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
    obtain ⟨n, _, c, hc, _, hsum, _⟩ := Q.primitive_spectral_resolution_of_formallyReal hfr 0
    have hunit : Q.unit ≠ 0 := ((P.simple_ideal_iff_restricted_simple hinner I hI.1).mp hI).1
    have hn : n ≠ 0 := by
      intro hn
      subst n
      exact hunit (by simpa only [Fin.sum_univ_zero] using hsum.symm)
    have hrank := Q.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hsum
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · right
      exact ⟨1, Q.faithfulHermitianEmbedding_of_rank_one hfr (by simpa only [h1, Nat.cast_one] using hrank)⟩
    · right
      exact Q.faithfulHermitianEmbedding_of_rank_two hfr (by simpa only [h2, Nat.cast_ofNat] using hrank)
    · apply h I hI
      change 3 ≤ Q.canonicalTraceOfFormallyReal hfr Q.unit
      rw [hrank]
      exact_mod_cast h3

end AlbertSequential.UnitalJordanProduct
