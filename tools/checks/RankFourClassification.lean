module

import GeneralEJARankFourClassification

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan)
    (hrank : 4 ≤ P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner) P.unit) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) :=
  P.exists_faithfulHermitianJordanEmbedding_of_simple_rank_ge_four hinner hsimple hrank

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (h : P.RankThreeSimpleFactorsAlbertOrHermitian hinner) :
    P.SimpleFactorsAlbertOrHermitian hinner :=
  (P.simpleFactorsAlbertOrHermitian_iff_rankThree hinner).mpr h

#print axioms UnitalJordanProduct.exists_faithfulHermitianJordanEmbedding_of_simple_rank_ge_four
#print axioms UnitalJordanProduct.simple_factor_has_hermitian_embedding_of_rank_ge_four
#print axioms UnitalJordanProduct.simpleFactorsAlbertOrHermitian_iff_rankThree
