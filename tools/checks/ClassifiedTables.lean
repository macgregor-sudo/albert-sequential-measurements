module

import GeneralEJASmallMenus

open AlbertSequential

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

example (hfr : P.FormallyReal) :
    (∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n) ↔
      P.HasAssociativeJordanEmbedding :=
  (P.canonicalProjectiveTables_iff_special_native hinner hfr).2

example (hfr : P.FormallyReal) :
    P.HasAssociativeJordanEmbedding ↔
      P.canonicalProjectiveTables hfr 4 ⊆ hilbertProjectiveTables.{0} ℂ 4 :=
  (P.special_iff_all_tables_and_four_tables_native hinner hfr).1.trans
    (P.special_iff_all_tables_and_four_tables_native hinner hfr).2

example (p : Fin 3 → E) (hp : ∀ i, P.product (p i) (p i) = p i) (ρ : E)
    (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation 3 ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w) :=
  P.exists_projectiveRepresentation_of_at_most_three_native (by decide) p hp hinner ρ hρ

example (p : Fin 2 → E) (hp : ∀ i, P.product (p i) (p i) = p i) (ρ : E)
    (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation 2 ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w) :=
  P.exists_projectiveRepresentation_of_at_most_three_native (by decide) p hp hinner ρ hρ

end

#print axioms UnitalJordanProduct.finiteHermitianEmbedding_or_albertIdeal_native
#print axioms UnitalJordanProduct.finiteHermitianEmbedding_iff_associativeJordanEmbedding_native
#print axioms UnitalJordanProduct.exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_native
#print axioms UnitalJordanProduct.exists_projectiveRepresentation_of_special_generatedMenu_native
#print axioms UnitalJordanProduct.exists_projectiveRepresentation_iff_zeroAlbertWeights_of_BPrimitive_native
#print axioms UnitalJordanProduct.canonicalProjectiveTables_iff_special_native
#print axioms UnitalJordanProduct.special_iff_all_tables_and_four_tables_native
#print axioms not_generatesAlbert_of_at_most_three_idempotents
#print axioms UnitalJordanProduct.not_albertIdeal_generatedMenu_of_at_most_three
#print axioms UnitalJordanProduct.exists_projectiveRepresentation_of_at_most_three_native
