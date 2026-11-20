module

import JordanTableFoil
import TwoAlbertTableMixture

open AlbertSequential
open scoped TwoAlbert

universe v

example (n : ℕ) : Convex ℝ (hilbertProjectiveTables.{v} ℝ n) ∧
    Convex ℝ (hilbertProjectiveTables.{v} ℂ n) ∧ Convex ℝ (quaternionicProjectiveTables.{v} n) :=
  ⟨convex_hilbertProjectiveTables_real n,convex_hilbertProjectiveTables_complex n,
    convex_quaternionicProjectiveTables n⟩

example {n : ℕ} (f : Fin 3 → Word (Fin n) → ℝ) (a : Fin 3 → ℝ)
    (hf : ∀ i, f i ∈ finiteJordanTables.{0} n) (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) :
    (∑ i, a i • f i) ∈ finiteJordanTables.{0} n :=
  finiteJordanTables_sum_mem f a hf ha hs

example (hclass : AllSimpleFactorsAlbertOrHermitian) (n : ℕ) :
    finiteJordanTables.{0} n =
      convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) :=
  finiteJordanTables_eq_convexHull_of_classifiedFactors hclass n

example (n : ℕ) : convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) ⊆
    finiteJordanTables.{0} n := convexHull_projective_union_albert_subset_finiteJordan n

example {n : ℕ} (p q : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (hgp : GeneratesAlbert p) (hgq : GeneratesAlbert q)
    (hg : TwoAlbert.product.GeneratesMenu (TwoAlbert.pair p q))
    (ρ σ : Albert) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    ∃ initial : TwoAlbert.Space, TwoAlbert.product.IsCanonicalDensity TwoAlbert.formallyReal initial ∧
      ∀ w, TwoAlbert.product.canonicalTraceOfFormallyReal TwoAlbert.formallyReal
        (TwoAlbert.product.sequentialBranchState (TwoAlbert.pair p q) initial w) =
        (1/2 : ℝ) * nativeWordProbability p ρ w + (1/2 : ℝ) * nativeWordProbability q σ w := by
  obtain ⟨_,⟨initial,hd,hw⟩,_,_⟩ :=
    TwoAlbert.paired_albert_mixture.{0} p q hp hq hgp hgq hg (1/2) (by norm_num) (by norm_num) ρ σ hρ hσ
  refine ⟨initial,hd,fun w => ?_⟩
  norm_num at hw ⊢
  exact hw w

#print axioms AlgebraicProjectiveData.weightedProduct_probability
#print axioms convex_hilbertProjectiveTables_real
#print axioms convex_hilbertProjectiveTables_complex
#print axioms convex_quaternionicProjectiveTables
#print axioms UnitalJordanProduct.mem_canonicalProjectiveTables_iff_functional
#print axioms finiteJordanTables_sum_mem
#print axioms selfAdjointOperatorJordan_formallyReal
#print axioms finiteComplexTables_subset_finiteJordan
#print axioms nativeAlbert_canonicalProjectiveTables_eq
#print axioms generated_nativeAlbert_table_not_complex
#print axioms TwoAlbert.paired_test_rank_two
#print axioms TwoAlbert.paired_test_not_BPrimitive
#print axioms TwoAlbert.paired_albert_mixture
#print axioms convexHull_projective_union_albert_subset_finiteJordan
#print axioms UnitalJordanProduct.canonicalProjectiveTables_subset_foil_of_classifiedFactors
#print axioms finiteJordanTables_eq_convexHull_of_classifiedFactors
#print axioms finiteJordan_linear_inequality_iff_of_classifiedFactors
