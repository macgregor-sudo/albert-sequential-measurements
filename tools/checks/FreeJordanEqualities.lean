module

import EqualityJordanIdentities
import EqualityFreeJordan

noncomputable section

open AlbertSequential AlbertSequential.AppF AlbertSequential.EqualityCountermodels

example {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i) :
    (∃ (c : Word (Fin n) →₀ ℝ) (ρ : Albert), IsProjectiveEquality c ∧ IsDensity ρ ∧
      c.sum (fun w a => a * nativeWordProbability p ρ w) ≠ 0) ↔
    ∃ x ∈ freeJordanWordSpan n, freeJordanToGroup x = 0 ∧ freeJordanToNative p hp x ≠ 0 :=
  projectiveViolation_iff_freeWordSpanKernel p hp

example {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (hg : GeneratesAlbert p) :
    ∃ x : FreeIdempotentJordan n, freeJordanToGroup x = 0 ∧ freeJordanToNative p hp x ≠ 0 :=
  exists_freeJordanKernel_of_generates p hp hg

example {E : Type} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)
    {n : ℕ} (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ)
    (c : Word (Fin n) →₀ ℝ) (h : freeWordCombination c = freeJordanZero n) :
    c.sum (fun w a => a * P.wordTable p φ w) = 0 :=
  freeWordCombination_zero_readout P p hp φ c h

example {E I : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)
    (p : I → E) (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ) (i j : I) :
    BasicWordEqualities (P.wordTable p φ) ∧
    P.wordTable p φ [(i, true), (j, true), (i, false)] =
      P.wordTable p φ [(i, true), (j, false), (i, false)] :=
  ⟨P.wordTable_basicWordEqualities p hp φ, P.wordTable_extraTwo p hp φ i j⟩

#print axioms specialJordanSubmodule_no_surjective_to_Albert
#print axioms freeJordanGenerator_idempotent
#print axioms freeJordanEvaluation_preserves_operations
#print axioms freeJordanEvaluation_unique
#print axioms freeWordCombination_zero_readout
#print axioms projectiveViolation_iff_freeWordSpanKernel
#print axioms exists_freeJordanKernel_of_generates
#print axioms exists_projectiveViolation_of_freeWordSpan_eq_univ
#print axioms UnitalJordanProduct.wordTable_basicWordEqualities
#print axioms UnitalJordanProduct.wordTable_extraOne
#print axioms UnitalJordanProduct.wordTable_extraTwo
#print axioms basicWordEqualities_do_not_imply_extraOne_at
#print axioms basicWordEqualities_do_not_imply_extraTwo_at
