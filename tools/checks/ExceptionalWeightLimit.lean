module

import JordanExceptionalWeightLimit

open AlbertSequential
open scoped InnerProductSpace

noncomputable section

universe uR uC uQ

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) {n k : ℕ} (p : Fin n → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (I : Fin k → (P.generatedMenuProduct p).AlbertIdeal) (hm : P.IsBPrimitiveMenu p) (ε : ℝ) (he : 0 < ε) :
    ∃ (L : ℕ) (c : FiniteRealWordFunctional n) (γ : ℝ),
      0 < γ ∧ c.HasHorizon L ∧
      (∀ (H : Type uR) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℝ H), 0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uC) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℂ H), 0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uQ) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicHilbertStructure H) (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure),
        0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      ∀ ρ, P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ →
        ε ≤ P.canonicalTraceFormOfFormallyReal (P.formallyReal_of_associative_inner hinner) ρ
          (∑ i, ((P.generatedMenuProduct p).idealUnit (I i).carrier).val) →
        c.evaluate (fun w => P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w)) ≤ -γ := by
  obtain ⟨L,c,γ,hγ,hL,hR,hC,hQ,h⟩ := P.uniformHilbertSeparator_exceptionalWeight.{uR,uC,uQ} p hinner I hm ε he
  exact ⟨L,c,γ,hγ,hL,hR,hC,hQ,fun ρ hd hw => h ρ ⟨hd,hw⟩⟩

#check UnitalJordanProduct.noUniformMargin_exceptionalWeight

#print axioms UnitalJordanProduct.isCompact_canonicalDensity
#print axioms UnitalJordanProduct.convex_canonicalDensity
#print axioms UnitalJordanProduct.isCompact_exceptionalWeightSlice
#print axioms UnitalJordanProduct.convex_exceptionalWeightSlice
#print axioms UnitalJordanProduct.uniformMomentSeparator_exceptionalWeight
#print axioms UnitalJordanProduct.uniformHilbertSeparator_exceptionalWeight
#print axioms UnitalJordanProduct.exceptionalUnit_idempotent
#print axioms UnitalJordanProduct.noUniformMargin_exceptionalWeight
