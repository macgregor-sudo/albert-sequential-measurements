module

import CyclicGeneratedPurity

open AlbertSequential
open scoped InnerProductSpace

noncomputable section

section
variable {I E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : UnitalJordanProduct E) (p : I → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

local notation "hfr" => P.formallyReal_of_associative_inner hinner
local notation "τ" => P.canonicalTraceOfFormallyReal hfr

/-- The negative outcome is primitive in the actual generated carrier.
No ambient primitivity or nonzero history premise is used. -/
example (hp : ∀ i, P.product (p i) (p i) = p i) (i : I) (v t : Word I) (ρ : E)
    (hq : (P.generatedMenuProduct p).IsPrimitive (P.generatedMenuOutcome p (i,false)))
    (M : AlgebraicProjectiveData I A)
    (hm : ∀ w ∈ [t ++ [(i,false)] ++ v ++ v.dropLast.reverse ++ [(i,false)], t ++ [(i,false)] ++ v, t ++ [(i,false)]],
      M.probability w = τ (P.sequentialBranchState p ρ w)) :
    let q : Outcome I := (i,false)
    let a := P.unit - p i
    let c := P.canonicalTraceFormOfFormallyReal hfr a (P.sequentialWordEffect p v) /
      P.canonicalTraceFormOfFormallyReal hfr a a
    outcomePurityElement (cyclicHilbertProjection M) q v c
      (wordAmplitude (cyclicHilbertProjection M) t (cyclicHilbertVector M)) = 0 := by
  intro q a c
  rw [← cyclicPurityElement_representation]
  exact P.cyclic_generatedPurity_null_history p hinner hp q hq v t ρ M hm

example (hp : ∀ i, P.product (p i) (p i) = p i) (q : Outcome I) (v : Word I) (ρ : E)
    (hq : (P.generatedMenuProduct p).IsPrimitive (P.generatedMenuOutcome p q))
    (M : AlgebraicProjectiveData I A)
    (hm : ∀ w, M.probability w = τ (P.sequentialBranchState p ρ w)) :
    outcomePurityElement (cyclicHilbertProjection M) q v (P.generatedPurityCoefficient p hinner q v) = 0 := by
  rw [← cyclicPurityElement_representation]
  exact P.cyclic_generatedPurity_zero_operator p hinner hp q hq v ρ M hm

end

#print axioms UnitalJordanProduct.sequentialWordEffect_quadratic_mirror
#print axioms UnitalJordanProduct.generated_primitive_quadratic_coefficient
#print axioms UnitalJordanProduct.generatedPurityCoefficient_eq_branchTrace_div
#print axioms UnitalJordanProduct.generatedPurity_three_effects
#print axioms UnitalJordanProduct.generatedPurity_effect_residual
#print axioms UnitalJordanProduct.generatedPurity_probability_residual
#print axioms cyclic_history_norm_sq
#print axioms cyclicPurity_threeWords
#print axioms UnitalJordanProduct.cyclic_generatedPurity_null_history
#print axioms UnitalJordanProduct.cyclic_generatedPurity_zero_operator
