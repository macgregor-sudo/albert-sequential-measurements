/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneratedPurityEffects
public import CyclicWordVectors

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential

section Cyclic

variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- The signed purity element in the actual associative word algebra. -/
def cyclicPurityElement (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v : Word ι) (c : ℝ) : CyclicWordAlgebra M :=
  let Q := cyclicWordElement M [q]
  let T := cyclicWordElement M v
  Q * (star T * T) * Q - c • Q

@[simp] theorem cyclicPurityElement_value (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v : Word ι) (c : ℝ) :
    (cyclicPurityElement M q v c : A) = outcomePurityElement M.projection q v c := by
  change wordAmplitude M.projection [q] * wordOperator M.projection v * wordAmplitude M.projection [q] -
    c • wordAmplitude M.projection [q] = _
  simp only [wordAmplitude_singleton,outcomePurityElement]

theorem cyclicPurityElement_selfAdjoint (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v : Word ι) (c : ℝ) : star (cyclicPurityElement M q v c) = cyclicPurityElement M q v c := by
  apply Subtype.ext
  change star (cyclicPurityElement M q v c : A) = _
  rw [cyclicPurityElement_value,outcomePurityElement_star M.projection M.selfAdjoint]

/-- Its cyclic image is the literal purity operator computed with the cyclic projections. -/
theorem cyclicPurityElement_representation (M : AlgebraicProjectiveData ι A) (q : Outcome ι)
    (v : Word ι) (c : ℝ) :
    cyclicHilbertRepresentation M (cyclicPurityElement M q v c) =
      outcomePurityElement (cyclicHilbertProjection M) q v c := by
  simp only [cyclicPurityElement,map_sub,map_mul,map_star,map_smul,wordAmplitude_singleton,
    cyclicHilbertRepresentation_word,wordOperator,outcomePurityElement]

/-- The squared norm on the literal history equals the square mass in the original state. -/
theorem cyclic_history_norm_sq (M : AlgebraicProjectiveData ι A) (Z : CyclicWordAlgebra M)
    (t : Word ι) :
    ‖cyclicHilbertRepresentation M Z
      (wordAmplitude (cyclicHilbertProjection M) t (cyclicHilbertVector M))‖ ^ 2 =
      M.squareMass ((Z : A) * wordAmplitude M.projection t) := by
  rw [← cyclicHilbertRepresentation_word]
  rw [← mul_apply_eq_comp,← map_mul,cyclicHilbertAction_vector,
    UniformSpace.Completion.norm_coe,cyclicPreHilbert_norm_sq]
  rfl

theorem cyclicPurity_threeWords (M : AlgebraicProjectiveData ι A)
    (q : Outcome ι) (v t : Word ι) (c : ℝ) :
    ‖cyclicHilbertRepresentation M (cyclicPurityElement M q v c)
      (wordAmplitude (cyclicHilbertProjection M) t (cyclicHilbertVector M))‖ ^ 2 =
      M.probability (t ++ [q] ++ v ++ purityMirror v ++ [q]) -
        2 * c * M.probability (t ++ [q] ++ v) + c ^ 2 * M.probability (t ++ [q]) := by
  rw [cyclic_history_norm_sq,cyclicPurityElement_value,purityResidual_threeHistories]

end Cyclic

namespace UnitalJordanProduct

open scoped InnerProductSpace

variable {E ι A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : UnitalJordanProduct E) (p : ι → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

local notation "B" => P.generatedMenuProduct p
local notation "hfr" => P.formallyReal_of_associative_inner hinner
local notation "τ" => P.canonicalTraceOfFormallyReal hfr

/-- Exactly the three words of Lemma 4.5 suffice on this history. -/
theorem cyclic_generatedPurity_null_history (hp : ∀ i, P.product (p i) (p i) = p i)
    (q : Outcome ι) (hq : (B).IsPrimitive (P.generatedMenuOutcome p q))
    (v t : Word ι) (ρ : E) (M : AlgebraicProjectiveData ι A)
    (hM : ∀ w ∈ [t ++ [q] ++ v ++ purityMirror v ++ [q], t ++ [q] ++ v,t ++ [q]],
      M.probability w = τ (P.sequentialBranchState p ρ w)) :
    cyclicHilbertRepresentation M
      (cyclicPurityElement M q v (P.generatedPurityCoefficient p hinner q v))
      (wordAmplitude (cyclicHilbertProjection M) t (cyclicHilbertVector M)) = 0 := by
  apply norm_eq_zero.mp
  apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [cyclicPurity_threeWords,hM _ (by simp),hM _ (by simp),hM _ (by simp)]
  exact P.generatedPurity_probability_residual p hinner hp q hq v t ρ

/-- All-word matching makes the actual bounded purity operator zero. -/
theorem cyclic_generatedPurity_zero_operator (hp : ∀ i, P.product (p i) (p i) = p i)
    (q : Outcome ι) (hq : (B).IsPrimitive (P.generatedMenuOutcome p q))
    (v : Word ι) (ρ : E) (M : AlgebraicProjectiveData ι A)
    (hM : ∀ w, M.probability w = τ (P.sequentialBranchState p ρ w)) :
    cyclicHilbertRepresentation M
      (cyclicPurityElement M q v (P.generatedPurityCoefficient p hinner q v)) = 0 := by
  let T := cyclicHilbertRepresentation M (cyclicPurityElement M q v (P.generatedPurityCoefficient p hinner q v))
  have hd : Dense (LinearMap.ker T.toLinearMap : Set (CyclicHilbert M)) := by
    apply (cyclicHilbert_cyclic M).mono
    apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact P.cyclic_generatedPurity_null_history p hinner hp q hq v t ρ M (fun w _ => hM w)
  have hall := hd.closure_eq
  rw [T.isClosed_ker.closure_eq] at hall
  ext x
  exact (Set.eq_univ_iff_forall.mp hall) x

end UnitalJordanProduct
end AlbertSequential
