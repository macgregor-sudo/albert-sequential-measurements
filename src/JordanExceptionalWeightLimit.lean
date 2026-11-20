/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanExceptionalWeightSeparator
public import NativeIdempotentClassification

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {k : ℕ} (I : Fin k → (P.generatedMenuProduct p).AlbertIdeal)

local notation "B" => P.generatedMenuProduct p
local notation "hB" => P.generatedMenuProduct_inner p hinner
local notation "hfr" => P.formallyReal_of_associative_inner hinner
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "cEx" => P.exceptionalUnit p I
def exceptionalSummandUnit (i : Fin k) : E := ((B).idealUnit (I i).carrier).val

include hinner in
private theorem idealUnit_val_product (i j : Fin k)
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ) :
    P.product (P.exceptionalSummandUnit p I i) (P.exceptionalSummandUnit p I j) = if i = j then P.exceptionalSummandUnit p I i else 0 := by
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact congrArg Subtype.val ((B).idealUnit_idempotent hB (I i).carrier (I i).isIdeal)
  · rw [ite_eq_right h]
    exact congrArg Subtype.val
      ((B).ideal_orthogonal_product_zero hB (I i).carrier (I i).isIdeal
        ((B).idealUnit (I i).carrier) ((B).idealUnit (I j).carrier) ((B).idealUnit_mem _)
        (horth j i (Ne.symm h) ((B).idealUnit_mem _)))

include hinner in
theorem exceptionalUnit_product_idealUnit
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ) (j : Fin k) :
    P.product cEx (P.exceptionalSummandUnit p I j) = P.exceptionalSummandUnit p I j := by
  classical
  change P.product (∑ i, P.exceptionalSummandUnit p I i) (P.exceptionalSummandUnit p I j) = _
  simp only [map_sum,LinearMap.sum_apply,P.idealUnit_val_product p hinner I _ _ horth]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

include hinner in
theorem exceptionalUnit_idempotent
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ) :
    P.product cEx cEx = cEx := by
  change P.product cEx (∑ i, P.exceptionalSummandUnit p I i) = ∑ i, P.exceptionalSummandUnit p I i
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => P.exceptionalUnit_product_idealUnit p hinner I horth i)

omit [FiniteDimensional ℝ E] in
private theorem complement_idempotent_of_idempotent (x : E) (hx : P.product x x = x) :
    P.product (P.unit-x) (P.unit-x) = P.unit-x := by
  have hu : P.product x P.unit = x := (P.commutative _ _).trans (P.unit_left x)
  simp only [map_sub,LinearMap.sub_apply,P.unit_left,hu,hx]
  abel

private theorem normalizedIdempotent_density (x : E) (hx : P.product x x = x) (h0 : x ≠ 0) :
    P.IsCanonicalDensity hfr ((τ x)⁻¹ • x) := by
  have hpos : 0 < τ x := by
    rw [← hx]
    exact P.canonicalTraceOfFormallyReal_square_positive hfr x h0
  refine ⟨P.nonnegative_smul_mem_squareCone x ⟨x,hx.symm⟩ _ (inv_nonneg.mpr hpos.le),?_⟩
  rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hpos.ne']

include hinner in
private theorem exceptionalUnit_ne_zero
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ) (j : Fin k) :
    cEx ≠ 0 := by
  intro hz
  have hu := P.exceptionalUnit_product_idealUnit p hinner I horth j
  rw [hz,map_zero,LinearMap.zero_apply] at hu
  have hz' : (B).idealUnit (I j).carrier = 0 := Subtype.ext hu.symm
  have hu' := (I j).unit
  have hsub : (⟨(B).idealUnit (I j).carrier,(B).idealUnit_mem (I j).carrier⟩ : (I j).carrier) = 0 :=
    Subtype.ext hz'
  rw [hsub,map_zero] at hu'
  have ht := congrArg albertTrace hu'
  rw [NativeAnalysis.albertTrace_zero,NativeAnalysis.albertTrace_unit] at ht
  norm_num at ht

private theorem continuous_readout_in_state (c : FiniteRealWordFunctional n) :
    Continuous (fun ρ => c.evaluate (fun w => τ (P.sequentialBranchState p ρ w))) := by
  have hs (w : Word (Fin n)) : Continuous (fun ρ => τ (P.sequentialBranchState p ρ w)) := by
    simp_rw [P.canonicalTrace_sequentialBranchState]
    exact ((P.canonicalTraceFormOfFormallyReal hfr).flip
      (P.sequentialWordEffect p w)).toContinuousLinearMap.continuous
  unfold FiniteRealWordFunctional.evaluate
  induction c.terms with
  | nil => simp only [List.map_nil,List.sum_nil]; exact continuous_const
  | cons t ts ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (continuous_const.mul (hs t.2)).add ih

/-- A fixed positive margin cannot extend down to all strictly positive
exceptional weights when the complementary generated summand is nonzero.
The zero-weight realization uses the classified converse. -/
theorem noUniformMargin_exceptionalWeight
    (hclass : (B).SimpleFactorsAlbertOrHermitian hB)
    (hp : ∀ i, P.product (p i) (p i) = p i)
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ)
    (hcomplete : ∀ J : (B).AlbertIdeal, ∃ i, (I i).carrier = J.carrier)
    (j : Fin k) (hcomp : cEx ≠ P.unit) (c : FiniteRealWordFunctional n) (γ : ℝ) (hγ : 0 < γ) :
    ¬ ((∀ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
        0 ≤ c.evaluate M.probability) ∧
      (∀ ρ, P.IsCanonicalDensity hfr ρ → 0 < P.exceptionalWeight p hinner I ρ →
        c.evaluate (fun w => τ (P.sequentialBranchState p ρ w)) ≤ -γ)) := by
  rintro ⟨hprojective,hbound⟩
  let q := P.unit - cEx
  let ρ₀ := (τ q)⁻¹ • q
  let ρ₁ := (τ cEx)⁻¹ • cEx
  have he : P.product cEx cEx = cEx := P.exceptionalUnit_idempotent p hinner I horth
  have hq : P.product q q = q := P.complement_idempotent_of_idempotent cEx he
  have hρ₀ : P.IsCanonicalDensity hfr ρ₀ :=
    P.normalizedIdempotent_density hinner q hq (sub_ne_zero.mpr (Ne.symm hcomp))
  have hρ₁ : P.IsCanonicalDensity hfr ρ₁ :=
    P.normalizedIdempotent_density hinner cEx he (P.exceptionalUnit_ne_zero p hinner I horth j)
  have hy (i : Fin k) : P.product q (P.exceptionalSummandUnit p I i) = 0 := by
    change P.product (P.unit - cEx) (P.exceptionalSummandUnit p I i) = 0
    rw [map_sub,LinearMap.sub_apply,P.unit_left,P.exceptionalUnit_product_idealUnit p hinner I horth,sub_self]
  have hzero (J : (B).AlbertIdeal) :
      P.canonicalTraceFormOfFormallyReal hfr ρ₀ ((B).idealUnit J.carrier).val = 0 := by
    obtain ⟨i,hi⟩ := hcomplete J
    rw [← hi,P.canonicalTraceFormOfFormallyReal_apply]
    change τ (P.product ((τ q)⁻¹ • q) (P.exceptionalSummandUnit p I i)) = 0
    rw [map_smul,LinearMap.smul_apply,hy,smul_zero,map_zero]
  have hw0 : P.exceptionalWeight p hinner I ρ₀ = 0 := by
    rw [exceptionalWeight,exceptionalUnit,map_sum]
    exact Finset.sum_eq_zero (fun i _ => hzero (I i))
  have hw1 : P.exceptionalWeight p hinner I ρ₁ = 1 := by
    rw [exceptionalWeight,P.canonicalTraceFormOfFormallyReal_apply]
    change τ (P.product ((τ cEx)⁻¹ • cEx) cEx) = 1
    rw [map_smul,LinearMap.smul_apply,he]
    exact hρ₁.2
  obtain ⟨d,M,_,hm⟩ := P.exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_of_classifiedFactors
    p hp hinner hclass ρ₀ hρ₀ hzero
  let mix (t : ℝ) := (1-t) • ρ₀ + t • ρ₁
  have hmWeight (t : ℝ) : P.exceptionalWeight p hinner I (mix t) = t := by
    change P.canonicalTraceFormOfFormallyReal hfr ((1-t) • ρ₀ + t • ρ₁) cEx = t
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
    change (1-t) * P.exceptionalWeight p hinner I ρ₀ + t * P.exceptionalWeight p hinner I ρ₁ = t
    rw [hw0,hw1,mul_zero,mul_one,zero_add]
  let g (t : ℝ) := c.evaluate (fun w => τ (P.sequentialBranchState p (mix t) w))
  have hcon : Continuous g := (P.continuous_readout_in_state p hinner c).comp
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const))
  have hset : Set.Ioc (0 : ℝ) 1 ⊆ {t | g t ≤ -γ} := by
    intro t ht
    apply hbound (mix t)
    · exact P.convex_canonicalDensity hinner hfr hρ₀ hρ₁ (sub_nonneg.mpr ht.2) ht.1.le (by ring)
    · rw [hmWeight]
      exact ht.1
  have h0 : (0 : ℝ) ∈ closure (Set.Ioc 0 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl,zero_le_one⟩
  have hb : g 0 ≤ -γ := closure_minimal hset (isClosed_le hcon continuous_const) h0
  have hn : 0 ≤ g 0 := by
    have hm0 : mix 0 = ρ₀ := by simp [mix]
    change 0 ≤ c.evaluate (fun w => τ (P.sequentialBranchState p (mix 0) w))
    have heq : M.probability = (fun w => τ (P.sequentialBranchState p ρ₀ w)) := funext hm
    rw [hm0,← heq]
    exact hprojective d M
  linarith

end AlbertSequential.UnitalJordanProduct
