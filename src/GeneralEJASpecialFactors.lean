/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneralEJAFactorEmbeddings
public import GeneralEJAGenerated
public import JordanSimpleFactors

/-! Assemble a single finite projective model from the represented simple
factors. The classification premise is an explicit input to this theorem. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- The simple-factor classification needed by the representation criterion. -/
def SimpleFactorsAlbertOrHermitian
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) : Prop :=
  ∀ (I : Submodule ℝ E) (hI : P.IsSimpleJordanIdeal I),
    (∃ J : P.AlbertIdeal, J.carrier = I) ∨
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (P.orthogonalIdealProduct hinner I hI.1) d)

/-- Given the simple-factor classification, zero Albert weights imply that
every idempotent menu is represented by one finite complex projective model. -/
theorem exists_projectiveRepresentation_of_zeroAlbertWeights_of_classifiedFactors {n : ℕ}
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hclass : P.SimpleFactorsAlbertOrHermitian hinner)
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (ω : E →ₗ[ℝ] ℝ) (hpos : ∀ x, 0 ≤ ω (P.product x x)) (hunit : ω P.unit = 1)
    (hzero : ∀ I : P.AlbertIdeal, ω (P.idealUnit I.carrier) = 0) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w = ω (P.sequentialWordEffect p w) := by
  classical
  obtain ⟨s, hI, D, hsimple, _, _, _, hDprod, hDunit, _, _, hInv⟩ :=
    P.exists_simple_unital_product_equivalence hinner
  let R (i : s) := P.orthogonalIdealProduct hinner i.val (hI i.val i.property)
  let keep (i : s) : Prop := ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (R i) d)
  let K := Subtype keep
  let Q := factorProduct (fun i : K => R i.val)
  have hvanish (i : s) (hi : ¬ keep i) (x : i.val) : ω x.val = 0 := by
    have hAlbert : ∃ J : P.AlbertIdeal, J.carrier = i.val :=
      (hclass i.val (hsimple i.val i.property)).resolve_right hi
    obtain ⟨J, hJ⟩ := hAlbert
    have hz : ω (P.idealUnit i.val) = 0 := hJ ▸ hzero J
    let ωi := ω.comp i.val.subtype
    have hR : (R i).FormallyReal := (R i).formallyReal_of_associative_inner
      (P.orthogonalIdealProduct_inner hinner i.val (hI i.val i.property))
    have ho : ωi = 0 := (R i).positiveFunctional_unit_zero hR ωi (fun y => hpos y.val) hz
    exact LinearMap.congr_fun ho x
  let extend : (∀ i : K, i.val.val) →ₗ[ℝ] (∀ i : s, i.val) :=
    { toFun := fun x i => if hi : keep i then x ⟨i, hi⟩ else 0
      map_add' := by intro x y; funext i; by_cases hi : keep i <;> simp [hi]
      map_smul' := by intro c x; funext i; by_cases hi : keep i <;> simp [hi] }
  let π : E →ₗ[ℝ] (∀ i : K, i.val.val) :=
    { toFun := fun x i => D x i.val
      map_add' := by intro x y; funext i; exact congrFun (D.map_add x y) i.val
      map_smul' := by intro c x; funext i; exact congrFun (D.map_smul c x) i.val }
  have hπprod (x y : E) : π (P.product x y) = Q.product (π x) (π y) :=
    funext fun i => hDprod x y i.val
  have hπunit : π P.unit = Q.unit := funext fun i => congrFun hDunit i.val
  let ωK := ω.comp (D.symm.toLinearMap.comp extend)
  have hrestore (x : E) : ωK (π x) = ω x := by
    change ω (D.symm (extend (π x))) = ω x
    conv_rhs => rw [← D.symm_apply_apply x]
    rw [hInv, hInv, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ω ((if hi : keep i then π x ⟨i, hi⟩ else 0 : i.val).val) = ω (D x i).val
    by_cases hi : keep i
    · rw [dite_eq_left hi]; rfl
    · rw [dite_eq_right hi, hvanish i hi, hvanish i hi]
  have hωpos (x : ∀ i : K, i.val.val) : 0 ≤ ωK (Q.product x x) := by
    have hsq : extend (Q.product x x) =
        D (P.product (D.symm (extend x)) (D.symm (extend x))) := by
      funext i
      rw [hDprod, D.apply_symm_apply]
      change (if hi : keep i then Q.product x x ⟨i, hi⟩ else 0) =
        (R i).product (if hi : keep i then x ⟨i, hi⟩ else 0) (if hi : keep i then x ⟨i, hi⟩ else 0)
      by_cases hi : keep i <;> simp [hi, Q]
    change 0 ≤ ω (D.symm (extend (Q.product x x)))
    rw [hsq, D.symm_apply_apply]
    exact hpos _
  have hωunit : ωK Q.unit = 1 := by rw [← hπunit, hrestore, hunit]
  have hpt (i : Fin n) : Q.product (π (p i)) (π (p i)) = π (p i) := by
    rw [← hπprod, hp i]
  obtain ⟨d, ⟨embedding⟩⟩ := exists_faithfulHermitianJordanEmbedding_of_factors
    (fun i : K => R i.val) (fun i => i.property)
  obtain ⟨M, hM, hword⟩ := embedding.exists_projectiveRepresentation_of_embedding
    (π ∘ p) hpt ωK hωpos hωunit
  refine ⟨d, M, hM, fun w => ?_⟩
  rw [hword, ← P.map_sequentialWordEffect Q π hπunit hπprod p w, hrestore]

/-- Core Theorem 4.11(a) on the actual generated algebra, conditional solely
on the simple-factor classification premise. -/
theorem exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_of_classifiedFactors {n : ℕ}
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hclass : (P.generatedMenuProduct p).SimpleFactorsAlbertOrHermitian (P.generatedMenuProduct_inner p hinner))
    (ρ : E) (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ)
    (hzero : ∀ I : (P.generatedMenuProduct p).AlbertIdeal,
      P.canonicalTraceFormOfFormallyReal (P.formallyReal_of_associative_inner hinner) ρ
        ((P.generatedMenuProduct p).idealUnit I.carrier).val = 0) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  let B := P.generatedMenuProduct p
  let ω := P.canonicalPairingFunctional hfr ρ
  let ωB := ω.comp (P.generatedMenuCarrier p).subtype
  have hposB (x : P.generatedMenuCarrier p) : 0 ≤ ωB (B.product x x) := by
    have hdual := (P.canonicalTraceRepresentative_positive_iff hfr ω).mp (by
      rw [P.canonicalTraceRepresentative_pairingFunctional]
      exact hρ.1)
    exact hdual x.val
  have hunitB : ωB B.unit = 1 := by
    change P.canonicalTraceFormOfFormallyReal hfr ρ P.unit = 1
    rw [P.canonicalTraceFormOfFormallyReal_unit]
    exact hρ.2
  have hpB (i : Fin n) : B.product (P.generatedMenuTest p i) (P.generatedMenuTest p i) =
      P.generatedMenuTest p i := Subtype.ext (hp i)
  obtain ⟨d, M, hM, hw⟩ := B.exists_projectiveRepresentation_of_zeroAlbertWeights_of_classifiedFactors
    (P.generatedMenuProduct_inner p hinner) hclass (P.generatedMenuTest p) hpB ωB hposB hunitB hzero
  refine ⟨d, M, hM, fun w => ?_⟩
  rw [hw, P.canonicalTrace_sequentialBranchState]
  change ω ((B.sequentialWordEffect (P.generatedMenuTest p) w).val) = ω (P.sequentialWordEffect p w)
  rw [P.generatedMenu_sequentialWordEffect]

end AlbertSequential.UnitalJordanProduct
