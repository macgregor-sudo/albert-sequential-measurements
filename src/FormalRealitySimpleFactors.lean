/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanSimpleFactors
public import JordanMappedIdealProducts
public import FormalRealityCanonicalTrace

/-! Finite simple unital factors under the original algebraic formal-reality
assumptions. Image ideals, products and units are actual transported objects;
there is no factor-classification or ambient-norm premise. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

theorem exists_simple_factors_of_formallyReal (hfr : P.FormallyReal) :
    ∃ (n : ℕ) (I : Fin n → Submodule ℝ E)
      (R : (i : Fin n) → UnitalJordanProduct (I i))
      (D : E ≃ₗ[ℝ] ((i : Fin n) → I i)),
      (∀ i,P.IsSimpleJordanIdeal (I i) ∧ (R i).IsSimpleJordan) ∧
      (∀ i (x y : I i),((R i).product x y).val=P.product x.val y.val) ∧
      (∀ i j,i≠j → ∀ x∈I i,∀ y∈I j,P.canonicalTraceFormOfFormallyReal hfr x y=0) ∧
      (⨆ i,I i)=⊤ ∧
      (∀ x y i,D (P.product x y) i=(R i).product (D x i) (D y i)) ∧
      D P.unit=(fun i => (R i).unit) ∧
      (∀ a x i,D (P.quadraticRepresentation a x) i=(R i).quadraticRepresentation (D a i) (D x i)) ∧
      (∑ i,((R i).unit).val)=P.unit ∧
      (∀ v : ((i : Fin n) → I i),D.symm v=∑ i,(v i).val) := by
  classical
  let B := P.canonicalTraceFormOfFormallyReal hfr
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr)
    (P.canonicalTraceFormOfFormallyReal_positive hfr)
  letI : InnerProductSpace.Core ℝ V := C
  letI : NormedAddCommGroup V := C.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have he (x y : V) : e (Q.product x y)=P.product (e x) (e y) := P.transportProduct_apply e x y
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z)=B (e x) (e (Q.product y z))
    simpa only [he] using P.canonicalTraceFormOfFormallyReal_associative hfr (e x) (e y) (e z)
  obtain ⟨s,hI,D0,hsimple,horth,htop,hfactor,hprod,hunit,hquad,hsum,hInv0⟩ :=
    Q.exists_simple_unital_product_equivalence hinnerQ
  let n := Fintype.card s
  let index : Fin n ≃ s := (Fintype.equivFin s).symm
  let F : Fin n → Submodule ℝ V := fun i => (index i).val
  let hF (i : Fin n) : Q.IsJordanIdeal (F i) := hI (index i).val (index i).property
  let S (i : Fin n) := Q.orthogonalIdealProduct hinnerQ (F i) (hF i)
  let u (i : Fin n) : F i := (S i).unit
  let hu (i : Fin n) (x : F i) : Q.product (u i).val x.val=x.val :=
    congrArg Subtype.val ((S i).unit_left x)
  let I : Fin n → Submodule ℝ E := fun i => (F i).map e.toLinearMap
  let leaf (i : Fin n) : F i ≃ₗ[ℝ] I i := e.submoduleMap (F i)
  let R (i : Fin n) : UnitalJordanProduct (I i) :=
    P.mappedIdealProduct Q e he (F i) (hF i) (u i) (hu i)
  let D1 : V ≃ₗ[ℝ] ((i : Fin n) → F i) :=
    D0.trans (LinearEquiv.piCongrLeft' ℝ (fun i : s => (i.val : Submodule ℝ V)) index.symm)
  let D : E ≃ₗ[ℝ] ((i : Fin n) → I i) :=
    e.symm.trans (D1.trans (LinearEquiv.piCongrRight leaf))
  have hleaf (i : Fin n) (x y : F i) : leaf i ((S i).product x y)=
      (R i).product (leaf i x) (leaf i y) :=
    P.mappedIdealProduct_equiv_product Q e he (F i) (hF i) (u i) (hu i) x y
  have hDprod (x y : E) (i : Fin n) : D (P.product x y) i=(R i).product (D x i) (D y i) := by
    change leaf i (D0 (e.symm (P.product x y)) (index i))=
      (R i).product (leaf i (D0 (e.symm x) (index i))) (leaf i (D0 (e.symm y) (index i)))
    rw [← P.transportProduct_inverse_apply e x y,hprod]
    exact hleaf i _ _
  refine ⟨n,I,R,D,?_,?_,?_,?_,hDprod,?_,?_,?_,?_⟩
  · intro i
    constructor
    · exact P.simpleJordanIdeal_map_equiv Q e he (F i) (hsimple (index i).val (index i).property)
    · exact P.mappedIdealProduct_simple Q e he (F i) (hF i) (u i) (hu i) (hfactor (index i))
  · intro i x y
    exact P.mappedIdealProduct_apply Q e he (F i) (hF i) (u i) (hu i) x y
  · intro i j hij x hx y hy
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change inner ℝ a b=0
    have hne : (index j).val≠(index i).val := fun h => hij (index.injective (Subtype.ext h)).symm
    exact ((F i).mem_orthogonal b).mp
      (horth (index j).val (index j).property (index i).val (index i).property hne hb) a ha
  · have hs : (⨆ i : s,(i.val : Submodule ℝ V))=⊤ := by
      simpa only [iSup_subtype,Finset.sup_eq_iSup,id_eq] using htop
    have hFtop : (⨆ i,F i)=⊤ := (Equiv.iSup_comp (g := fun i : s => (i.val : Submodule ℝ V)) index).trans hs
    have hmaptop : (⊤ : Submodule ℝ V).map e.toLinearMap=⊤ := by
      apply top_unique
      intro x _
      exact ⟨e.symm x,trivial,e.apply_symm_apply x⟩
    have h := congrArg (fun K : Submodule ℝ V => K.map e.toLinearMap) hFtop
    rw [Submodule.map_iSup,hmaptop] at h
    exact h
  · funext i
    change leaf i (D0 Q.unit (index i))=(R i).unit
    rw [congrFun hunit (index i)]
    rfl
  · intro a x i
    simp only [quadraticRepresentation_apply,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,
      RingHom.id_apply,hDprod]
  · change (∑ i,e (Q.idealUnit (F i)))=P.unit
    rw [← map_sum]
    have hsumF : (∑ i,Q.idealUnit (F i))=Q.unit :=
      (Equiv.sum_comp index (fun i : s => Q.idealUnit i.val)).trans hsum
    rw [hsumF]
    exact P.transportProduct_unit e
  · intro v
    let reindex := LinearEquiv.piCongrLeft' ℝ
      (fun k : s => (k.val : Submodule ℝ V)) index.symm
    let v0 := reindex.symm (fun i => (leaf i).symm (v i))
    change e (D0.symm v0)=∑ i,(v i).val
    rw [hInv0,map_sum]
    rw [← Equiv.sum_comp index (fun k : s => e (v0 k).val)]
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrFun (reindex.apply_symm_apply (fun i => (leaf i).symm (v i))) i
    change v0 (index i)=(leaf i).symm (v i) at hi
    rw [hi]
    exact congrArg Subtype.val ((leaf i).apply_symm_apply (v i))

end AlbertSequential.UnitalJordanProduct
