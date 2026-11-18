/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanNormalizedTrace
public import JordanPrimitiveTransport
public import FormalRealityPositiveForm

/-! Canonical primitive-normalized trace under exactly the original algebraic
finite-sum formal-reality assumptions. The positive-form carrier is isolated;
all products, primitivity and quadratic maps are transported. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

theorem primitive_spectral_resolution_of_positive_form
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsym : ∀ x y,B x y=B y x)
    (hpos : ∀ x,x≠0 → 0<B x x)
    (hassoc : ∀ x y z,B (P.product x y) z=B x (P.product y z)) (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E),
      (∀ i,P.IsPrimitive (c i)) ∧
      (∀ i j,i≠j → P.product (c i) (c j)=0) ∧
      (∑ i,c i)=P.unit ∧ a=∑ i,lam i • c i := by
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B hsym hpos
  letI : InnerProductSpace.Core ℝ V := C
  letI : NormedAddCommGroup V := C.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z)=B (e x) (e (Q.product y z))
    simpa only [Q,P.transportProduct_apply] using hassoc (e x) (e y) (e z)
  obtain ⟨n,lam,c,hc,ho,hs,ha⟩ := Q.primitive_spectral_resolution hinnerQ (e.symm a)
  refine ⟨n,lam,fun i => e (c i),?_,?_,?_,?_⟩
  · intro i
    exact (P.transportProduct_isPrimitive_iff e (c i)).mp (hc i)
  · intro i j hij
    simpa only [Q,P.transportProduct_apply,map_zero] using congrArg e (ho i j hij)
  · simpa only [map_sum,Q,P.transportProduct_unit] using congrArg e hs
  · simpa only [map_sum,map_smul,RingHom.id_apply,LinearEquiv.apply_symm_apply] using congrArg e ha

theorem primitive_spectral_resolution_of_formallyReal
    (hfr : P.FormallyReal) (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E),
      (∀ i,P.IsPrimitive (c i)) ∧
      (∀ i j,i≠j → P.product (c i) (c j)=0) ∧
      (∑ i,c i)=P.unit ∧ a=∑ i,lam i • c i :=
  P.primitive_spectral_resolution_of_positive_form P.regularTraceForm
    P.regularTraceForm_symmetric (P.regularTraceForm_positive_of_formallyReal hfr)
    P.regularTraceForm_associative a

theorem exists_normalized_trace_with_laws_of_positive_form
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsym : ∀ x y,B x y=B y x)
    (hpos : ∀ x,x≠0 → 0<B x x)
    (hassoc : ∀ x y z,B (P.product x y) z=B x (P.product y z)) :
    ∃ tau : E →ₗ[ℝ] ℝ,
      (∀ q,P.IsPrimitive q → tau q=1) ∧
      (∀ x y z,tau (P.product (P.product x y) z)=tau (P.product x (P.product y z))) ∧
      (∀ x,x≠0 → 0<tau (P.product x x)) ∧
      (∀ q x,P.IsPrimitive q → P.quadraticRepresentation q x=tau (P.product q x) • q) := by
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B hsym hpos
  letI : InnerProductSpace.Core ℝ V := C
  letI : NormedAddCommGroup V := C.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z)=B (e x) (e (Q.product y z))
    simpa only [Q,P.transportProduct_apply] using hassoc (e x) (e y) (e z)
  obtain ⟨sigma,hnorm,ha,hpositive,hcompression⟩ := Q.exists_normalized_trace_with_laws hinnerQ
  let tau := sigma.comp e.symm.toLinearMap
  have hprim (q : E) (hq : P.IsPrimitive q) : Q.IsPrimitive (e.symm q) :=
    (P.transportProduct_isPrimitive_iff e (e.symm q)).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hq)
  refine ⟨tau,?_,?_,?_,?_⟩
  · intro q hq
    exact hnorm _ (hprim q hq)
  · intro x y z
    have h := ha (e.symm x) (e.symm y) (e.symm z)
    simpa only [tau,LinearMap.comp_apply,LinearEquiv.coe_coe,Q,P.transportProduct_inverse_apply] using h
  · intro x hx
    have hx' : e.symm x≠0 := fun hz => hx (e.symm.injective (hz.trans (map_zero e.symm).symm))
    have h := hpositive (e.symm x) hx'
    simpa only [tau,LinearMap.comp_apply,LinearEquiv.coe_coe,Q,P.transportProduct_inverse_apply] using h
  · intro q x hq
    have h := congrArg e (hcompression (e.symm q) (e.symm x) (hprim q hq))
    simpa only [tau,LinearMap.comp_apply,LinearEquiv.coe_coe,Q,P.transportProduct_quadraticRepresentation,LinearEquiv.apply_symm_apply,
      map_smul,RingHom.id_apply,P.transportProduct_inverse_apply] using h

theorem exists_normalized_trace_with_laws_of_formallyReal (hfr : P.FormallyReal) :
    ∃ tau : E →ₗ[ℝ] ℝ,
      (∀ q,P.IsPrimitive q → tau q=1) ∧
      (∀ x y z,tau (P.product (P.product x y) z)=tau (P.product x (P.product y z))) ∧
      (∀ x,x≠0 → 0<tau (P.product x x)) ∧
      (∀ q x,P.IsPrimitive q → P.quadraticRepresentation q x=tau (P.product q x) • q) :=
  P.exists_normalized_trace_with_laws_of_positive_form P.regularTraceForm
    P.regularTraceForm_symmetric (P.regularTraceForm_positive_of_formallyReal hfr)
    P.regularTraceForm_associative

theorem normalized_trace_unique_of_formallyReal (hfr : P.FormallyReal)
    (tau sigma : E →ₗ[ℝ] ℝ) (htau : ∀ q,P.IsPrimitive q → tau q=1)
    (hsigma : ∀ q,P.IsPrimitive q → sigma q=1) : tau=sigma := by
  ext x
  obtain ⟨n,lam,c,hc,_,_,hx⟩ := P.primitive_spectral_resolution_of_formallyReal hfr x
  rw [hx,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul,htau _ (hc i),hsigma _ (hc i)]

theorem existsUnique_primitiveNormalizedTrace_of_formallyReal (hfr : P.FormallyReal) :
    ∃! tau : E →ₗ[ℝ] ℝ,∀ q,P.IsPrimitive q → tau q=1 := by
  obtain ⟨tau,htau,_⟩ := P.exists_normalized_trace_with_laws_of_formallyReal hfr
  exact ⟨tau,htau,fun sigma hsigma => P.normalized_trace_unique_of_formallyReal hfr sigma tau hsigma htau⟩

/-- Canonical trace with only the original finite-sum formal-reality premise. -/
def canonicalTraceOfFormallyReal (hfr : P.FormallyReal) : E →ₗ[ℝ] ℝ :=
  Classical.choose (P.exists_normalized_trace_with_laws_of_formallyReal hfr)

theorem canonicalTraceOfFormallyReal_primitive (hfr : P.FormallyReal)
    (q : E) (hq : P.IsPrimitive q) : P.canonicalTraceOfFormallyReal hfr q=1 :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws_of_formallyReal hfr)).1 q hq

theorem canonicalTraceOfFormallyReal_associative (hfr : P.FormallyReal)
    (x y z : E) : P.canonicalTraceOfFormallyReal hfr (P.product (P.product x y) z)=
      P.canonicalTraceOfFormallyReal hfr (P.product x (P.product y z)) :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws_of_formallyReal hfr)).2.1 x y z

theorem canonicalTraceOfFormallyReal_square_positive (hfr : P.FormallyReal)
    (x : E) (hx : x≠0) : 0<P.canonicalTraceOfFormallyReal hfr (P.product x x) :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws_of_formallyReal hfr)).2.2.1 x hx

theorem canonicalTraceOfFormallyReal_primitive_compression (hfr : P.FormallyReal)
    (q x : E) (hq : P.IsPrimitive q) :
    P.quadraticRepresentation q x=P.canonicalTraceOfFormallyReal hfr (P.product q x) • q :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws_of_formallyReal hfr)).2.2.2 q x hq

def canonicalTraceFormOfFormallyReal (hfr : P.FormallyReal) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  P.functionalProductForm (P.canonicalTraceOfFormallyReal hfr)

@[simp] theorem canonicalTraceFormOfFormallyReal_apply (hfr : P.FormallyReal) (x y : E) :
    P.canonicalTraceFormOfFormallyReal hfr x y=P.canonicalTraceOfFormallyReal hfr (P.product x y) := rfl

theorem canonicalTraceFormOfFormallyReal_symmetric (hfr : P.FormallyReal) (x y : E) :
    P.canonicalTraceFormOfFormallyReal hfr x y=P.canonicalTraceFormOfFormallyReal hfr y x := by
  simp only [P.canonicalTraceFormOfFormallyReal_apply,P.commutative x y]

theorem canonicalTraceFormOfFormallyReal_associative (hfr : P.FormallyReal) (x y z : E) :
    P.canonicalTraceFormOfFormallyReal hfr (P.product x y) z=
      P.canonicalTraceFormOfFormallyReal hfr x (P.product y z) :=
  P.canonicalTraceOfFormallyReal_associative hfr x y z

theorem canonicalTraceFormOfFormallyReal_positive (hfr : P.FormallyReal) (x : E) (hx : x≠0) :
    0<P.canonicalTraceFormOfFormallyReal hfr x x :=
  P.canonicalTraceOfFormallyReal_square_positive hfr x hx

theorem canonicalTraceFormOfFormallyReal_unit (hfr : P.FormallyReal) (x : E) :
    P.canonicalTraceFormOfFormallyReal hfr x P.unit=P.canonicalTraceOfFormallyReal hfr x := by
  rw [P.canonicalTraceFormOfFormallyReal_apply,P.commutative x P.unit,P.unit_left]

theorem canonicalTraceFormOfFormallyReal_primitive_norm (hfr : P.FormallyReal)
    (q : E) (hq : P.IsPrimitive q) : P.canonicalTraceFormOfFormallyReal hfr q q=1 := by
  rw [P.canonicalTraceFormOfFormallyReal_apply,hq.1,
    P.canonicalTraceOfFormallyReal_primitive hfr q hq]

end AlbertSequential.UnitalJordanProduct
