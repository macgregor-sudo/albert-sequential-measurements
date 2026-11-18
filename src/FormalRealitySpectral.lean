/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SquarePositiveFunctional
public import JordanProductTransport
public import JordanGeneratedAlgebra
public import JordanAssociativeSpectral
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Algebraic formal reality yields actual distinct-idempotent spectra.
The separation functional's form is only used associatively on the literal
one-generator algebra. No global associative-inner-form premise is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem exists_square_positive_functional_algebraic (hfr : P.FormallyReal) :
    ∃ f : E →ₗ[ℝ] ℝ, ∀ x : E, x≠0 → 0<f (P.product x x) := by
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : V ≃ₗ[ℝ] E :=
    (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ)).trans
      (Module.finBasis ℝ E).equivFun.symm
  obtain ⟨f,hf⟩ := (P.transportProduct e).exists_square_positive_functional
    (P.transportProduct_formallyReal hfr e)
  refine ⟨f.comp e.symm.toLinearMap,?_⟩
  intro x hx
  have hx' : e.symm x≠0 := fun hz => hx (e.symm.injective (hz.trans (map_zero e.symm).symm))
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,transportProduct,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk] using hf (e.symm x) hx'

def functionalProductForm (f : E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun x := f.comp (P.product x)
  map_add' x y := by
    ext z
    change f (P.product (x+y) z)=f (P.product x z)+f (P.product y z)
    rw [P.product.map_add,LinearMap.add_apply,map_add]
  map_smul' r x := by
    ext y
    change f (P.product (r • x) y)=r • f (P.product x y)
    rw [P.product.map_smul,LinearMap.smul_apply,map_smul]

theorem associative_spectral_resolution_of_positive_form
    (hprod : ∀ x y z, P.product (P.product x y) z=P.product x (P.product y z))
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y=B y x)
    (hpos : ∀ x, x≠0 → 0<B x x)
    (hassoc : ∀ x y z, B (P.product x y) z=B x (P.product y z)) (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ P.product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B hsym hpos
  letI : InnerProductSpace.Core ℝ V := C
  letI : NormedAddCommGroup V := C.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hprodQ (x y z : V) : Q.product (Q.product x y) z=Q.product x (Q.product y z) := by
    apply e.injective
    simpa only [Q,P.transportProduct_apply] using hprod (e x) (e y) (e z)
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z)=B (e x) (e (Q.product y z))
    simpa only [Q,P.transportProduct_apply] using hassoc (e x) (e y) (e z)
  exact P.spectral_resolution_transport e a
    (Q.associative_spectral_resolution hprodQ hinnerQ (e.symm a))

theorem spectral_resolution_of_formallyReal (hfr : P.FormallyReal) (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ P.product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  obtain ⟨f,hf⟩ := P.exists_square_positive_functional_algebraic hfr
  let W := P.powerSpan a
  let Q := P.powerSpanProduct a
  let g : W →ₗ[ℝ] ℝ := f.comp W.subtype
  let B := Q.functionalProductForm g
  have hsym (x y : W) : B x y=B y x :=
    congrArg g (Q.commutative x y)
  have hpos (x : W) (hx : x≠0) : 0<B x x := by
    exact hf x.val (fun hz => hx (Subtype.ext hz))
  have hassoc (x y z : W) : B (Q.product x y) z=B x (Q.product y z) :=
    congrArg g (P.powerSpanProduct_associative a x y z)
  obtain ⟨n,lam,c,hlam,hc,ho,hs,ha⟩ :=
    Q.associative_spectral_resolution_of_positive_form
      (P.powerSpanProduct_associative a) B hsym hpos hassoc
      ⟨a,P.generator_mem_powerSpan a⟩
  refine ⟨n,lam,fun i => (c i).val,hlam,?_,?_,?_,?_⟩
  · intro i
    exact ⟨fun hz => (hc i).1 (Subtype.ext hz),congrArg Subtype.val (hc i).2⟩
  · intro i j hij
    exact congrArg Subtype.val (ho i j hij)
  · simpa only [map_sum,Submodule.subtype_apply,Q,P.powerSpanProduct_unit] using
      congrArg (P.powerSpan a).subtype hs
  · simpa only [map_sum,map_smul,RingHom.id_apply,Submodule.subtype_apply] using
      congrArg (P.powerSpan a).subtype ha

end AlbertSequential.UnitalJordanProduct
