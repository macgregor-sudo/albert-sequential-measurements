/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FormalRealityCanonicalTrace
public import JordanSquareConeTransport
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Exact real finite-dimensional canonical-trace Riesz representation. All
functional positivity tests actual squares, not a selected set of effects.
No norm is exported on the original algebraic carrier. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

theorem exists_canonicalTraceRepresentative_with_laws (hfr : P.FormallyReal)
    (f : E →ₗ[ℝ] ℝ) :
    ∃ rho : E,
      (∀ x,P.canonicalTraceFormOfFormallyReal hfr rho x=f x) ∧
      (rho∈P.squareCone ↔ ∀ y,0≤f (P.product y y)) ∧
      P.canonicalTraceOfFormallyReal hfr rho=f P.unit := by
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
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z)=B (e x) (e (Q.product y z))
    simpa only [Q,P.transportProduct_apply] using
      P.canonicalTraceFormOfFormallyReal_associative hfr (e x) (e y) (e z)
  let g : V →L[ℝ] ℝ := (f.comp e.toLinearMap).toContinuousLinearMap
  let sigma : V := (InnerProductSpace.toDual ℝ V).symm g
  have hmodel (x : V) : inner ℝ sigma x=f (e x) :=
    InnerProductSpace.toDual_symm_apply (x := x) (y := g)
  have hrepr (x : E) : B (e sigma) x=f x := by
    have h := hmodel (e.symm x)
    change B (e sigma) (e (e.symm x))=f (e (e.symm x)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  refine ⟨e sigma,hrepr,?_,?_⟩
  · constructor
    · intro hrho y
      have hsigma : sigma∈Q.squareCone := (P.transportProduct_squareCone_iff e sigma).mpr hrho
      have ht := (Q.squareCone_self_dual hinnerQ sigma).mp hsigma
        (Q.product (e.symm y) (e.symm y)) ⟨e.symm y,rfl⟩
      rw [hmodel] at ht
      simpa only [Q,P.transportProduct_apply,LinearEquiv.apply_symm_apply] using ht
    · intro hpositive
      apply (P.transportProduct_squareCone_iff e sigma).mp
      apply (Q.squareCone_self_dual hinnerQ sigma).mpr
      rintro z ⟨y,rfl⟩
      rw [hmodel]
      simpa only [Q,P.transportProduct_apply] using hpositive (e y)
  · rw [← P.canonicalTraceFormOfFormallyReal_unit hfr (e sigma)]
    exact hrepr P.unit

def canonicalTraceRepresentative (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ) : E :=
  Classical.choose (P.exists_canonicalTraceRepresentative_with_laws hfr f)

theorem canonicalTraceRepresentative_pairing (hfr : P.FormallyReal)
    (f : E →ₗ[ℝ] ℝ) (x : E) :
    P.canonicalTraceFormOfFormallyReal hfr (P.canonicalTraceRepresentative hfr f) x=f x :=
  (Classical.choose_spec (P.exists_canonicalTraceRepresentative_with_laws hfr f)).1 x

theorem canonicalTraceRepresentative_positive_iff (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ) :
    P.canonicalTraceRepresentative hfr f∈P.squareCone ↔ ∀ y,0≤f (P.product y y) :=
  (Classical.choose_spec (P.exists_canonicalTraceRepresentative_with_laws hfr f)).2.1

theorem canonicalTraceRepresentative_trace (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ) :
    P.canonicalTraceOfFormallyReal hfr (P.canonicalTraceRepresentative hfr f)=f P.unit :=
  (Classical.choose_spec (P.exists_canonicalTraceRepresentative_with_laws hfr f)).2.2

theorem canonicalTraceRepresentative_unique (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ)
    (rho : E) (h : ∀ x,P.canonicalTraceFormOfFormallyReal hfr rho x=f x) :
    rho=P.canonicalTraceRepresentative hfr f := by
  let d := rho-P.canonicalTraceRepresentative hfr f
  have hz : P.canonicalTraceFormOfFormallyReal hfr d d=0 := by
    simp only [d,map_sub,LinearMap.sub_apply,h,P.canonicalTraceRepresentative_pairing,sub_self]
  have hd : d=0 := by
    by_contra hd
    exact (ne_of_gt (P.canonicalTraceFormOfFormallyReal_positive hfr d hd)) hz
  exact sub_eq_zero.mp hd

theorem exists_unique_canonicalTraceRepresentative (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ) :
    ∃! rho : E,∀ x,P.canonicalTraceFormOfFormallyReal hfr rho x=f x :=
  ⟨P.canonicalTraceRepresentative hfr f,P.canonicalTraceRepresentative_pairing hfr f,
    fun rho h => P.canonicalTraceRepresentative_unique hfr f rho h⟩

theorem canonicalTraceRepresentative_add (hfr : P.FormallyReal) (f g : E →ₗ[ℝ] ℝ) :
    P.canonicalTraceRepresentative hfr (f+g)=
      P.canonicalTraceRepresentative hfr f+P.canonicalTraceRepresentative hfr g := by
  symm
  apply P.canonicalTraceRepresentative_unique hfr (f+g)
  intro x
  simp only [map_add,LinearMap.add_apply,P.canonicalTraceRepresentative_pairing]

theorem canonicalTraceRepresentative_smul (hfr : P.FormallyReal) (r : ℝ) (f : E →ₗ[ℝ] ℝ) :
    P.canonicalTraceRepresentative hfr (r • f)=r • P.canonicalTraceRepresentative hfr f := by
  symm
  apply P.canonicalTraceRepresentative_unique hfr (r • f)
  intro x
  simp only [map_smul,LinearMap.smul_apply,P.canonicalTraceRepresentative_pairing]

def canonicalTraceRepresentativeLinear (hfr : P.FormallyReal) : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] E where
  toFun := P.canonicalTraceRepresentative hfr
  map_add' := P.canonicalTraceRepresentative_add hfr
  map_smul' := P.canonicalTraceRepresentative_smul hfr

def canonicalPairingFunctional (hfr : P.FormallyReal) (rho : E) : E →ₗ[ℝ] ℝ :=
  P.canonicalTraceFormOfFormallyReal hfr rho

theorem canonicalTraceRepresentative_pairingFunctional (hfr : P.FormallyReal) (rho : E) :
    P.canonicalTraceRepresentative hfr (P.canonicalPairingFunctional hfr rho)=rho :=
  (P.canonicalTraceRepresentative_unique hfr _ rho (fun _ => rfl)).symm

theorem positiveFunctional_unit_zero (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ)
    (hpositive : ∀ y,0≤f (P.product y y)) (hzero : f P.unit=0) : f=0 := by
  obtain ⟨y,hy⟩ := (P.canonicalTraceRepresentative_positive_iff hfr f).mpr hpositive
  have ht : P.canonicalTraceOfFormallyReal hfr (P.product y y)=0 := by
    rw [← hy,P.canonicalTraceRepresentative_trace,hzero]
  have hy0 : y=0 := by
    by_contra hy0
    exact (ne_of_gt (P.canonicalTraceOfFormallyReal_square_positive hfr y hy0)) ht
  have hrho : P.canonicalTraceRepresentative hfr f=0 := by
    rw [hy,hy0]
    simp
  apply LinearMap.ext
  intro x
  change f x=0
  rw [← P.canonicalTraceRepresentative_pairing hfr f x,hrho]
  simp

def IsCanonicalDensity (hfr : P.FormallyReal) (rho : E) : Prop :=
  rho∈P.squareCone ∧ P.canonicalTraceOfFormallyReal hfr rho=1

theorem normalized_positiveFunctional_density (hfr : P.FormallyReal) (f : E →ₗ[ℝ] ℝ)
    (hpositive : ∀ y,0≤f (P.product y y)) (hnorm : f P.unit=1) :
    P.IsCanonicalDensity hfr (P.canonicalTraceRepresentative hfr f) :=
  ⟨(P.canonicalTraceRepresentative_positive_iff hfr f).mpr hpositive,
    (P.canonicalTraceRepresentative_trace hfr f).trans hnorm⟩

theorem exists_unique_canonicalDensity_representative (hfr : P.FormallyReal)
    (f : E →ₗ[ℝ] ℝ) (hpositive : ∀ y,0≤f (P.product y y)) (hnorm : f P.unit=1) :
    ∃! rho : E,P.IsCanonicalDensity hfr rho ∧
      ∀ x,f x=P.canonicalTraceOfFormallyReal hfr (P.product rho x) := by
  refine ⟨P.canonicalTraceRepresentative hfr f,
    ⟨P.normalized_positiveFunctional_density hfr f hpositive hnorm,?_⟩,?_⟩
  · intro x
    exact (P.canonicalTraceRepresentative_pairing hfr f x).symm
  · intro rho hrho
    apply P.canonicalTraceRepresentative_unique hfr f rho
    intro x
    exact (hrho.2 x).symm

end AlbertSequential.UnitalJordanProduct
