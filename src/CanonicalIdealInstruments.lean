/- SPDX-License-Identifier: Apache-2.0 -/
module
public import IdealJordanInstruments
public import JordanStateRiesz

/-!
# Ideal tests on a finite formally real Jordan algebra

The measured effect is the Riesz representative for the canonical Jordan
trace form. A positive-form copy of the carrier connects the operational
conditions to the finite-dimensional Lüders classification.

This file consolidates the five original owner-directed production modules
from the 2026-11-17 formal-reality-bridge producer return.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.CanonicalInstruments

section Definitions

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "B" => P.canonicalTraceFormOfFormallyReal hfr

def IsEffect (f : E) : Prop := f∈P.squareCone ∧ P.unit-f∈P.squareCone

/-- The Riesz representative of the trace after applying the yes map. -/
def measuredEffect (T : E→ₗ[ℝ]E) : E :=
  P.canonicalTraceRepresentative hfr ((τ).comp T)

def IsIdeal (T1 T0 : E→ₗ[ℝ]E) (a : E) : Prop :=
  (∀ ρ,P.IsCanonicalDensity hfr ρ → B ρ a=1 → T1 ρ=ρ) ∧
  (∀ ρ,P.IsCanonicalDensity hfr ρ → B ρ a=0 → T0 ρ=ρ)

def IsSharpEffect (a : E) : Prop :=
  ¬ ∃ σ f,P.IsCanonicalDensity hfr σ ∧ IsEffect P f ∧ B σ f=1 ∧
    ∀ ρ,P.IsCanonicalDensity hfr ρ → (B ρ a=0 ∨ B ρ a=1) → B ρ f=0

/-- The ideality and sharpness conditions of Definition 3.2 for a finite instrument. -/
def IsIdealTest (T1 T0 : E →ₗ[ℝ] E) : Prop :=
  let a := measuredEffect P hfr T1
  IsIdeal P hfr T1 T0 a ∧ IsSharpEffect P hfr a

include hfr

theorem measuredEffect_calibration (T : E→ₗ[ℝ]E) (x : E) :
    τ (T x)=B x (measuredEffect P hfr T) := by
  have h := P.canonicalTraceRepresentative_pairing hfr ((τ).comp T) x
  change τ (P.product (measuredEffect P hfr T) x)=τ (T x) at h
  change τ (T x)=τ (P.product x (measuredEffect P hfr T))
  rw [P.commutative]
  exact h.symm

theorem measuredEffect_unique (T : E→ₗ[ℝ]E) (a : E)
    (ha : ∀ x,τ (T x)=B x a) : a=measuredEffect P hfr T := by
  apply P.canonicalTraceRepresentative_unique hfr ((τ).comp T) a
  intro x
  rw [P.canonicalTraceFormOfFormallyReal_symmetric]
  exact (ha x).symm

theorem existsUnique_measuredEffect (T : E→ₗ[ℝ]E) :
    ∃! a : E,∀ x,τ (T x)=B x a :=
  ⟨measuredEffect P hfr T,measuredEffect_calibration P hfr T,
    fun a ha => measuredEffect_unique P hfr T a ha⟩

theorem trace_nonnegative_on_squareCone (x : E) (hx : x∈P.squareCone) : 0≤τ x := by
  obtain ⟨y,rfl⟩ := hx
  by_cases hy : y=0
  · simp [hy]
  · exact (P.canonicalTraceOfFormallyReal_square_positive hfr y hy).le

theorem measuredEffect_positive (T : E→ₗ[ℝ]E)
    (hpos : ∀ x∈P.squareCone,T x∈P.squareCone) : measuredEffect P hfr T∈P.squareCone := by
  apply (P.canonicalTraceRepresentative_positive_iff hfr ((τ).comp T)).mpr
  intro y
  exact trace_nonnegative_on_squareCone P hfr _ (hpos _ ⟨y,rfl⟩)

theorem measuredEffects_sum_unit (T1 T0 : E→ₗ[ℝ]E)
    (hn : ∀ x,τ (T1 x+T0 x)=τ x) :
    measuredEffect P hfr T1+measuredEffect P hfr T0=P.unit := by
  have hfun : (τ).comp T1+(τ).comp T0=τ := by
    ext x
    change τ (T1 x)+τ (T0 x)=τ x
    simpa only [map_add] using hn x
  change P.canonicalTraceRepresentative hfr ((τ).comp T1)+
    P.canonicalTraceRepresentative hfr ((τ).comp T0)=P.unit
  rw [← P.canonicalTraceRepresentative_add,hfun]
  symm
  apply P.canonicalTraceRepresentative_unique hfr τ P.unit
  intro x
  change τ (P.product P.unit x)=τ x
  rw [P.unit_left]

theorem measuredEffect_isEffect (T1 T0 : E→ₗ[ℝ]E)
    (h1 : ∀ x∈P.squareCone,T1 x∈P.squareCone)
    (h0 : ∀ x∈P.squareCone,T0 x∈P.squareCone)
    (hn : ∀ x,τ (T1 x+T0 x)=τ x) : IsEffect P (measuredEffect P hfr T1) := by
  refine ⟨measuredEffect_positive P hfr T1 h1,?_⟩
  have hs := measuredEffects_sum_unit P hfr T1 T0 hn
  have he : P.unit-measuredEffect P hfr T1=measuredEffect P hfr T0 := by rw [← hs]; abel
  rw [he]
  exact measuredEffect_positive P hfr T0 h0

theorem trace_quadratic_idempotent (p x : E) (hp : P.product p p=p) :
    τ (P.quadraticRepresentation p x)=B x p := by
  rw [P.quadraticRepresentation_apply,map_sub,map_smul]
  change (2 : ℝ)*τ (P.product p (P.product p x))-
    τ (P.product (P.product p p) x)=τ (P.product x p)
  rw [← P.canonicalTraceOfFormallyReal_associative hfr p p x]
  simp only [hp]
  rw [P.commutative p x]
  ring

theorem measuredEffect_of_quadraticRepresentation (p : E) (hp : P.product p p=p) :
    measuredEffect P hfr (P.quadraticRepresentation p)=p := by
  symm
  apply measuredEffect_unique P hfr
  intro x
  exact trace_quadratic_idempotent P hfr p x hp

end Definitions

section TransportMaps

section Linear
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def pullbackMap (e : F≃ₗ[ℝ]E) (T : E→ₗ[ℝ]E) : F→ₗ[ℝ]F :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

@[simp] theorem map_pullbackMap (e : F≃ₗ[ℝ]E) (T : E→ₗ[ℝ]E) (x : F) :
    e (pullbackMap e T x)=T (e x) := e.apply_symm_apply _

theorem pullbackMap_injective (e : F≃ₗ[ℝ]E) : Function.Injective (pullbackMap e) := by
  intro T S h
  ext x
  have hx := congrArg (fun L : F→ₗ[ℝ]F => e (L (e.symm x))) h
  simpa only [map_pullbackMap,LinearEquiv.apply_symm_apply] using hx

theorem pullbackMap_quadratic (P : UnitalJordanProduct E) (e : F≃ₗ[ℝ]E) (p : E) :
    pullbackMap e (P.quadraticRepresentation p)=
      (P.transportProduct e).quadraticRepresentation (e.symm p) := by
  ext x
  apply e.injective
  rw [map_pullbackMap,P.transportProduct_quadraticRepresentation,LinearEquiv.apply_symm_apply]

end Linear
section Transport
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (e : F≃ₗ[ℝ]E)
  (hB : ∀ x y : F,inner ℝ x y=P.canonicalTraceFormOfFormallyReal hfr (e x) (e y))
local notation "Q" => P.transportProduct e
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "B" => P.canonicalTraceFormOfFormallyReal hfr
include hfr hB

omit [FiniteDimensional ℝ F] in
theorem inner_associative_transport (x y z : F) :
    inner ℝ ((Q).product x y) z=inner ℝ x ((Q).product y z) := by
  rw [hB,hB,P.transportProduct_apply,P.transportProduct_apply]
  exact P.canonicalTraceFormOfFormallyReal_associative hfr (e x) (e y) (e z)

omit [FiniteDimensional ℝ F] in
theorem trace_transport (x : F) : PositiveInstruments.trace Q x=τ (e x) := by
  change inner ℝ x (Q).unit=τ (e x)
  rw [hB,P.transportProduct_unit,P.canonicalTraceFormOfFormallyReal_unit]

omit [FiniteDimensional ℝ F] in
theorem density_transport (x : F) :
    PositiveInstruments.IsDensity Q x ↔ P.IsCanonicalDensity hfr (e x) := by
  change (x∈(Q).squareCone ∧ PositiveInstruments.trace Q x=1) ↔
    (e x∈P.squareCone ∧ τ (e x)=1)
  rw [P.transportProduct_squareCone_iff,trace_transport P hfr e hB]

omit hfr hB [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem effect_transport (x : F) :
    PositiveInstruments.IsEffect Q x ↔ IsEffect P (e x) := by
  change (x∈(Q).squareCone ∧ (Q).unit-x∈(Q).squareCone) ↔
    (e x∈P.squareCone ∧ P.unit-e x∈P.squareCone)
  rw [P.transportProduct_squareCone_iff,P.transportProduct_squareCone_iff,
    map_sub,P.transportProduct_unit]

/-- Actual conjugated positive normalized instrument, not an assumed
simulation/transport contract. -/
def transportedInstrument (T1 T0 : E→ₗ[ℝ]E)
    (h1 : ∀ x∈P.squareCone,T1 x∈P.squareCone)
    (h0 : ∀ x∈P.squareCone,T0 x∈P.squareCone)
    (hn : ∀ x,τ (T1 x+T0 x)=τ x) : PositiveInstruments.PositiveBinaryInstrument Q where
  yes := pullbackMap e T1
  no := pullbackMap e T0
  yes_positive := by
    intro x hx
    apply (P.transportProduct_squareCone_iff e _).mpr
    rw [map_pullbackMap]
    exact h1 (e x) ((P.transportProduct_squareCone_iff e x).mp hx)
  no_positive := by
    intro x hx
    apply (P.transportProduct_squareCone_iff e _).mpr
    rw [map_pullbackMap]
    exact h0 (e x) ((P.transportProduct_squareCone_iff e x).mp hx)
  normalized := by
    intro x
    rw [PositiveInstruments.trace_add]
    simp only [trace_transport P hfr e hB,map_pullbackMap]
    simpa only [map_add] using hn (e x)

theorem measuredEffect_transport (r : PositiveInstruments.PositiveBinaryInstrument Q)
    (T : E→ₗ[ℝ]E) (hT : ∀ x,e (r.yes x)=T (e x)) :
    e (PositiveInstruments.measuredEffect Q r)=measuredEffect P hfr T := by
  apply measuredEffect_unique P hfr T
  intro x
  have h := PositiveInstruments.measuredEffect_pairing Q r (e.symm x)
  rw [hB,trace_transport P hfr e hB] at h
  simpa only [LinearEquiv.apply_symm_apply,hT] using h.symm

end Transport

end TransportMaps

section TransportIdeality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (e : F≃ₗ[ℝ]E)
  (hB : ∀ x y : F,inner ℝ x y=P.canonicalTraceFormOfFormallyReal hfr (e x) (e y))
local notation "Q" => P.transportProduct e
include hfr hB

theorem ideality_transport (r : PositiveInstruments.PositiveBinaryInstrument Q)
    (T1 T0 : E→ₗ[ℝ]E) (h1 : ∀ x,e (r.yes x)=T1 (e x))
    (h0 : ∀ x,e (r.no x)=T0 (e x)) :
    PositiveInstruments.IsIdeal Q r ↔
      IsIdeal P hfr T1 T0 (e (PositiveInstruments.measuredEffect Q r)) := by
  simp only [PositiveInstruments.IsIdeal,IsIdeal,e.surjective.forall,
    ← density_transport P hfr e hB,← hB,← h1,← h0,e.injective.eq_iff]

omit [FiniteDimensional ℝ F] in
theorem sharpness_transport (a : F) :
    PositiveInstruments.IsSharpEffect Q a ↔ IsSharpEffect P hfr (e a) := by
  simp only [PositiveInstruments.IsSharpEffect,IsSharpEffect,e.surjective.exists,
    e.surjective.forall,← density_transport P hfr e hB,← effect_transport P e,← hB]

theorem idealTest_transport (r : PositiveInstruments.PositiveBinaryInstrument Q)
    (T1 T0 : E→ₗ[ℝ]E) (h1 : ∀ x,e (r.yes x)=T1 (e x))
    (h0 : ∀ x,e (r.no x)=T0 (e x)) :
    (PositiveInstruments.IsIdeal Q r ∧
      PositiveInstruments.IsSharpEffect Q (PositiveInstruments.measuredEffect Q r)) ↔
    (IsIdeal P hfr T1 T0 (measuredEffect P hfr T1) ∧
      IsSharpEffect P hfr (measuredEffect P hfr T1)) := by
  rw [← measuredEffect_transport P hfr e hB r T1 h1]
  exact and_congr (ideality_transport P hfr e hB r T1 T0 h1 h0)
    (sharpness_transport P hfr e hB (PositiveInstruments.measuredEffect Q r))

end TransportIdeality

section QuadraticPositivity

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
include hfr

omit hfr [FiniteDimensional ℝ E] in
theorem complementary_idempotent (p : E) (hp : P.product p p=p) :
    P.product (P.unit-p) (P.unit-p)=P.unit-p := by
  have hu (x : E) : P.product x P.unit=x := by rw [P.commutative,P.unit_left]
  simp only [map_sub,LinearMap.sub_apply,P.unit_left,hu,hp]
  abel

theorem quadraticRepresentation_preserves_squareCone (a x : E) (hx : x∈P.squareCone) :
    P.quadraticRepresentation a x∈P.squareCone := by
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E
    (P.canonicalTraceFormOfFormallyReal hfr)
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr)
    (P.canonicalTraceFormOfFormallyReal_positive hfr)
  let _ : InnerProductSpace.Core ℝ V := C
  let _ : NormedAddCommGroup V := C.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V≃ₗ[ℝ]E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hB (u v : V) : inner ℝ u v=P.canonicalTraceFormOfFormallyReal hfr (e u) (e v) := rfl
  have hinner (u v w : V) : inner ℝ (Q.product u v) w=inner ℝ u (Q.product v w) :=
    inner_associative_transport P hfr e hB u v w
  have hx' : e.symm x∈Q.squareCone := (P.transportProduct_squareCone_iff e _).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hx)
  have hpos := UnitalJordanProduct.quadraticRepresentation_preserves_squareCone Q hinner (e.symm a) (e.symm x) hx'
  have h := (P.transportProduct_squareCone_iff e _).mp hpos
  simpa only [Q,P.transportProduct_quadraticRepresentation,LinearEquiv.apply_symm_apply] using h

theorem quadratic_pair_normalized (p : E) (hp : P.product p p=p) (x : E) :
    τ (P.quadraticRepresentation p x+P.quadraticRepresentation (P.unit-p) x)=τ x := by
  rw [map_add,trace_quadratic_idempotent P hfr p x hp,
    trace_quadratic_idempotent P hfr (P.unit-p) x (complementary_idempotent P p hp),
    map_sub,P.canonicalTraceFormOfFormallyReal_unit]
  ring

end QuadraticPositivity

section Classification

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
include hfr

/-- The finite Euclidean Jordan algebra case of Theorem 3.3. -/
theorem idealTest_iff_quadraticRepresentation (T1 T0 : E→ₗ[ℝ]E)
    (h1 : ∀ x∈P.squareCone,T1 x∈P.squareCone)
    (h0 : ∀ x∈P.squareCone,T0 x∈P.squareCone)
    (hn : ∀ x,τ (T1 x+T0 x)=τ x) :
    IsIdealTest P hfr T1 T0 ↔
    ∃ p : E,P.product p p=p ∧ measuredEffect P hfr T1=p ∧
      T1=P.quadraticRepresentation p ∧ T0=P.quadraticRepresentation (P.unit-p) := by
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E
    (P.canonicalTraceFormOfFormallyReal hfr)
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr)
    (P.canonicalTraceFormOfFormallyReal_positive hfr)
  let _ : InnerProductSpace.Core ℝ V := C
  let _ : NormedAddCommGroup V := C.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V≃ₗ[ℝ]E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hB (x y : V) : inner ℝ x y=P.canonicalTraceFormOfFormallyReal hfr (e x) (e y) := rfl
  have hinner (x y z : V) : inner ℝ (Q.product x y) z=inner ℝ x (Q.product y z) :=
    inner_associative_transport P hfr e hB x y z
  let r := transportedInstrument P hfr e hB T1 T0 h1 h0 hn
  have hy (x : V) : e (r.yes x)=T1 (e x) := map_pullbackMap e T1 x
  have hz (x : V) : e (r.no x)=T0 (e x) := map_pullbackMap e T0 x
  have hlogical := idealTest_transport P hfr e hB r T1 T0 hy hz
  have hclassifier := PositiveInstruments.idealTest_iff_quadraticRepresentation Q hinner r
  constructor
  · intro hnativ
    obtain ⟨q,hq,hyq,hzq⟩ := hclassifier.mp (hlogical.mpr hnativ)
    have hp : P.product (e q) (e q)=e q := by
      simpa only [Q,P.transportProduct_apply] using congrArg e hq
    have hyraw : T1=P.quadraticRepresentation (e q) := by
      apply pullbackMap_injective e
      change r.yes=pullbackMap e (P.quadraticRepresentation (e q))
      rw [pullbackMap_quadratic,LinearEquiv.symm_apply_apply]
      exact hyq
    have hzraw : T0=P.quadraticRepresentation (P.unit-e q) := by
      apply pullbackMap_injective e
      change r.no=pullbackMap e (P.quadraticRepresentation (P.unit-e q))
      rw [pullbackMap_quadratic,map_sub,LinearEquiv.symm_apply_apply]
      exact hzq
    refine ⟨e q,hp,?_,hyraw,hzraw⟩
    rw [hyraw]
    exact measuredEffect_of_quadraticRepresentation P hfr (e q) hp
  · rintro ⟨p,hp,_,hyraw,hzraw⟩
    have hq : Q.product (e.symm p) (e.symm p)=e.symm p := by
      apply e.injective
      rw [P.transportProduct_apply,LinearEquiv.apply_symm_apply,hp]
    have hyq : r.yes=Q.quadraticRepresentation (e.symm p) := by
      change pullbackMap e T1=Q.quadraticRepresentation (e.symm p)
      rw [hyraw,pullbackMap_quadratic]
    have hzq : r.no=Q.quadraticRepresentation (Q.unit-e.symm p) := by
      change pullbackMap e T0=Q.quadraticRepresentation (Q.unit-e.symm p)
      rw [hzraw,pullbackMap_quadratic,map_sub]
      rfl
    exact hlogical.mp (hclassifier.mpr ⟨e.symm p,hq,hyq,hzq⟩)

/-- A calibrated presentation determines the measured effect by Riesz uniqueness. -/
theorem idealTest_iff_quadraticRepresentation_of_calibration (T1 T0 : E→ₗ[ℝ]E)
    (h1 : ∀ x∈P.squareCone,T1 x∈P.squareCone)
    (h0 : ∀ x∈P.squareCone,T0 x∈P.squareCone)
    (hn : ∀ x,τ (T1 x+T0 x)=τ x) (a : E)
    (ha : ∀ x,τ (T1 x)=P.canonicalTraceFormOfFormallyReal hfr x a) :
    (IsIdeal P hfr T1 T0 a ∧ IsSharpEffect P hfr a) ↔
    ∃ p : E,P.product p p=p ∧ a=p ∧
      T1=P.quadraticRepresentation p ∧ T0=P.quadraticRepresentation (P.unit-p) := by
  rw [measuredEffect_unique P hfr T1 a ha]
  exact idealTest_iff_quadraticRepresentation P hfr T1 T0 h1 h0 hn

/-- Quadratic maps for an idempotent and its complement give an ideal test. -/
theorem quadratic_pair_isIdealTest (p : E) (hp : P.product p p=p) :
    IsIdealTest P hfr (P.quadraticRepresentation p) (P.quadraticRepresentation (P.unit-p)) := by
  apply (idealTest_iff_quadraticRepresentation P hfr _ _
    (quadraticRepresentation_preserves_squareCone P hfr p)
    (quadraticRepresentation_preserves_squareCone P hfr (P.unit-p))
    (quadratic_pair_normalized P hfr p hp)).mpr
  exact ⟨p,hp,measuredEffect_of_quadraticRepresentation P hfr p hp,rfl,rfl⟩

end Classification

end AlbertSequential.CanonicalInstruments
