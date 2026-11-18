/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanPeircePositiveMultiplication
public import Mathlib.LinearAlgebra.Trace

/-! Actual regular trace of ordinary finite-dimensional Jordan product data.
No norm/inner product, formal reality or spectral premise is assumed. Full
positive definiteness and canonical primitive-normalized trace are separate. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- The ordinary associative-operator commutator of actual product maps. -/
def innerDerivation (a b : E) : E →ₗ[ℝ] E :=
  (P.product a).comp (P.product b)-(P.product b).comp (P.product a)

@[simp] theorem innerDerivation_apply (a b x : E) :
    P.innerDerivation a b x=P.product a (P.product b x)-P.product b (P.product a x) := rfl

theorem innerDerivation_product (a b x y : E) :
    P.innerDerivation a b (P.product x y)=
      P.product (P.innerDerivation a b x) y+P.product x (P.innerDerivation a b y) := by
  exact congrArg Element.value (RealJordan.innerDerivation_mul
    (Element.mk a : P.Element) (Element.mk b) (Element.mk x) (Element.mk y))

theorem innerDerivation_product_commutator (a b z : E) :
    P.product (P.innerDerivation a b z)=
      (P.innerDerivation a b)*(P.product z)-(P.product z)*(P.innerDerivation a b) := by
  ext x
  change P.product (P.innerDerivation a b z) x=
    P.innerDerivation a b (P.product z x)-P.product z (P.innerDerivation a b x)
  rw [P.innerDerivation_product]
  abel

/-- Regular trace is operator trace of L_x; no primitive normalization. -/
def regularTrace : E →ₗ[ℝ] ℝ := (LinearMap.trace ℝ E).comp P.product

@[simp] theorem regularTrace_apply (x : E) :
    P.regularTrace x=LinearMap.trace ℝ E (P.product x) := rfl

def regularTraceForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun x := P.regularTrace.comp (P.product x)
  map_add' x y := by
    ext z
    change P.regularTrace (P.product (x+y) z)=P.regularTrace (P.product x z)+P.regularTrace (P.product y z)
    rw [P.product.map_add,LinearMap.add_apply,map_add]
  map_smul' r x := by
    ext z
    change P.regularTrace (P.product (r • x) z)=r • P.regularTrace (P.product x z)
    rw [P.product.map_smul,LinearMap.smul_apply,map_smul]

@[simp] theorem regularTraceForm_apply (x y : E) :
    P.regularTraceForm x y=P.regularTrace (P.product x y) := rfl

theorem regularTrace_innerDerivation_zero (a b z : E) :
    P.regularTrace (P.innerDerivation a b z)=0 := by
  rw [P.regularTrace_apply,P.innerDerivation_product_commutator]
  simpa only [Ring.lie_def] using LinearMap.trace_lie (P.innerDerivation a b) (P.product z)

theorem regularTraceForm_symmetric (x y : E) :
    P.regularTraceForm x y=P.regularTraceForm y x := by
  simp only [P.regularTraceForm_apply,P.commutative x y]

theorem regularTraceForm_associative (x y z : E) :
    P.regularTraceForm (P.product x y) z=P.regularTraceForm x (P.product y z) := by
  have h := P.regularTrace_innerDerivation_zero z x y
  rw [P.innerDerivation_apply,map_sub,P.commutative z (P.product x y),
    P.commutative z y] at h
  exact sub_eq_zero.mp h

theorem regularTraceForm_unit (x : E) :
    P.regularTraceForm x P.unit=P.regularTrace x := by
  rw [P.regularTraceForm_apply,P.commutative x P.unit,P.unit_left]

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

omit [FiniteDimensional ℝ E] in
theorem quadraticRepresentation_isIdempotent (q : E) (hq : P.product q q=q) :
    IsIdempotentElem (P.quadraticRepresentation q) := by
  ext x
  exact P.quadraticRepresentation_idempotent_apply q x hq

omit [FiniteDimensional ℝ E] in
theorem peirceHalfProjection_isIdempotent (q : E) (hq : P.product q q=q) :
    IsIdempotentElem (P.peirceHalfProjection q) := by
  ext x
  exact P.peirceHalfProjection_idempotent q x hq

/-- Exact algebraic rank formula, with no inner-product premise. -/
theorem regularTrace_idempotent_formula (q : E) (hq : P.product q q=q) :
    P.regularTrace q=
      (Module.finrank ℝ (LinearMap.range (P.quadraticRepresentation q)) : ℝ)+
        (1/2 : ℝ)*(Module.finrank ℝ (LinearMap.range (P.peirceHalfProjection q)) : ℝ) := by
  have hQ := P.quadraticRepresentation_isIdempotent q hq
  have hH := P.peirceHalfProjection_isIdempotent q hq
  have hL : P.product q=P.quadraticRepresentation q+(1/2 : ℝ) • P.peirceHalfProjection q := by
    ext z
    exact P.leftMultiplication_projection_decomposition q z hq
  rw [P.regularTrace_apply,hL,map_add,map_smul,(LinearMap.IsIdempotentElem.isProj_range (P.quadraticRepresentation q) hQ).trace,(LinearMap.IsIdempotentElem.isProj_range (P.peirceHalfProjection q) hH).trace]
  rfl

theorem regularTrace_idempotent_nonnegative (q : E) (hq : P.product q q=q) :
    0≤P.regularTrace q := by
  rw [P.regularTrace_idempotent_formula q hq]
  exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem regularTrace_idempotent_positive (q : E) (hq : P.product q q=q) (hne : q≠0) :
    0<P.regularTrace q := by
  have hQ := P.quadraticRepresentation_isIdempotent q hq
  have hQne : P.quadraticRepresentation q≠0 := by
    intro hz
    have h := congrArg (fun f : E →ₗ[ℝ] E => f q) hz
    rw [P.quadraticRepresentation_idempotent_self q hq,LinearMap.zero_apply] at h
    exact hne h
  have htrace : LinearMap.trace ℝ E (P.quadraticRepresentation q)≠0 := by
    intro hz
    exact hQne ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hQ).mp hz)
  have hdim : (Module.finrank ℝ (LinearMap.range (P.quadraticRepresentation q)) : ℝ)≠0 := by
    rwa [← (LinearMap.IsIdempotentElem.isProj_range (P.quadraticRepresentation q) hQ).trace]
  have hpos : 0<(Module.finrank ℝ (LinearMap.range (P.quadraticRepresentation q)) : ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) hdim.symm
  rw [P.regularTrace_idempotent_formula q hq]
  exact add_pos_of_pos_of_nonneg hpos (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

/-- Unit regular trace is vector-space dimension, not Jordan rank. -/
theorem regularTrace_unit : P.regularTrace P.unit=(Module.finrank ℝ E : ℝ) := by
  have hunit : P.product P.unit=(1 : Module.End ℝ E) := by
    ext x
    exact P.unit_left x
  rw [P.regularTrace_apply,hunit,LinearMap.trace_one]

end AlbertSequential.UnitalJordanProduct
