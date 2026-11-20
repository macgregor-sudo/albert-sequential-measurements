/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneralEJAWordTransport
public import JordanPeircePositiveMultiplication
import Mathlib.Tactic.Module

/-! Primitive runs and the Peirce correction for a marginalized test. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- An effect inserted after the given chronological prefix. -/
def prefixEffectMap (p : I → E) : Word I → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | a :: u => (P.quadraticRepresentation (P.sequentialOutcome p a)).comp (prefixEffectMap p u)

theorem sequentialWordEffect_append (p : I → E) (u v : Word I) :
    P.sequentialWordEffect p (u ++ v) = P.prefixEffectMap p u (P.sequentialWordEffect p v) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, sequentialWordEffect, prefixEffectMap, LinearMap.comp_apply, ih]

/-- Reading both branches of an idempotent test discards exactly its half-Peirce component. -/
theorem nonselectiveQuadratic_eq_sub_peirceHalf {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation q x + P.quadraticRepresentation (P.unit - q) x =
      x - P.peirceHalfProjection q x := by
  have hunit : P.product q P.unit = q := (P.commutative _ _).trans (P.unit_left _)
  have hcomp : P.product (P.unit - q) (P.unit - q) = P.unit - q := by
    simp only [map_sub, LinearMap.sub_apply, P.unit_left, hunit, hq]
    abel
  rw [P.quadraticRepresentation_apply q, P.quadraticRepresentation_apply (P.unit - q), hq, hcomp]
  simp only [P.peirceHalfProjection_apply, map_sub, LinearMap.sub_apply, P.unit_left]
  module

/-- For a marginalized middle outcome, the correction is the suffix's
half-Peirce effect propagated backwards through the actual prefix. -/
theorem sequentialWordEffect_middle_marginal (p : I → E) (u v : Word I) (i : I)
    (hi : P.product (p i) (p i) = p i) :
    P.sequentialWordEffect p (u ++ (i, true) :: v) +
        P.sequentialWordEffect p (u ++ (i, false) :: v) =
      P.sequentialWordEffect p (u ++ v) -
        P.prefixEffectMap p u (P.peirceHalfProjection (p i) (P.sequentialWordEffect p v)) := by
  simp only [P.sequentialWordEffect_append, sequentialWordEffect, sequentialOutcome,
    Bool.false_eq_true, ↓reduceIte, ← map_add, ← map_sub, P.nonselectiveQuadratic_eq_sub_peirceHalf hi]

theorem sequentialWordEffect_terminal_marginal (p : I → E) (u : Word I) (i : I)
    (hi : P.product (p i) (p i) = p i) :
    P.sequentialWordEffect p (u ++ [(i, true)]) + P.sequentialWordEffect p (u ++ [(i, false)]) =
      P.sequentialWordEffect p u := by
  have hunit : P.product (p i) P.unit = p i := (P.commutative _ _).trans (P.unit_left _)
  simpa only [List.append_nil, sequentialWordEffect, P.peirceHalfProjection_apply, hunit, hi, sub_self,
    smul_zero, map_zero, sub_zero] using P.sequentialWordEffect_middle_marginal p u [] i hi

theorem sequentialBranchState_smul (p : I → E) (a : ℝ) (ρ : E) (w : Word I) :
    P.sequentialBranchState p (a • ρ) w = a • P.sequentialBranchState p ρ w := by
  induction w generalizing ρ with
  | nil => rfl
  | cons b w ih =>
      simp only [sequentialBranchState, List.foldl_cons, map_smul]
      exact ih _

section CanonicalTrace

variable [FiniteDimensional ℝ E] (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

/-- The product of the consecutive canonical overlaps after the first letter. -/
def primitiveRunTransitions (p : I → E) : Outcome I → Word I → ℝ
  | _, [] => 1
  | a, b :: w =>
      τ (P.product (P.sequentialOutcome p a) (P.sequentialOutcome p b)) *
        primitiveRunTransitions p b w

/-- The initial overlap times all consecutive overlaps for a nonempty primitive run. -/
theorem canonicalTrace_primitiveRun_product (p : I → E) (ρ : E) (a : Outcome I) (w : Word I)
    (hp : ∀ b ∈ a :: w, P.IsPrimitive (P.sequentialOutcome p b)) :
    τ (P.sequentialBranchState p ρ (a :: w)) =
      τ (P.product ρ (P.sequentialOutcome p a)) * P.primitiveRunTransitions hfr p a w := by
  have step (x : E) (b : Outcome I) (v : Word I)
      (hb : P.IsPrimitive (P.sequentialOutcome p b)) :
      τ (P.sequentialBranchState p x (b :: v)) =
        τ (P.product x (P.sequentialOutcome p b)) *
          τ (P.sequentialBranchState p (P.sequentialOutcome p b) v) := by
    change τ (P.sequentialBranchState p
      (P.quadraticRepresentation (P.sequentialOutcome p b) x) v) = _
    rw [P.canonicalTraceOfFormallyReal_primitive_compression hfr _ _ hb, P.sequentialBranchState_smul,
      map_smul, smul_eq_mul, P.commutative (P.sequentialOutcome p b) x]
  induction w generalizing a ρ with
  | nil =>
      rw [step ρ a [] (hp a (List.mem_cons_self ..))]
      change _ * τ (P.sequentialOutcome p a) = _ * 1
      rw [P.canonicalTraceOfFormallyReal_primitive hfr _ (hp a (List.mem_cons_self ..))]
  | cons b w ih =>
      rw [step ρ a (b :: w) (hp a (List.mem_cons_self ..)),
        ih (P.sequentialOutcome p a) b (fun c hc => hp c (List.mem_cons_of_mem _ hc))]
      rfl

theorem canonicalPairing_primitiveRun_product (p : I → E) (ρ : E) (a : Outcome I) (w : Word I)
    (hp : ∀ b ∈ a :: w, P.IsPrimitive (P.sequentialOutcome p b)) :
    P.canonicalPairingFunctional hfr ρ (P.sequentialWordEffect p (a :: w)) =
      τ (P.product ρ (P.sequentialOutcome p a)) * P.primitiveRunTransitions hfr p a w := by
  rw [← P.canonicalTrace_sequentialBranchState hfr]
  exact P.canonicalTrace_primitiveRun_product hfr p ρ a w hp

/-- Trace probabilities obey the same middle-marginal correction as effects. -/
theorem canonicalTrace_middle_marginal (p : I → E) (ρ : E) (u v : Word I) (i : I)
    (hi : P.product (p i) (p i) = p i) :
    τ (P.sequentialBranchState p ρ (u ++ (i, true) :: v)) +
        τ (P.sequentialBranchState p ρ (u ++ (i, false) :: v)) =
      τ (P.sequentialBranchState p ρ (u ++ v)) -
        P.canonicalPairingFunctional hfr ρ
          (P.prefixEffectMap p u (P.peirceHalfProjection (p i) (P.sequentialWordEffect p v))) := by
  simp only [P.canonicalTrace_sequentialBranchState hfr, ← map_add, ← map_sub,
    P.sequentialWordEffect_middle_marginal p u v i hi]

end CanonicalTrace

end AlbertSequential.UnitalJordanProduct
