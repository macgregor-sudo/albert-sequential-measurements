/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EqualityRepeatableCountermodels
public import GeneralEJAWordTransport
import Mathlib.Tactic.Module

@[expose] public section
noncomputable section

namespace AlbertSequential
namespace UnitalJordanProduct

open EqualityCountermodels
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

private theorem idem_complement {q : E} (hq : P.product q q = q) :
    P.product (P.unit - q) (P.unit - q) = P.unit - q := by
  have hu : P.product q P.unit = q := (P.commutative _ _).trans (P.unit_left q)
  simp only [map_sub, LinearMap.sub_apply, P.unit_left, hu, hq]
  abel

private theorem U_complement_idem {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation (P.unit - q) x = x - (2 : ℝ) • P.product q x +
      P.quadraticRepresentation q x := by
  rw [P.quadraticRepresentation_apply, P.idem_complement hq, P.quadraticRepresentation_apply, hq]
  simp only [map_sub, LinearMap.sub_apply, P.unit_left]
  module

private theorem U_complement_comp_zero {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation (P.unit - q) (P.quadraticRepresentation q x) = 0 := by
  rw [P.U_complement_idem hq, P.quadraticRepresentation_idempotent_apply q x hq]
  rw [(P.mem_peirceOne _ _).mp (P.quadraticRepresentation_mem_peirceOne q x hq)]
  module

private theorem U_comp_complement_zero {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation q (P.quadraticRepresentation (P.unit - q) x) = 0 := by
  simpa only [sub_sub_cancel] using P.U_complement_comp_zero (P.idem_complement hq) x

private theorem U_after_L {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation q (P.product q x) = P.quadraticRepresentation q x := by
  have h := (P.mem_peirceOne _ _).mp (P.quadraticRepresentation_mem_peirceOne q x hq)
  simpa only [P.quadraticRepresentation_apply, hq, map_sub, map_smul] using h

/-- The Jordan table associated with a linear readout and the printed quadratic effects. -/
def wordTable {I : Type*} (p : I → E) (φ : E →ₗ[ℝ] ℝ) (w : Word I) : ℝ :=
  φ (P.sequentialWordEffect p w)

private theorem effect_add_append {I : Type*} (p : I → E)
    (u v w z : Word I)
    (h : P.sequentialWordEffect p v + P.sequentialWordEffect p w = P.sequentialWordEffect p z) :
    P.sequentialWordEffect p (u ++ v) + P.sequentialWordEffect p (u ++ w) =
      P.sequentialWordEffect p (u ++ z) := by
  induction u with
  | nil => exact h
  | cons a u ih =>
      simp only [List.cons_append, sequentialWordEffect, ← map_add, ih]

private theorem effect_eq_append {I : Type*} (p : I → E)
    (u v w : Word I) (h : P.sequentialWordEffect p v = P.sequentialWordEffect p w) :
    P.sequentialWordEffect p (u ++ v) = P.sequentialWordEffect p (u ++ w) := by
  induction u with
  | nil => exact h
  | cons a u ih => simp only [List.cons_append, sequentialWordEffect, ih]

private theorem effect_zero_append {I : Type*} (p : I → E)
    (u v : Word I) (h : P.sequentialWordEffect p v = 0) :
    P.sequentialWordEffect p (u ++ v) = 0 := by
  induction u with
  | nil => exact h
  | cons a u ih => simp only [List.cons_append, sequentialWordEffect, ih, map_zero]

/-- Every word table of idempotents in a unital real Jordan algebra satisfies the three basic
relations of 6.17(b), for arbitrary prefixes, suffixes and readouts. -/
theorem wordTable_basicWordEqualities {I : Type*} (p : I → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ) :
    BasicWordEqualities (P.wordTable p φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u i
    have h := P.effect_add_append p u [(i, true)] [(i, false)] [] (by
      simp only [sequentialWordEffect, sequentialOutcome, Bool.false_eq_true,
        ↓reduceIte, P.quadraticRepresentation_unit, hp, P.idem_complement (hp i)]
      abel)
    simpa only [wordTable, ← map_add, List.append_nil] using congrArg φ h
  · intro u v i b
    have h := P.effect_eq_append p u ([(i, b), (i, b)] ++ v) ([(i, b)] ++ v) (by
      cases b <;> simp only [List.cons_append, List.nil_append, sequentialWordEffect, sequentialOutcome,
        Bool.false_eq_true, ↓reduceIte] <;>
        exact P.quadraticRepresentation_idempotent_apply _ _ (by first | exact hp i | exact P.idem_complement (hp i)))
    simpa only [wordTable, List.append_assoc] using congrArg φ h
  · intro u v i b
    have h := P.effect_zero_append p u ([(i, b), (i, !b)] ++ v) (by
      cases b <;> simp only [List.cons_append, List.nil_append, sequentialWordEffect, sequentialOutcome,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      · exact P.U_complement_comp_zero (hp i) _
      · exact P.U_comp_complement_zero (hp i) _)
    simpa only [wordTable, map_zero, List.append_assoc] using congrArg φ h

/-- First extra equality of 6.17(b), in the printed order of the two signed sides. -/
theorem wordTable_extraOne {I : Type*} (p : I → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ) (i j : I) :
    P.wordTable p φ [(i, false), (j, true)] - P.wordTable p φ [(i, true), (j, true)] -
      P.wordTable p φ [(j, true)] =
    P.wordTable p φ [(j, false), (i, true)] - P.wordTable p φ [(j, true), (i, true)] -
      P.wordTable p φ [(i, true)] := by
  simp only [wordTable, sequentialWordEffect, sequentialOutcome, Bool.false_eq_true,
    ↓reduceIte, P.quadraticRepresentation_unit, hp, ← map_sub]
  congr 1
  rw [P.U_complement_idem (hp i), P.U_complement_idem (hp j), P.commutative (p i) (p j)]
  module

/-- Second extra equality of 6.17(b), with the positive middle outcome on the left. -/
theorem wordTable_extraTwo {I : Type*} (p : I → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ) (i j : I) :
    P.wordTable p φ [(i, true), (j, true), (i, false)] =
      P.wordTable p φ [(i, true), (j, false), (i, false)] := by
  simp only [wordTable, sequentialWordEffect, sequentialOutcome, Bool.false_eq_true,
    ↓reduceIte, P.quadraticRepresentation_unit, P.idem_complement (hp i)]
  congr 1
  have hz : P.quadraticRepresentation (p i) (P.unit - p i) = 0 := by
    rw [map_sub, P.quadraticRepresentation_unit, hp, P.quadraticRepresentation_idempotent_self _ (hp i),
      sub_self]
  have hu (x : E) : P.product x P.unit = x := (P.commutative _ _).trans (P.unit_left x)
  calc
    P.quadraticRepresentation (p i) (P.quadraticRepresentation (p j) (P.unit - p i)) =
        P.quadraticRepresentation (p i) (P.quadraticRepresentation (p j) (P.unit - p i)) +
          (0 : E) := by rw [add_zero]
    _ = P.quadraticRepresentation (p i)
        (P.quadraticRepresentation (p j) (P.unit - p i) + (P.unit - p i) -
          (2 : ℝ) • P.product (p j) (P.unit - p i)) := by
        simp only [map_sub, map_add, map_smul, hz, add_zero, hu]
        rw [P.commutative (p j) (p i), P.U_after_L (hp i)]
        module
    _ = P.quadraticRepresentation (p i)
        (P.quadraticRepresentation (P.unit - p j) (P.unit - p i)) := by
        rw [P.U_complement_idem (hp j)]
        congr 1
        abel

end UnitalJordanProduct
end AlbertSequential
