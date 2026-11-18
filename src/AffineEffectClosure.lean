/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-! An affine function on the closure of a nonempty finite-dimensional convex
set is determined by its values there, without a continuity hypothesis. -/
@[expose] public section
noncomputable section
open scoped Topology

namespace AlbertSequential

theorem affine_zero_on_convex_closure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E}
    (hS : Convex ℝ S) (hne : S.Nonempty) (f : E → ℝ)
    (hf : ∀ x ∈ closure S, ∀ y ∈ closure S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • x + (1 - t) • y) = t * f x + (1 - t) * f y)
    (hzero : ∀ y ∈ S, f y = 0) : ∀ x ∈ closure S, f x = 0 := by
  obtain ⟨a, ha⟩ := hne.intrinsicInterior hS
  obtain ⟨a', ha', rfl⟩ := mem_intrinsicInterior.mp ha
  have haS : (a' : E) ∈ S := @interior_subset _ _ (Subtype.val ⁻¹' S) _ ha'
  letI : Nonempty (affineSpan ℝ S) := ⟨a'⟩
  intro x hx
  have hxspan : x ∈ affineSpan ℝ S :=
    closure_minimal (subset_affineSpan ℝ S) (affineSpan ℝ S).isClosed_of_finiteDimensional hx
  let x' : affineSpan ℝ S := ⟨x, hxspan⟩
  have h0 := AffineMap.lineMap_apply_zero (k := ℝ) a' x'
  obtain ⟨t, ht, hyt⟩ :=
    (AffineMap.lineMap_continuous.tendsto' 0 a' h0).eventually_mem
      (mem_interior_iff_mem_nhds.mp ha') |>.exists_lt
  let y : E := (AffineMap.lineMap a' x' t : affineSpan ℝ S)
  have hyS : y ∈ S := hyt
  have hyEq : y = (1 - t) • (a' : E) + t • x := by
    change (affineSpan ℝ S).subtype (AffineMap.lineMap a' x' t) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    rfl
  let α : ℝ := -t / (1 - t)
  have hden : 0 < 1 - t := by linarith
  have hα : 0 < α := div_pos (neg_pos.mpr ht) hden
  have hα1 : α ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have hcoef1 : (1 - α) * (1 - t) = 1 := by
    dsimp [α]
    field_simp
    ring
  have hcoef2 : α + (1 - α) * t = 0 := by
    dsimp [α]
    field_simp
    ring
  have heq : α • x + (1 - α) • y = (a' : E) := by
    rw [hyEq, smul_add, smul_smul, smul_smul, hcoef1, one_smul]
    calc
      α • x + ((a' : E) + ((1 - α) * t) • x) =
          (a' : E) + (α + (1 - α) * t) • x := by module
      _ = (a' : E) := by rw [hcoef2, zero_smul, add_zero]
  have h := hf x hx y (subset_closure hyS) α hα.le hα1
  rw [heq, hzero _ haS, hzero _ hyS, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hα.ne'

end AlbertSequential
