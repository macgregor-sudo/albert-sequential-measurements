/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordCoordinates

public section
noncomputable section

namespace LemmaB

open scoped BigOperators

variable (p : Params ℝ)

def cliffordReflection (a : ComparisonClifford p) : ComparisonClifford p :=
  a - (2 * cliffordCoordinates p a 7) • cliffordGhost p

theorem cliffordCoordinates_reflection (a : ComparisonClifford p) :
    cliffordCoordinates p (cliffordReflection p a) = sig (cliffordCoordinates p a) := by
  unfold cliffordReflection
  rw [map_sub, map_smul, cliffordCoordinates_ghost]
  funext i
  fin_cases i <;> simp [sig]
  ring

private def plus (c : ℝ) (i : Fin 3) (a : ComparisonClifford p) : ComparisonClifford p :=
  c • a + cliffordGenerator p i * a

private def minus (c : ℝ) (i : Fin 3) (a : ComparisonClifford p) : ComparisonClifford p :=
  c • a - cliffordGenerator p i * a

def cliffordTransition : Fin 4 → Fin 4 → ComparisonClifford p → ComparisonClifford p :=
  ![![id, id, id, id],
    ![id, (p.mB • ·), plus p p.c1 0 ∘ cliffordReflection p,
      cliffordReflection p ∘ minus p p.c3 2],
    ![id, cliffordReflection p ∘ minus p p.c1 0, (p.mC • ·),
      plus p p.c2 1 ∘ cliffordReflection p],
    ![id, plus p p.c3 2 ∘ cliffordReflection p,
      cliffordReflection p ∘ minus p p.c2 1, (p.mD • ·)]]

theorem cliffordCoordinates_transition (x y : Fin 4) (a : ComparisonClifford p) :
    cliffordCoordinates p (cliffordTransition p x y a) = T p x y (cliffordCoordinates p a) := by
  fin_cases x <;> fin_cases y <;>
    simp [cliffordTransition, plus, minus, T, cliffordCoordinates_reflection, cliffordCoordinates_generator_mul,
      h1, h2, h3, h1s, h2s, h3s]

abbrev CliffordFrames := Fin 4 → ComparisonClifford p

def cliffordFrameCoordinates (F : CliffordFrames p) : V ℝ :=
  fun x => cliffordCoordinates p (F x)

def cliffordFrameEquiv : CliffordFrames p ≃ₗ[ℝ] V ℝ :=
  LinearEquiv.piCongrRight (fun _ => cliffordCoordinateEquiv p)

theorem cliffordFrameEquiv_apply (F : CliffordFrames p) :
    cliffordFrameEquiv p F = cliffordFrameCoordinates p F := by
  funext i
  simp [cliffordFrameEquiv, cliffordFrameCoordinates, LinearEquiv.piCongrRight_apply]

def cliffordComparisonForm (F G : CliffordFrames p) : ℝ :=
  ∑ x, ∑ y, cliffordPairing p (F x) (cliffordTransition p x y (G y))

theorem cliffordComparisonForm_eq_Q (F G : CliffordFrames p) :
    cliffordComparisonForm p F G = Q p (cliffordFrameCoordinates p F) (cliffordFrameCoordinates p G) := by
  simp only [cliffordComparisonForm, Q, cliffordPairing_eq_W, cliffordCoordinates_transition,
    cliffordFrameCoordinates]

def cliffordComparisonProjection (x : Fin 4) (F : CliffordFrames p) : CliffordFrames p :=
  Pi.single x ((mOf p x)⁻¹ • ∑ y, cliffordTransition p x y (F y))

theorem cliffordCoordinates_projection (x : Fin 4) (F : CliffordFrames p) :
    cliffordFrameCoordinates p (cliffordComparisonProjection p x F) =
      P p x (cliffordFrameCoordinates p F) := by
  funext i
  by_cases hi : i = x
  · subst i
    simp [cliffordFrameCoordinates, cliffordComparisonProjection, P, src, map_sum,
      cliffordCoordinates_transition]
  · simp [hi, cliffordFrameCoordinates, cliffordComparisonProjection, P]

theorem cliffordCoordinates_anchor :
    cliffordFrameCoordinates p (Pi.single 0 1) = xi := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [cliffordFrameCoordinates, xi]
  · simp [hi, cliffordFrameCoordinates, xi]

def cliffordComparisonPath (w : List (Fin 4)) : CliffordFrames p :=
  w.foldl (fun F x => cliffordComparisonProjection p x F) (Pi.single 0 1)

theorem cliffordCoordinates_path (w : List (Fin 4)) :
    cliffordFrameCoordinates p (cliffordComparisonPath p w) = uhat p w := by
  induction w using List.reverseRecOn with
  | nil => exact cliffordCoordinates_anchor p
  | append_singleton w x ih =>
    simp only [cliffordComparisonPath, uhat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [cliffordCoordinates_projection]
    exact congrArg (P p x) ih

theorem cliffordComparisonPath_gram (u v : List (Fin 4)) :
    cliffordComparisonForm p (cliffordComparisonPath p u) (cliffordComparisonPath p v) =
      Q p (uhat p u) (uhat p v) := by
  rw [cliffordComparisonForm_eq_Q, cliffordCoordinates_path, cliffordCoordinates_path]

end LemmaB
