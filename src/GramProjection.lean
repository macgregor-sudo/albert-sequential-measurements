/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteGramModel
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The M2/M3 projection mechanism on a genuine spanning Gram family.
No positive-mass condition or division by a Gram diagonal is used. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev GramWordIndex {n L : ℕ} {f : Word (Fin n) → ℝ}
    (W : FiniteGramWitness n L f) := {w // w ∈ W.words}

structure FiniteGramVectorFamily {n L : ℕ} {f : Word (Fin n) → ℝ}
    (W : FiniteGramWitness n L f) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vector : GramWordIndex W → E
  inner_eq : ∀ u v, inner ℝ (vector u) (vector v) = W.gram u v
  spans : Submodule.span ℝ (Set.range vector) = ⊤

theorem inner_eq_zero_of_mem_span {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : ι → E) (z : E)
    (h : ∀ i, inner ℝ (v i) z = 0) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range v)) : inner ℝ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih => simp only [real_inner_smul_left, ih, mul_zero]

theorem eq_zero_of_spanning_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : ι → E)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) (z : E)
    (h : ∀ i, inner ℝ (v i) z = 0) : z = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  apply inner_eq_zero_of_mem_span v z h
  rw [hspan]
  exact Submodule.mem_top

namespace FiniteGramVectorFamily
variable {n L : ℕ} {f : Word (Fin n) → ℝ}
variable {W : FiniteGramWitness n L f} {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem vector_split (F : FiniteGramVectorFamily W E)
    (v : GramWordIndex W) (i : Fin n) (hlen : v.val.length < L)
    (hred : IsReducedWord (v.val ++ [(i, true)]))
    (hy : v.val ++ [(i, true)] ∈ W.words)
    (hn : v.val ++ [(i, false)] ∈ W.words) :
    F.vector v = F.vector ⟨v.val ++ [(i, true)], hy⟩ +
      F.vector ⟨v.val ++ [(i, false)], hn⟩ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_spanning_inner F.vector F.spans
  intro u
  rw [inner_sub_right, inner_add_right, F.inner_eq, F.inner_eq, F.inner_eq]
  exact sub_eq_zero.mpr (W.complement u v i hlen hred hy hn).symm

def yesEndingSpan (F : FiniteGramVectorFamily W E) (i : Fin n) : Submodule ℝ E :=
  Submodule.span ℝ (F.vector '' {u | u.val.getLast? = some (i, true)})

theorem yesEnding_mem (F : FiniteGramVectorFamily W E) (i : Fin n)
    (u : GramWordIndex W) (hu : u.val.getLast? = some (i, true)) :
    F.vector u ∈ F.yesEndingSpan i :=
  Submodule.subset_span ⟨u, hu, rfl⟩

theorem noEnding_orthogonal (F : FiniteGramVectorFamily W E) (i : Fin n)
    (v : GramWordIndex W) (hv : v.val.getLast? = some (i, false)) :
    F.vector v ∈ (F.yesEndingSpan i)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  change x ∈ Submodule.span ℝ (F.vector '' {u | u.val.getLast? = some (i, true)}) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [F.inner_eq]
    exact W.orthogonal u v i hu hv
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih => simp only [real_inner_smul_left, ih, mul_zero]

variable [FiniteDimensional ℝ E]

theorem projection_append_yes (F : FiniteGramVectorFamily W E)
    (v : GramWordIndex W) (i : Fin n) (hlen : v.val.length < L)
    (hred : IsReducedWord (v.val ++ [(i, true)]))
    (hy : v.val ++ [(i, true)] ∈ W.words)
    (hn : v.val ++ [(i, false)] ∈ W.words) :
    (F.yesEndingSpan i).starProjection (F.vector v) =
      F.vector ⟨v.val ++ [(i, true)], hy⟩ := by
  apply Submodule.eq_starProjection_of_mem_orthogonal'
    (z := F.vector ⟨v.val ++ [(i, false)], hn⟩)
  · apply F.yesEnding_mem i
    simp
  · apply F.noEnding_orthogonal i
    simp
  · exact F.vector_split v i hlen hred hy hn

theorem projection_append_no (F : FiniteGramVectorFamily W E)
    (v : GramWordIndex W) (i : Fin n) (hlen : v.val.length < L)
    (hred : IsReducedWord (v.val ++ [(i, true)]))
    (hy : v.val ++ [(i, true)] ∈ W.words)
    (hn : v.val ++ [(i, false)] ∈ W.words) :
    F.vector v - (F.yesEndingSpan i).starProjection (F.vector v) =
      F.vector ⟨v.val ++ [(i, false)], hn⟩ := by
  rw [F.projection_append_yes v i hlen hred hy hn, F.vector_split v i hlen hred hy hn]
  simp

end FiniteGramVectorFamily
end AlbertSequential
