/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
noncomputable section
namespace AlbertSequential.FiniteConvexity
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Convex combinations with a fixed finite number of actual points. -/
def combinationImage (s : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    ((stdSimplex ℝ (Fin n)) ×ˢ {z : Fin n → E | ∀ i, z i ∈ s})

theorem combinationImage_compact (s : Set E) (hs : IsCompact s) (n : ℕ) :
    IsCompact (combinationImage s n) := by
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod
    (isCompact_pi_infinite (fun _ => hs))).image
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd))

theorem combinationImage_subset_convexHull (s : Set E) (n : ℕ) :
    combinationImage s n ⊆ convexHull ℝ s := by
  rintro _ ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩
  exact mem_convexHull_of_exists_fintype w z hw.1 hw.2 hz rfl

/-- Fixed dimension gives a finite union of compact combination images;
no claim that an arbitrary infinite-dimensional convex hull is compact. -/
theorem compact_convexHull (s : Set E) (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  have heq : convexHull ℝ s =
      ⋃ n : Fin (Module.finrank ℝ E+2), combinationImage s n.val := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι,inst,z,w,hz,ha,hw,hsum,hxsum⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      letI := inst
      have hc : Fintype.card ι ≤ Module.finrank ℝ E+1 :=
        ha.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let n : Fin (Module.finrank ℝ E+2) := ⟨Fintype.card ι,by omega⟩
      let e := Fintype.equivFin ι
      let w' : Fin n.val → ℝ := fun i => w (e.symm i)
      let z' : Fin n.val → E := fun i => z (e.symm i)
      apply Set.mem_iUnion.mpr
      refine ⟨n,⟨(w',z'),⟨?_,?_⟩,?_⟩⟩
      · constructor
        · intro i; exact (hw _).le
        · exact (Fintype.sum_equiv e w w' (fun i => by simp [w'])).symm.trans hsum
      · intro i; exact hz ⟨_,rfl⟩
      · exact (Fintype.sum_equiv e (fun i => w i • z i)
          (fun i => w' i • z' i) (fun i => by simp [w',z'])).symm.trans hxsum
    · exact Set.iUnion_subset (fun n => combinationImage_subset_convexHull s n.val)
  rw [heq]
  exact isCompact_iUnion (fun n => combinationImage_compact s hs n.val)

end AlbertSequential.FiniteConvexity
