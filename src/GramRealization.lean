/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GramFactor
public import Mathlib.LinearAlgebra.Span.Basic

/-! Real Gram vectors spanning exactly rank(G) dimensions, including singular G.
The construction uses the span of factor columns and then an orthonormal basis. -/

@[expose] public section
noncomputable section
namespace AlbertSequential
open Module

def gramColumnSpan {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  Submodule.span ℝ (Set.range fun i => WithLp.toLp 2 (B.transpose i))

def gramColumnVector {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (i : ι) :
    gramColumnSpan B :=
  ⟨WithLp.toLp 2 (B.transpose i), Submodule.subset_span ⟨i, rfl⟩⟩

theorem gramColumnVector_spans {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) :
    Submodule.span ℝ (Set.range (gramColumnVector B)) = ⊤ := by
  exact (Submodule.span_range_subtype_eq_top_iff (gramColumnSpan B)
    (fun i => Submodule.subset_span ⟨i, rfl⟩)).mpr rfl

theorem gramColumnSpan_finrank {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) :
    finrank ℝ (gramColumnSpan B) = B.rank := by
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] (ι → ℝ) := WithLp.linearEquiv 2 ℝ _
  have hmap : (gramColumnSpan B).map e.toLinearMap =
      Submodule.span ℝ (Set.range B.col) := by
    unfold gramColumnSpan
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  calc
    finrank ℝ (gramColumnSpan B) =
        finrank ℝ ((gramColumnSpan B).map e.toLinearMap) :=
      (e.finrank_map_eq _).symm
    _ = B.rank := by rw [hmap, ← Matrix.rank_eq_finrank_span_cols]

theorem gramColumnVector_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B G : Matrix ι ι ℝ) (hG : G = B.transpose * B) (i j : ι) :
    inner ℝ (gramColumnVector B i) (gramColumnVector B j) = G i j := by
  change inner ℝ (WithLp.toLp 2 (B.transpose i)) (WithLp.toLp 2 (B.transpose j)) = G i j
  rw [inner_matrix_col_col]
  have hstar : B.conjTranspose = B.transpose := by ext a b; rfl
  rw [hstar, ← hG]

theorem exists_spanning_realGramVectors {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    ∃ v : ι → EuclideanSpace ℝ (Fin G.rank),
      (∀ i j, inner ℝ (v i) (v j) = G i j) ∧
      Submodule.span ℝ (Set.range v) = ⊤ := by
  obtain ⟨B, hB⟩ := exists_realGramFactor hG
  have hdim : finrank ℝ (gramColumnSpan B) = G.rank := by
    rw [gramColumnSpan_finrank, realGramFactor_rank B G hB]
  rw [← hdim]
  let e := (stdOrthonormalBasis ℝ (gramColumnSpan B)).repr
  refine ⟨fun i => e (gramColumnVector B i), ?_, ?_⟩
  · intro i j
    rw [e.inner_map_map, gramColumnVector_inner B G hB]
  · have hs := congrArg (fun p : Submodule ℝ (gramColumnSpan B) =>
        p.map e.toLinearEquiv.toLinearMap) (gramColumnVector_spans B)
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearEquiv.range, Function.comp_def, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] using hs

end AlbertSequential
