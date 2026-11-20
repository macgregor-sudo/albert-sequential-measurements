/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.TableValues
public import LengthSeven.Gram28ScalarRules
public import TableModel.WalkSpaceRelations

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven.TableModel

open AlbertSequential

theorem comparisonGram_eq_upsilon (τ : TraceData)
    (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    LemmaB.Q (comparisonParams τ) (LemmaB.uhat (comparisonParams τ) u) (LemmaB.uhat (comparisonParams τ) v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) := by
  rw [← comparison_pathVec τ hB hC hD u, ← comparison_pathVec τ hB hC hD v]
  exact algebraicWalk_gram_eq_upsilon (comparisonWalkSpace τ hB hC hD) τ
    (comparison_hypotheses τ hB hC hD) u v hu hv

theorem gram_eq_comparison_of_gram28Hyp {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : WalkForm V} {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (h : Gram28Hyp W τ S) (hrep : W.Reproduces S f) (ht : TableValues τ f)
    (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) =
      LemmaB.Q (comparisonParams τ) (LemmaB.uhat (comparisonParams τ) u) (LemmaB.uhat (comparisonParams τ) v) :=
  (WalkForm.gram_eq_upsilon_of_gram28Hyp h hrep ht u v hu hv).trans
    (comparisonGram_eq_upsilon τ hB hC hD u v hu hv).symm

theorem native_gram_eq_comparison_of_gram28Hyp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (S : Set (Word Letter)) (h : Gram28Hyp W (nativeTraceData p) S)
    (hrep : W.Reproduces S (nativeWordProbability p (p 0)))
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) = LemmaB.Q (comparisonParams (nativeTraceData p))
      (LemmaB.uhat (comparisonParams (nativeTraceData p)) u)
      (LemmaB.uhat (comparisonParams (nativeTraceData p)) v) :=
  gram_eq_comparison_of_gram28Hyp h hrep (tableValues_native p hp)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos p hp hA 0 1 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos p hp hA 0 2 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos p hp hA 0 3 (by decide)).1) u v hu hv

end AlbertSequential.LengthSeven.TableModel
