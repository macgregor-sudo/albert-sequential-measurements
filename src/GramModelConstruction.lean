/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GramProjection

/-! Actual projection/vector data from a finite spanning Gram family. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

def emptyGramIndex {n L : ℕ} {f : Word (Fin n) → ℝ}
    (W : FiniteGramWitness n L f) : GramWordIndex W :=
  ⟨[], (W.complete []).mpr ⟨Nat.zero_le L, trivial⟩⟩

namespace FiniteGramVectorFamily
variable {n L : ℕ} {f : Word (Fin n) → ℝ}
variable {W : FiniteGramWitness n L f} {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def projectiveModel (F : FiniteGramVectorFamily W E) :
    RealVectorProjectiveData (Fin n) E where
  projection i := (F.yesEndingSpan i).starProjection.toLinearMap
  idempotent i x := congrArg (fun p : E →L[ℝ] E => p x)
    (F.yesEndingSpan i).isIdempotentElem_starProjection
  symmetric i x y := (F.yesEndingSpan i).inner_starProjection_left_eq_right x y
  initial := F.vector (emptyGramIndex W)
  normalized := by
    rw [F.inner_eq, W.diagonal]
    exact W.normalized

theorem projectiveModel_append (F : FiniteGramVectorFamily W E)
    (v : GramWordIndex W) (i : Fin n) (b : Bool) (hlen : v.val.length < L)
    (hred : IsReducedWord (v.val ++ [(i, true)]))
    (hy : v.val ++ [(i, true)] ∈ W.words)
    (hn : v.val ++ [(i, false)] ∈ W.words)
    (hb : v.val ++ [(i, b)] ∈ W.words) :
    F.projectiveModel.outcome (i, b) (F.vector v) =
      F.vector ⟨v.val ++ [(i, b)], hb⟩ := by
  cases b
  · exact F.projection_append_no v i hlen hred hy hn
  · exact F.projection_append_yes v i hlen hred hy hn

end FiniteGramVectorFamily
end AlbertSequential
