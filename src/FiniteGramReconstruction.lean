/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GramModelConstruction
public import GramRealization
public import ReducedWords

/-! Every supplied full finite Gram witness has a real vector-state
projective realization in exactly its Gram rank dimensions. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

namespace FiniteGramVectorFamily
variable {n L : ℕ} {f : Word (Fin n) → ℝ}
variable {W : FiniteGramWitness n L f} {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem branchVector_eq (F : FiniteGramVectorFamily W E)
    (w : Word (Fin n)) (hw : w ∈ W.words) :
    F.projectiveModel.branchVector w = F.vector ⟨w, hw⟩ := by
  revert hw
  induction w using List.reverseRecOn with
  | nil => intro hw; rfl
  | append_singleton w a ih =>
    intro hw
    rcases a with ⟨i, b⟩
    obtain ⟨hL, hred⟩ := (W.complete _).mp hw
    have hlen := reducedWord_snoc_length w (i, b) L hL
    have hpref : w ∈ W.words := (W.complete w).mpr
      ⟨Nat.le_of_lt hlen, isReducedWord_prefix w [(i, b)] hred⟩
    have htrue : IsReducedWord (w ++ [(i, true)]) :=
      (isReducedWord_append_outcome_iff w i b true).mp hred
    have hfalse : IsReducedWord (w ++ [(i, false)]) :=
      (isReducedWord_append_outcome_iff w i b false).mp hred
    have hy : w ++ [(i, true)] ∈ W.words := (W.complete _).mpr
      ⟨by simpa only [List.length_append, List.length_singleton] using hL, htrue⟩
    have hn : w ++ [(i, false)] ∈ W.words := (W.complete _).mpr
      ⟨by simpa only [List.length_append, List.length_singleton] using hL, hfalse⟩
    rw [RealVectorProjectiveData.branchVector_append_singleton, ih hpref]
    exact F.projectiveModel_append ⟨w, hpref⟩ i b hlen htrue hy hn hw

theorem probability_eq (F : FiniteGramVectorFamily W E)
    (w : Word (Fin n)) (hw : w ∈ W.words) :
    F.projectiveModel.probability w = f w := by
  unfold RealVectorProjectiveData.probability
  rw [F.branchVector_eq w hw, F.inner_eq, W.diagonal]

end FiniteGramVectorFamily

theorem finiteGram_reconstruction {n L : ℕ} {f : Word (Fin n) → ℝ}
    (W : FiniteGramWitness n L f) :
    ∃ M : FiniteRealVectorProjectiveModel n W.gram.rank,
      ∀ w ∈ W.words, M.probability w = f w := by
  classical
  obtain ⟨v, hv, hspan⟩ := exists_spanning_realGramVectors W.positive
  let F : FiniteGramVectorFamily W (EuclideanSpace ℝ (Fin W.gram.rank)) :=
    ⟨v, hv, hspan⟩
  exact ⟨F.projectiveModel, F.probability_eq⟩

end AlbertSequential
