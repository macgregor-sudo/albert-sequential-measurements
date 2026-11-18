/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteGramReconstruction
public import VectorGramNecessity

/-! Exact finite-real vector-state characterization on all reduced words ≤ L.
The arbitrary-dimensional R/C/H operator-state bridge is separate. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

def FiniteGramWitness.changeTable {n L : ℕ} {f g : Word (Fin n) → ℝ}
    (W : FiniteGramWitness n L g)
    (h : ∀ w ∈ W.words, g w = f w) : FiniteGramWitness n L f where
  words := W.words
  complete := W.complete
  gram := W.gram
  positive := W.positive
  normalized := by
    rw [← h [] (emptyGramIndex W).property]
    exact W.normalized
  probabilities w hw := by rw [← h w hw]; exact W.probabilities w hw
  diagonal u := (W.diagonal u).trans (h u.val u.property)
  complement := W.complement
  orthogonal := W.orthogonal

theorem finiteGram_iff_finiteRealModel {n L : ℕ} {f : Word (Fin n) → ℝ} :
    Nonempty (FiniteGramWitness n L f) ↔
      ∃ d, ∃ M : FiniteRealVectorProjectiveModel n d,
        ∀ w, w.length ≤ L → IsReducedWord w → M.probability w = f w := by
  constructor
  · rintro ⟨W⟩
    obtain ⟨M, hM⟩ := finiteGram_reconstruction W
    exact ⟨W.gram.rank, M, fun w hlen hred => hM w ((W.complete w).mpr ⟨hlen, hred⟩)⟩
  · rintro ⟨d, M, hM⟩
    obtain ⟨W⟩ := M.finiteGram L
    exact ⟨W.changeTable (fun w hw =>
      hM w ((W.complete w).mp hw).1 ((W.complete w).mp hw).2)⟩

end AlbertSequential
