module

public import ChoiKrausAlgebra
public import ComplexPositiveFactor

/-! Finite matrix Choi/Kraus equivalence with explicit zero-map support.
The d²-column Kraus list may contain zero matrices, and no minimality or
nonzero-map premise is imported from rank-sized versions of Choi's theorem.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def factorKraus {d : ℕ} (B : ChoiMatrix d) : List (ComplexMatrix d) :=
  Finset.univ.toList.map (fun s : Fin d × Fin d => fun k i => B (i, k) s)

-- Allow the rewriter to unfold the Matrix type synonyms after list unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem factorKraus_choi {d : ℕ} (B : ChoiMatrix d) :
    krausChoi (factorKraus B) = B * B.conjTranspose := by
  classical
  unfold krausChoi factorKraus
  rw [List.map_map, Finset.sum_map_toList]
  ext i j
  simp [rankOneChoi, Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply]

theorem choi_positive_iff_kraus {d : ℕ} (C : ChoiMatrix d) :
    C.PosSemidef ↔ ∃ K : List (ComplexMatrix d),
      ∀ Y, choiAction C Y = krausAction K Y := by
  constructor
  · intro hC
    obtain ⟨B, hB⟩ := exists_complexPositiveFactor hC
    refine ⟨factorKraus B, fun Y => ?_⟩
    rw [hB, ← factorKraus_choi, krausChoi_action]
  · rintro ⟨K, hK⟩
    have heq : C = krausChoi K :=
      choiAction_injective (fun Y => (hK Y).trans (krausChoi_action K Y).symm)
    rw [heq]
    exact krausChoi_positive K

end AlbertSequential
