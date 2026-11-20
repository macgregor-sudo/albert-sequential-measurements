/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThreeAtomAndFourPoint

/-! Four atoms selected from three frames always have a quaternionic carrier. -/
@[expose] public section
noncomputable section

namespace AlbertSequential

theorem four_atoms_from_three_frames_contained (F : Fin 3 → NativeJordanFrame)
    (s : Fin 4 → Fin 3 × Fin 3) :
    ∃ Q : QuaternionicWindow, ∀ i, (F (s i).1).atom (s i).2 ∈ Q.subalgebra.carrier := by
  let p : Fin 4 → Albert := fun i => (F (s i).1).atom (s i).2
  have hp (i : Fin 4) : IsAtom (p i) := (F (s i).1).atoms (s i).2
  have h : ¬ Function.Injective (fun i => (s i).1) := by
    intro hi
    have hc := Fintype.card_le_of_injective _ hi
    simp at hc
  obtain ⟨i, j, hrow, hij⟩ := Function.not_injective_iff.mp h
  apply lemma_A_degenerate p hp
  refine ⟨i, j, hij, ?_⟩
  by_cases hcol : (s i).2 = (s j).2
  · exact Or.inl (by simp only [p, hrow, hcol])
  · right
    change jordanMul ((F (s i).1).atom (s i).2) ((F (s j).1).atom (s j).2) = 0
    rw [← hrow]
    exact (F (s i).1).orthogonal _ _ hcol

theorem fourPointInvariant_from_three_frames_zero (F : Fin 3 → NativeJordanFrame)
    (s : Fin 4 → Fin 3 × Fin 3) :
    fourPointInvariant (fun i => (F (s i).1).atom (s i).2) = 0 :=
  (fourPointInvariant_eq_zero_iff _ (fun i => (F (s i).1).atoms (s i).2)).mpr
    (four_atoms_from_three_frames_contained F s)

end AlbertSequential
