/- SPDX-License-Identifier: Apache-2.0 -/
module
public import OptimalSpectralFrames
public import BinaryKrausDilation

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder

/-- Least number of ancillary coordinates for the menu's sharp outcome projections. -/
def menuDefectRank {d : ℕ} {X : Type*} [Fintype X] (A : X → ComplexMatrix d) : ℕ :=
  Finset.univ.sup (fun x => (A x - A x ^ 2).rank)

theorem simultaneousCornerProjections_iff {d m : ℕ} {X : Type*} [Fintype X]
    (A : X → ComplexMatrix d) (hA : ∀ x, (A x).PosSemidef)
    (hAc : ∀ x, (1 - A x).PosSemidef) :
    (let J : Matrix (Fin d ⊕ Fin m) (Fin d) ℂ := fromRows 1 0
     ∃ P : X → Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℂ, ∀ x,
       (P x)ᴴ = P x ∧ P x * P x = P x ∧ Jᴴ * P x * J = A x) ↔ menuDefectRank A ≤ m := by
  classical
  constructor
  · rintro ⟨P,hP⟩
    apply Finset.sup_le
    intro x _
    obtain ⟨_,hp,hc⟩ := hP x
    rw [sharpDilation_firstSummand_compression] at hc
    simpa only [hc] using sharpDilation_defect_rank_le (P x) hp
  · intro h
    have hx (x : X) : (A x - A x ^ 2).rank ≤ Fintype.card (Fin m) := by
      rw [Fintype.card_fin]
      exact (Finset.le_sup (f := fun y => (A y - A y ^ 2).rank) (Finset.mem_univ x)).trans h
    choose P hP using fun x => exists_optimalSpectralFrames (hA x) (hAc x) (hx x)
    exact ⟨P, fun x => ⟨(hP x).1,(hP x).2.1,(hP x).2.2.1⟩⟩

end AlbertSequential
