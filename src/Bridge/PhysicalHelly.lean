/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Bridge.UniverseCriterion
public import Joins.Helly

@[expose] public section
noncomputable section
namespace AlbertChallenge.Bridge
open AlbertChallenge
universe v

theorem not_generates_iff_some_physical {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ Generates p ↔ ∃ ρ, IsDensity ρ ∧ HasClassIModel.{v} p ρ :=
  ((AlbertSequential.generatesAlbert_iff_generatedSubalgebra_eq_top _).symm.trans
    (generates_toT p)).not.symm.trans (proper_iff_hasClassIModel p hp)

theorem physical_helly {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    ((∃ ρ, IsDensity ρ ∧ HasClassIModel.{v} p ρ) ↔ ∀ ρ, IsDensity ρ → HasClassIModel.{v} p ρ) ∧
    ((∃ ρ, IsDensity ρ ∧ HasClassIModel.{v} p ρ) ↔
      ∀ s : Finset (Fin n), s.card ≤ 5 →
        ∃ ρ, IsDensity ρ ∧ HasClassIModel.{v} (p ∘ (s.orderEmbOfFin rfl)) ρ) := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro h ρ hd
    obtain ⟨d,M,_,hw⟩ := (printed_albert_criterion p hp).2.1.mp
      ((proper_iff_hasClassIModel p hp).mpr h) ρ hd
    exact hasClassIModel_of_finite p ρ M hw
  · intro h
    obtain ⟨ρ,hd⟩ := exists_isDensity
    exact ⟨ρ,hd,h ρ hd⟩
  · intro h s _
    exact (not_generates_iff_some_physical _ (fun i => hp _)).mp
      (not_generates_comp p _ ((not_generates_iff_some_physical p hp).mpr h))
  · intro h
    apply (not_generates_iff_some_physical p hp).mp
    apply not_generates_of_small p hp
    intro k hk f hf
    let s := Finset.univ.image f
    have hc : s.card ≤ 5 := (Finset.card_image_le.trans (by simpa using hk))
    have hs := (not_generates_iff_some_physical _ (fun i => hp (s.orderEmbOfFin rfl i))).mpr (h s hc)
    apply mt _ hs
    intro hg B hB
    apply hg B
    intro i
    have hi : f i ∈ (s : Set (Fin n)) := Finset.mem_image_of_mem f (Finset.mem_univ i)
    rw [← Finset.range_orderEmbOfFin s rfl] at hi
    obtain ⟨j,hj⟩ := hi
    simpa [Function.comp_apply,hj] using hB j

end AlbertChallenge.Bridge
