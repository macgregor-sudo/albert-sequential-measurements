/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedKrausFamilies
public import KrausCertaintySupport

/-! The yes effect is identity on a chosen reset tag and zero on the chosen
no tag. The resulting support claim holds on all input matrices. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential
variable {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]

theorem taggedKrausList_effect_inclusion (t : T) (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜)) (s : T) :
    rectangularKrausEffect (taggedKrausList t K) * taggedBlockInclusion (ι := ι) s =
      taggedBlockInclusion (ι := ι) s * rectangularKrausEffect (K s) := by
  rw [taggedKrausList_effect, Matrix.sum_mul, Finset.sum_eq_single s]
  · simp only [Matrix.mul_assoc, taggedBlockInclusion_same, Matrix.mul_one]
  · intro u _ hus
    simp only [Matrix.mul_assoc, taggedBlockInclusion_distinct u s hus, Matrix.mul_zero]
  · simp

theorem mem_taggedKrausList (t : T) (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜))
    (V : Matrix (Sigma ι) (Sigma ι) 𝕜) (hV : V ∈ taggedKrausList t K) :
    ∃ s, ∃ A ∈ K s, V = taggedBlockKraus s t A := by
  obtain ⟨L,hL,hV⟩ := List.mem_flatten.mp hV
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hL
  obtain ⟨A,hA,hAV⟩ := List.mem_map.mp hV
  exact ⟨s,A,hA,hAV.symm⟩

theorem taggedKrausList_certainty_support (t u : T)
    (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜)) (L : ∀ s, List (Matrix (ι u) (ι s) 𝕜))
    (ht : rectangularKrausEffect (K t) = 1) (hu : rectangularKrausEffect (K u) = 0) :
    (∀ V ∈ taggedKrausList t K, rectangularKrausEffect (taggedKrausList t K) * V = V) ∧
    (∀ V ∈ taggedKrausList u L, rectangularKrausEffect (taggedKrausList t K) * V = 0) := by
  constructor
  · intro V hV
    obtain ⟨s,A,_,rfl⟩ := mem_taggedKrausList t K V hV
    simp only [taggedBlockKraus, ← Matrix.mul_assoc]
    rw [taggedKrausList_effect_inclusion t K t, ht, Matrix.mul_one]
  · intro V hV
    obtain ⟨s,A,_,rfl⟩ := mem_taggedKrausList u L V hV
    simp only [taggedBlockKraus, ← Matrix.mul_assoc]
    rw [taggedKrausList_effect_inclusion t K u, hu, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.zero_mul]

end AlbertSequential
