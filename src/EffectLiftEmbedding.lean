/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SequentialEffectLifts

/-!
Finite word lifts commute with injective linear embeddings of the native
effect space. This lets reconstruction use the actual generated subalgebra
without assuming that it fills the whole Albert algebra.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Embedding
variable {ι A J K : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J] [AddCommGroup K] [Module ℝ K]

theorem sequentialEffectLift_map_native (P : ι → A) (θ : Word ι → J) (H : J →ₗ[ℝ] K)
    {Z : A} {x : J} (h : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P (fun w => H (θ w)) Z (H x) := by
  have hall : ∀ z ∈ sequentialEffectLiftSpace P θ,
      HasSequentialEffectLift P (fun w => H (θ w)) z.1 (H z.2) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => rcases hz with ⟨w, rfl⟩; exact hasSequentialEffectLift_word P _ w
    | zero => simpa only [Prod.fst_zero, Prod.snd_zero, map_zero] using hasSequentialEffectLift_zero P _
    | add z y hz hy ihz ihy =>
        simpa only [Prod.fst_add, Prod.snd_add, map_add] using hasSequentialEffectLift_add P _ ihz ihy
    | smul r z hz ih =>
        simpa only [Prod.smul_fst, Prod.smul_snd, map_smul] using hasSequentialEffectLift_smul P _ r ih
  exact hall (Z, x) h

theorem sequentialEffectLift_of_injective_native (P : ι → A) (θ : Word ι → J)
    (H : J →ₗ[ℝ] K) (hH : Function.Injective H) {Z : A} {x : J}
    (h : HasSequentialEffectLift P (fun w => H (θ w)) Z (H x)) :
    HasSequentialEffectLift P θ Z x := by
  have hall : ∀ z ∈ sequentialEffectLiftSpace P (fun w => H (θ w)),
      ∃ y : J, HasSequentialEffectLift P θ z.1 y ∧ H y = z.2 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨w, rfl⟩
        exact ⟨θ w, hasSequentialEffectLift_word P θ w, rfl⟩
    | zero => exact ⟨0, hasSequentialEffectLift_zero P θ, map_zero H⟩
    | add z y hz hy ihz ihy =>
        rcases ihz with ⟨u, hu, he⟩
        rcases ihy with ⟨v, hv, hf⟩
        exact ⟨u + v, hasSequentialEffectLift_add P θ hu hv, by rw [map_add, he, hf]; rfl⟩
    | smul r z hz ih =>
        rcases ih with ⟨u, hu, he⟩
        exact ⟨r • u, hasSequentialEffectLift_smul P θ r hu, by rw [map_smul, he]; rfl⟩
  obtain ⟨y, hy, he⟩ := hall (Z, H x) h
  have hyx : y = x := hH he
  simpa only [hyx] using hy

end Embedding
end AlbertSequential
