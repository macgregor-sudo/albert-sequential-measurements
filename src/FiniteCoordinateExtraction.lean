/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompactConstraints

/-! Compactness extracts one common finite coordinate set for all pairs.
This is not a pointwise choice of a separating coordinate or a native no-go. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem exists_finite_distinguishing_coordinates
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {L : Set Y} (hK : IsCompact K) (hL : IsCompact L)
    (f : I → X → ℝ) (g : I → Y → ℝ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (hnone : ∀ x ∈ K, ∀ y ∈ L, ∃ i, f i x ≠ g i y) :
    ∃ F : Finset I, ∀ x ∈ K, ∀ y ∈ L, ∃ i ∈ F, f i x ≠ g i y := by
  classical
  obtain ⟨F, δ, hδ, hF⟩ := exists_finite_positive_error_gap (hK.prod hL)
    (fun i (z : X × Y) => f i z.1 - g i z.2)
    (fun i => (hf i).comp continuous_fst |>.sub ((hg i).comp continuous_snd))
    (fun _ => 0) (by
      rintro ⟨⟨x,y⟩, hxy, heq⟩
      obtain ⟨i, hi⟩ := hnone x hxy.1 y hxy.2
      exact hi (sub_eq_zero.mp (heq i)))
  refine ⟨F, fun x hx y hy => ?_⟩
  obtain ⟨i, hi, hbound⟩ := hF (x,y) ⟨hx,hy⟩
  refine ⟨i, hi, fun heq => ?_⟩
  have hbad : δ ≤ 0 := by simpa [heq] using hbound
  exact (not_le_of_gt hδ) hbad

theorem exists_finite_distinguishing_coordinates_containing
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {L : Set Y} (hK : IsCompact K) (hL : IsCompact L)
    (f : I → X → ℝ) (g : I → Y → ℝ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (hnone : ∀ x ∈ K, ∀ y ∈ L, ∃ i, f i x ≠ g i y) (e : I) :
    ∃ F : Finset I, e ∈ F ∧
      ∀ x ∈ K, ∀ y ∈ L, ∃ i ∈ F, f i x ≠ g i y := by
  classical
  obtain ⟨F,hF⟩ := exists_finite_distinguishing_coordinates hK hL f g hf hg hnone
  refine ⟨insert e F, Finset.mem_insert_self _ _, fun x hx y hy => ?_⟩
  obtain ⟨i,hi,hne⟩ := hF x hx y hy
  exact ⟨i,Finset.mem_insert_of_mem hi,hne⟩

theorem disjoint_coordinate_images_of_distinguishing
    {X Y I : Type*} (K : Set X) (L : Set Y)
    (f : I → X → ℝ) (g : I → Y → ℝ) (F : Finset I)
    (hF : ∀ x ∈ K, ∀ y ∈ L, ∃ i ∈ F, f i x ≠ g i y) :
    Disjoint ((fun x => fun i : F => f i x) '' K)
      ((fun y => fun i : F => g i y) '' L) := by
  rw [Set.disjoint_left]
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  obtain ⟨i,hi,hne⟩ := hF x hx y hy
  exact hne (congrFun heq ⟨i,hi⟩).symm

end AlbertSequential
