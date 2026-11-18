/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneratedAlbertOperations

/-! Actual native word effects span the entire generated Jordan subalgebra.
From e/3 the forward branch is one third of the effect of the reversed word;
this exact chronology is the source of the finite Hankel Gram witness.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

def nativeWordEffectSpan {ι : Type*} (p : ι → Albert) : Submodule ℝ Albert :=
  Submodule.span ℝ (Set.range (nativeWordEffect p))

theorem nativeWordEffect_mem_span {ι : Type*} (p : ι → Albert) (w : Word ι) :
    nativeWordEffect p w ∈ nativeWordEffectSpan p := Submodule.subset_span ⟨w, rfl⟩

theorem nativeWordEffectSpan_outcome {ι : Type*} (p : ι → Albert) (a : Outcome ι)
    {x : Albert} (hx : x ∈ nativeWordEffectSpan p) :
    quadraticMap (nativeOutcome p a) x ∈ nativeWordEffectSpan p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨w, rfl⟩
      exact nativeWordEffect_mem_span p (a :: w)
  | zero => simpa only [quadraticMap_zero_right] using (nativeWordEffectSpan p).zero_mem
  | add x y hx hy ihx ihy =>
      rw [quadraticMap_add_right]
      exact (nativeWordEffectSpan p).add_mem ihx ihy
  | smul r x hx ih =>
      rw [quadraticMap_smul_right]
      exact (nativeWordEffectSpan p).smul_mem r ih

theorem nativeWordEffectSpan_reflection {ι : Type*} (p : ι → Albert) (i : ι)
    {x : Albert} (hx : x ∈ nativeWordEffectSpan p) :
    quadraticMap ((2 : ℝ) • p i - albertUnit) x ∈ nativeWordEffectSpan p := by
  rw [quadraticMap_symmetry]
  exact (nativeWordEffectSpan p).sub_mem ((nativeWordEffectSpan p).smul_mem (2 : ℝ)
    ((nativeWordEffectSpan p).add_mem
      (nativeWordEffectSpan_outcome p (i, true) hx)
      (nativeWordEffectSpan_outcome p (i, false) hx))) hx

theorem nativeReflectionWord_mem_effectSpan {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (g : List ι) {x : Albert} (hx : x ∈ nativeWordEffectSpan p) :
    (nativeReflectionWordAutomorphism p hp g).linearEquiv x ∈ nativeWordEffectSpan p := by
  induction g with
  | nil => exact hx
  | cons i g ih =>
      simp only [nativeReflectionWordAutomorphism, nativeAutomorphismComposition_apply,
        atomReflectionAutomorphism_apply]
      exact nativeWordEffectSpan_reflection p i ih

theorem nativeOrbitPoint_mem_effectSpan {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (α : ReflectionOrbitLabel ι) :
    nativeOrbitPoint p hp α ∈ nativeWordEffectSpan p := by
  apply nativeReflectionWord_mem_effectSpan p hp
  simpa only [nativeWordEffect, nativeOutcome, ↓reduceIte, nativeAtom_quadratic_unit _ (hp α.2)] using
    nativeWordEffect_mem_span p [(α.2, true)]

theorem nativeWordEffectSpan_eq_generated {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) : nativeWordEffectSpan p = nativeOrbitSpan p hp := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact nativeWordEffect_mem_orbitSpan p hp w
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | none => exact nativeWordEffect_mem_span p []
    | some α => exact nativeOrbitPoint_mem_effectSpan p hp α

theorem nativeWordEffectSpan_eq_top {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) : nativeWordEffectSpan p = ⊤ := by
  rw [nativeWordEffectSpan_eq_generated p hp, nativeOrbitSpan_eq_top_of_generates p hp hg]

theorem nativeBranchState_e3_reverse {ι : Type*} (p : ι → Albert) (w : Word ι) :
    nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 3 : ℝ) • nativeWordEffect p w.reverse := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [nativeBranchState_append, List.reverse_append, List.reverse_singleton, List.singleton_append]
      change quadraticMap (nativeOutcome p a)
        (nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w) =
          (1 / 3 : ℝ) • quadraticMap (nativeOutcome p a) (nativeWordEffect p w.reverse)
      rw [ih, quadraticMap_smul_right]

theorem nativeWordProbability_append_pairing {ι : Type*} (p : ι → Albert)
    (ρ : Albert) (u v : Word ι) :
    nativeWordProbability p ρ (u ++ v) =
      tracePairing (nativeBranchState p ρ u) (nativeWordEffect p v) := by
  change albertTrace (nativeBranchState p ρ (u ++ v)) = _
  rw [nativeBranchState_append]
  exact nativeWordProbability_eq_pairing p _ v

theorem nativeHankel_e3_pairing {ι : Type*} (p : ι → Albert) (u v : Word ι) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (u ++ v) =
      (1 / 3 : ℝ) * tracePairing (nativeWordEffect p u.reverse) (nativeWordEffect p v) := by
  rw [nativeWordProbability_append_pairing, nativeBranchState_e3_reverse, tracePairing_smul_left]

end AlbertSequential
