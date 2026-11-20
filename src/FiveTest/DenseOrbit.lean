/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilityAlbertGroup
public import NativeReflectionOrbit
public import ComplexWindowDeterminantAndMax

@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis WindowProbability

private theorem fourPointOmegaPoly_continuous {X : Type*} [TopologicalSpace X]
    (a b c d e f g h i j k l m : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (he : Continuous e) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hi : Continuous i) (hj : Continuous j) (hk : Continuous k) (hl : Continuous l) (hm : Continuous m) :
    Continuous (fun x => fourPointOmegaPoly (a x) (b x) (c x) (d x) (e x) (f x)
      (g x) (h x) (i x) (j x) (k x) (l x) (m x)) := by
  unfold fourPointOmegaPoly
  fun_prop

private theorem fpOverlap_continuous (i j : Fin 4) :
    Continuous (fun p : Fin 4 → Albert => fpOverlap p i j) := by
  have h : Continuous (fun p : Fin 4 → Albert => (p i,p j)) := (continuous_apply i).prodMk (continuous_apply j)
  exact (continuous_tracePairing.comp h).congr (fun _ => rfl)

private theorem products_continuous (i j : Fin 4) :
    Continuous (fun p : Fin 4 → Albert => jordanMul (p i) (p j)) := by
  have h : Continuous (fun p : Fin 4 → Albert => (p i,p j)) := (continuous_apply i).prodMk (continuous_apply j)
  exact (continuous_jordanMul.comp h).congr (fun _ => rfl)

private theorem fpTriangle_continuous (i j k : Fin 4) :
    Continuous (fun p : Fin 4 → Albert => fpTriangle p i j k) := by
  have h : Continuous (fun p : Fin 4 → Albert => (jordanMul (p i) (p j), p k)) := (products_continuous i j).prodMk (continuous_apply k)
  exact (continuous_tracePairing.comp h).congr (fun _ => rfl)

private theorem fpDouble_continuous (i j k l : Fin 4) :
    Continuous (fun p : Fin 4 → Albert => tracePairing (jordanMul (p i) (p j)) (jordanMul (p k) (p l))) := by
  have h : Continuous (fun p : Fin 4 → Albert => (jordanMul (p i) (p j), jordanMul (p k) (p l))) := (products_continuous i j).prodMk (products_continuous k l)
  exact (continuous_tracePairing.comp h).congr (fun _ => rfl)

theorem continuous_fourPointInvariant : Continuous fourPointInvariant := by
  have d1 : Continuous fpDoublePair1 := fpDouble_continuous 0 1 2 3
  have d2 : Continuous fpDoublePair2 := fpDouble_continuous 0 2 1 3
  have d3 : Continuous fpDoublePair3 := fpDouble_continuous 0 3 1 2
  unfold fourPointInvariant
  apply fourPointOmegaPoly_continuous
  · exact fpOverlap_continuous 0 1
  · exact fpOverlap_continuous 0 2
  · exact fpOverlap_continuous 0 3
  · exact fpOverlap_continuous 1 2
  · exact fpOverlap_continuous 1 3
  · exact fpOverlap_continuous 2 3
  · exact fpTriangle_continuous 0 1 2
  · exact fpTriangle_continuous 0 1 3
  · exact fpTriangle_continuous 0 2 3
  · exact fpTriangle_continuous 1 2 3
  · exact (d2.add d3).sub d1
  · exact (d1.add d3).sub d2
  · exact (d1.add d2).sub d3

open scoped WindowProbability
local instance : NormedAddCommGroup Octonion := inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion := inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert := inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert := inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

/-- A dense range of finite reflection words gives four actual finite orbit
labels with positive invariant, from just one seed in the generating menu. -/
theorem exists_positive_reflection_quad_of_dense {I : Type*} (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (i : I) (hd : DenseRange (X := AlbertAutomorphismGroup) (fun w : List I =>
      (nativeAutoToCompactAuto (nativeReflectionWordAutomorphism p hp w) : AlbertAutomorphismGroup))) :
    ∃ w : Fin 4 → List I, 0 < fourPointInvariant (fun k => nativeOrbitPoint p hp (w k,i)) := by
  let s : AlbertAtomSpace := ⟨p i,hp i⟩
  obtain ⟨g,hg⟩ := albertAtomAction_transitive s
  choose h hh using fun k => albertAtomAction_transitive (⟨maximizerConfig k,maximizerConfig_isAtom k⟩ : AlbertAtomSpace)
  let F := fun u : Fin 4 → AlbertAutomorphismGroup => fourPointInvariant (fun k => albertAutAction (u k) (p i))
  have hc : Continuous F := by
    apply continuous_fourPointInvariant.comp
    apply continuous_pi
    intro k
    have hg : Continuous (fun u : Fin 4 → AlbertAutomorphismGroup =>
        (u k, recoveredCoordinateEquiv (p i))) := (continuous_apply k).prodMk continuous_const
    exact recoveredCoordinateEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp
      (AlbertAutomorphismGroup.continuous_evaluation.comp hg)
  have hseed (k : Fin 4) : albertAutAction (h k * g⁻¹) (p i) = maximizerConfig k := by
    change ((h k * g⁻¹) • s).val = _
    rw [← hg,mul_smul,inv_smul_smul,hh]
  have he : 0 < F (fun k => h k * g⁻¹) := by
    simp only [F,hseed,fourPointInvariant_maximizerConfig]
    norm_num
  have hprod := DenseRange.piMap (Y := fun _ : Fin 4 => AlbertAutomorphismGroup) (fun _ => hd)
  obtain ⟨w,hw⟩ := hprod.exists_mem_open (isOpen_lt continuous_const hc) ⟨_,he⟩
  refine ⟨w,?_⟩
  change 0 < fourPointInvariant (fun k => recoveredCoordinateEquiv.symm
    ((nativeAutoToCompactAuto (nativeReflectionWordAutomorphism p hp (w k))).equiv
    (recoveredCoordinateEquiv (p i)))) at hw
  simpa only [nativeAutoToCompactAuto_apply,LinearEquiv.symm_apply_apply,nativeOrbitPoint] using hw

end AlbertSequential
