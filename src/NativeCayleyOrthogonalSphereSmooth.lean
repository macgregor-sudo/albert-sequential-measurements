/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCayleyOrthogonalSphere

/-! The standard analytic sphere embeds in the checked native Cayley atlas. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.NativeCayley

open Function Metric NativeAnalysis Set Topology WindowProbability
open scoped ContDiff Manifold

local instance : Fact (Module.finrank ℝ OrthogonalSphereAmbient = 8 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The orthogonal sphere included in the native atom space with its original topology. -/
def orthogonalSphereAtom (p : AlbertAtomSpace) (x : OrthogonalSphere) : AlbertAtomSpace :=
  ((orthogonalAtomSphere p).symm x).val

theorem orthogonalSphereAtom_val (p : AlbertAtomSpace) (x : OrthogonalSphere) :
    (orthogonalSphereAtom p x).val =
      (chosenAtomNormalizer p.val p.property).linearEquiv.symm (orthogonalSphereEmbedding x.val) :=
  rfl

theorem range_orthogonalSphereAtom (p : AlbertAtomSpace) :
    range (orthogonalSphereAtom p) = orthogonalAtomLocus p := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ((orthogonalAtomSphere p).symm x).property
  · intro hq
    use orthogonalAtomSphere p ⟨q, hq⟩
    exact congrArg Subtype.val ((orthogonalAtomSphere p).symm_apply_apply ⟨q, hq⟩)

theorem isClosedEmbedding_orthogonalSphereAtom (p : AlbertAtomSpace) :
    IsClosedEmbedding (orthogonalSphereAtom p) :=
  (isClosed_orthogonalAtomLocus p).isClosedEmbedding_subtypeVal.comp (orthogonalAtomSphere p).symm.isClosedEmbedding

/-- Subtype inclusion of the actual native analytic atom space into the native Albert vector space. -/
theorem contMDiff_nativeAtom_val :
    ContMDiff (𝓘(ℝ, CayleyModel)) (𝓘(ℝ, Albert)) ω (Subtype.val : AlbertAtomSpace → Albert) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  intro p x
  have h := contDiff_chartEmbedding (Classical.choose (exists_positive_pivot p)) (n := ω)
  rw [extChartAt_model_space_eq_id]
  change ContDiffOn ℝ ω (chartEmbedding (Classical.choose (exists_positive_pivot p))) _
  exact h.contDiffOn

/-- Real analyticity into the actual atlas, using the ordinary stereographic sphere structure. -/
theorem contMDiff_orthogonalSphereAtom (p : AlbertAtomSpace) :
    ContMDiff (𝓡 8) (𝓘(ℝ, CayleyModel)) ω (orthogonalSphereAtom p) := by
  let g := (chosenAtomNormalizer p.val p.property).linearEquiv.symm.toContinuousLinearEquiv
  let f := fun x : OrthogonalSphere => g (orthogonalSphereEmbedding x.val)
  have hSphere : ContMDiff (𝓡 8) (𝓘(ℝ, OrthogonalSphereAmbient)) ω
      (Subtype.val : OrthogonalSphere → OrthogonalSphereAmbient) := contMDiff_coe_sphere
  have hf : ContMDiff (𝓡 8) (𝓘(ℝ, Albert)) ω f :=
    (g.toContinuousLinearMap.contDiff.comp contDiff_orthogonalSphereEmbedding).contMDiff.comp hSphere
  rw [contMDiff_iff_target]
  refine ⟨continuous_subtype_val.comp (orthogonalAtomSphere p).symm.continuous, ?_⟩
  intro q
  rw [extChartAt_source]
  let i := Classical.choose (exists_positive_pivot q)
  change ContMDiffOn (𝓡 8) (𝓘(ℝ, CayleyModel)) ω (chartCoordinates i ∘ f)
    (f ⁻¹' {a : Albert | 0 < a.1 i})
  exact (contDiffOn_chartCoordinates i (n := ω)).contMDiffOn.comp hf.contMDiffOn (fun _ hx => hx)

/-- The analytic parametrization has injective manifold derivative at every point. -/
theorem mfderiv_orthogonalSphereAtom_injective (p : AlbertAtomSpace) (x : OrthogonalSphere) :
    Injective (mfderiv (𝓡 8) (𝓘(ℝ, CayleyModel)) (orthogonalSphereAtom p) x) := by
  let g := (chosenAtomNormalizer p.val p.property).linearEquiv.toContinuousLinearEquiv
  let f := fun q : AlbertAtomSpace => orthogonalSphereCoordinates (g q.val)
  have hfa : ContMDiff (𝓘(ℝ, CayleyModel)) (𝓘(ℝ, OrthogonalSphereAmbient)) ω f :=
    (contDiff_orthogonalSphereCoordinates.comp g.toContinuousLinearMap.contDiff).contMDiff.comp
      contMDiff_nativeAtom_val
  have he : f ∘ orthogonalSphereAtom p = (Subtype.val : OrthogonalSphere → OrthogonalSphereAmbient) := by
    funext y
    change orthogonalSphereCoordinates ((chosenAtomNormalizer p.val p.property).linearEquiv
      (orthogonalSphereAtom p y).val) = y.val
    rw [orthogonalSphereAtom_val, LinearEquiv.apply_symm_apply, orthogonalSphereCoordinates_embedding]
  have hComp :
      mfderiv (𝓡 8) (𝓘(ℝ, OrthogonalSphereAmbient)) (f ∘ orthogonalSphereAtom p) x =
        (mfderiv (𝓘(ℝ, CayleyModel)) (𝓘(ℝ, OrthogonalSphereAmbient)) f (orthogonalSphereAtom p x)).comp
          (mfderiv (𝓡 8) (𝓘(ℝ, CayleyModel)) (orthogonalSphereAtom p) x) :=
    mfderiv_comp x (hfa.mdifferentiableAt (by simp))
      ((contMDiff_orthogonalSphereAtom p).mdifferentiableAt (by simp))
  have hSphere : Injective (mfderiv (𝓡 8) (𝓘(ℝ, OrthogonalSphereAmbient))
      (Subtype.val : OrthogonalSphere → OrthogonalSphereAmbient) x) := by
    convert! injective_mvfderiv_subtypeVal_sphere (n := 8) x
  intro a b hab
  apply hSphere
  rw [← he, hComp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hab]

end AlbertSequential.NativeCayley
