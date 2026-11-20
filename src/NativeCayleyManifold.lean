/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeCayleyChart
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.NativeCayley

open WindowProbability NativeAnalysis Set Function
open scoped Manifold ContDiff

/-- All sixteen real coordinates of an affine pair of octonions. -/
abbrev CayleyModel := Fin 16 → ℝ

def affineRealCoordinates : AffineCoordinates ≃L[ℝ] CayleyModel :=
  (octonionPairCoordinates.trans (LinearEquiv.piCongrLeft' ℝ (fun _ => ℝ)
    (Fintype.equivFinOfCardEq spinorCoordinate_card))).toContinuousLinearEquiv

def pivotRegion (i : Fin 3) : Set AlbertAtomSpace := {p | 0 < p.val.1 i}

theorem isOpen_pivotRegion (i : Fin 3) : IsOpen (pivotRegion i) :=
  isOpen_lt continuous_const (((continuous_apply i).comp continuous_fst).comp continuous_subtype_val)

/-- From the native ambient carrier to the coordinates at the selected pivot. -/
def chartCoordinates (i : Fin 3) (p : Albert) : CayleyModel :=
  affineRealCoordinates (firstPivotCoordinates ((pivotAutomorphism i).linearEquiv p))

/-- The actual Albert element underlying the inverse chart. -/
def chartEmbedding (i : Fin 3) (x : CayleyModel) : Albert :=
  (pivotAutomorphism i).linearEquiv.symm (affineAtomEmbedding (affineRealCoordinates.symm x))

theorem contDiffOn_chartCoordinates (i : Fin 3) {n : ℕ∞ω} :
    ContDiffOn ℝ n (chartCoordinates i) {p : Albert | 0 < p.1 i} := by
  have h := (pivotAutomorphism i).linearEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    (n := n)
  refine affineRealCoordinates.toContinuousLinearMap.contDiff.comp_contDiffOn
    (contDiffOn_firstPivotCoordinates.comp h.contDiffOn ?_)
  intro p hp
  change 0 < ((pivotAutomorphism i).linearEquiv p).1 0
  rwa [pivotAutomorphism_first]

theorem contDiff_chartEmbedding (i : Fin 3) {n : ℕ∞ω} : ContDiff ℝ n (chartEmbedding i) :=
  (pivotAutomorphism i).linearEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    (contDiff_affineAtomEmbedding.comp affineRealCoordinates.symm.toContinuousLinearMap.contDiff)

theorem isAtom_chartEmbedding (i : Fin 3) (x : CayleyModel) : IsAtom (chartEmbedding i x) :=
  (pivotAutomorphism i).symm.map_isAtom (isAtom_affineAtomEmbedding _)

theorem chartEmbedding_pivot_pos (i : Fin 3) (x : CayleyModel) : 0 < (chartEmbedding i x).1 i := by
  rw [← pivotAutomorphism_first i (chartEmbedding i x)]
  unfold chartEmbedding
  rw [LinearEquiv.apply_symm_apply, affineAtomEmbedding_pivot]
  exact inv_pos.mpr (chartDyad_trace_pos _ _)

theorem chartCoordinates_chartEmbedding (i : Fin 3) (x : CayleyModel) :
    chartCoordinates i (chartEmbedding i x) = x := by
  unfold chartCoordinates chartEmbedding
  rw [LinearEquiv.apply_symm_apply, firstPivotCoordinates_affineAtomEmbedding,
    ContinuousLinearEquiv.apply_symm_apply]

theorem chartEmbedding_chartCoordinates (i : Fin 3) (p : AlbertAtomSpace) (hp : p ∈ pivotRegion i) :
    chartEmbedding i (chartCoordinates i p.val) = p.val := by
  unfold chartEmbedding chartCoordinates
  rw [ContinuousLinearEquiv.symm_apply_apply, affineAtomEmbedding_firstPivotCoordinates,
    LinearEquiv.symm_apply_apply]
  · exact (pivotAutomorphism i).map_isAtom p.property
  · rwa [pivotAutomorphism_first]

/-- The positive-pivot open chart, onto all sixteen real coordinates. -/
def pivotChart (i : Fin 3) : OpenPartialHomeomorph AlbertAtomSpace CayleyModel where
  toFun := fun p => chartCoordinates i p.val
  invFun := fun x => ⟨chartEmbedding i x, isAtom_chartEmbedding i x⟩
  source := pivotRegion i
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun x _ => chartEmbedding_pivot_pos i x
  left_inv' := fun p hp => Subtype.ext (chartEmbedding_chartCoordinates i p hp)
  right_inv' := fun x _ => chartCoordinates_chartEmbedding i x
  continuousOn_toFun := (contDiffOn_chartCoordinates i (n := 1)).continuousOn.comp
    continuous_subtype_val.continuousOn (fun _ hp => hp)
  continuousOn_invFun := ((contDiff_chartEmbedding i (n := 1)).continuous.subtype_mk
    (isAtom_chartEmbedding i)).continuousOn
  open_source := isOpen_pivotRegion i
  open_target := isOpen_univ

def pivotRegionHomeomorph (i : Fin 3) : (pivotRegion i : Type) ≃ₜ CayleyModel :=
  (pivotChart i).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ CayleyModel)

theorem iUnion_pivotChart_source : (⋃ i : Fin 3, (pivotChart i).source) = (univ : Set AlbertAtomSpace) := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨i, hi⟩ := exists_positive_pivot p
  exact mem_iUnion.mpr ⟨i, hi⟩

theorem contDiffOn_pivotChart_transition (i j : Fin 3) {n : ℕ∞ω} :
    ContDiffOn ℝ n ((pivotChart i).symm.trans (pivotChart j))
      ((pivotChart i).symm.trans (pivotChart j)).source := by
  change ContDiffOn ℝ n (chartCoordinates j ∘ chartEmbedding i) _
  refine (contDiffOn_chartCoordinates j).comp (contDiff_chartEmbedding i).contDiffOn ?_
  intro x hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  exact hx.2

instance instCayleyChartedSpace : ChartedSpace CayleyModel AlbertAtomSpace where
  atlas := range pivotChart
  chartAt := fun p => pivotChart (Classical.choose (exists_positive_pivot p))
  mem_chart_source := fun p => Classical.choose_spec (exists_positive_pivot p)
  chart_mem_atlas := fun p => mem_range_self (Classical.choose (exists_positive_pivot p))

/-- The native Cayley plane is a real-analytic manifold modeled on sixteen real coordinates. -/
instance instCayleyAnalyticManifold : IsManifold (𝓘(ℝ, CayleyModel)) ω AlbertAtomSpace := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
    preimage_id_eq, range_id, inter_univ, id_eq] using contDiffOn_pivotChart_transition i j (n := ω)

theorem cayleyModel_finrank : Module.finrank ℝ CayleyModel = 16 := by simp

theorem isCompact_nativeAtomSet : IsCompact {p : Albert | IsAtom p} := isCompact_atomSet

end AlbertSequential.NativeCayley
