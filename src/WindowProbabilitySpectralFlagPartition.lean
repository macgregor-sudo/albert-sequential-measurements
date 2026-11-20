/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlagCharts
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Function ENNReal

def translatedSpectralAngularFlag (U : SpectralUnitary) (v : Fin 6 → ℝ) : SpectralFlag :=
  spectralFlagTranslate U (spectralAngularFlag v)

theorem continuous_translatedSpectralAngularFlag (U : SpectralUnitary) :
    Continuous (translatedSpectralAngularFlag U) :=
  (spectralFlagTranslate U).continuous.comp continuous_spectralAngularFlag

theorem translatedSpectralAngularFlag_unitary (U : SpectralUnitary) (v : Fin 6 → ℝ) :
    translatedSpectralAngularFlag U v =
      spectralFlagOfUnitary (U * spectralExpUnitary (spectralAngularOffsets v)) :=
  spectralFlag_smul_unitary _ _

theorem isOpen_translatedSpectralAngularImage (C : SpectralAngularChart) (U : SpectralUnitary) :
    IsOpen (translatedSpectralAngularFlag U '' C.source) := by
  change IsOpen ((spectralFlagTranslate U ∘ spectralAngularFlag) '' C.source)
  rw [Set.image_comp]
  exact (spectralFlagTranslate U).isOpenMap _ C.openImage

/-- A finite, disjoint Borel partition by subsets of the fixed angular chart's translates. -/
structure SpectralAngularPartition (C : SpectralAngularChart) where
  count : ℕ
  translate : Fin count → SpectralUnitary
  patch : Fin count → Set SpectralFlag
  measurablePatch : ∀ i, MeasurableSet (patch i)
  patch_subset : ∀ i, patch i ⊆ translatedSpectralAngularFlag (translate i) '' C.source
  covers : (⋃ i, patch i) = univ
  disjoint : Pairwise (Disjoint on patch)

theorem exists_spectralAngularPartition (C : SpectralAngularChart) : Nonempty (SpectralAngularPartition C) := by
  classical
  let patch (U : SpectralUnitary) := translatedSpectralAngularFlag U '' C.source
  have hcover : (Set.univ : Set SpectralFlag) ⊆ ⋃ U, patch U := by
    intro F _
    obtain ⟨U, hU⟩ := spectralFlag_transitive F
    apply mem_iUnion.mpr
    refine ⟨U, 0, C.zeroMem, ?_⟩
    change U • spectralAngularFlag 0 = F
    rwa [spectralAngularFlag_zero]
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover patch
    (isOpen_translatedSpectralAngularImage C) hcover
  let e := (Fintype.equivFin s).symm
  let U (i : Fin (Fintype.card s)) : SpectralUnitary := (e i).val
  let Q (i : Fin (Fintype.card s)) : Set SpectralFlag := patch (U i)
  let P (i : Fin (Fintype.card s)) : Set SpectralFlag := Q i \ ⋃ j, ⋃ _ : j < i, Q j
  have hQcover (F : SpectralFlag) : ∃ i, F ∈ Q i := by
    have h := hs (mem_univ F)
    obtain ⟨V, hV⟩ := mem_iUnion.mp h
    obtain ⟨hVs, hV⟩ := mem_iUnion.mp hV
    refine ⟨e.symm ⟨V, hVs⟩, ?_⟩
    simpa only [Q, U, Equiv.apply_symm_apply] using hV
  refine ⟨⟨_, U, P, ?_, fun _ => sdiff_subset, ?_, ?_⟩⟩
  · intro i
    have hQ (j : Fin (Fintype.card s)) : MeasurableSet (Q j) :=
      (isOpen_translatedSpectralAngularImage C (U j)).measurableSet
    exact (hQ i).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hQ j)
  · refine eq_univ_iff_forall.mpr fun F => ?_
    let t := Finset.univ.filter (fun i => F ∈ Q i)
    obtain ⟨i, hi⟩ := hQcover F
    have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let j := t.min' ht
    have hj : F ∈ Q j := (Finset.mem_filter.mp (t.min'_mem ht)).2
    apply mem_iUnion.mpr
    refine ⟨j, hj, ?_⟩
    intro h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    obtain ⟨hklt, hk⟩ := mem_iUnion.mp hk
    have hkt : k ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact (not_lt_of_ge (t.min'_le _ hkt)) hklt
  · intro i j hij
    apply disjoint_left.mpr
    intro F hi hj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hj.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hlt, hi.1⟩⟩)
    · exact hi.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hlt, hj.1⟩⟩)

namespace SpectralAngularPartition

variable {C : SpectralAngularChart} (A : SpectralAngularPartition C)

/-- The actual angular parameter domain for one measurable patch. -/
def domain (i : Fin A.count) : Set (Fin 6 → ℝ) :=
  C.source ∩ translatedSpectralAngularFlag (A.translate i) ⁻¹' A.patch i

theorem measurableSet_domain (i : Fin A.count) : MeasurableSet (A.domain i) :=
  C.openSource.measurableSet.inter ((continuous_translatedSpectralAngularFlag _).measurable (A.measurablePatch i))

theorem domain_subset_ball (i : Fin A.count) : A.domain i ⊆ Metric.ball 0 1 :=
  inter_subset_left.trans C.source_ball

theorem image_domain (i : Fin A.count) : translatedSpectralAngularFlag (A.translate i) '' A.domain i = A.patch i := by
  ext F
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv.2
  · intro hF
    obtain ⟨v, hv, rfl⟩ := A.patch_subset i hF
    exact ⟨v, ⟨hv,hF⟩, rfl⟩

theorem injOn_domain (i : Fin A.count) : InjOn (translatedSpectralAngularFlag (A.translate i)) (A.domain i) := by
  intro v hv w hw h
  exact C.leftInverse.injOn hv.1 hw.1 ((spectralFlagTranslate _).injective h)

theorem lintegral_partition (μ : Measure SpectralFlag) (f : SpectralFlag → ℝ≥0∞) :
    (∫⁻ F, f F ∂μ) = ∑ i, ∫⁻ F in A.patch i, f F ∂μ := by
  simpa only [A.covers, Measure.restrict_univ, tsum_fintype] using
    (lintegral_iUnion (μ := μ) A.measurablePatch A.disjoint f)

end SpectralAngularPartition
end AlbertSequential.WindowProbability
