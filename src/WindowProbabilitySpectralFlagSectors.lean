/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlagPartition
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Function ENNReal Matrix Matrix.Norms.Frobenius

abbrev SpectralBlockCoordinates := (Fin 3 → ℝ) × (Fin 6 → ℝ)

def spectralAngularCoordinateBlock (U : SpectralUnitary) (q : SpectralBlockCoordinates) : Fin 9 → ℝ :=
  hermitianMatrixRealCoordinates (spectralFlagEvaluate q.1 (translatedSpectralAngularFlag U q.2))

theorem spectralAngularCoordinateBlock_apply (U : SpectralUnitary) (q : SpectralBlockCoordinates) :
    spectralAngularCoordinateBlock U q = hermitianMatrixRealCoordinates
      (spectralConjugate (U * spectralExpUnitary (spectralAngularOffsets q.2)) q.1) := by
  rw [spectralAngularCoordinateBlock, translatedSpectralAngularFlag_unitary, spectralFlagEvaluate_unitary]

theorem continuous_spectralAngularCoordinateBlock (U : SpectralUnitary) :
    Continuous (spectralAngularCoordinateBlock U) :=
  spectralMatrixOutput.continuous.comp (continuous_spectralFlagEvaluate.comp
    (continuous_fst.prodMk ((continuous_translatedSpectralAngularFlag U).comp continuous_snd)))

private theorem hermitian_coordinates_injective {X Y : ComplexMatrix3} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : hermitianMatrixRealCoordinates X = hermitianMatrixRealCoordinates Y) : X = Y :=
  congrArg Subtype.val (hermitianMatrixRealCoordinateEquiv.injective
    (show hermitianMatrixRealCoordinateEquiv ⟨X, hX⟩ = hermitianMatrixRealCoordinateEquiv ⟨Y, hY⟩ from h))

def spectralFlagCoordinateRegion (Ω : Set (Fin 3 → ℝ)) : Set (Fin 9 → ℝ) :=
  (fun p : (Fin 3 → ℝ) × SpectralFlag => hermitianMatrixRealCoordinates (spectralFlagEvaluate p.1 p.2)) ''
    (Ω ×ˢ (Set.univ : Set SpectralFlag))

namespace SpectralAngularPartition

variable {C : SpectralAngularChart} (A : SpectralAngularPartition C)

def coordinateSector (Ω : Set (Fin 3 → ℝ)) (i : Fin A.count) : Set (Fin 9 → ℝ) :=
  spectralAngularCoordinateBlock (A.translate i) '' (Ω ×ˢ A.domain i)

theorem coordinateBlock_injOn (Ω : Set (Fin 3 → ℝ)) (hΩ : ∀ c ∈ Ω, StrictAnti c) (i : Fin A.count) :
    InjOn (spectralAngularCoordinateBlock (A.translate i)) (Ω ×ˢ A.domain i) := by
  rintro ⟨c, v⟩ ⟨hc, hv⟩ ⟨d, w⟩ ⟨hd, hw⟩ h
  let F := translatedSpectralAngularFlag (A.translate i) v
  let G := translatedSpectralAngularFlag (A.translate i) w
  have hMat : spectralFlagEvaluate c F = spectralFlagEvaluate d G :=
    hermitian_coordinates_injective (spectralFlagEvaluate_isHermitian c F)
      (spectralFlagEvaluate_isHermitian d G) h
  have he : (c, F) = (d, G) := spectralFlagEvaluate_injective_of_strictAnti (hΩ c hc) (hΩ d hd) hMat
  have hc_eq : c = d := congrArg (fun z : (Fin 3 → ℝ) × SpectralFlag => z.1) he
  have hF_eq : F = G := congrArg (fun z : (Fin 3 → ℝ) × SpectralFlag => z.2) he
  exact Prod.ext hc_eq (A.injOn_domain i hv hw hF_eq)

theorem measurableSet_coordinateSector (Ω : Set (Fin 3 → ℝ)) (hΩ : MeasurableSet Ω)
    (hOrder : ∀ c ∈ Ω, StrictAnti c) (i : Fin A.count) : MeasurableSet (A.coordinateSector Ω i) :=
  (hΩ.prod (A.measurableSet_domain i)).image_of_continuousOn_injOn
    (continuous_spectralAngularCoordinateBlock _).continuousOn (A.coordinateBlock_injOn Ω hOrder i)

theorem disjoint_coordinateSectors (Ω : Set (Fin 3 → ℝ)) (hΩ : ∀ c ∈ Ω, StrictAnti c) :
    Pairwise (Disjoint on A.coordinateSector Ω) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨c, v⟩, ⟨hc, hv⟩, rfl⟩ := hx
  obtain ⟨⟨d, w⟩, ⟨hd, hw⟩, he⟩ := hy
  let F := translatedSpectralAngularFlag (A.translate i) v
  let G := translatedSpectralAngularFlag (A.translate j) w
  have hMat : spectralFlagEvaluate c F = spectralFlagEvaluate d G :=
    hermitian_coordinates_injective (spectralFlagEvaluate_isHermitian c F)
      (spectralFlagEvaluate_isHermitian d G) he.symm
  have hPair : (c,F) = (d,G) := spectralFlagEvaluate_injective_of_strictAnti (hΩ c hc) (hΩ d hd) hMat
  have hFlag : F = G := congrArg (fun z : (Fin 3 → ℝ) × SpectralFlag => z.2) hPair
  have hFj : F ∈ A.patch j := by
    rw [hFlag]
    exact hw.2
  exact disjoint_left.mp (A.disjoint hij) hv.2 hFj

theorem union_coordinateSectors (Ω : Set (Fin 3 → ℝ)) :
    (⋃ i, A.coordinateSector Ω i) = spectralFlagCoordinateRegion Ω := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨⟨c, v⟩, ⟨hc, _⟩, rfl⟩ := hi
    exact ⟨(c, translatedSpectralAngularFlag (A.translate i) v), ⟨hc, mem_univ _⟩, rfl⟩
  · rintro ⟨⟨c, F⟩, ⟨hc, _⟩, rfl⟩
    have hF : F ∈ ⋃ i, A.patch i := A.covers.symm ▸ mem_univ F
    obtain ⟨i, hi⟩ := mem_iUnion.mp hF
    rw [← A.image_domain i] at hi
    obtain ⟨v, hv, rfl⟩ := hi
    exact mem_iUnion.mpr ⟨i, (c, v), ⟨hc, hv⟩, rfl⟩

theorem lintegral_coordinateSector_partition (Ω : Set (Fin 3 → ℝ)) (hΩ : MeasurableSet Ω)
    (hOrder : ∀ c ∈ Ω, StrictAnti c) (μ : Measure (Fin 9 → ℝ)) (f : (Fin 9 → ℝ) → ℝ≥0∞) :
    (∫⁻ x in spectralFlagCoordinateRegion Ω, f x ∂μ) = ∑ i, ∫⁻ x in A.coordinateSector Ω i, f x ∂μ := by
  rw [← A.union_coordinateSectors]
  simpa only [tsum_fintype] using lintegral_iUnion (μ := μ)
    (A.measurableSet_coordinateSector Ω hΩ hOrder) (A.disjoint_coordinateSectors Ω hOrder) f

end SpectralAngularPartition

def spectralPositiveChamber : Set (Fin 3 → ℝ) := {c | StrictAnti c ∧ ∀ i, 0 < c i}

theorem isOpen_spectralPositiveChamber : IsOpen spectralPositiveChamber := by
  have h : {c : Fin 3 → ℝ | ∀ i, 0 < c i} = ⋂ i : Fin 3, {c : Fin 3 → ℝ | 0 < c i} := by
    ext c
    simp
  have hp : IsOpen {c : Fin 3 → ℝ | ∀ i, 0 < c i} := by
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  exact isOpen_strictAnti_fin3.inter hp

end AlbertSequential.WindowProbability
