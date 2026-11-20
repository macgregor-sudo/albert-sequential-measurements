/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlagSectors
public import WindowProbabilitySpectralFlagOrder
public import WindowProbabilitySpectralRegularity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Matrix ComplexOrder

def sortedSpectrumOfHermitian (M : Hermitian3) : Fin 3 → ℝ := sortedHermitianSpectrum M.property

/-- The actual ordered eigenvalues of the Hermitian matrix encoded by nine real coordinates. -/
def sortedSpectrumAtCoords (x : Fin 9 → ℝ) : Fin 3 → ℝ :=
  sortedSpectrumOfHermitian (hermitianMatrixRealCoordinateEquiv.symm x)

theorem sortedSpectrumAtCoords_evaluate (c : Fin 3 → ℝ) (hc : StrictAnti c) (F : SpectralFlag) :
    sortedSpectrumAtCoords (hermitianMatrixRealCoordinates (spectralFlagEvaluate c F)) = c := by
  let X : Hermitian3 := ⟨spectralFlagEvaluate c F, spectralFlagEvaluate_isHermitian c F⟩
  change sortedSpectrumOfHermitian
    (hermitianMatrixRealCoordinateEquiv.symm (hermitianMatrixRealCoordinateEquiv X)) = c
  rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply]
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
  have h := spectralFlagEvaluate_unitary c U
  have hX : (spectralConjugate U c).IsHermitian := h ▸ X.property
  let Y : Hermitian3 := ⟨spectralConjugate U c, hX⟩
  have he : X = Y := Subtype.ext h
  rw [he]
  exact sortedHermitianSpectrum_spectralConjugate U c hc hX

theorem sortedSpectrumAtCoords_angularCoordinateBlock (U : SpectralUnitary) (c : Fin 3 → ℝ)
    (hc : StrictAnti c) (v : Fin 6 → ℝ) :
    sortedSpectrumAtCoords (spectralAngularCoordinateBlock U (c,v)) = c :=
  sortedSpectrumAtCoords_evaluate c hc (translatedSpectralAngularFlag U v)

theorem posDef_simple_mem_spectralFlagCoordinateRegion (X : ComplexMatrix3) (hX : X.PosDef)
    (hsimple : Function.Injective hX.isHermitian.eigenvalues) :
    hermitianMatrixRealCoordinates X ∈ spectralFlagCoordinateRegion spectralPositiveChamber := by
  obtain ⟨c, F, hc, hFX⟩ := exists_spectralFlagEvaluate_of_simple X hX.isHermitian hsimple
  have hs := sortedSpectrumAtCoords_evaluate c hc F
  rw [hFX] at hs
  have hn (i : Fin 3) : 0 < c i := by
    let M : Hermitian3 := ⟨X, hX.isHermitian⟩
    change sortedSpectrumOfHermitian
      (hermitianMatrixRealCoordinateEquiv.symm (hermitianMatrixRealCoordinateEquiv M)) = c at hs
    rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply] at hs
    have h := show 0 < sortedSpectrumOfHermitian M i from sortedHermitianSpectrum_pos hX i
    rwa [hs] at h
  exact ⟨(c,F), ⟨⟨hc,hn⟩, mem_univ _⟩, congrArg hermitianMatrixRealCoordinates hFX⟩

theorem posDef_discriminant_mem_spectralFlagCoordinateRegion (X : ComplexMatrix3) (hX : X.PosDef)
    (hd : cubicMatrixDiscriminant (1 / 2 : ℂ) X ≠ 0) :
    hermitianMatrixRealCoordinates X ∈ spectralFlagCoordinateRegion spectralPositiveChamber := by
  apply posDef_simple_mem_spectralFlagCoordinateRegion X hX
  let hH := hX.isHermitian
  rw [cubicMatrixDiscriminant_eq_eigenvalue_gaps X hH] at hd
  have h01 : hH.eigenvalues 0 ≠ hH.eigenvalues 1 := fun h => hd (by simp [h])
  have h02 : hH.eigenvalues 0 ≠ hH.eigenvalues 2 := fun h => hd (by simp [h])
  have h12 : hH.eigenvalues 1 ≠ hH.eigenvalues 2 := fun h => hd (by simp [h])
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (h01 hij).elim | exact (h01 hij.symm).elim |
      exact (h02 hij).elim | exact (h02 hij.symm).elim | exact (h12 hij).elim | exact (h12 hij.symm).elim

theorem measurableSet_spectralFlagCoordinateRegion (Ω : Set (Fin 3 → ℝ)) (hΩ : MeasurableSet Ω)
    (hOrder : ∀ c ∈ Ω, StrictAnti c) : MeasurableSet (spectralFlagCoordinateRegion Ω) := by
  obtain ⟨C⟩ := exists_spectralAngularChart
  obtain ⟨A⟩ := exists_spectralAngularPartition C
  rw [← A.union_coordinateSectors]
  exact MeasurableSet.iUnion (A.measurableSet_coordinateSector Ω hΩ hOrder)

/-- The actual ordered spectrum is Borel on the simple ordered spectral region. -/
theorem measurable_sortedSpectrumAtCoords_on_region (Ω : Set (Fin 3 → ℝ)) (hΩ : MeasurableSet Ω)
    (hOrder : ∀ c ∈ Ω, StrictAnti c) :
    Measurable (fun x : spectralFlagCoordinateRegion Ω => sortedSpectrumAtCoords x.val) := by
  intro t ht
  have heq : (fun x : spectralFlagCoordinateRegion Ω => sortedSpectrumAtCoords x.val) ⁻¹' t =
      Subtype.val ⁻¹' spectralFlagCoordinateRegion (Ω ∩ t) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨c,F⟩, ⟨hc,hF⟩, he⟩ := x.property
      refine ⟨(c,F), ⟨⟨hc,?_⟩,hF⟩, he⟩
      change sortedSpectrumAtCoords x.val ∈ t at hx
      have he' : hermitianMatrixRealCoordinates (spectralFlagEvaluate c F) = x.val := he
      have hs := (sortedSpectrumAtCoords_evaluate c (hOrder c hc) F).symm.trans
        (congrArg sortedSpectrumAtCoords he')
      exact hs.symm ▸ hx
    · rintro ⟨⟨c,F⟩, ⟨⟨hc,htc⟩,_⟩, he⟩
      change sortedSpectrumAtCoords x.val ∈ t
      have he' : hermitianMatrixRealCoordinates (spectralFlagEvaluate c F) = x.val := he
      have hs := (sortedSpectrumAtCoords_evaluate c (hOrder c hc) F).symm.trans
        (congrArg sortedSpectrumAtCoords he')
      exact hs ▸ htc
  rw [heq]
  exact measurable_subtype_coe (measurableSet_spectralFlagCoordinateRegion (Ω ∩ t) (hΩ.inter ht)
    (fun c hc => hOrder c hc.1))

/-- No change to the spectrum function is needed for a measure carried by the simple region. -/
theorem aemeasurable_sortedSpectrumAtCoords_of_ae_mem (Ω : Set (Fin 3 → ℝ)) (hΩ : MeasurableSet Ω)
    (hOrder : ∀ c ∈ Ω, StrictAnti c) (μ : Measure (Fin 9 → ℝ))
    (hμ : ∀ᵐ x ∂μ, x ∈ spectralFlagCoordinateRegion Ω) : AEMeasurable sortedSpectrumAtCoords μ := by
  have hreg := measurableSet_spectralFlagCoordinateRegion Ω hΩ hOrder
  obtain ⟨g, hg, hEq⟩ := (MeasurableEmbedding.subtype_coe hreg).exists_measurable_extend
    (measurable_sortedSpectrumAtCoords_on_region Ω hΩ hOrder) (fun _ => ⟨0⟩)
  refine ⟨g, hg, ?_⟩
  filter_upwards [hμ] with x hx
  exact (congrFun hEq ⟨x,hx⟩).symm

end AlbertSequential.WindowProbability
