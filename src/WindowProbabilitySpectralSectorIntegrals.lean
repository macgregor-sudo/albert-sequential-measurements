/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralAngularWeight
public import WindowProbabilitySpectralProduct
public import WindowProbabilitySpectralGramWeight
public import WindowProbabilitySpectralFlagSectors
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Apply the actual pointwise Weyl factor to the finite spectral atlas. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set NormedSpace
open scoped Matrix Matrix.Norms.Frobenius ENNReal

/-- The angular integration weight in the six real coordinates of the atlas. -/
def spectralAngularWeight (v : Fin 6 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |(spectralAngularRealDerivative (spectralAngularOffsets v)).det|

/-- The actual unnormalized three-eigenvalue weight at environment dimension four. -/
def spectralFourColumnWeight (x : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x)

/-- One translated spectral chart in the nine Lebesgue coordinates. -/
def spectralCoordinateSectorChart (U : SpectralUnitary) (q : Fin 9 → ℝ) : Fin 9 → ℝ :=
  spectralAngularCoordinateBlock U (spectralProductCoordinates q)

private theorem spectralAngularOffsets_product_snd (q : Fin 9 → ℝ) :
    spectralAngularOffsets (spectralProductCoordinates q).2 = spectralOrbitOffsets q := by
  rw [spectralProductCoordinates_snd]
  funext i
  fin_cases i <;> apply Complex.ext <;> rfl

private theorem spectralCoordinateSectorChart_eq_comp (U : SpectralUnitary) :
    spectralCoordinateSectorChart U = spectralUnitaryCoordinateConjugation U ∘ spectralExpChart 0 := by
  funext q
  let V := spectralExpUnitary (spectralOrbitOffsets q)
  let x := spectralVariations q
  let M : Hermitian3 := ⟨spectralFlagEvaluate x (spectralFlagOfUnitary V),
    spectralFlagEvaluate_isHermitian x (spectralFlagOfUnitary V)⟩
  have hM : M.val = spectralConjugate V x := spectralFlagEvaluate_unitary x V
  have h1 : spectralExpChart 0 q = hermitianMatrixRealCoordinateEquiv M := by
    rw [spectralExpChart_apply]
    change _ = hermitianMatrixRealCoordinates M.val
    rw [hM]
    have hStar : star (exp (spectralSkewMatrix (spectralOrbitOffsets q))) =
        exp (-spectralSkewMatrix (spectralOrbitOffsets q)) := spectralExpUnitary_star_val _
    simp only [spectralConjugate, spectralDiagonal, complexUnitaryConjugate, V, x,
      spectralExpUnitary_val, hStar, Pi.zero_apply, zero_add]
  have h2 : spectralUnitaryCoordinateConjugation U (hermitianMatrixRealCoordinateEquiv M) =
      hermitianMatrixRealCoordinateEquiv (hermitianUnitaryConjugate U M) := by
    change hermitianMatrixRealCoordinateEquiv (hermitianUnitaryConjugate U
      (hermitianMatrixRealCoordinateEquiv.symm (hermitianMatrixRealCoordinateEquiv M))) = _
    rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply]
  change spectralAngularCoordinateBlock U (spectralProductCoordinates q) =
    spectralUnitaryCoordinateConjugation U (spectralExpChart 0 q)
  rw [h1, h2, spectralAngularCoordinateBlock_apply, spectralAngularOffsets_product_snd,
    spectralProductCoordinates_fst, spectralConjugate_mul]
  change _ = hermitianMatrixRealCoordinates (hermitianUnitaryConjugate U M).val
  rw [hermitianUnitaryConjugate_apply, hM]

private theorem differentiable_spectralCoordinateSectorChart (U : SpectralUnitary) :
    Differentiable ℝ (spectralCoordinateSectorChart U) := by
  rw [spectralCoordinateSectorChart_eq_comp]
  exact (spectralUnitaryCoordinateConjugation U).differentiable.comp
    ((contDiff_spectralExpChart 0).differentiable one_ne_zero)

private theorem abs_det_spectralCoordinateSectorChart (U : SpectralUnitary) (q : Fin 9 → ℝ) :
    let x := (spectralProductCoordinates q).1
    |(fderiv ℝ (spectralCoordinateSectorChart U) q).det| =
      (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 *
      |(spectralAngularRealDerivative (spectralAngularOffsets (spectralProductCoordinates q).2)).det| := by
  intro x
  rw [spectralCoordinateSectorChart_eq_comp]
  have hF : HasFDerivAt (spectralExpChart 0) (fderiv ℝ (spectralExpChart 0) q) q :=
    ((contDiff_spectralExpChart 0).differentiable one_ne_zero q).hasFDerivAt
  rw [((spectralUnitaryCoordinateConjugation U).hasFDerivAt.comp q hF).fderiv]
  have hcomp (A B : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ)) : (A.comp B).det = A.det * B.det :=
    LinearMap.det_comp A.toLinearMap B.toLinearMap
  rw [hcomp, abs_mul, abs_det_spectralUnitaryCoordinateConjugation spectralHermitianVolume U,
    one_mul, abs_det_spectralExpChart spectralHermitianVolume]
  simp only [zero_add, spectralAngularOffsets_product_snd]
  rfl

private theorem spectralCoordinateSectorChart_image (U : SpectralUnitary)
    (D : Set (Fin 3 → ℝ)) (A : Set (Fin 6 → ℝ)) :
    spectralCoordinateSectorChart U '' (spectralProductCoordinates ⁻¹' (D ×ˢ A)) =
      spectralAngularCoordinateBlock U '' (D ×ˢ A) := by
  change (spectralAngularCoordinateBlock U ∘ spectralProductCoordinates) '' _ = _
  rw [image_comp, spectralProductCoordinates.surjective.image_preimage]

private theorem gramWeight_spectralCoordinateSectorChart (U : SpectralUnitary)
    (q : Fin 9 → ℝ) (hx : ∀ i, 0 < (spectralProductCoordinates q).1 i) :
    complexFourColumnGramWeight (hermitianMatrixRealCoordinateEquiv.symm (spectralCoordinateSectorChart U q)) =
      Real.exp (-(∑ i, (spectralProductCoordinates q).1 i)) * ∏ i, (spectralProductCoordinates q).1 i := by
  let p := spectralProductCoordinates q
  let V := U * spectralExpUnitary (spectralAngularOffsets p.2)
  let M : Hermitian3 := ⟨spectralFlagEvaluate p.1 (spectralFlagOfUnitary V),
    spectralFlagEvaluate_isHermitian p.1 (spectralFlagOfUnitary V)⟩
  have hM : M.val = spectralConjugate V p.1 := spectralFlagEvaluate_unitary p.1 V
  have he : spectralCoordinateSectorChart U q = hermitianMatrixRealCoordinateEquiv M := by
    change spectralAngularCoordinateBlock U p = hermitianMatrixRealCoordinates M.val
    rw [spectralAngularCoordinateBlock_apply, hM]
  rw [he, hermitianMatrixRealCoordinateEquiv.symm_apply_apply]
  exact complexFourColumnGramWeight_of_unitaryDiagonal V p.1 hx M hM

/-- On one measurable chart patch the exact Gram weight separates into the
Vandermonde-weighted eigenvalue integral and a common angular integral. -/
theorem lintegral_gramSpectralSector {C : SpectralAngularChart} (A : SpectralAngularPartition C)
    (i : Fin A.count) (f : (Fin 9 → ℝ) → ℝ≥0∞) (g : (Fin 3 → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hRead : ∀ x ∈ spectralPositiveChamber, ∀ v ∈ A.domain i,
      f (spectralAngularCoordinateBlock (A.translate i) (x, v)) = g x) :
    (∫⁻ y in A.coordinateSector spectralPositiveChamber i,
      ENNReal.ofReal (complexFourColumnGramWeight (hermitianMatrixRealCoordinateEquiv.symm y)) * f y) =
      (∫⁻ x in spectralPositiveChamber, spectralFourColumnWeight x * g x) *
        ∫⁻ v in A.domain i, spectralAngularWeight v := by
  let U := A.translate i
  let S := spectralProductCoordinates ⁻¹' (spectralPositiveChamber ×ˢ A.domain i)
  let L := spectralCoordinateSectorChart U
  have hS : MeasurableSet S := spectralProductCoordinates.measurable
    (isOpen_spectralPositiveChamber.measurableSet.prod (A.measurableSet_domain i))
  have hInj : InjOn L S := by
    intro q hq r hr hqr
    apply spectralProductCoordinates.injective
    exact (A.coordinateBlock_injOn spectralPositiveChamber (fun _ hx => hx.1) i) hq hr hqr
  have hImage : L '' S = A.coordinateSector spectralPositiveChamber i :=
    spectralCoordinateSectorChart_image U spectralPositiveChamber (A.domain i)
  have hW : Measurable spectralFourColumnWeight := by unfold spectralFourColumnWeight fourColumnEigenvalueWeight; fun_prop
  have hWG : Measurable (fun x => spectralFourColumnWeight x * g x) := hW.mul hg
  have hK : Measurable spectralAngularWeight :=
    (continuous_spectralAngularJacobian.comp continuous_spectralAngularOffsets).measurable.ennreal_ofReal
  rw [← hImage, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun q _ => ((differentiable_spectralCoordinateSectorChart U q).hasFDerivAt).hasFDerivWithinAt) hInj,
    ← lintegral_spectralProductCoordinates_mul spectralPositiveChamber (A.domain i)
      isOpen_spectralPositiveChamber.measurableSet (A.measurableSet_domain i)
      (fun x => spectralFourColumnWeight x * g x) spectralAngularWeight hWG hK]
  apply setLIntegral_congr_fun hS
  intro q hq
  let x := (spectralProductCoordinates q).1
  let v := (spectralProductCoordinates q).2
  have hx : x ∈ spectralPositiveChamber := hq.1
  have hv : v ∈ A.domain i := hq.2
  have hδ : 0 ≤ (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 := by positivity
  have hWgt : (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 *
      (Real.exp (-(∑ i, x i)) * ∏ i, x i) = Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x := by
    rw [fourColumnEigenvalueWeight, Fin.prod_univ_three]
    ring
  change ENNReal.ofReal |(fderiv ℝ (spectralCoordinateSectorChart U) q).det| *
    (ENNReal.ofReal (complexFourColumnGramWeight
      (hermitianMatrixRealCoordinateEquiv.symm (spectralCoordinateSectorChart U q))) *
      f (spectralAngularCoordinateBlock U (x, v))) =
    (spectralFourColumnWeight x * g x) * spectralAngularWeight v
  rw [abs_det_spectralCoordinateSectorChart, gramWeight_spectralCoordinateSectorChart U q hx.2,
    hRead x hx v hv, spectralFourColumnWeight, spectralAngularWeight,
    ENNReal.ofReal_mul hδ]
  have hA : ENNReal.ofReal ((x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2) *
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i) =
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * fourColumnEigenvalueWeight x) := by
    rw [← ENNReal.ofReal_mul hδ, hWgt]
  rw [← hA]
  ac_rfl

end AlbertSequential.WindowProbability
