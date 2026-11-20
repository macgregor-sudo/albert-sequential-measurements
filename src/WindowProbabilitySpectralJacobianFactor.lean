/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralChart
public import WindowProbabilitySpectralJacobian
public import WindowProbabilitySpectralGramSupport

/-! Separate the actual spectral chart derivative into an angular map,
the diagonal commutator weights, and a unitary coordinate change. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory NormedSpace
open scoped Matrix Matrix.Norms.Frobenius ENNReal

/-- The angular linearization of the exponential, left-translated by its unitary value. -/
def spectralAngularMatrixDerivative (v : Fin 3 → ℂ) : (Fin 9 → ℝ) →L[ℝ] ComplexMatrix3 :=
  let U := (spectralExpUnitary v : ComplexMatrix3)
  let L := (ContinuousLinearMap.snd ℝ ComplexMatrix3 ComplexMatrix3).comp spectralChartInputs
  U.conjTranspose • (fderiv ℝ (fun A : ComplexMatrix3 => exp A) (spectralSkewMatrix v)).comp L

/-- The first three real directions are radial and the angular block is independent of eigenvalues. -/
def spectralAngularRealDerivative (v : Fin 3 → ℂ) : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  let L := spectralMatrixOutput.comp (spectralAngularMatrixDerivative v)
  LinearMap.toContinuousLinearMap
    { toFun := fun q i => if i.val < 3 then q i else L q i
      map_add' := by intro q r; funext i; by_cases h : i.val < 3 <;> simp [h, Pi.add_apply]
      map_smul' := by intro c q; funext i; by_cases h : i.val < 3 <;> simp [h, Pi.smul_apply] }

/-- Real matrix coordinates transported by native unitary conjugation. -/
def spectralUnitaryCoordinateConjugation (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  let e := hermitianMatrixRealCoordinateEquiv
  (e.toLinearMap.comp
    ((hermitianUnitaryConjugate U).toLinearMap.comp e.symm.toLinearMap)).toContinuousLinearMap

/-- The angular derivative is skew-Hermitian at every chart point. -/
theorem spectralAngularMatrixDerivative_conjTranspose (q w : Fin 9 → ℝ) :
    (spectralAngularMatrixDerivative (spectralOrbitOffsets q) w).conjTranspose =
      -spectralAngularMatrixDerivative (spectralOrbitOffsets q) w := by
  let F (x : Fin 9 → ℝ) := spectralExpUnitary (spectralOrbitOffsets x)
  let L := (ContinuousLinearMap.snd ℝ ComplexMatrix3 ComplexMatrix3).comp spectralChartInputs
  let A := (fderiv ℝ (fun M : ComplexMatrix3 => exp M) (L q)).comp L
  have hU : HasFDerivAt (fun x => (F x : ComplexMatrix3)) A q :=
    (((exp_analytic (𝕂 := ℝ) (L q)).differentiableAt.hasFDerivAt).comp q L.hasFDerivAt)
  exact unitary_tangent_conjTranspose F A q w hU

/-- At every point, the actual spectral chart derivative factors through the
angular derivative and the nine explicit commutator weights. -/
theorem fderiv_spectralExpChart_factor (s : Fin 3 → ℝ) (q : Fin 9 → ℝ) :
    let v := spectralOrbitOffsets q
    let weight := Matrix.diagonal (spectralLinearizationWeights (s + spectralVariations q))
    fderiv ℝ (spectralExpChart s) q =
      (spectralUnitaryCoordinateConjugation (spectralExpUnitary v)).comp
        (weight.mulVecLin.toContinuousLinearMap.comp (spectralAngularRealDerivative v)) := by
  intro v W
  let F (x : Fin 9 → ℝ) := spectralExpUnitary (spectralOrbitOffsets x)
  let E := (ContinuousLinearMap.snd ℝ ComplexMatrix3 ComplexMatrix3).comp spectralChartInputs
  let E' := (fderiv ℝ (fun M : ComplexMatrix3 => exp M) (E q)).comp E
  let D' := (ContinuousLinearMap.fst ℝ ComplexMatrix3 ComplexMatrix3).comp spectralChartInputs
  let D (x : Fin 9 → ℝ) := Matrix.diagonal (fun i => (s i : ℂ)) + D' x
  have hF : HasFDerivAt (fun x => (F x : ComplexMatrix3)) E' q :=
    ((exp_analytic (𝕂 := ℝ) (E q)).differentiableAt.hasFDerivAt).comp q E.hasFDerivAt
  have hD : HasFDerivAt D D' q := D'.hasFDerivAt.const_add _
  let G (x : Fin 9 → ℝ) := (F x : ComplexMatrix3) * D x * (F x : ComplexMatrix3).conjTranspose
  have hfun : spectralExpChart s = spectralMatrixOutput ∘ G := by
    funext x
    rw [spectralExpChart_apply]
    change _ = hermitianMatrixRealCoordinates
      (exp (spectralSkewMatrix (spectralOrbitOffsets x)) *
        (Matrix.diagonal (fun i => (s i : ℂ)) + Matrix.diagonal (fun i => (spectralVariations x i : ℂ))) *
        (spectralExpUnitary (spectralOrbitOffsets x) : ComplexMatrix3).conjTranspose)
    rw [Matrix.diagonal_add, ← Matrix.star_eq_conjTranspose, spectralExpUnitary_star_val]
    simp only [Complex.ofReal_add]
  have hS : DifferentiableAt ℝ (fun x => (F x : ComplexMatrix3).conjTranspose) q := by
    have hEq : (fun x => (F x : ComplexMatrix3).conjTranspose) = fun x => exp (-E x) := by
      funext x
      rw [← Matrix.star_eq_conjTranspose]
      exact spectralExpUnitary_star_val (spectralOrbitOffsets x)
    rw [hEq]
    exact (exp_analytic (𝕂 := ℝ) (-E q)).differentiableAt.comp q E.differentiableAt.neg
  have hG : DifferentiableAt ℝ G q := (hF.differentiableAt.mul hD.differentiableAt).mul hS
  have hderiv := (spectralMatrixOutput.hasFDerivAt.comp q hG.hasFDerivAt).fderiv
  rw [hfun, hderiv]
  apply ContinuousLinearMap.ext
  intro w
  let K := spectralAngularMatrixDerivative v w
  let B := D' w + K * D q - D q * K
  have hB : B.IsHermitian := by
    have hDiagonal (r : Fin 3 → ℝ) :
        (Matrix.diagonal (fun i => (r i : ℂ))).IsHermitian :=
      Matrix.isHermitian_diagonal_iff.mpr (fun _ => by simp [IsSelfAdjoint])
    have hDq : (D q).IsHermitian := (hDiagonal s).add (hDiagonal (spectralVariations q))
    have hDw : (D' w).IsHermitian := hDiagonal (spectralVariations w)
    have hK : K.conjTranspose = -K := spectralAngularMatrixDerivative_conjTranspose q w
    change B.conjTranspose = B
    simp only [B, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      hDq.eq, hDw.eq, hK, mul_neg, neg_mul]
    abel
  let Bₕ : Hermitian3 := ⟨B, hB⟩
  have hG' : fderiv ℝ G q w = (F q : ComplexMatrix3) * B * (F q : ComplexMatrix3).conjTranspose :=
    fderiv_unitaryConjugation_movingFrame F D E' D' q w hF hD
  change spectralMatrixOutput (fderiv ℝ G q w) =
    spectralUnitaryCoordinateConjugation (spectralExpUnitary v) (W.mulVec (spectralAngularRealDerivative v w))
  rw [hG']
  have hcoords : hermitianMatrixRealCoordinateEquiv Bₕ = W.mulVec (spectralAngularRealDerivative v w) := by
    change hermitianMatrixRealCoordinates B = _
    have hDiag : D q = Matrix.diagonal (fun i => (((s + spectralVariations q) i : ℝ) : ℂ)) := by
      change Matrix.diagonal (fun i => (s i : ℂ)) + Matrix.diagonal (fun i => (spectralVariations q i : ℂ)) = _
      rw [Matrix.diagonal_add]
      simp only [Pi.add_apply, Complex.ofReal_add]
    have ho : spectralAngularRealDerivative v w =
        ![(spectralVariations w) 0, (spectralVariations w) 1, (spectralVariations w) 2,
          (K 0 1).re, (K 0 1).im, (K 0 2).re, (K 0 2).im, (K 1 2).re, (K 1 2).im] := by
      funext i
      fin_cases i <;> rfl
    change hermitianMatrixRealCoordinates
      (Matrix.diagonal (fun i => (spectralVariations w i : ℂ)) + K * D q - D q * K) = _
    rw [hDiag, ho]
    exact spectralCommutator_coordinates (s + spectralVariations q) (spectralVariations w) K
  rw [← hcoords]
  change hermitianMatrixRealCoordinates ((F q : ComplexMatrix3) * B * (F q : ComplexMatrix3).conjTranspose) =
    hermitianMatrixRealCoordinateEquiv (hermitianUnitaryConjugate (spectralExpUnitary v)
      (hermitianMatrixRealCoordinateEquiv.symm (hermitianMatrixRealCoordinateEquiv Bₕ)))
  rw [hermitianMatrixRealCoordinateEquiv.symm_apply_apply]
  rfl

/-- Unit modulus of the determinant of an actual abstract frame conjugation in real coordinates. -/
theorem abs_det_spectralUnitaryCoordinateConjugation (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (U : Matrix.unitaryGroup (Fin 3) ℂ) : |(spectralUnitaryCoordinateConjugation U).det| = 1 := by
  change |LinearMap.det (hermitianMatrixRealCoordinateEquiv.toLinearMap.comp
    ((hermitianUnitaryConjugate U).toLinearMap.comp hermitianMatrixRealCoordinateEquiv.symm.toLinearMap))| = 1
  rw [LinearMap.det_conj, abs_det_native_unitaryConjugation μ U]

/-- The absolute Jacobian of the actual spectral chart is the squared
Vandermonde times an angular factor independent of the eigenvalues. -/
theorem abs_det_spectralExpChart (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (s : Fin 3 → ℝ) (q : Fin 9 → ℝ) :
    let x := s + spectralVariations q
    |(fderiv ℝ (spectralExpChart s) q).det| =
      (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 *
      |(spectralAngularRealDerivative (spectralOrbitOffsets q)).det| := by
  intro x
  let v := spectralOrbitOffsets q
  let U := spectralExpUnitary v
  have hu := abs_det_spectralUnitaryCoordinateConjugation μ U
  have hx : 0 ≤ (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 := by positivity
  have hW : ((Matrix.diagonal (spectralLinearizationWeights x)).mulVecLin.toContinuousLinearMap).det =
      (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 := by
    change LinearMap.det (Matrix.diagonal (spectralLinearizationWeights x)).mulVecLin = _
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin', spectralLinearization_det]
  have h := fderiv_spectralExpChart_factor s q
  change fderiv ℝ (spectralExpChart s) q =
    (spectralUnitaryCoordinateConjugation U).comp
      ((Matrix.diagonal (spectralLinearizationWeights x)).mulVecLin.toContinuousLinearMap.comp
        (spectralAngularRealDerivative v)) at h
  have hcomp (A B : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ)) : (A.comp B).det = A.det * B.det :=
    LinearMap.det_comp A.toLinearMap B.toLinearMap
  rw [h, hcomp, hcomp, abs_mul, abs_mul, hu,
    one_mul, hW, abs_of_nonneg hx]

end AlbertSequential.WindowProbability
