module

import WindowProbabilitySpectralChart
import WindowProbabilitySpectralJacobian
import WindowProbabilitySpectralGramSupport
import WindowProbabilitySpectralJacobianFactor
import WindowProbabilitySpectralAngularWeight
import WindowProbabilitySpectralProduct
import WindowProbabilitySpectralGramWeight

#print axioms AlbertSequential.WindowProbability.spectralExpUnitary_val
#print axioms AlbertSequential.WindowProbability.spectralExpUnitary_star_val
#print axioms AlbertSequential.WindowProbability.continuous_spectralExpUnitary
#print axioms AlbertSequential.WindowProbability.spectralExpChart_apply
#print axioms AlbertSequential.WindowProbability.fderiv_spectralExpChart_zero
#print axioms AlbertSequential.WindowProbability.spectralExpChart_localHomeomorph
#print axioms AlbertSequential.WindowProbability.unitary_tangent_conjTranspose
#print axioms AlbertSequential.WindowProbability.fderiv_unitaryConjugation_movingFrame
#print axioms AlbertSequential.WindowProbability.spectralCommutator_coordinates
#print axioms AlbertSequential.WindowProbability.measurable_rawFourColumnHermitianGram
#print axioms AlbertSequential.WindowProbability.rawFourColumnHermitianGramLaw_eq_density
#print axioms AlbertSequential.WindowProbability.ae_complexFourColumnGramDensityMeasure_posDef_simple
#print axioms AlbertSequential.WindowProbability.measurePreserving_hermitianMatrixRealCoordinateEquiv
#print axioms AlbertSequential.WindowProbability.abs_det_native_unitaryConjugation
#print axioms AlbertSequential.WindowProbability.spectralAngularMatrixDerivative_conjTranspose
#print axioms AlbertSequential.WindowProbability.fderiv_spectralExpChart_factor
#print axioms AlbertSequential.WindowProbability.abs_det_spectralUnitaryCoordinateConjugation
#print axioms AlbertSequential.WindowProbability.abs_det_spectralExpChart
#print axioms AlbertSequential.WindowProbability.continuous_spectralAngularJacobian
#print axioms AlbertSequential.WindowProbability.spectralAngularRealDerivative_zero
#print axioms AlbertSequential.WindowProbability.measurePreserving_spectralProductCoordinates
#print axioms AlbertSequential.WindowProbability.spectralProductCoordinates_fst
#print axioms AlbertSequential.WindowProbability.spectralProductCoordinates_snd
#print axioms AlbertSequential.WindowProbability.lintegral_spectralProductCoordinates_mul
#print axioms AlbertSequential.WindowProbability.complexFourColumnGramWeight_of_unitaryDiagonal

open MeasureTheory AlbertSequential AlbertSequential.WindowProbability

example (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] (s : Fin 3 → ℝ) (q : Fin 9 → ℝ) :
    let x := s + spectralVariations q
    |(fderiv ℝ (spectralExpChart s) q).det| =
      (x 1 - x 0)^2 * (x 2 - x 0)^2 * (x 2 - x 1)^2 *
        |(spectralAngularRealDerivative (spectralOrbitOffsets q)).det| :=
  abs_det_spectralExpChart μ s q
