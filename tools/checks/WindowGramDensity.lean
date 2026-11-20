module

import WindowProbabilityGramLaw
import WindowProbabilityGramDensity

open AlbertSequential AlbertSequential.WindowProbability MeasureTheory

example (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] :
    (standardComplexGaussianMatrix 4).map (fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose) =
      (complexFourColumnGramDensityMeasure μ).map (Subtype.val : Hermitian3 → ComplexMatrix3) :=
  fourColumnGaussianGram_eq_density μ

example (u : Fin 9 → ℝ) :
    LinearMap.det (fderiv ℝ complexCholeskyChart u).toLinearMap = u 0 ^ 4 * u 5 ^ 2 :=
  complexCholeskyChart_det_fderiv u

#print axioms fourColumnGaussianGram_eq_density
#print axioms complexCholeskyChart_det_fderiv
#print axioms measurePreserving_hermitianUnitaryConjugate
#print axioms ae_fourColumnGram_posDef
