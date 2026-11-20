module

import WindowProbabilityTransport
import WindowProbabilityLaplace
open AlbertSequential AlbertSequential.WindowProbability MeasureTheory
example (W : ComplexWindow) (μ : Measure Albert) :
    (μ.map normalizeAlbert).map (projectedMatrix W) = (μ.map (projectedMatrix W)).map normalizeMatrix :=
  map_projectedMatrix_normalizeAlbert W μ
#print axioms map_projectedMatrix_normalizeAlbert
#print axioms projectedMatrix_atom_rankOne_iff
#print axioms measure_eq_of_local_exponential_transforms
