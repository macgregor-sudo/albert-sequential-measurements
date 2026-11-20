module

import CompanionQuadrangleTopology

noncomputable section

open AlbertSequential AlbertSequential.ProjectiveMetricInvariant
open AlbertSequential.WindowProbability

example :
    IsOpen (quadrangleLocus : Set (Fin 4 → AlbertAtomSpace)) ∧ Dense quadrangleLocus :=
  ⟨quadrangleLocus_isOpen, quadrangleLocus_dense⟩

example (t : Fin 3 ↪ Fin 4) :
    IsOpen ({p : Fin 4 → AlbertAtomSpace |
      ¬ ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p (t j)).val q.val = 0}) ∧
      Dense ({p : Fin 4 → AlbertAtomSpace |
        ¬ ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p (t j)).val q.val = 0}) :=
  ⟨tripleNoncollinear_isOpen t, tripleNoncollinear_dense t⟩

#print axioms quadrangleLocus_isOpen
#print axioms quadrangleLocus_dense
#print axioms ae_off_polar_line
#print axioms dense_off_polar_line
#print axioms polar_unique_of_two_distinct
#print axioms atomMeasure_comap_orbitAveraging
