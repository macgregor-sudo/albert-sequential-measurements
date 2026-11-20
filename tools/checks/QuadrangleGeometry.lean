module

import CompanionQuadrangleGeometry

noncomputable section

open AlbertSequential AlbertSequential.ProjectiveMetricInvariant
open AlbertSequential.WindowProbability

example (a b : AlbertAtomSpace) (h : a ≠ b) :
    ∃! q : AlbertAtomSpace, tracePairing q.val a.val = 0 ∧ tracePairing q.val b.val = 0 :=
  existsUnique_polar_through_distinct a b h

example :
    ∃ p ∈ quadrangleLocus, ∃ q ∈ quadrangleLocus,
      fourPointInvariant (fun i => (p i).val) ≠ fourPointInvariant (fun i => (q i).val) :=
  fourPointInvariant_not_constant_on_quadrangles

#print axioms existsUnique_polar_through_distinct
#print axioms standardRealQuadrangle_mem
#print axioms standardRealQuadrangle_invariant_zero
#print axioms maximizerConfig_mem_quadrangleLocus
#print axioms cubicNorm_eq_zero_of_common_polar
#print axioms fourPointInvariant_not_constant_on_quadrangles
