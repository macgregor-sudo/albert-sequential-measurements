module

import TetrahedronHilbert

open AlbertSequential
open scoped Matrix

universe u

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Fin 4 → H →L[ℝ] H) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder P o R j k l m Q)
    (hpos : ∀ x y, x ≠ y → 0 < o x y) (hP : P j ≠ 0) :
    tetrahedronNormalizedAtOrder o R j k l m Q = 0 :=
  hilbert_tetrahedronNormalized_eq_zero P o R j k l m Q hR hpos hP

example : tetrahedronNormalizedAtOrder (fun _ _ => 1) (fun _ _ _ => 1) 0 1 2 3 (fun _ => 1) = 0 := by
  simp [tetrahedronNormalizedAtOrder, tetrahedronTriangleRadius, Matrix.det_fin_three]

#check @fpTetraDtet_eq_normalizedAtOrder
#check @tetrahedronDiscriminant_eq_radius_sq_mul_normalized
#check @hilbert_fpTetraDtet_eq_zero
#check @tetrahedronHolonomyData_constants
#check @tetrahedronNormalized_eq_holonomy_discriminant
#check @tetrahedronNormalizedHolonomy_defects_zero
#check @tetrahedronNormalizedHolonomy_clifford
#print axioms fpTetraDtet_eq_normalizedAtOrder
#print axioms tetrahedronDiscriminant_eq_radius_sq_mul_normalized
#print axioms hilbert_tetrahedronNormalized_eq_zero
#print axioms hilbert_fpTetraDtet_eq_zero
#print axioms tetrahedronHolonomyData_constants
#print axioms tetrahedronNormalized_eq_holonomy_discriminant
#print axioms tetrahedronNormalizedHolonomy_defects_zero
#print axioms tetrahedronNormalizedHolonomy_clifford
