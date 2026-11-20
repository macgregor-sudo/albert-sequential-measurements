module

import FiniteVectorTetrahedronPaper

open AlbertSequential AlbertSequential.CornerHolonomy

example (o : Fin 4 → Fin 4 → ℝ) :
    finiteTetrahedronNormalizers o 0 = Real.sqrt (o 0 1 * o 1 2 * o 2 0) ∧
    finiteTetrahedronNormalizers o 1 = Real.sqrt (o 0 2 * o 2 3 * o 3 0) ∧
    finiteTetrahedronNormalizers o 2 = Real.sqrt (o 0 3 * o 3 1 * o 1 0) :=
  ⟨rfl,rfl,rfl⟩

example (o : Fin 4 → Fin 4 → ℝ) (Q : Fin 3 → ℝ) :
    finiteTetrahedronMixed o Q 0 = Q 0 / Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0) ∧
    finiteTetrahedronMixed o Q 1 = Q 1 / Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0) ∧
    finiteTetrahedronMixed o Q 2 = Q 2 / Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0) :=
  ⟨rfl,rfl,rfl⟩

example (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (Q : Fin 3 → ℝ) :
    let s := finiteTetrahedronParameters o R Q
    let c := finiteTetrahedronCosines o R
    let K := finiteTetrahedronMixed o Q
    s.gramMatrix 0 0 = 1 - c 0 ^ 2 ∧
    s.gramMatrix 0 1 = c 0 * c 1 - K 0 ∧
    s.gramMatrix 0 2 = c 0 * c 2 - K 2 ∧
    s.gramMatrix 1 2 = c 1 * c 2 - K 1 ∧
    s.d0 = finiteTetrahedronFarCosine o R -
      (c 0 * c 1 * c 2 - c 0 * s.gramMatrix 1 2 -
        c 1 * s.gramMatrix 0 2 - c 2 * s.gramMatrix 0 1) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

#check finiteVectorTetrahedron
#print axioms finiteVectorTetrahedron_of_corner
#print axioms finiteVectorTetrahedron
