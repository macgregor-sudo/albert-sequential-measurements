/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteVectorTetrahedron

@[expose] public section

noncomputable section

namespace AlbertSequential.CornerHolonomy

/-- Cyclic order (j,k,l,m)=(0,1,2,3), with the printed square-root normalizers. -/
def finiteTetrahedronNormalizers (o : Fin 4 → Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (o 0 1 * o 1 2 * o 2 0), Real.sqrt (o 0 2 * o 2 3 * o 3 0),
    Real.sqrt (o 0 3 * o 3 1 * o 1 0)]

def finiteTetrahedronHolonomies {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Fin 4 → H →L[ℝ] H) (o : Fin 4 → Fin 4 → ℝ) : Fin 3 → H →L[ℝ] H :=
  let ν := finiteTetrahedronNormalizers o
  normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) (ν 0) (ν 1) (ν 2)

def finiteTetrahedronCosines (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 3 → ℝ :=
  let ν := finiteTetrahedronNormalizers o
  ![R 0 1 2 / ν 0, R 0 2 3 / ν 1, R 0 3 1 / ν 2]

def finiteTetrahedronFarCosine (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  R 1 2 3 / Real.sqrt (o 1 2 * o 2 3 * o 3 1)

/-- The three inputs are Q indexed in cyclic order (123,231,312), with base 0. -/
def finiteTetrahedronMixed (o : Fin 4 → Fin 4 → ℝ) (Q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Q 0 / Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0),
    Q 1 / Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0),
    Q 2 / Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0)]

def finiteTetrahedronParameters (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Q : Fin 3 → ℝ) : CliffordScalarParameters :=
  let K := finiteTetrahedronMixed o Q
  cornerCliffordParameters (finiteTetrahedronCosines o R) (K 0) (K 2) (K 1)
    (finiteTetrahedronFarCosine o R)

/-- Companion Lemma 2.1 for arbitrary bounded orthogonal projections on a real
Hilbert space. Only the four stated finite-vector relations are used. -/
theorem finiteVectorTetrahedron {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (P : Fin 4 → H →L[ℝ] H) (hproj : ∀ i, IsStarProjection (P i)) (Ω : H)
    (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (Q : Fin 3 → ℝ)
    (_hpos : ∀ a b, a ≠ b → 0 < o a b)
    (hH : let h := finiteTetrahedronHolonomies P o
      let ξ := P 0 Ω
      ∀ i η, η ∈ holonomyDegreeSpan h ξ 2 →
        hermitianPart (h i) η = finiteTetrahedronCosines o R i • η)
    (hU : let h := finiteTetrahedronHolonomies P o
      let ξ := P 0 Ω
      ∀ i η, η ∈ holonomyDegreeSpan h ξ 2 →
        (star (h i) * h i) η = η ∧ (h i * star (h i)) η = η)
    (hP : let h := finiteTetrahedronHolonomies P o
      let ξ := P 0 Ω
      let N := fun i => skewHermitianPart (h i)
      let s := finiteTetrahedronParameters o R Q
      ∀ i j, i ≠ j → ∀ η, η ∈ holonomyDegreeSpan h ξ 1 →
        (N i * N j + N j * N i) η = (-2 * s.gramMatrix i j) • η)
    (hC : let h := finiteTetrahedronHolonomies P o
      let ξ := P 0 Ω
      hermitianPart (h 0 * h 1 * h 2) ξ = finiteTetrahedronFarCosine o R • ξ) :
    let ξ := P 0 Ω
    let N := fun i => skewHermitianPart (finiteTetrahedronHolonomies P o i)
    let s := finiteTetrahedronParameters o R Q
    let M := Matrix.of s.gramMatrix
    cliffordVolume N ξ = s.d0 • ξ ∧
      ‖cliffordVolume N ξ‖^2 = M.det * ‖ξ‖^2 ∧
      (M.det - s.d0^2) * ‖ξ‖^2 = 0 := by
  let h := finiteTetrahedronHolonomies P o
  let K := finiteTetrahedronMixed o Q
  exact finiteVectorTetrahedron_of_corner (P 0) h (hproj 0).isIdempotentElem
    (hproj 0).isSelfAdjoint (normalizedCyclicHolonomies_supported _ _ _ _
      (hproj 0).isIdempotentElem _ _ _) (finiteTetrahedronCosines o R)
    (K 0) (K 2) (K 1) (finiteTetrahedronFarCosine o R) Ω hH hU hP hC

end AlbertSequential.CornerHolonomy
