/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PositiveFunctionalNull

/-! Defined scalar/vector defects for the printed constructive scalar telescope.
None of the square/Clifford defects is assumed to vanish. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure CliffordScalarParameters where
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  d0 : ℝ

namespace CliffordScalarParameters
def diagonal (s : CliffordScalarParameters) : Fin 3 → ℝ := ![s.m1, s.m2, s.m3]
def gramMatrix (s : CliffordScalarParameters) : Fin 3 → Fin 3 → ℝ :=
  ![![s.m1, s.u, s.v], ![s.u, s.m2, s.w], ![s.v, s.w, s.m3]]
def q (s : CliffordScalarParameters) : Fin 3 → ℝ := ![s.w, -s.v, s.u]
def expectedCross (s : CliffordScalarParameters) : Fin 3 → ℝ :=
  ![-s.m1 * s.w, s.m2 * s.v - 2 * s.u * s.w, -s.m3 * s.u]
def discriminant (s : CliffordScalarParameters) : ℝ :=
  s.m1 * s.m2 * s.m3 + 2 * s.u * s.v * s.w -
    s.m1 * s.w ^ 2 - s.m2 * s.v ^ 2 - s.m3 * s.u ^ 2 - s.d0 ^ 2

theorem gramMatrix_diagonal (s : CliffordScalarParameters) (i : Fin 3) :
    s.gramMatrix i i = s.diagonal i := by
  fin_cases i <;> rfl
end CliffordScalarParameters

def realStarPairing {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (φ : A →ₗ[ℝ] ℝ) (x y : A) : ℝ := φ (star x * y)

section RealStarPairing
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_add_left (x y z : A) :
    realStarPairing φ (x + y) z = realStarPairing φ x z + realStarPairing φ y z := by
  simp only [realStarPairing, star_add, add_mul, map_add]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_add_right (x y z : A) :
    realStarPairing φ x (y + z) = realStarPairing φ x y + realStarPairing φ x z := by
  simp only [realStarPairing, mul_add, map_add]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_sub_left (x y z : A) :
    realStarPairing φ (x - y) z = realStarPairing φ x z - realStarPairing φ y z := by
  simp only [realStarPairing, star_sub, sub_mul, map_sub]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_sub_right (x y z : A) :
    realStarPairing φ x (y - z) = realStarPairing φ x y - realStarPairing φ x z := by
  simp only [realStarPairing, mul_sub, map_sub]

omit [SMulCommClass ℝ A A] in
theorem realStarPairing_smul_left (r : ℝ) (x y : A) :
    realStarPairing φ (r • x) y = r * realStarPairing φ x y := by
  simp only [realStarPairing, star_smul, star_trivial, smul_mul_assoc, map_smul, smul_eq_mul]

omit [IsScalarTower ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_smul_right (r : ℝ) (x y : A) :
    realStarPairing φ x (r • y) = r * realStarPairing φ x y := by
  simp only [realStarPairing, mul_smul_comm, map_smul, smul_eq_mul]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_symmetric (hstar : ∀ x, φ (star x) = φ x) (x y : A) :
    realStarPairing φ x y = realStarPairing φ y x := positiveForm_symmetric φ hstar x y

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem realStarPairing_sub_add (hstar : ∀ x, φ (star x) = φ x) (x y : A) :
    realStarPairing φ (x - y) (x + y) =
      realStarPairing φ x x - realStarPairing φ y y := by
  rw [realStarPairing_sub_left, realStarPairing_add_right, realStarPairing_add_right,
    realStarPairing_symmetric φ hstar y x]
  ring

end RealStarPairing

section Defects
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]

def cliffordTripleVector (N : Fin 3 → A) (ξ : A) : A := N 0 * N 1 * N 2 * ξ
def cliffordVolume (N : Fin 3 → A) : A :=
  (1 / 2 : ℝ) • (N 0 * N 1 * N 2 - N 2 * N 1 * N 0)
def cliffordGramVector (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) : A :=
  cliffordTripleVector N ξ + s.w • (N 0 * ξ) - s.v • (N 1 * ξ) + s.u • (N 2 * ξ)
def cliffordDataError (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) : A :=
  cliffordVolume N * ξ - s.d0 • ξ
def cliffordVolumeError (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) : A :=
  cliffordVolume N * ξ - cliffordGramVector N ξ s

def cliffordSquareDefect (N : Fin 3 → A) (s : CliffordScalarParameters) (i : Fin 3) (x : A) : A :=
  N i * (N i * x) + s.diagonal i • x
def cliffordPairDefect (N : Fin 3 → A) (s : CliffordScalarParameters) (i j : Fin 3) (x : A) : A :=
  N i * (N j * x) + N j * (N i * x) + (2 * s.gramMatrix i j) • x

def cliffordGramDefect (φ : A →ₗ[ℝ] ℝ) (N : Fin 3 → A) (ξ : A)
    (s : CliffordScalarParameters) (i j : Fin 3) : ℝ :=
  realStarPairing φ (N i * ξ) (N j * ξ) - s.gramMatrix i j * realStarPairing φ ξ ξ
def cliffordCrossDefect (φ : A →ₗ[ℝ] ℝ) (N : Fin 3 → A) (ξ : A)
    (s : CliffordScalarParameters) (i : Fin 3) : ℝ :=
  realStarPairing φ (cliffordTripleVector N ξ) (N i * ξ) -
    s.expectedCross i * realStarPairing φ ξ ξ
def cliffordNormDefect (φ : A →ₗ[ℝ] ℝ) (N : Fin 3 → A) (ξ : A)
    (s : CliffordScalarParameters) : ℝ :=
  realStarPairing φ (cliffordTripleVector N ξ) (cliffordTripleVector N ξ) -
    s.m1 * s.m2 * s.m3 * realStarPairing φ ξ ξ

end Defects
end AlbertSequential
