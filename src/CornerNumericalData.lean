/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NormalizedHolonomyDefects
public import PrimitivePurityDecomposition

/-! State-independent scalar inputs for the actual one-base constructor.
Exactly sixteen real data fields; symmetric edge lookup is constructed.
The Prop below contains only listed scalar equations, never an operator
relation, native purity claim, telescope identity or no-go conclusion. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure CornerNumericalData where
  o01 : ℝ
  o02 : ℝ
  o03 : ℝ
  o12 : ℝ
  o23 : ℝ
  o31 : ℝ
  r012 : ℝ
  r023 : ℝ
  r031 : ℝ
  r123 : ℝ
  q123 : ℝ
  q231 : ℝ
  q312 : ℝ
  ν0 : ℝ
  ν1 : ℝ
  ν2 : ℝ

namespace CornerNumericalData
def overlap (d : CornerNumericalData) : Fin 4 → Fin 4 → ℝ :=
  ![![1, d.o01, d.o02, d.o03], ![d.o01, 1, d.o12, d.o31],
    ![d.o02, d.o12, 1, d.o23], ![d.o03, d.o31, d.o23, 1]]
def normalizer (d : CornerNumericalData) : Fin 3 → ℝ := ![d.ν0, d.ν1, d.ν2]
def normalizerSquare (d : CornerNumericalData) : Fin 3 → ℝ :=
  ![d.o01 * d.o12 * d.o02, d.o02 * d.o23 * d.o03, d.o03 * d.o31 * d.o01]
def hermitianConstants (d : CornerNumericalData) : Fin 3 → ℝ :=
  ![d.r012 / d.ν0, d.r023 / d.ν1, d.r031 / d.ν2]
def mixed12 (d : CornerNumericalData) : ℝ := d.o02 * d.q123 / (d.ν0 * d.ν1)
def mixed13 (d : CornerNumericalData) : ℝ := d.o01 * d.q312 / (d.ν0 * d.ν2)
def mixed23 (d : CornerNumericalData) : ℝ := d.o03 * d.q231 / (d.ν1 * d.ν2)
def cubicConstant (d : CornerNumericalData) : ℝ :=
  d.o01 * d.o02 * d.o03 * d.r123 / (d.ν0 * d.ν1 * d.ν2)
def scalarParameters (d : CornerNumericalData) : CliffordScalarParameters :=
  CornerHolonomy.cornerCliffordParameters d.hermitianConstants d.mixed12 d.mixed13 d.mixed23 d.cubicConstant

theorem overlap_symmetric (d : CornerNumericalData) (a b : Fin 4) : d.overlap a b = d.overlap b a := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The third mixed contraction is ordered (h2,h0), with Q312. -/
theorem mixed13_reverse_denominator (d : CornerNumericalData) :
    d.mixed13 = d.o01 * d.q312 / (d.ν2 * d.ν0) := by
  rw [mixed13, mul_comm d.ν2 d.ν0]

end CornerNumericalData

structure CornerScalarConditions (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) : Prop where
  normalizers_nonzero : ∀ i, d.normalizer i ≠ 0
  normalizers_square : ∀ i, d.normalizer i ^ 2 = d.normalizerSquare i
  pair_access : ∀ a b, a ≠ b → C a [(b, true)] = d.overlap a b
  triangle_012 : C 0 [(2, true)] + C 0 [(1, true), (2, true)] -
    C 0 [(1, false), (2, true)] = 2 * d.r012
  triangle_023 : C 0 [(3, true)] + C 0 [(2, true), (3, true)] -
    C 0 [(2, false), (3, true)] = 2 * d.r023
  triangle_031 : C 0 [(1, true)] + C 0 [(3, true), (1, true)] -
    C 0 [(3, false), (1, true)] = 2 * d.r031
  triangle_123 : C 1 [(3, true)] + C 1 [(2, true), (3, true)] -
    C 1 [(2, false), (3, true)] = 2 * d.r123
  triple_123 : weightedWordScalar (C 0) (polarizedTripleWordTerms 1 2 3) = 4 * d.q123
  triple_231 : weightedWordScalar (C 0) (polarizedTripleWordTerms 2 3 1) = 4 * d.q231
  triple_312 : weightedWordScalar (C 0) (polarizedTripleWordTerms 3 1 2) = 4 * d.q312

namespace CliffordScalarParameters
theorem gramMatrix_symmetric (s : CliffordScalarParameters) (i j : Fin 3) :
    s.gramMatrix i j = s.gramMatrix j i := by
  fin_cases i <;> fin_cases j <;> rfl
end CliffordScalarParameters

/-- This exact symmetry is valid even when the mixed T defects differ. -/
theorem cliffordPairDefect_swap {A : Type*} [Ring A] [Module ℝ A]
    (N : Fin 3 → A) (s : CliffordScalarParameters) (i j : Fin 3) (ξ : A) :
    cliffordPairDefect N s i j ξ = cliffordPairDefect N s j i ξ := by
  simp only [cliffordPairDefect, s.gramMatrix_symmetric i j]
  abel

end AlbertSequential
