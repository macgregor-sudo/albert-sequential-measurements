/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.NativeBinding
public import FixedSCornerConditions
public import FixedSNativeLeaves
public import FiniteCornerWitness

/-! # Generic eleven-step corner data, scalar conditions, discriminant, and native leaves

Generalizes the fixed-S constructor infrastructure (`FixedSCornerScalars`,
`FixedSCornerConditions`, `FixedSCornerDiscriminants`, `FixedSNativeLeaves`,
`FixedSConstructedWitness`) to arbitrary four atoms `p : Fin 4 → Albert` with
`∀ i, IsAtom (p i)` and `0 < fourPointInvariant p`.

Public exports (`AlbertSequential.BlockB`):
- Permutation symmetry & overlap bounds: `fourPointInvariant_swapBase_eq`,
  `fourPointInvariant_swapBase`, `atom_overlap_bounds`, `atom_overlap_pos`,
  `atom_overlap_lt_one`;
- Base-0 corner data and scalar access: `atomCornerData`, `atomCornerScalar`,
  `atomCorner_conditions`, `atomCorner_discriminant_eq`, `atomCorner_discriminant_pos`,
  `atomCorner_discriminant_swapBase`;
- Native leaf vanishing & telescope witnesses: `atomCorner_leaf_native_zero`,
  `atomCorner_constructor_native_zero`, `atomCorner_combined_leaves_native_zero`,
  `atomCornerSingleBaseWitness*`, `atomCornerWitness*`. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace AlbertSequential.BlockB

open AlbertSequential
open AlbertSequential.NativeAnalysis
open AlbertSequential.ConstructorCalibration
open scoped BigOperators

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

section OverlapAndSymmetry

theorem fourPointInvariant_swapBase_eq (p : Fin 4 → Albert) (j : Fin 4) :
    fourPointInvariant (p ∘ Equiv.swap 0 j) = fourPointInvariant p :=
  fourPointInvariant_perm_invariant (Equiv.swap 0 j) p

theorem fourPointInvariant_swapBase (p : Fin 4 → Albert) (j : Fin 4)
    (hA : 0 < fourPointInvariant p) :
    0 < fourPointInvariant (p ∘ Equiv.swap 0 j) := by
  rw [fourPointInvariant_swapBase_eq]
  exact hA

theorem atom_overlap_bounds (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i j : Fin 4) (hij : i ≠ j) :
    0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1 :=
  LengthSeven.overlap_bounds_of_fourPoint_pos p hp hA i j hij

theorem atom_overlap_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i j : Fin 4) (hij : i ≠ j) :
    0 < tracePairing (p i) (p j) :=
  (atom_overlap_bounds p hp hA i j hij).1

theorem atom_overlap_lt_one (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i j : Fin 4) (hij : i ≠ j) :
    tracePairing (p i) (p j) < 1 :=
  (atom_overlap_bounds p hp hA i j hij).2

end OverlapAndSymmetry

section CornerData

/-- Sixteen-field state-independent corner data at base `0` for an arbitrary atom quadruple `p`. -/
def atomCornerData (p : Fin 4 → Albert) : CornerNumericalData where
  o01 := tracePairing (p 0) (p 1)
  o02 := tracePairing (p 0) (p 2)
  o03 := tracePairing (p 0) (p 3)
  o12 := tracePairing (p 1) (p 2)
  o23 := tracePairing (p 2) (p 3)
  o31 := tracePairing (p 3) (p 1)
  r012 := tracePairing (p 0) (jordanMul (p 1) (p 2))
  r023 := tracePairing (p 0) (jordanMul (p 2) (p 3))
  r031 := tracePairing (p 0) (jordanMul (p 3) (p 1))
  r123 := tracePairing (p 1) (jordanMul (p 2) (p 3))
  q123 := tracePairing (p 0) (jordanTriple (p 1) (p 2) (p 3))
  q231 := tracePairing (p 0) (jordanTriple (p 2) (p 3) (p 1))
  q312 := tracePairing (p 0) (jordanTriple (p 3) (p 1) (p 2))
  ν0 := Real.sqrt (tracePairing (p 0) (p 1) * tracePairing (p 1) (p 2) * tracePairing (p 0) (p 2))
  ν1 := Real.sqrt (tracePairing (p 0) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 0) (p 3))
  ν2 := Real.sqrt (tracePairing (p 0) (p 3) * tracePairing (p 3) (p 1) * tracePairing (p 0) (p 1))

/-- Native word probabilities starting from atom `p a`. -/
def atomCornerScalar (p : Fin 4 → Albert) (a : Fin 4) (w : Word (Fin 4)) : ℝ :=
  nativeWordProbability p (p a) w

theorem atomCornerData_overlap_ne (p : Fin 4 → Albert) {a b : Fin 4} (hab : a ≠ b) :
    (atomCornerData p).overlap a b = tracePairing (p a) (p b) := by
  fin_cases a <;> fin_cases b <;>
    dsimp [atomCornerData, CornerNumericalData.overlap]
  all_goals first
    | exact absurd rfl hab
    | exact congrArg₂ tracePairing rfl rfl
    | exact tracePairing_comm _ _

theorem atomCornerData_overlap_eq_nativeOverlaps (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (a b : Fin 4) :
    (atomCornerData p).overlap a b = nativeOverlaps p a b := by
  by_cases hab : a = b
  · subst hab
    have hself : tracePairing (p a) (p a) = 1 := by
      unfold tracePairing
      rw [(hp a).1, (hp a).2]
    fin_cases a <;> dsimp [atomCornerData, CornerNumericalData.overlap, nativeOverlaps] <;>
      exact hself.symm
  · exact atomCornerData_overlap_ne p hab

theorem atomCornerData_normalizer_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i : Fin 3) :
    0 < (atomCornerData p).normalizer i := by
  have h01 := atom_overlap_pos p hp hA 0 1 (by decide)
  have h02 := atom_overlap_pos p hp hA 0 2 (by decide)
  have h03 := atom_overlap_pos p hp hA 0 3 (by decide)
  have h12 := atom_overlap_pos p hp hA 1 2 (by decide)
  have h23 := atom_overlap_pos p hp hA 2 3 (by decide)
  have h31 := atom_overlap_pos p hp hA 3 1 (by decide)
  fin_cases i
  · exact Real.sqrt_pos.mpr (by positivity)
  · exact Real.sqrt_pos.mpr (by positivity)
  · exact Real.sqrt_pos.mpr (by positivity)

theorem atomCornerData_normalizer_nonzero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i : Fin 3) :
    (atomCornerData p).normalizer i ≠ 0 :=
  ne_of_gt (atomCornerData_normalizer_pos p hp hA i)

theorem atomCornerData_normalizer_square (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (i : Fin 3) :
    (atomCornerData p).normalizer i ^ 2 = (atomCornerData p).normalizerSquare i := by
  have h01 := (atom_overlap_pos p hp hA 0 1 (by decide)).le
  have h02 := (atom_overlap_pos p hp hA 0 2 (by decide)).le
  have h03 := (atom_overlap_pos p hp hA 0 3 (by decide)).le
  have h12 := (atom_overlap_pos p hp hA 1 2 (by decide)).le
  have h23 := (atom_overlap_pos p hp hA 2 3 (by decide)).le
  have h31 := (atom_overlap_pos p hp hA 3 1 (by decide)).le
  fin_cases i
  · exact Real.sq_sqrt (by positivity)
  · exact Real.sq_sqrt (by positivity)
  · exact Real.sq_sqrt (by positivity)

theorem atomCornerScalar_pair_access (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (a b : Fin 4) :
    atomCornerScalar p a [(b, true)] = tracePairing (p a) (p b) := by
  rw [atomCornerScalar, nativeWordProbability_eq_pairing,
    nativeWordEffect_singleton p (fun i => (hp i).1)]
  rfl

theorem atomCornerScalar_triangle_access (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (a b c : Fin 4) :
    atomCornerScalar p a [(c, true)] + atomCornerScalar p a [(b, true), (c, true)] -
      atomCornerScalar p a [(b, false), (c, true)] =
        2 * tracePairing (p a) (jordanMul (p b) (p c)) := by
  rw [← signedAccessScalar_value]
  exact native_scalar_triangle_access p (fun i => (hp i).1) (p a) b c

theorem atomCornerScalar_triple_access (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (a b c d : Fin 4) :
    weightedWordScalar (atomCornerScalar p a) (polarizedTripleWordTerms b c d) =
      4 * tracePairing (p a) (jordanTriple (p b) (p c) (p d)) := by
  rw [jordanTriple_eq_access]
  exact native_scalar_polarizedTriple_access p (fun i => (hp i).1) (p a) b c d

theorem atomCorner_conditions (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    CornerScalarConditions (atomCornerData p) (atomCornerScalar p) := by
  refine ⟨atomCornerData_normalizer_nonzero p hp hA,
    atomCornerData_normalizer_square p hp hA,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [atomCornerScalar_pair_access p hp, atomCornerData_overlap_ne p hab]
  · exact atomCornerScalar_triangle_access p hp 0 1 2
  · exact atomCornerScalar_triangle_access p hp 0 2 3
  · exact atomCornerScalar_triangle_access p hp 0 3 1
  · exact atomCornerScalar_triangle_access p hp 1 2 3
  · exact atomCornerScalar_triple_access p hp 0 1 2 3
  · exact atomCornerScalar_triple_access p hp 0 2 3 1
  · exact atomCornerScalar_triple_access p hp 0 3 1 2

end CornerData

section Discriminant

private def cornerDiscriminantPoly (d : CornerNumericalData) : ℝ :=
  let b₁ := d.r012 ^ 2 - d.o01 * d.o12 * d.o02;
  let b₂ := d.r023 ^ 2 - d.o02 * d.o23 * d.o03;
  let b₃ := d.r031 ^ 2 - d.o03 * d.o31 * d.o01;
  let b₁₂ := d.o02 * d.q123 - d.r012 * d.r023;
  let b₂₃ := d.o03 * d.q231 - d.r023 * d.r031;
  let b₁₃ := d.o01 * d.q312 - d.r031 * d.r012;
  let s := d.o01 * d.o02 * d.o03 * d.r123 - d.r012 * d.r023 * d.r031 -
    d.r012 * b₂₃ - d.r023 * b₁₃ - d.r031 * b₁₂;
  -(b₁ * b₂ * b₃ + 2 * b₁₂ * b₂₃ * b₁₃ -
    b₁ * b₂₃ ^ 2 - b₂ * b₁₃ ^ 2 - b₃ * b₁₂ ^ 2) - s ^ 2

private theorem cornerNumericalData_discriminant_mul_nu
    (d : CornerNumericalData)
    (h0 : d.ν0 ≠ 0) (h1 : d.ν1 ≠ 0) (h2 : d.ν2 ≠ 0)
    (hs0 : d.ν0 ^ 2 = d.o01 * d.o12 * d.o02)
    (hs1 : d.ν1 ^ 2 = d.o02 * d.o23 * d.o03)
    (hs2 : d.ν2 ^ 2 = d.o03 * d.o31 * d.o01) :
    d.scalarParameters.discriminant * (d.ν0 ^ 2 * d.ν1 ^ 2 * d.ν2 ^ 2) =
      cornerDiscriminantPoly d := by
  let b₁ := d.r012 ^ 2 - d.o01 * d.o12 * d.o02
  let b₂ := d.r023 ^ 2 - d.o02 * d.o23 * d.o03
  let b₃ := d.r031 ^ 2 - d.o03 * d.o31 * d.o01
  let b₁₂ := d.o02 * d.q123 - d.r012 * d.r023
  let b₂₃ := d.o03 * d.q231 - d.r023 * d.r031
  let b₁₃ := d.o01 * d.q312 - d.r031 * d.r012
  let s := d.o01 * d.o02 * d.o03 * d.r123 - d.r012 * d.r023 * d.r031 -
    d.r012 * b₂₃ - d.r023 * b₁₃ - d.r031 * b₁₂
  have hm1 : d.scalarParameters.m1 = -b₁ / d.ν0 ^ 2 := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, Matrix.cons_val_zero, b₁]
    rw [← hs0]
    field_simp [h0]
    ring
  have hm2 : d.scalarParameters.m2 = -b₂ / d.ν1 ^ 2 := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, Matrix.cons_val_one, Matrix.cons_val_zero, b₂]
    rw [← hs1]
    field_simp [h1]
    ring
  have hm3 : d.scalarParameters.m3 = -b₃ / d.ν2 ^ 2 := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons, b₃]
    rw [← hs2]
    field_simp [h2]
    ring
  have hu : d.scalarParameters.u = -b₁₂ / (d.ν0 * d.ν1) := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, CornerNumericalData.mixed12,
      Matrix.cons_val_zero, Matrix.cons_val_one, b₁₂]
    field_simp [h0, h1]
    ring
  have hv : d.scalarParameters.v = -b₁₃ / (d.ν0 * d.ν2) := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, CornerNumericalData.mixed13,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, b₁₃]
    field_simp [h0, h2]
    ring
  have hw : d.scalarParameters.w = -b₂₃ / (d.ν1 * d.ν2) := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerNumericalData.hermitianConstants, CornerNumericalData.mixed23,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, b₂₃]
    field_simp [h1, h2]
    ring
  have hd0 : d.scalarParameters.d0 = s / (d.ν0 * d.ν1 * d.ν2) := by
    simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
      CornerHolonomy.cornerScalarPart, CornerNumericalData.hermitianConstants,
      CornerNumericalData.mixed12, CornerNumericalData.mixed13, CornerNumericalData.mixed23,
      CornerNumericalData.cubicConstant, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, s, b₁₂, b₁₃, b₂₃]
    field_simp [h0, h1, h2]
    ring
  rw [CliffordScalarParameters.discriminant, hm1, hm2, hm3, hu, hv, hw, hd0,
    cornerDiscriminantPoly]
  dsimp only [b₁, b₂, b₃, b₁₂, b₂₃, b₁₃, s]
  field_simp [h0, h1, h2]
  ring

theorem atomCorner_discriminant_mul_normalizers (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    (atomCornerData p).scalarParameters.discriminant *
        ((atomCornerData p).ν0 ^ 2 * (atomCornerData p).ν1 ^ 2 * (atomCornerData p).ν2 ^ 2) =
      tetrahedronDiscriminant (nativeOverlaps p) (nativeTriangles p) (nativeCornerQ p) := by
  have h0 : (atomCornerData p).ν0 ≠ 0 := atomCornerData_normalizer_nonzero p hp hA 0
  have h1 : (atomCornerData p).ν1 ≠ 0 := atomCornerData_normalizer_nonzero p hp hA 1
  have h2 : (atomCornerData p).ν2 ≠ 0 := atomCornerData_normalizer_nonzero p hp hA 2
  have hs0 : (atomCornerData p).ν0 ^ 2 =
      (atomCornerData p).o01 * (atomCornerData p).o12 * (atomCornerData p).o02 :=
    atomCornerData_normalizer_square p hp hA 0
  have hs1 : (atomCornerData p).ν1 ^ 2 =
      (atomCornerData p).o02 * (atomCornerData p).o23 * (atomCornerData p).o03 :=
    atomCornerData_normalizer_square p hp hA 1
  have hs2 : (atomCornerData p).ν2 ^ 2 =
      (atomCornerData p).o03 * (atomCornerData p).o31 * (atomCornerData p).o01 :=
    atomCornerData_normalizer_square p hp hA 2
  rw [cornerNumericalData_discriminant_mul_nu (atomCornerData p) h0 h1 h2 hs0 hs1 hs2]
  dsimp only [cornerDiscriminantPoly, atomCornerData]
  simp only [tetrahedronDiscriminant, nativeOverlaps, nativeTriangles,
    nativeCornerQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [tracePairing_comm (p 2) (p 0), tracePairing_comm (p 3) (p 0),
    tracePairing_comm (p 1) (p 0)]

theorem atomCorner_discriminant_eq (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    (atomCornerData p).scalarParameters.discriminant =
      fourPointInvariant p /
        (tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) *
         tracePairing (p 1) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 3) (p 1)) := by
  have h01 := atom_overlap_pos p hp hA 0 1 (by decide)
  have h02 := atom_overlap_pos p hp hA 0 2 (by decide)
  have h03 := atom_overlap_pos p hp hA 0 3 (by decide)
  have h12 := atom_overlap_pos p hp hA 1 2 (by decide)
  have h23 := atom_overlap_pos p hp hA 2 3 (by decide)
  have h31 := atom_overlap_pos p hp hA 3 1 (by decide)
  have hmul := atomCorner_discriminant_mul_normalizers p hp hA
  rw [tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant p] at hmul
  have hs0 : (atomCornerData p).ν0 ^ 2 =
      tracePairing (p 0) (p 1) * tracePairing (p 1) (p 2) * tracePairing (p 0) (p 2) :=
    atomCornerData_normalizer_square p hp hA 0
  have hs1 : (atomCornerData p).ν1 ^ 2 =
      tracePairing (p 0) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 0) (p 3) :=
    atomCornerData_normalizer_square p hp hA 1
  have hs2 : (atomCornerData p).ν2 ^ 2 =
      tracePairing (p 0) (p 3) * tracePairing (p 3) (p 1) * tracePairing (p 0) (p 1) :=
    atomCornerData_normalizer_square p hp hA 2
  rw [hs0, hs1, hs2] at hmul
  change (atomCornerData p).scalarParameters.discriminant * _ =
    tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) *
      fourPointInvariant p at hmul
  have hden : tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) *
      tracePairing (p 1) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 3) (p 1) ≠ 0 := by
    positivity
  have h0123 : tracePairing (p 0) (p 1) ≠ 0 ∧ tracePairing (p 0) (p 2) ≠ 0 ∧
      tracePairing (p 0) (p 3) ≠ 0 := ⟨h01.ne', h02.ne', h03.ne'⟩
  apply (eq_div_iff hden).mpr
  have heq : (atomCornerData p).scalarParameters.discriminant *
      (tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3)) *
      (tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) *
        tracePairing (p 1) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 3) (p 1)) =
      fourPointInvariant p *
        (tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3)) := by
    linear_combination hmul
  have hc : tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h0123.1 h0123.2.1) h0123.2.2
  exact mul_right_cancel₀ hc (by linear_combination heq)

theorem atomCorner_discriminant_pos (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    0 < (atomCornerData p).scalarParameters.discriminant := by
  rw [atomCorner_discriminant_eq p hp hA]
  have h01 := atom_overlap_pos p hp hA 0 1 (by decide)
  have h02 := atom_overlap_pos p hp hA 0 2 (by decide)
  have h03 := atom_overlap_pos p hp hA 0 3 (by decide)
  have h12 := atom_overlap_pos p hp hA 1 2 (by decide)
  have h23 := atom_overlap_pos p hp hA 2 3 (by decide)
  have h31 := atom_overlap_pos p hp hA 3 1 (by decide)
  positivity

private theorem overlapProd_swapBase (p : Fin 4 → Albert) (j : Fin 4) :
    tracePairing (p (Equiv.swap 0 j 0)) (p (Equiv.swap 0 j 1)) *
        tracePairing (p (Equiv.swap 0 j 0)) (p (Equiv.swap 0 j 2)) *
        tracePairing (p (Equiv.swap 0 j 0)) (p (Equiv.swap 0 j 3)) *
        tracePairing (p (Equiv.swap 0 j 1)) (p (Equiv.swap 0 j 2)) *
        tracePairing (p (Equiv.swap 0 j 2)) (p (Equiv.swap 0 j 3)) *
        tracePairing (p (Equiv.swap 0 j 3)) (p (Equiv.swap 0 j 1)) =
      tracePairing (p 0) (p 1) * tracePairing (p 0) (p 2) * tracePairing (p 0) (p 3) *
        tracePairing (p 1) (p 2) * tracePairing (p 2) (p 3) * tracePairing (p 3) (p 1) := by
  fin_cases j
  · have h0 : Equiv.swap (0 : Fin 4) ⟨0, by decide⟩ = 1 := by decide
    simp only [h0, Equiv.Perm.one_apply]
  · have h0 : Equiv.swap (0 : Fin 4) ⟨1, by decide⟩ 0 = 1 := by decide
    have h1 : Equiv.swap (0 : Fin 4) ⟨1, by decide⟩ 1 = 0 := by decide
    have h2 : Equiv.swap (0 : Fin 4) ⟨1, by decide⟩ 2 = 2 := by decide
    have h3 : Equiv.swap (0 : Fin 4) ⟨1, by decide⟩ 3 = 3 := by decide
    rw [h0, h1, h2, h3, tracePairing_comm (p 1) (p 0), tracePairing_comm (p 1) (p 3),
      tracePairing_comm (p 3) (p 0)]
    ring
  · have h0 : Equiv.swap (0 : Fin 4) ⟨2, by decide⟩ 0 = 2 := by decide
    have h1 : Equiv.swap (0 : Fin 4) ⟨2, by decide⟩ 1 = 1 := by decide
    have h2 : Equiv.swap (0 : Fin 4) ⟨2, by decide⟩ 2 = 0 := by decide
    have h3 : Equiv.swap (0 : Fin 4) ⟨2, by decide⟩ 3 = 3 := by decide
    rw [h0, h1, h2, h3, tracePairing_comm (p 2) (p 1), tracePairing_comm (p 2) (p 0),
      tracePairing_comm (p 1) (p 0)]
    ring
  · have h0 : Equiv.swap (0 : Fin 4) ⟨3, by decide⟩ 0 = 3 := by decide
    have h1 : Equiv.swap (0 : Fin 4) ⟨3, by decide⟩ 1 = 1 := by decide
    have h2 : Equiv.swap (0 : Fin 4) ⟨3, by decide⟩ 2 = 2 := by decide
    have h3 : Equiv.swap (0 : Fin 4) ⟨3, by decide⟩ 3 = 0 := by decide
    rw [h0, h1, h2, h3, tracePairing_comm (p 3) (p 2), tracePairing_comm (p 3) (p 0),
      tracePairing_comm (p 2) (p 0)]
    ring

theorem atomCorner_discriminant_swapBase (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (j : Fin 4) :
    (atomCornerData (p ∘ Equiv.swap 0 j)).scalarParameters.discriminant =
      (atomCornerData p).scalarParameters.discriminant := by
  have hpj : ∀ i, IsAtom ((p ∘ Equiv.swap 0 j) i) := fun i => hp (Equiv.swap 0 j i)
  have hAj : 0 < fourPointInvariant (p ∘ Equiv.swap 0 j) := fourPointInvariant_swapBase p j hA
  rw [atomCorner_discriminant_eq (p ∘ Equiv.swap 0 j) hpj hAj,
    atomCorner_discriminant_eq p hp hA, fourPointInvariant_swapBase_eq]
  exact congrArg (fourPointInvariant p / ·) (overlapProd_swapBase p j)

end Discriminant

section NativeLeaves

theorem atomCorner_leaf_native_zero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (l : SupportedPurityLeaf (Fin 4))
    (hl : LeafCalibrated (atomCornerScalar p) l) :
    l.wordFunctional.evaluate (nativeWordProbability p ρ) = 0 := by
  have ha : nativeOutcome p l.outcome = p l.outcome.1 := by
    change (if l.outcome.2 then _ else _) = _
    rw [hl.1]
    rfl
  apply l.wordFunctional_native_zero p (fun a => (hp a).1) ρ
  · rw [ha]
    exact hp l.outcome.1
  · rw [hl.2, ha]
    exact nativeWordProbability_eq_pairing _ _ _

theorem atomCorner_constructor_native_zero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) :
    ∀ o ∈ cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p),
      o.leaf.wordFunctional.evaluate (nativeWordProbability p ρ) = 0 := by
  intro o ho
  exact atomCorner_leaf_native_zero p hp ρ o.leaf
    (cornerResidualTelescope_calibrated _ _ o ho)

theorem atomCorner_combined_leaves_native_zero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) :
    ∀ o ∈ combinedCornerOccurrences
        (fun j => atomCornerData (p ∘ Equiv.swap 0 j))
        (fun j => atomCornerScalar (p ∘ Equiv.swap 0 j))
        (fun j => (Equiv.swap 0 j : Fin 4 → Fin 4))
        (fun _ => 1),
      o.leaf.wordFunctional.evaluate (nativeWordProbability p ρ) = 0 := by
  intro o ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  change (SupportedPurityLeaf.relabel (Equiv.swap 0 j : Fin 4 → Fin 4) v.leaf).wordFunctional.evaluate _ = 0
  rw [SupportedPurityLeaf.wordFunctional_relabel, FiniteRealWordFunctional.evaluate_relabel]
  have hpj : ∀ i, IsAtom ((p ∘ Equiv.swap 0 j) i) := fun i => hp (Equiv.swap 0 j i)
  have hz := atomCorner_constructor_native_zero (p ∘ Equiv.swap 0 j) hpj ρ v hv
  simpa only [nativeWordProbability_relabel] using hz

end NativeLeaves

section Witnesses

/-- Single-base (base `0`) explicit residual-telescope separator for arbitrary four atoms `p`. -/
def atomCornerSingleBaseWitness (p : Fin 4 → Albert) (m : ℝ) : FiniteRealWordFunctional 4 :=
  constructiveResidualSeparator
    (cornerBaseFunctional (atomCornerData p))
    (cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p))
    m

theorem atomCornerSingleBaseWitness_model_nonnegative
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData (Fin 4) A) (m : ℝ) (hm : 0 < m) :
    0 ≤ (atomCornerSingleBaseWitness p m).evaluate M.probability :=
  constructiveResidualSeparator_model_nonnegative M
    (cornerBaseFunctional (atomCornerData p))
    (cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p))
    m hm (by
      rw [cornerBaseFunctional_evaluate]
      exact cornerResidualTelescope_identity (atomCornerData p) (atomCornerScalar p)
        (atomCorner_conditions p hp hA) M)

theorem atomCornerSingleBaseWitness_native_le
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (hρ : IsDensity ρ) (m : ℝ) (hm : 0 < m)
    (hmargin : m ≤ (atomCornerData p).scalarParameters.discriminant *
      nativeWordProbability p ρ [(0, true)]) :
    (atomCornerSingleBaseWitness p m).evaluate (nativeWordProbability p ρ) ≤ -(m / 2) := by
  apply constructiveResidualSeparator_target_margin
  · exact hm
  · exact hρ.2
  · exact atomCorner_constructor_native_zero p hp ρ
  · rw [cornerBaseFunctional_evaluate]
    exact hmargin

/-- Four-base combined residual-telescope witness for arbitrary four atoms `p`,
obtained by relabelling base `0` at `p ∘ Equiv.swap 0 j` back along `Equiv.swap 0 j`. -/
def atomCornerWitness (p : Fin 4 → Albert) (m : ℝ) : FiniteRealWordFunctional 4 :=
  combinedCornerWitness
    (fun j => atomCornerData (p ∘ Equiv.swap 0 j))
    (fun j => atomCornerScalar (p ∘ Equiv.swap 0 j))
    (fun j => (Equiv.swap 0 j : Fin 4 → Fin 4))
    (fun _ => 1)
    m

theorem atomCornerWitness_combinedBase_evaluate (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (g : Word (Fin 4) → ℝ) :
    (combinedCornerBase
      (fun j => atomCornerData (p ∘ Equiv.swap 0 j))
      (fun j => (Equiv.swap 0 j : Fin 4 → Fin 4))
      (fun _ => 1)).evaluate g =
      (atomCornerData p).scalarParameters.discriminant * ∑ j : Fin 4, g [(j, true)] := by
  simp only [combinedCornerBase, FiniteRealWordFunctional.evaluate_combine,
    List.map_ofFn, Function.comp_def, FiniteRealWordFunctional.evaluate_scale,
    FiniteRealWordFunctional.evaluate_relabel, cornerBaseFunctional_evaluate,
    one_mul, relabelWord_cons, relabelWord_nil, relabelOutcome, Equiv.swap_apply_left,
    List.sum_ofFn]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun x => p ((Equiv.swap 0 j) x)) = p ∘ Equiv.swap 0 j from rfl,
    atomCorner_discriminant_swapBase p hp hA j]

theorem atomCornerWitness_model_nonnegative
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData (Fin 4) A) (m : ℝ) (hm : 0 < m) :
    0 ≤ (atomCornerWitness p m).evaluate M.probability := by
  refine combinedCornerWitness_model_nonnegative _ _ _ _ ?_ M m hm
  intro j
  exact atomCorner_conditions (p ∘ Equiv.swap 0 j)
    (fun i => hp (Equiv.swap 0 j i)) (fourPointInvariant_swapBase p j hA)

theorem atomCornerWitness_horizon (p : Fin 4 → Albert) (m : ℝ) :
    (atomCornerWitness p m).HasHorizon 11 :=
  combinedCornerWitness_horizon _ _ _ _ m

theorem atomCornerWitness_native_le (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ) (m : ℝ) (hm : 0 < m)
    (hmargin : m ≤ (atomCornerData p).scalarParameters.discriminant *
      tracePairing ρ (p 0 + p 1 + p 2 + p 3)) :
    (atomCornerWitness p m).evaluate (nativeWordProbability p ρ) ≤ -(m / 2) := by
  refine combinedCornerWitness_target_margin _ _ _ _ m hm
    (nativeWordProbability p ρ) hρ.2 (atomCorner_combined_leaves_native_zero p hp ρ) ?_
  rw [atomCornerWitness_combinedBase_evaluate p hp hA]
  have hsum : (∑ j : Fin 4, nativeWordProbability p ρ [(j, true)]) =
      tracePairing ρ (p 0 + p 1 + p 2 + p 3) := by
    have hsing (j : Fin 4) : nativeWordProbability p ρ [(j, true)] = tracePairing ρ (p j) := by
      rw [nativeWordProbability_eq_pairing, nativeWordEffect_singleton p (fun i => (hp i).1)]
      rfl
    simp only [hsing, Fin.sum_univ_four, tracePairing_add_right]
  rw [hsum]
  exact hmargin

end Witnesses

end AlbertSequential.BlockB
