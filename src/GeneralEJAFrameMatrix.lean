/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameProjections
public import GeneralEJAFrameDiagonalCoefficients
public import Mathlib.Data.Matrix.Basis

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "A" => W r t
local notation "Mat" => Matrix (Fin n) (Fin n) A
local notation "bar" => P.peirceCoefficientConjugate hfr c C

theorem peirceCoefficient_conjugate_unit : bar C.unit = C.unit := by
  rw [P.peirceCoefficientConjugate_apply, C.unit_form]
  module

def PeirceCoefficientHermitian (M : Mat) : Prop := ∀ i j, M j i = bar (M i j)

def peirceCoefficientMatrixEdge (i j : Fin n) (a : A) : Mat :=
  Matrix.single i j a + Matrix.single j i (bar a)

variable (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hrs : r < s) (hst : s < t)
    (D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst)

def frameProjectedEdge (i j : Fin n) (hij : i < j) : E →ₗ[ℝ] W i j :=
  LinearMap.codRestrict (W i j) (P.frameEdgeProjection c i j)
    (P.frameEdgeProjection_mem c hc hor hunit hinner i j hij)

local notation "projEdge" => P.frameProjectedEdge c hc hor hunit hinner

def peirceFrameMatrixEntry (i j : Fin n) : E →ₗ[ℝ] A :=
  if hij : i = j then (P.frameDiagonalCoefficient c hfr i).smulRight C.unit
  else if hlt : i < j then (D.chart i j hlt).toLinearMap.comp (projEdge i j hlt)
  else
    let hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    (bar).comp ((D.chart j i hgt).toLinearMap.comp (projEdge j i hgt))

def peirceFrameMatrix : E →ₗ[ℝ] Mat where
  toFun x i j := P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D i j x
  map_add' x y := Matrix.ext fun i j =>
    map_add (P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D i j) x y
  map_smul' a x := Matrix.ext fun i j =>
    map_smul (P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D i j) a x

local notation "F" => P.peirceFrameMatrix hfr c C hc hor hunit hinner hrs hst D

theorem peirceFrameMatrix_diagonal (i : Fin n) (x : E) :
    F x i i = P.frameDiagonalCoefficient c hfr i x • C.unit := by
  change P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D i i x = _
  rw [peirceFrameMatrixEntry, dite_eq_left rfl, LinearMap.smulRight_apply]

theorem peirceFrameMatrix_upper {i j : Fin n} (hij : i < j) (x : E) :
    F x i j = D.chart i j hij (projEdge i j hij x) := by
  change P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D i j x = _
  rw [peirceFrameMatrixEntry, dite_eq_right (ne_of_lt hij), dite_eq_left hij]
  rfl

theorem peirceFrameMatrix_lower {i j : Fin n} (hij : i < j) (x : E) :
    F x j i = bar (D.chart i j hij (projEdge i j hij x)) := by
  change P.peirceFrameMatrixEntry hfr c C hc hor hunit hinner hrs hst D j i x = _
  rw [peirceFrameMatrixEntry, dite_eq_right (ne_of_gt hij), dite_eq_right (not_lt_of_ge hij.le)]
  rfl

theorem peirceFrameMatrix_hermitian (x : E) : P.PeirceCoefficientHermitian hfr c C (F x) := by
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [P.peirceFrameMatrix_lower hfr c C hc hor hunit hinner hrs hst D h,
      P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D h]
  · rw [P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D,
      (bar).map_smul, P.peirceCoefficient_conjugate_unit hfr c C]
  · rw [P.peirceFrameMatrix_lower hfr c C hc hor hunit hinner hrs hst D h,
      P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D h,
      P.peirceCoefficientConjugate_involutive hfr c C]

theorem peirceFrameMatrix_injective : Function.Injective F := by
  intro x y h
  have hd (i : Fin n) : P.frameDiagonalCoefficient c hfr i x = P.frameDiagonalCoefficient c hfr i y := by
    have hdiag := congrArg (fun M : Mat => M i i) h
    rw [P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D,
      P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D] at hdiag
    exact smul_left_injective ℝ (P.peirceTriangle_unit_ne_zero hfr c C) hdiag
  have he (i j : Fin n) (hij : i < j) : P.frameEdgeProjection c i j x = P.frameEdgeProjection c i j y := by
    have hedge := congrArg (fun M : Mat => M i j) h
    rw [P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D hij,
      P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D hij] at hedge
    exact congrArg Subtype.val ((D.chart i j hij).injective hedge)
  calc
    x = (∑ i, P.quadraticRepresentation (c i) x) +
        ∑ ij : IncreasingFramePairs n, P.frameEdgeProjection c ij.val.1 ij.val.2 x :=
      P.framePeirce_reconstruct c hc hor hunit hinner x
    _ = (∑ i, P.quadraticRepresentation (c i) y) +
        ∑ ij : IncreasingFramePairs n, P.frameEdgeProjection c ij.val.1 ij.val.2 y := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [P.canonicalTraceOfFormallyReal_primitive_compression hfr (c i) x (hc i),
          P.canonicalTraceOfFormallyReal_primitive_compression hfr (c i) y (hc i)]
        exact congrArg (fun q : ℝ => q • c i) (hd i)
      · exact Finset.sum_congr rfl (fun ij _ => he ij.val.1 ij.val.2 ij.property)
    _ = y := (P.framePeirce_reconstruct c hc hor hunit hinner y).symm

theorem peirceFrameMatrix_unit : F P.unit = Matrix.diagonal (fun _ : Fin n => C.unit) := by
  have hdiag (i : Fin n) : P.frameDiagonalCoefficient c hfr i P.unit = 1 := by
    change P.canonicalTraceOfFormallyReal hfr (P.product (c i) P.unit) = 1
    rw [P.commutative (c i) P.unit, P.unit_left, P.canonicalTraceOfFormallyReal_primitive hfr (c i) (hc i)]
  have hedge (i j : Fin n) (hij : i < j) : projEdge i j hij P.unit = 0 := by
    apply Subtype.ext
    change P.frameEdgeProjection c i j P.unit = 0
    rw [← hunit, map_sum]
    simp only [P.frameEdgeProjection_on_framePrimitive c hc hor, Finset.sum_const_zero]
  apply Matrix.ext
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D h, hedge, map_zero,
      Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · rw [P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D, hdiag, one_smul,
      Matrix.diagonal_apply_eq]
  · rw [P.peirceFrameMatrix_lower hfr c C hc hor hunit hinner hrs hst D h, hedge, map_zero, map_zero,
      Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem peirceFrameMatrix_on_primitive (k : Fin n) : F (c k) = Matrix.single k k C.unit := by
  have hedge (i j : Fin n) (hij : i < j) : projEdge i j hij (c k) = 0 :=
    Subtype.ext (P.frameEdgeProjection_on_framePrimitive c hc hor i j k)
  apply Matrix.ext
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D h, hedge, map_zero,
      Matrix.single_apply_of_ne _ _ _ _ _ (fun ⟨hi, hj⟩ => (ne_of_lt h) (hi.symm.trans hj))]
  · rw [P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D,
      P.frameDiagonalCoefficient_on_framePrimitive c hfr hc hor, Matrix.single_apply]
    by_cases hk : i = k
    · subst i
      simp
    · simp [hk, Ne.symm hk]
  · rw [P.peirceFrameMatrix_lower hfr c C hc hor hunit hinner hrs hst D h, hedge, map_zero, map_zero,
      Matrix.single_apply_of_ne _ _ _ _ _ (fun ⟨hi, hj⟩ => (ne_of_gt h) (hi.symm.trans hj))]

theorem peirceFrameMatrix_on_edge {i j : Fin n} (hij : i < j) (x : W i j) :
    F x.val = P.peirceCoefficientMatrixEdge hfr c C i j (D.chart i j hij x) := by
  have hedge (k l : Fin n) (hkl : k < l) (h : ¬ (k = i ∧ l = j)) : projEdge k l hkl x.val = 0 := by
    apply Subtype.ext
    change P.frameEdgeProjection c k l x.val = 0
    rw [P.frameEdgeProjection_on_frameEdge c hkl hij x.property, ite_eq_right h]
  have hself : projEdge i j hij x.val = x := by
    apply Subtype.ext
    change P.frameEdgeProjection c i j x.val = x.val
    rw [P.frameEdgeProjection_on_frameEdge c hij hij x.property, ite_eq_left ⟨rfl, rfl⟩]
  apply Matrix.ext
  intro k l
  change F x.val k l =
    Matrix.single i j (D.chart i j hij x) k l + Matrix.single j i (bar (D.chart i j hij x)) k l
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [P.peirceFrameMatrix_upper hfr c C hc hor hunit hinner hrs hst D hkl]
    by_cases h : k = i ∧ l = j
    · rcases h with ⟨rfl, rfl⟩
      rw [hself, Matrix.single_apply_same,
        Matrix.single_apply_of_row_ne (ne_of_gt hij), add_zero]
    · rw [hedge k l hkl h, map_zero, Matrix.single_apply_of_ne _ _ _ _ _
        (fun h' => h ⟨h'.1.symm, h'.2.symm⟩),
        Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; exact (lt_asymm hij hkl)), add_zero]
  · rw [P.peirceFrameMatrix_diagonal hfr c C hc hor hunit hinner hrs hst D,
      P.frameDiagonalCoefficient_on_frameEdge c hfr hc _ x.property, zero_smul,
      Matrix.single_apply_of_ne _ _ _ _ _ (fun ⟨hi, hj⟩ => (ne_of_lt hij) (hi.trans hj.symm)),
      Matrix.single_apply_of_ne _ _ _ _ _ (fun ⟨hj, hi⟩ => (ne_of_lt hij) (hi.trans hj.symm)), add_zero]
  · rw [P.peirceFrameMatrix_lower hfr c C hc hor hunit hinner hrs hst D hkl]
    by_cases h : l = i ∧ k = j
    · rcases h with ⟨rfl, rfl⟩
      rw [hself, Matrix.single_apply_same,
        Matrix.single_apply_of_row_ne (ne_of_lt hij), zero_add]
    · rw [hedge l k hkl h, map_zero, map_zero,
        Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; exact (lt_asymm hij hkl)),
        Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h ⟨h'.2.symm, h'.1.symm⟩), add_zero]

end AlbertSequential.UnitalJordanProduct
