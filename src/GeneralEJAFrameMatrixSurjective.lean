/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameMatrixRealization

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
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C
local notation "edge" => P.peirceCoefficientMatrixEdge hfr c C

theorem peirceCoefficient_eq_scalar_of_conjugate_fixed (a : A) (ha : a = bar a) :
    B a C.unit • C.unit = a := by
  rw [P.peirceCoefficientConjugate_apply] at ha
  linear_combination (norm := module) (-1 / 2 : ℝ) • ha

omit [FiniteDimensional ℝ E] in
private theorem diagonalSingles_diagonal (Y : Mat) (i : Fin n) :
    (∑ k, Matrix.single k k (Y k k) i i) = Y i i := by
  calc
    _ = Matrix.single i i (Y i i) i i :=
      Finset.sum_eq_single (f := fun k : Fin n => Matrix.single k k (Y k k) i i) i
        (fun k _ h => Matrix.single_apply_of_row_ne h _ _ _)
        (fun h => (h (Finset.mem_univ i)).elim)
    _ = _ := Matrix.single_apply_same i i (Y i i)

omit [FiniteDimensional ℝ E] in
private theorem diagonalSingles_upper (Y : Mat) {i j : Fin n} (hij : i < j) :
    (∑ k, Matrix.single k k (Y k k) i j) = 0 :=
  Finset.sum_eq_zero fun k _ =>
    Matrix.single_apply_of_ne k k (Y k k) i j (fun h => (ne_of_lt hij) (h.1.symm.trans h.2))

private theorem edgeSingles_diagonal (Y : Mat) (i : Fin n) :
    (∑ kl : IncreasingFramePairs n, edge kl.val.1 kl.val.2 (Y kl.val.1 kl.val.2) i i) = 0 := by
  apply Finset.sum_eq_zero
  intro kl _
  change Matrix.single kl.val.1 kl.val.2 (Y kl.val.1 kl.val.2) i i +
    Matrix.single kl.val.2 kl.val.1 (bar (Y kl.val.1 kl.val.2)) i i = 0
  rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => (ne_of_lt kl.property) (h.1.trans h.2.symm)),
    Matrix.single_apply_of_ne _ _ _ _ _ (fun h => (ne_of_lt kl.property) (h.2.trans h.1.symm)), add_zero]

private theorem edgeSingles_upper (Y : Mat) {i j : Fin n} (hij : i < j) :
    (∑ kl : IncreasingFramePairs n, edge kl.val.1 kl.val.2 (Y kl.val.1 kl.val.2) i j) = Y i j := by
  let ij : IncreasingFramePairs n := ⟨(i,j), hij⟩
  calc
    _ = edge i j (Y i j) i j :=
      Finset.sum_eq_single ij
        (fun kl _ hk => by
          change Matrix.single kl.val.1 kl.val.2 (Y kl.val.1 kl.val.2) i j +
            Matrix.single kl.val.2 kl.val.1 (bar (Y kl.val.1 kl.val.2)) i j = 0
          rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hk (Subtype.ext (Prod.ext h.1 h.2))),
            Matrix.single_apply_of_ne _ _ _ _ _ (by
              intro h
              have hj : j < i := by simpa only [h.1, h.2] using kl.property
              exact (lt_asymm hij) hj), add_zero])
        (fun h => (h (Finset.mem_univ ij)).elim)
    _ = _ := by
      change Matrix.single i j (Y i j) i j + Matrix.single j i (bar (Y i j)) i j = _
      rw [Matrix.single_apply_same, Matrix.single_apply_of_row_ne (ne_of_gt hij), add_zero]

section Map

variable (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hrs : r < s) (hst : s < t)
    (D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst)

local notation "F" => P.peirceFrameMatrix hfr c C hc hor hunit hinner hrs hst D

theorem peirceFrameMatrix_surjective_hermitian (Y : Mat)
    (hY : P.PeirceCoefficientHermitian hfr c C Y) :
    ∃ x, F x = Y := by
  let a (i : Fin n) : ℝ := B (Y i i) C.unit
  let u (ij : IncreasingFramePairs n) : W ij.val.1 ij.val.2 :=
    (D.chart ij.val.1 ij.val.2 ij.property).symm (Y ij.val.1 ij.val.2)
  let x := (∑ i, a i • c i) + ∑ ij : IncreasingFramePairs n, (u ij).val
  have hd (i : Fin n) : a i • C.unit = Y i i :=
    P.peirceCoefficient_eq_scalar_of_conjugate_fixed hfr c C (Y i i) (hY i i)
  have hx :
      F x = (∑ i, Matrix.single i i (Y i i)) +
        ∑ ij : IncreasingFramePairs n, edge ij.val.1 ij.val.2 (Y ij.val.1 ij.val.2) := by
    change F ((∑ i, a i • c i) + ∑ ij : IncreasingFramePairs n, (u ij).val) = _
    rw [map_add, map_sum, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, P.peirceFrameMatrix_on_primitive hfr c C hc hor hunit hinner hrs hst D,
        Matrix.smul_single, hd]
    · apply Finset.sum_congr rfl
      intro ij _
      rw [P.peirceFrameMatrix_on_edge hfr c C hc hor hunit hinner hrs hst D ij.property]
      change edge ij.val.1 ij.val.2
        (D.chart ij.val.1 ij.val.2 ij.property ((D.chart ij.val.1 ij.val.2 ij.property).symm _)) = _
      rw [LinearEquiv.apply_symm_apply]
  have hup (i j : Fin n) (hij : i ≤ j) : F x i j = Y i j := by
    rw [hx, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply]
    rcases lt_or_eq_of_le hij with h | rfl
    · rw [P.diagonalSingles_upper c Y h, P.edgeSingles_upper hfr c C Y h, zero_add]
    · rw [P.diagonalSingles_diagonal c Y, P.edgeSingles_diagonal hfr c C Y, add_zero]
  refine ⟨x, Matrix.ext fun i j => ?_⟩
  by_cases hij : i ≤ j
  · exact hup i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    rw [P.peirceFrameMatrix_hermitian hfr c C hc hor hunit hinner hrs hst D x j i, hY j i, hup j i hji]

end Map

structure PeirceHermitianMatrixEquivalence extends P.FaithfulPeirceHermitianMatrixMap hfr c C where
  onto : ∀ Y : Mat, P.PeirceCoefficientHermitian hfr c C Y → ∃ x, map x = Y

theorem exists_peirceHermitianMatrixEquivalence_of_simple
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) (hrs : r < s) (hst : s < t)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j) :
    ∃ C₀ : P.PeirceTriangleCoordinates (P.formallyReal_of_associative_inner hinner) c r s t,
      Nonempty (P.PeirceHermitianMatrixEquivalence (P.formallyReal_of_associative_inner hinner) c C₀) := by
  let hfr₀ := P.formallyReal_of_associative_inner hinner
  obtain ⟨C₀⟩ := P.exists_peirceTriangleCoordinates_of_simple c hc hor hunit hinner hsimple
    (ne_of_lt hrs) (ne_of_lt (lt_trans hrs hst)) (ne_of_lt hst)
  have hconn (i j : Fin n) (hij : i < j) : W i j ≠ ⊥ :=
    P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j (ne_of_lt hij)
  obtain ⟨C₁, _, _, D, hform⟩ := P.exists_peirceIncreasingFrameChart_normalized hfr₀ c C₀ hc hor hunit hrs hst
    hfirst hconn
  exact ⟨C₁, ⟨{
    map := P.peirceFrameMatrix hfr₀ c C₁ hc hor hunit hinner hrs hst D
    injective := P.peirceFrameMatrix_injective hfr₀ c C₁ hc hor hunit hinner hrs hst D
    hermitian := P.peirceFrameMatrix_hermitian hfr₀ c C₁ hc hor hunit hinner hrs hst D
    unit := P.peirceFrameMatrix_unit hfr₀ c C₁ hc hor hunit hinner hrs hst D
    jordan := P.peirceFrameMatrix_product hfr₀ c C₁ hc hor hunit hinner hrs hst D hform
    onto := P.peirceFrameMatrix_surjective_hermitian hfr₀ c C₁ hc hor hunit hinner hrs hst D }⟩⟩

end AlbertSequential.UnitalJordanProduct
