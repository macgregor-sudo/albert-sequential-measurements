/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationFixedSBasis
import Mathlib.Tactic.FinCases

/-! The literal normalized S columns intertwine the published complex projectors. -/
@[expose] public section
noncomputable section
open scoped Matrix BigOperators
namespace AlbertSequential.NativeAnalysis
open MatchingModels

def fixedSLeftRawColumns : Fin 4 → Fin 3 → Octonion :=
  ![![octOne, 0, 0], ![octOne, octOne, 0], ![octOne, octI, octOne], ![octOne, octJ, octL]]

def fixedSLeftScale : Fin 4 → ℝ :=
  ![1, (Real.sqrt 2)⁻¹, (Real.sqrt 3)⁻¹, (Real.sqrt 3)⁻¹]

def fixedSLeftColumns (i : Fin 4) (j : Fin 3) : Octonion :=
  fixedSLeftScale i • fixedSLeftRawColumns i j

def fixedSComplexRawBlocks : Fin 4 → Fin 3 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0], ![1, 1, 0], ![1, -dfailsC1, 1], ![1, -dfailsC2, -dfailsC3]]

def fixedSComplexStack (z : Fin 3 → Octonion) (r : Fin 12) : ℂ :=
  let ij := fin3ProdFin4Equiv12.symm r
  fixedSComplexCoordinates (z ij.1) ij.2

def fixedSRealStack (z : Fin 3 → Octonion) (r : AlbertColumnCoordinate) : ℝ :=
  octonionRealCoordinates (z r.1) r.2

def fixedSRealStackOf (z : AlbertColumnCoordinate → ℝ) (j : Fin 3) : Octonion :=
  octonionRealCoordinates.symm (fun k => z (j,k))

theorem fixedSRealStackOf_stack (z : Fin 3 → Octonion) :
    fixedSRealStackOf (fixedSRealStack z) = z := by
  funext j
  exact LinearEquiv.symm_apply_apply octonionRealCoordinates (z j)

theorem fixedSRealStack_of (z : AlbertColumnCoordinate → ℝ) :
    fixedSRealStack (fixedSRealStackOf z) = z := by
  funext r
  exact congrFun (LinearEquiv.apply_symm_apply octonionRealCoordinates _) r.2

private theorem fixedSBlockCol12_apply (X Y Z : Matrix (Fin 4) (Fin 4) ℂ)
    (j : Fin 3) (k l : Fin 4) :
    blockCol12 X Y Z (fin3ProdFin4Equiv12 (j,k)) l = (![X,Y,Z] j) k l := by
  unfold blockCol12
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  fin_cases j <;> rfl

private theorem fixedSComplexBlock_apply (i : Fin 4) (j : Fin 3) (k l : Fin 4) :
    dfailsIsometry i (fin3ProdFin4Equiv12 (j,k)) l =
      (fixedSLeftScale i : ℂ) * fixedSComplexRawBlocks i j k l := by
  fin_cases i <;> fin_cases j <;>
    simp [dfailsIsometry, fixedSBlockCol12_apply, fixedSLeftScale, fixedSComplexRawBlocks,
      invSqrt2C, invSqrt3C, Matrix.smul_apply, smul_eq_mul]

private theorem fixedSRawColumns_complex (i : Fin 4) (j : Fin 3) (x : Octonion) :
    fixedSComplexCoordinates (octonionMul (fixedSLeftRawColumns i j) x) =
      fixedSComplexRawBlocks i j *ᵥ fixedSComplexCoordinates x := by
  fin_cases i <;> fin_cases j <;>
    simp [fixedSLeftRawColumns, fixedSComplexRawBlocks, octonionMul_zero_left,
      octonionMul_one_left, fixedSComplexCoordinates_i, fixedSComplexCoordinates_j,
      fixedSComplexCoordinates_ell]

private theorem fixedSRawColumns_adjoint (i : Fin 4) (j : Fin 3) (x : Octonion) :
    fixedSComplexCoordinates (octonionMul (octonionConj (fixedSLeftRawColumns i j)) x) =
      (fixedSComplexRawBlocks i j)ᴴ *ᵥ fixedSComplexCoordinates x := by
  have ci : octonionConj octI = -octI := by
    have hr : octonionReal octI = 0 := rfl
    rw [octConj_eq_two_real_sub, hr, mul_zero, zero_smul, zero_sub]
  have cj : octonionConj octJ = -octJ := by
    have hr : octonionReal octJ = 0 := rfl
    rw [octConj_eq_two_real_sub, hr, mul_zero, zero_smul, zero_sub]
  have cl : octonionConj octL = -octL := by
    have hr : octonionReal octL = 0 := rfl
    rw [octConj_eq_two_real_sub, hr, mul_zero, zero_smul, zero_sub]
  fin_cases i <;> fin_cases j <;>
    simp [fixedSLeftRawColumns, fixedSComplexRawBlocks, octonionConj_one, octonionConj_zero,
      octonionMul_zero_left, octonionMul_one_left, ci, cj, cl, octonionMul_neg_left,
      fixedSComplexCoordinates_i, fixedSComplexCoordinates_j, fixedSComplexCoordinates_ell,
      dfailsC1_conjTranspose, dfailsC2_conjTranspose, dfailsC3_conjTranspose, Matrix.neg_mulVec]

theorem fixedSLeftColumn_complex (i : Fin 4) (x : Octonion) :
    fixedSComplexStack (fun j => octonionMul (fixedSLeftColumns i j) x) =
      dfailsIsometry i *ᵥ fixedSComplexCoordinates x := by
  funext r
  obtain ⟨⟨j,k⟩, rfl⟩ := fin3ProdFin4Equiv12.surjective r
  simp only [fixedSComplexStack, Equiv.symm_apply_apply, fixedSLeftColumns, octonionMul_smul_left,
    map_smul, fixedSRawColumns_complex, Pi.smul_apply, Matrix.mulVec, dotProduct,
    fixedSComplexBlock_apply, mul_assoc, ← Finset.mul_sum, Complex.real_smul]

theorem fixedSLeftColumn_adjoint_complex (i : Fin 4) (z : Fin 3 → Octonion) :
    fixedSComplexCoordinates (∑ j, octonionMul (octonionConj (fixedSLeftColumns i j)) (z j)) =
      (dfailsIsometry i)ᴴ *ᵥ fixedSComplexStack z := by
  funext k
  rw [map_sum, Matrix.mulVec, dotProduct, ← Equiv.sum_comp fin3ProdFin4Equiv12, Fintype.sum_prod_type]
  simp only [Finset.sum_apply, Matrix.conjTranspose_apply, fixedSLeftColumns, octonionConj_smul,
    octonionMul_smul_left, map_smul, Pi.smul_apply, fixedSRawColumns_adjoint, fixedSComplexStack,
    Equiv.symm_apply_apply, fixedSComplexBlock_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
    Matrix.mulVec, dotProduct, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem octonionLeftColumn_adjoint_mulVec (v z : Fin 3 → Octonion) :
    (octonionLeftColumn v)ᵀ *ᵥ fixedSRealStack z =
      octonionRealCoordinates (∑ j, octonionMul (octonionConj (v j)) (z j)) := by
  funext k
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply, octonionLeftColumn_apply, fixedSRealStack]
  rw [← octonionRealCoordinates_pairing, octDot_mul_left, octonionRealCoordinates_pairing]
  simp only [LinearEquiv.apply_symm_apply]
  change Pi.single k 1 ⬝ᵥ _ = _
  simp only [single_one_dotProduct]

theorem fixedSLeftColumns_unit (i : Fin 4) : octonionColumnNormSq (fixedSLeftColumns i) = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹)^2 = 1 / 2 := by norm_num [inv_pow, Real.sq_sqrt]
  have h3 : ((Real.sqrt 3)⁻¹)^2 = 1 / 3 := by norm_num [inv_pow, Real.sq_sqrt]
  have hz : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero _).mpr rfl
  have hi : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; norm_num [octI]
  have hj : octNormSq octJ = 1 := by rw [octNormSq_eq_coords]; norm_num [octJ]
  have hl : octNormSq octL = 1 := by rw [octNormSq_eq_coords]; norm_num [octL]
  unfold octonionColumnNormSq
  simp only [Fin.sum_univ_three, fixedSLeftColumns, octNormSq_smul]
  fin_cases i <;>
    norm_num [fixedSLeftScale, fixedSLeftRawColumns, hz, octNormSq_one, hi, hj, hl, h2, h3]

/-- The coordinate action of each real rank-eight projector equals that of the
published complex projector, with the same real coordinate equivalence for every test. -/
theorem fixedSLeftProjection_complex (i : Fin 4) (z : Fin 3 → Octonion) :
    fixedSComplexStack (fixedSRealStackOf (octonionLeftProjection (fixedSLeftColumns i) *ᵥ fixedSRealStack z)) =
      dfailsProj i *ᵥ fixedSComplexStack z := by
  rw [octonionLeftProjection, fixedSLeftColumns_unit, inv_one, one_smul, ← Matrix.mulVec_mulVec,
    octonionLeftColumn_adjoint_mulVec, octonionLeftColumn_mulVec]
  change fixedSComplexStack (fixedSRealStackOf (fixedSRealStack (fun j =>
    octonionMul (fixedSLeftColumns i j) (∑ k, octonionMul (octonionConj (fixedSLeftColumns i k)) (z k))))) = _
  rw [fixedSRealStackOf_stack, fixedSLeftColumn_complex, fixedSLeftColumn_adjoint_complex,
    Matrix.mulVec_mulVec]
  rfl


/-- A common chart mapping the literal positive (i) generator to (C_1)
cannot also intertwine the published `dfailsIsometry` for the second slot of C. -/
theorem fixedSPositiveGenerator_incompatible_withPublishedColumn
    (F : Octonion ≃ₗ[ℝ] (Fin 4 → ℂ))
    (hPositive : ∀ x, F (octonionMul octI x) = dfailsC1 *ᵥ F x)
    (hColumn : ∀ x k, F (octonionMul (fixedSLeftColumns 2 1) x) k =
      (dfailsIsometry 2 *ᵥ F x) (fin3ProdFin4Equiv12 (1,k))) : False := by
  apply fixedS_positive_i_incompatible F hPositive
  intro x
  funext k
  have h := hColumn x k
  have hc : fixedSLeftColumns 2 1 = fixedSLeftScale 2 • octI := rfl
  rw [hc, octonionMul_smul_left, map_smul, Pi.smul_apply, Complex.real_smul, Matrix.mulVec, dotProduct] at h
  simp only [fixedSComplexBlock_apply, mul_assoc, ← Finset.mul_sum] at h
  have hs : ((fixedSLeftScale 2 : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    change (Real.sqrt 3)⁻¹ ≠ 0
    exact inv_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
  exact mul_left_cancel₀ hs h

end AlbertSequential.NativeAnalysis
