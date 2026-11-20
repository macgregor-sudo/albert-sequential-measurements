/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationEndpoint
import Mathlib.Tactic.FinCases

/-! The signed complex coordinates of the published fixed-S left-multiplication model. -/
@[expose] public section
noncomputable section
open scoped Matrix BigOperators
namespace AlbertSequential.NativeAnalysis
open MatchingModels

private theorem octAdd_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem octAdd_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem octSmul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem octSmul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

def fixedSComplexCoordinates : Octonion ≃ₗ[ℝ] (Fin 4 → ℂ) where
  toFun x := ![⟨x.1.re, -x.1.imK⟩, ⟨x.2.imK, -x.2.re⟩,
    ⟨x.1.imJ, -x.1.imI⟩, ⟨-x.2.imI, -x.2.imJ⟩]
  invFun z := (⟨(z 0).re, -(z 2).im, (z 2).re, -(z 0).im⟩,
    ⟨-(z 1).im, -(z 3).re, -(z 3).im, (z 1).re⟩)
  left_inv x := by apply Prod.ext <;> apply Quaternion.ext <;> simp
  right_inv z := by funext i; fin_cases i <;> apply Complex.ext <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> apply Complex.ext <;> simp [octAdd_fst, octAdd_snd, add_comm]
  map_smul' r x := by
    funext i
    fin_cases i <;> apply Complex.ext <;> simp [octSmul_fst, octSmul_snd]

theorem fixedSComplexCoordinates_apply (x : Octonion) (i : Fin 4) :
    fixedSComplexCoordinates x i = ![⟨x.1.re, -x.1.imK⟩, ⟨x.2.imK, -x.2.re⟩,
      ⟨x.1.imJ, -x.1.imI⟩, ⟨-x.2.imI, -x.2.imJ⟩] i := rfl

theorem fixedSComplexCoordinates_pairing (x y : Octonion) :
    octDot x y = ∑ i, (star (fixedSComplexCoordinates x i) * fixedSComplexCoordinates y i).re := by
  rw [octDot_eq_coords, Fin.sum_univ_four]
  simp [fixedSComplexCoordinates_apply, Complex.mul_re]
  ring

theorem fixedSComplexCoordinates_i (x : Octonion) :
    fixedSComplexCoordinates (octonionMul octI x) = (-dfailsC1) *ᵥ fixedSComplexCoordinates x := by
  funext i
  simp only [fixedSComplexCoordinates_apply]
  fin_cases i <;> apply Complex.ext <;>
    simp [octonionMul, octI, dfailsC1, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      fixedSComplexCoordinates_apply, Complex.mul_re, Complex.mul_im]

theorem fixedSComplexCoordinates_j (x : Octonion) :
    fixedSComplexCoordinates (octonionMul octJ x) = (-dfailsC2) *ᵥ fixedSComplexCoordinates x := by
  funext i
  simp only [fixedSComplexCoordinates_apply]
  fin_cases i <;> apply Complex.ext <;>
    simp [octonionMul, octJ, dfailsC2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      fixedSComplexCoordinates_apply]

theorem fixedSComplexCoordinates_ell (x : Octonion) :
    fixedSComplexCoordinates (octonionMul octL x) = (-dfailsC3) *ᵥ fixedSComplexCoordinates x := by
  funext i
  simp only [fixedSComplexCoordinates_apply]
  fin_cases i <;> apply Complex.ext <;>
    simp [octonionMul, octL, dfailsC3, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      fixedSComplexCoordinates_apply, Complex.mul_re, Complex.mul_im]

theorem fixedSComplexCoordinates_volume (x : Octonion) :
    fixedSComplexCoordinates (octonionMul octI (octonionMul octJ (octonionMul octL x))) =
      (-dfailsJ) *ᵥ fixedSComplexCoordinates x := by
  rw [fixedSComplexCoordinates_i, fixedSComplexCoordinates_j, fixedSComplexCoordinates_ell,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, dfailsC1_C2_C3]

/-- The positive generator convention and the signs of the published C column conflict. -/
theorem fixedS_positive_i_incompatible
    (F : Octonion ≃ₗ[ℝ] (Fin 4 → ℂ))
    (h : ∀ x, F (octonionMul octI x) = dfailsC1 *ᵥ F x) :
    ¬ ∀ x, F (octonionMul octI x) = (-dfailsC1) *ᵥ F x := by
  intro h'
  let v := (Pi.single 2 1 : Fin 4 → ℂ)
  let x := F.symm v
  have he : dfailsC1 *ᵥ v = (-dfailsC1) *ᵥ v := by
    rw [← F.apply_symm_apply v]
    exact (h x).symm.trans (h' x)
  have hentry := congrFun he 0
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hentry
  change Complex.I = -Complex.I at hentry
  have hi := congrArg Complex.im hentry
  norm_num at hi

end AlbertSequential.NativeAnalysis
