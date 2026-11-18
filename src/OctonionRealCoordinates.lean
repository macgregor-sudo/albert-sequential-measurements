/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeAlbertLaws

/-! Literal eight real coordinates, with the compact Euclidean pairing. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

abbrev OctonionCoordinate := Fin 2 × Fin 4

def octonionRealCoordinates : Octonion ≃ₗ[ℝ] (OctonionCoordinate → ℝ) where
  toFun x i := if i.1 = 0 then ![x.1.re, x.1.imI, x.1.imJ, x.1.imK] i.2
    else ![x.2.re, x.2.imI, x.2.imJ, x.2.imK] i.2
  invFun v := (⟨v (0,0), v (0,1), v (0,2), v (0,3)⟩,
    ⟨v (1,0), v (1,1), v (1,2), v (1,3)⟩)
  left_inv x := by apply Prod.ext <;> rfl
  right_inv v := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' r x := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem octonionRealCoordinates_apply (x : Octonion) (i : OctonionCoordinate) :
    octonionRealCoordinates x i =
      if i.1 = 0 then ![x.1.re, x.1.imI, x.1.imJ, x.1.imK] i.2
      else ![x.2.re, x.2.imI, x.2.imJ, x.2.imK] i.2 := rfl

theorem octonionRealCoordinates_pairing (x y : Octonion) :
    octDot x y = ∑ i, octonionRealCoordinates x i * octonionRealCoordinates y i := by
  rw [octDot_eq_coords]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four,
    octonionRealCoordinates_apply]
  ring

abbrev SpinorCoordinate := Fin 2 × OctonionCoordinate

theorem spinorCoordinate_card : Fintype.card SpinorCoordinate = 16 := by decide

def octonionPairCoordinates : (Octonion × Octonion) ≃ₗ[ℝ] (SpinorCoordinate → ℝ) where
  toFun x i := octonionRealCoordinates (if i.1 = 0 then x.1 else x.2) i.2
  invFun v := (octonionRealCoordinates.symm (fun i => v (0,i)),
    octonionRealCoordinates.symm (fun i => v (1,i)))
  left_inv x := by
    change (octonionRealCoordinates.symm (octonionRealCoordinates x.1),
      octonionRealCoordinates.symm (octonionRealCoordinates x.2)) = x
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv v := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;>
      exact congrFun (LinearEquiv.apply_symm_apply octonionRealCoordinates _) j
  map_add' x y := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> exact congrFun (map_add octonionRealCoordinates _ _) j
  map_smul' r x := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> exact congrFun (map_smul octonionRealCoordinates r _) j

@[simp] theorem octonionPairCoordinates_apply (x : Octonion × Octonion)
    (i : SpinorCoordinate) : octonionPairCoordinates x i =
      octonionRealCoordinates (if i.1 = 0 then x.1 else x.2) i.2 := rfl

theorem octonionPairCoordinates_pairing (x y : Octonion × Octonion) :
    octDot x.1 y.1 + octDot x.2 y.2 =
      ∑ i, octonionPairCoordinates x i * octonionPairCoordinates y i := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, octonionPairCoordinates_apply,
    ↓reduceIte, one_ne_zero]
  rw [octonionRealCoordinates_pairing, octonionRealCoordinates_pairing]

end AlbertSequential.NativeAnalysis
