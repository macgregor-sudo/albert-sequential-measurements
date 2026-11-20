/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeAlbertTableMixtures
public import PrintedSlotLaws
import JordanRegularTrace

@[expose] public section
noncomputable section

namespace AlbertSequential

open scoped BigOperators

def albertDerivations : Submodule ℝ (Albert →ₗ[ℝ] Albert) where
  carrier := {D | ∀ x y, D (jordanMul x y) = jordanMul (D x) y + jordanMul x (D y)}
  zero_mem' := by simp [LinearMap.zero_apply, jordanMul_zero_left, jordanMul_zero_right]
  add_mem' {D E} hD hE := by
    intro x y
    simp only [LinearMap.add_apply, hD x y, hE x y, jordanMul_add_left, jordanMul_add_right]
    abel
  smul_mem' r D hD := by
    intro x y
    simp only [LinearMap.smul_apply, hD x y, jordanMul_smul_left, jordanMul_smul_right, smul_add]

abbrev AlbertDerivation := albertDerivations

theorem albertDerivation_mul (D : AlbertDerivation) (x y : Albert) :
    D.val (jordanMul x y) = jordanMul (D.val x) y + jordanMul x (D.val y) := D.property x y

theorem albertDerivation_unit (D : AlbertDerivation) : D.val albertUnit = 0 := by
  have h : D.val albertUnit = D.val albertUnit + D.val albertUnit := by
    simpa only [jordanMul_albertUnit_left, jordanMul_albertUnit_right] using
      albertDerivation_mul D albertUnit albertUnit
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

def albertInnerDerivation (x y : Albert) : AlbertDerivation :=
  ⟨nativeAlbertProduct.innerDerivation x y, nativeAlbertProduct.innerDerivation_product x y⟩

theorem albertInnerDerivation_apply (x y z : Albert) :
    (albertInnerDerivation x y).val z = jordanMul x (jordanMul y z) - jordanMul y (jordanMul x z) := rfl

def derivationUpperSlot (k : Fin 3) : Octonion →ₗ[ℝ] Albert := ![slotElem01,slotElem02,slotElem12] k

def derivationSlotCoord (k : Fin 3) : Albert →ₗ[ℝ] Octonion where
  toFun x := x.2 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def derivationFirst (k : Fin 3) : Fin 3 := ![0,0,1] k
def derivationSecond (k : Fin 3) : Fin 3 := ![1,2,2] k

def derivationSlotWeight (i k : Fin 3) : ℝ :=
  if i = derivationFirst k ∨ i = derivationSecond k then 1/2 else 0

@[simp] theorem derivationSlotCoord_upperSlot (k l : Fin 3) (x : Octonion) :
    derivationSlotCoord k (derivationUpperSlot l x) = if k = l then x else 0 := by
  fin_cases k <;> fin_cases l <;> rfl

@[simp] theorem derivationSlotCoord_diagAtom (k i : Fin 3) : derivationSlotCoord k (diagAtom i) = 0 := rfl

private theorem diagAtom_diag_coordinate (i k : Fin 3) :
    (diagAtom i).1 k = if k = i then 1 else 0 := rfl

private theorem diagAtom_upper_coordinate (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl

theorem jordanMul_diagAtom_diagonal (i k : Fin 3) (x : Albert) :
    (jordanMul (diagAtom i) x).1 k = if i = k then x.1 k else 0 := by
  fin_cases k <;> fin_cases i <;>
    simp [jordanMul_diag_0,jordanMul_diag_1,jordanMul_diag_2,diagAtom_diag_coordinate,
      diagAtom_upper_coordinate,octDot_zero_left]

theorem jordanMul_diagAtom_offDiagonal (i k : Fin 3) (x : Albert) :
    (jordanMul (diagAtom i) x).2 k = derivationSlotWeight i k • x.2 k := by
  fin_cases k <;> fin_cases i <;>
    simp [jordanMul_off_0,jordanMul_off_1,jordanMul_off_2,diagAtom_diag_coordinate,
      diagAtom_upper_coordinate,derivationSlotWeight,derivationFirst,derivationSecond,
      octonionMul_zero_left,octonionMul_zero_right,octonionConj_zero]

theorem jordanMul_diagAtom_upperSlot (i k : Fin 3) (x : Octonion) :
    jordanMul (diagAtom i) (derivationUpperSlot k x) = derivationSlotWeight i k • derivationUpperSlot k x := by
  apply Prod.ext <;> funext j
  · rw [jordanMul_diagAtom_diagonal]
    fin_cases k <;> simp [derivationUpperSlot,show ∀ r (y : Albert), (r • y).1 j = r * y.1 j from fun _ _ => rfl,
      show ∀ v, (slotElem01 v).1 j = 0 from fun _ => rfl,
      show ∀ v, (slotElem02 v).1 j = 0 from fun _ => rfl,
      show ∀ v, (slotElem12 v).1 j = 0 from fun _ => rfl]
  · rw [jordanMul_diagAtom_offDiagonal]
    change derivationSlotWeight i j • derivationSlotCoord j (derivationUpperSlot k x) =
      derivationSlotWeight i k • derivationSlotCoord j (derivationUpperSlot k x)
    by_cases h : j = k
    · subst j; rfl
    · simp [h]

private theorem jordanMul_diagAtom_diagAtom (i j : Fin 3) :
    jordanMul (diagAtom i) (diagAtom j) = if i = j then diagAtom i else 0 := by
  split
  · rename_i h
    subst j
    exact (diagAtom_isAtom i).1
  · exact diagAtom_orthogonal ‹i ≠ j›

def albertDerivationFrameCoords : AlbertDerivation →ₗ[ℝ] (Fin 3 → Octonion) where
  toFun D k := derivationSlotCoord k (D.val (diagAtom (derivationFirst k)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem albertDerivationFrameCoords_unit_rel (D : AlbertDerivation) :
    ∑ i : Fin 3, D.val (diagAtom i) = 0 := by
  rw [← map_sum, diagAtom_sum_eq_unit, albertDerivation_unit]

theorem albertDerivation_diagAtom_half (D : AlbertDerivation) (i : Fin 3) :
    D.val (diagAtom i) = (2 : ℝ) • jordanMul (diagAtom i) (D.val (diagAtom i)) := by
  have h := albertDerivation_mul D (diagAtom i) (diagAtom i)
  rw [(diagAtom_isAtom i).1, jordanMul_comm (D.val _) (diagAtom i)] at h
  simpa only [two_smul ℝ] using h

theorem albertDerivation_diagAtom_diagonal_zero (D : AlbertDerivation) (i k : Fin 3) :
    (D.val (diagAtom i)).1 k = 0 := by
  have h := congrArg (fun x : Albert => x.1 k) (albertDerivation_diagAtom_half D i)
  change (D.val (diagAtom i)).1 k = 2 * (jordanMul (diagAtom i) (D.val (diagAtom i))).1 k at h
  rw [jordanMul_diagAtom_diagonal] at h
  split at h <;> linarith

theorem albertDerivation_diagAtom_offDiagonal_zero (D : AlbertDerivation) (i k : Fin 3)
    (h₁ : i ≠ derivationFirst k) (h₂ : i ≠ derivationSecond k) :
    derivationSlotCoord k (D.val (diagAtom i)) = 0 := by
  have h := congrArg (derivationSlotCoord k) (albertDerivation_diagAtom_half D i)
  rw [map_smul] at h
  change derivationSlotCoord k (D.val (diagAtom i)) =
    (2 : ℝ) • (jordanMul (diagAtom i) (D.val (diagAtom i))).2 k at h
  rw [jordanMul_diagAtom_offDiagonal] at h
  simpa [derivationSlotWeight,h₁,h₂] using h

def albertDerivationFrameMotion (k : Fin 3) (x : Octonion) : AlbertDerivation :=
  (4 : ℝ) • albertInnerDerivation (derivationUpperSlot k x) (diagAtom (derivationFirst k))

theorem albertDerivationFrameMotion_apply_diagAtom (k i : Fin 3) (x : Octonion) :
    (albertDerivationFrameMotion k x).val (diagAtom i) =
      if i = derivationFirst k then derivationUpperSlot k x
      else if i = derivationSecond k then -derivationUpperSlot k x else 0 := by
  change (4 : ℝ) • (albertInnerDerivation _ _).val (diagAtom i) = _
  have hf : derivationSlotWeight (derivationFirst k) k = 1/2 := by simp [derivationSlotWeight]
  have hterm : jordanMul (derivationUpperSlot k x) (jordanMul (diagAtom (derivationFirst k)) (diagAtom i)) =
      if i = derivationFirst k then (1/2 : ℝ) • derivationUpperSlot k x else 0 := by
    by_cases he : i = derivationFirst k
    · rw [he, (diagAtom_isAtom _).1, jordanMul_comm, jordanMul_diagAtom_upperSlot, hf, ite_eq_left rfl]
    · rw [jordanMul_diagAtom_diagAtom, ite_eq_right (Ne.symm he), jordanMul_zero_right, ite_eq_right he]
  rw [albertInnerDerivation_apply, hterm, jordanMul_comm (derivationUpperSlot k x) (diagAtom i),
    jordanMul_diagAtom_upperSlot, jordanMul_smul_right, jordanMul_diagAtom_upperSlot, hf]
  fin_cases k <;> fin_cases i <;>
    simp [derivationSlotWeight,derivationFirst,derivationSecond] <;> module

theorem albertDerivationFrameCoords_surjective : Function.Surjective albertDerivationFrameCoords := by
  intro x
  refine ⟨∑ k, albertDerivationFrameMotion k (x k), ?_⟩
  funext i
  rw [map_sum, Finset.sum_apply]
  have hx (k : Fin 3) : albertDerivationFrameCoords (albertDerivationFrameMotion k (x k)) i =
      if i = k then x i else 0 := by
    change derivationSlotCoord i ((albertDerivationFrameMotion k (x k)).val (diagAtom (derivationFirst i))) = _
    rw [albertDerivationFrameMotion_apply_diagAtom]
    fin_cases i <;> fin_cases k <;> simp [derivationFirst,derivationSecond]
  simp [hx]

theorem albertDerivationFrameCoords_zero_iff (D : AlbertDerivation) :
    albertDerivationFrameCoords D = 0 ↔ ∀ i, D.val (diagAtom i) = 0 := by
  constructor
  · intro h i
    have hm (k : Fin 3) : derivationSlotCoord k (D.val (diagAtom (derivationFirst k))) = 0 :=
      congrFun h k
    have hd (k : Fin 3) : derivationSlotCoord k (D.val (diagAtom 0)) +
        derivationSlotCoord k (D.val (diagAtom 1)) + derivationSlotCoord k (D.val (diagAtom 2)) = 0 := by
      simpa only [map_sum,map_add,map_zero,Fin.sum_univ_three] using
        congrArg (derivationSlotCoord k) (albertDerivationFrameCoords_unit_rel D)
    have ha : ∀ i k, derivationSlotCoord k (D.val (diagAtom i)) = 0 := by
      intro j k
      fin_cases k <;> fin_cases j
      · exact hm 0
      · have hz := albertDerivation_diagAtom_offDiagonal_zero D 2 0 (by decide) (by decide)
        have he : derivationSlotCoord 0 (D.val (diagAtom 0)) = 0 := hm 0
        change derivationSlotCoord 0 (D.val (diagAtom 1)) = 0
        simpa only [he, hz, zero_add, add_zero] using hd 0
      · exact albertDerivation_diagAtom_offDiagonal_zero D 2 0 (by decide) (by decide)
      · exact hm 1
      · exact albertDerivation_diagAtom_offDiagonal_zero D 1 1 (by decide) (by decide)
      · have hz := albertDerivation_diagAtom_offDiagonal_zero D 1 1 (by decide) (by decide)
        have he : derivationSlotCoord 1 (D.val (diagAtom 0)) = 0 := hm 1
        change derivationSlotCoord 1 (D.val (diagAtom 2)) = 0
        simpa only [he, hz, zero_add] using hd 1
      · exact albertDerivation_diagAtom_offDiagonal_zero D 0 2 (by decide) (by decide)
      · exact hm 2
      · have hz := albertDerivation_diagAtom_offDiagonal_zero D 0 2 (by decide) (by decide)
        have he : derivationSlotCoord 2 (D.val (diagAtom 1)) = 0 := hm 2
        change derivationSlotCoord 2 (D.val (diagAtom 2)) = 0
        simpa only [hz, he, zero_add] using hd 2
    exact Prod.ext (funext (albertDerivation_diagAtom_diagonal_zero D i)) (funext (ha i))
  · intro h
    funext k
    change derivationSlotCoord k (D.val (diagAtom (derivationFirst k))) = 0
    rw [h,map_zero]

end AlbertSequential
