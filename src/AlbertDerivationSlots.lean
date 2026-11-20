/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertDerivationFrame
public import OctonionRealCoordinates

@[expose] public section
noncomputable section

namespace AlbertSequential

open scoped BigOperators

abbrev AlbertFrameFixedDerivation := LinearMap.ker albertDerivationFrameCoords

theorem albertFrameFixedDerivation_diag (D : AlbertFrameFixedDerivation) (i : Fin 3) :
    D.val.val (diagAtom i) = 0 :=
  (albertDerivationFrameCoords_zero_iff D.val).mp (LinearMap.mem_ker.mp D.property) i

theorem derivationUpper_extract (k : Fin 3) (x : Albert) :
    (4 : ℝ) • jordanMul (diagAtom (derivationFirst k)) (jordanMul (diagAtom (derivationSecond k)) x) =
      derivationUpperSlot k (derivationSlotCoord k x) := by
  fin_cases k
  · exact peirce01_extract x
  · exact peirce02_extract x
  · exact peirce12_extract x

private theorem derivationUpperSlot_diagonal (k n : Fin 3) (x : Octonion) : (derivationUpperSlot k x).1 n = 0 := by
  fin_cases k <;> rfl

private theorem diagAtom_diag (k n : Fin 3) : (diagAtom k).1 n = if n = k then 1 else 0 := rfl

private theorem diagAtom_off (k n : Fin 3) : (diagAtom k).2 n = 0 := rfl

theorem jordanMul_derivationUpperSlot_same (k : Fin 3) (x y : Octonion) :
    jordanMul (derivationUpperSlot k x) (derivationUpperSlot k y) =
      octDot x y • (diagAtom (derivationFirst k) + diagAtom (derivationSecond k)) := by
  have hOff (l k : Fin 3) (z : Octonion) : (derivationUpperSlot k z).2 l = if l = k then z else 0 :=
    derivationSlotCoord_upperSlot l k z
  have hD (r : ℝ) (u : Albert) (l : Fin 3) : ((r • u) : Albert).1 l = r * u.1 l := rfl
  have hU (r : ℝ) (u : Albert) (l : Fin 3) : ((r • u) : Albert).2 l = r • u.2 l := rfl
  have hA (u v : Albert) (l : Fin 3) : (u + v).1 l = u.1 l + v.1 l := rfl
  have hB (u v : Albert) (l : Fin 3) : (u + v).2 l = u.2 l + v.2 l := rfl
  apply Prod.ext <;> funext i <;> fin_cases i <;> fin_cases k <;>
    simp [jordanMul_diag_0,jordanMul_diag_1,jordanMul_diag_2,jordanMul_off_0,jordanMul_off_1,jordanMul_off_2,
      derivationUpperSlot_diagonal,hOff,hD,hU,hA,hB,diagAtom_diag,diagAtom_off,derivationFirst,derivationSecond,
      octDot_zero_right,octonionConj_zero,octonionMul_zero_left,octonionMul_zero_right]

def albertFrameFixedSlotAction (D : AlbertFrameFixedDerivation) (k : Fin 3) : Octonion →ₗ[ℝ] Octonion :=
  (derivationSlotCoord k).comp (D.val.val.comp (derivationUpperSlot k))

theorem albertFrameFixedSlotAction_mul (D : AlbertFrameFixedDerivation) (k : Fin 3) (x : Octonion) :
    D.val.val (derivationUpperSlot k x) = derivationUpperSlot k (albertFrameFixedSlotAction D k x) := by
  let E := derivationUpperSlot k x
  have hE : (4 : ℝ) • jordanMul (diagAtom (derivationFirst k)) (jordanMul (diagAtom (derivationSecond k)) E) = E := by
    rw [derivationUpper_extract]
    simp [E]
  have hD := congrArg D.val.val hE
  rw [map_smul, albertDerivation_mul, albertFrameFixedDerivation_diag, jordanMul_zero_left, zero_add,
    albertDerivation_mul, albertFrameFixedDerivation_diag, jordanMul_zero_left, zero_add,
    derivationUpper_extract] at hD
  exact hD.symm

theorem albertFrameFixedSlotAction_skew (D : AlbertFrameFixedDerivation) (k : Fin 3) (x y : Octonion) :
    octDot (albertFrameFixedSlotAction D k x) y + octDot x (albertFrameFixedSlotAction D k y) = 0 := by
  have h := albertDerivation_mul D.val (derivationUpperSlot k x) (derivationUpperSlot k y)
  rw [jordanMul_derivationUpperSlot_same,map_smul,map_add,albertFrameFixedDerivation_diag,
    albertFrameFixedDerivation_diag,add_zero,smul_zero,albertFrameFixedSlotAction_mul,
    albertFrameFixedSlotAction_mul,jordanMul_derivationUpperSlot_same,jordanMul_derivationUpperSlot_same] at h
  have hc := congrArg (fun z : Albert => z.1 (derivationFirst k)) h
  have hcoord (r : ℝ) : ((r • (diagAtom (derivationFirst k) + diagAtom (derivationSecond k))) : Albert).1
      (derivationFirst k) = r := by
    have hne : derivationFirst k ≠ derivationSecond k := by fin_cases k <;> decide
    change r * ((diagAtom (derivationFirst k)).1 (derivationFirst k) +
      (diagAtom (derivationSecond k)).1 (derivationFirst k)) = r
    simp [diagAtom_diag,hne]
  change (0 : ℝ) = _ + _ at hc
  rw [hcoord,hcoord] at hc
  exact hc.symm

theorem albertFrameFixedSlotAction_triality (D : AlbertFrameFixedDerivation) (x y : Octonion) :
    albertFrameFixedSlotAction D 1 (octonionMul x y) =
      octonionMul (albertFrameFixedSlotAction D 0 x) y + octonionMul x (albertFrameFixedSlotAction D 2 y) := by
  have hj (a b : Octonion) : jordanMul (derivationUpperSlot 0 a) (derivationUpperSlot 2 b) =
      (1/2 : ℝ) • derivationUpperSlot 1 (octonionMul a b) := jordanMul_slotElem01_slotElem12 a b
  have h := albertDerivation_mul D.val (derivationUpperSlot 0 x) (derivationUpperSlot 2 y)
  rw [hj,map_smul,albertFrameFixedSlotAction_mul,albertFrameFixedSlotAction_mul,
    albertFrameFixedSlotAction_mul,hj,hj,← smul_add] at h
  have hc := congrArg (derivationSlotCoord 1) h
  simp only [map_add,map_smul,derivationSlotCoord_upperSlot,ite_true] at hc
  exact (smul_right_injective Octonion (by norm_num : (1/2 : ℝ) ≠ 0)) hc

private theorem octonion_right_nucleus_scalar (z : Octonion)
    (h : ∀ x y, octonionMul (octonionMul x y) z = octonionMul x (octonionMul y z)) :
    z = octonionScalar z.1.re := by
  have h0 := h octI octJ
  have h1 := h octI octL
  have h2 := h octJ octL
  have c0 := congrArg (fun x : Octonion => x.2.re) h0
  have c1 := congrArg (fun x : Octonion => x.2.imI) h0
  have c2 := congrArg (fun x : Octonion => x.2.imJ) h0
  have c3 := congrArg (fun x : Octonion => x.2.imK) h0
  have c4 := congrArg (fun x : Octonion => x.2.imJ) h1
  have c5 := congrArg (fun x : Octonion => x.2.imK) h1
  have c6 := congrArg (fun x : Octonion => x.2.imK) h2
  simp [octI,octJ,octL,octonionMul] at c0 c1 c2 c3 c4 c5 c6
  apply Prod.ext
  · apply Quaternion.ext
    · rfl
    all_goals (change _ = (0 : ℝ); linarith)
  · apply Quaternion.ext <;> change _ = (0 : ℝ) <;> linarith

private theorem albert_span_coordinates (x : Albert) :
    x = (∑ i, x.1 i • diagAtom i) + ∑ i, derivationUpperSlot i (x.2 i) := by
  have hD (u v : Albert) (j : Fin 3) : (u + v).1 j = u.1 j + v.1 j := rfl
  have hU (u v : Albert) (j : Fin 3) : (u + v).2 j = u.2 j + v.2 j := rfl
  have hsm (r : ℝ) (u : Albert) (j : Fin 3) : ((r • u) : Albert).1 j = r * u.1 j := rfl
  have hsm' (r : ℝ) (u : Albert) (j : Fin 3) : ((r • u) : Albert).2 j = r • u.2 j := rfl
  have off (k l : Fin 3) (z : Octonion) : (derivationUpperSlot l z).2 k = if k = l then z else 0 :=
    derivationSlotCoord_upperSlot k l z
  apply Prod.ext <;> funext j <;> fin_cases j <;>
    simp [Fin.sum_univ_three,hD,hU,hsm,hsm',off,diagAtom_diag,diagAtom_off,derivationUpperSlot_diagonal]

theorem albertFrameFixed_zero_of_firstSlot_zero (D : AlbertFrameFixedDerivation)
    (hD : ∀ x, albertFrameFixedSlotAction D 0 x = 0) : D = 0 := by
  have hact (x y : Octonion) : albertFrameFixedSlotAction D 1 (octonionMul x y) =
      octonionMul x (albertFrameFixedSlotAction D 2 y) := by
    simpa [hD,octonionMul_zero_left] using albertFrameFixedSlotAction_triality D x y
  have heq (x : Octonion) : albertFrameFixedSlotAction D 1 x = albertFrameFixedSlotAction D 2 x := by
    simpa only [octonionMul_one_left] using hact octOne x
  let z := albertFrameFixedSlotAction D 2 octOne
  have hz (x : Octonion) : albertFrameFixedSlotAction D 1 x = octonionMul x z := by
    simpa only [octonionMul_one_right] using hact x octOne
  have hzn (x y : Octonion) : octonionMul (octonionMul x y) z = octonionMul x (octonionMul y z) := by
    simpa only [← heq y,hz] using hact x y
  have hzs : z = octonionScalar z.1.re := octonion_right_nucleus_scalar z hzn
  have hsk := albertFrameFixedSlotAction_skew D 2 octOne octOne
  change octDot z octOne + octDot octOne z = 0 at hsk
  have hzr : z.1.re = 0 := by
    rw [octDot_comm z octOne] at hsk
    change octDot (octonionScalar 1) z + octDot (octonionScalar 1) z = 0 at hsk
    rw [octDot_scalar_left, one_mul] at hsk
    change z.1.re + z.1.re = 0 at hsk
    linarith
  have hz0 : z = 0 := by rw [hzs,hzr]; rfl
  have hk (k : Fin 3) (x : Octonion) : albertFrameFixedSlotAction D k x = 0 := by
    fin_cases k
    · exact hD x
    · change albertFrameFixedSlotAction D 1 x = 0
      rw [hz,hz0,octonionMul_zero_right]
    · change albertFrameFixedSlotAction D 2 x = 0
      rw [← heq,hz,hz0,octonionMul_zero_right]
  apply Subtype.ext
  apply Subtype.ext
  ext x
  change D.val.val x = 0
  conv_lhs => rw [albert_span_coordinates x]
  simp only [map_add,map_sum,map_smul,albertFrameFixedDerivation_diag,smul_zero,Finset.sum_const_zero,
    albertFrameFixedSlotAction_mul,hk,map_zero,add_zero]

end AlbertSequential
