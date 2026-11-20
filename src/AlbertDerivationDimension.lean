/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertDerivationSlots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section
noncomputable section

namespace AlbertSequential

open scoped BigOperators
open NativeAnalysis

private def octIndex : OctonionCoordinate ≃ Fin 8 :=
  (Fintype.equivFin OctonionCoordinate).trans (finCongr (by decide))

private def octCoordinates : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  octonionRealCoordinates.trans (LinearEquiv.funCongrLeft ℝ ℝ octIndex.symm)

private theorem octCoordinates_dot (x y : Octonion) :
    octDot x y = ∑ i, octCoordinates x i * octCoordinates y i := by
  rw [octonionRealCoordinates_pairing]
  exact (Equiv.sum_comp octIndex.symm (fun i => octonionRealCoordinates x i * octonionRealCoordinates y i)).symm

private def octAxis (i : Fin 8) : Octonion := octCoordinates.symm (Pi.single i 1)

@[simp] private theorem octCoordinates_axis (i j : Fin 8) :
    octCoordinates (octAxis i) j = if j = i then 1 else 0 := by
  rw [octAxis,LinearEquiv.apply_symm_apply,Pi.single_apply]

@[simp] private theorem octDot_axis (x : Octonion) (i : Fin 8) :
    octDot x (octAxis i) = octCoordinates x i := by
  rw [octCoordinates_dot]
  simp [mul_ite]

private theorem oct_axisExpansion (x : Octonion) : x = ∑ i, octCoordinates x i • octAxis i := by
  apply octCoordinates.injective
  funext j
  rw [map_sum,Finset.sum_apply]
  simp [map_smul,mul_ite]

abbrev AlbertSkewCoordinate := {ij : Fin 8 × Fin 8 // ij.1 < ij.2}

def albertFrameFixedSkewCoords : AlbertFrameFixedDerivation →ₗ[ℝ] (AlbertSkewCoordinate → ℝ) where
  toFun D ij := octCoordinates (albertFrameFixedSlotAction D 0 (octAxis ij.val.2)) ij.val.1
  map_add' D E := by
    funext ij
    change octCoordinates (albertFrameFixedSlotAction D 0 (octAxis ij.val.2) +
      albertFrameFixedSlotAction E 0 (octAxis ij.val.2)) ij.val.1 = _
    rw [map_add]
    rfl
  map_smul' r D := by
    funext ij
    change octCoordinates (r • albertFrameFixedSlotAction D 0 (octAxis ij.val.2)) ij.val.1 = _
    rw [map_smul]
    rfl

private theorem albertFrameFixedSkewCoords_apply (D : AlbertFrameFixedDerivation) (ij : AlbertSkewCoordinate) :
    albertFrameFixedSkewCoords D ij =
      octCoordinates (albertFrameFixedSlotAction D 0 (octAxis ij.val.2)) ij.val.1 := rfl

theorem albertFrameFixedSkewCoords_injective : Function.Injective albertFrameFixedSkewCoords := by
  intro D E hDE
  apply sub_eq_zero.mp
  let F := D-E
  have hF : albertFrameFixedSkewCoords F = 0 := by
    change albertFrameFixedSkewCoords (D-E) = 0
    rw [map_sub albertFrameFixedSkewCoords D E,hDE,sub_self]
  have hco (i j : Fin 8) (h : i < j) :
      octCoordinates (albertFrameFixedSlotAction F 0 (octAxis j)) i = 0 := congrFun hF ⟨(i,j),h⟩
  have hsk (i j : Fin 8) : octCoordinates (albertFrameFixedSlotAction F 0 (octAxis j)) i +
      octCoordinates (albertFrameFixedSlotAction F 0 (octAxis i)) j = 0 := by
    have h := albertFrameFixedSlotAction_skew F 0 (octAxis j) (octAxis i)
    rw [octDot_comm (octAxis j)] at h
    simpa only [octDot_axis] using h
  have hcol (j : Fin 8) : albertFrameFixedSlotAction F 0 (octAxis j) = 0 := by
    apply octCoordinates.injective
    rw [map_zero]
    funext i
    change octCoordinates (albertFrameFixedSlotAction F 0 (octAxis j)) i = 0
    rcases lt_trichotomy i j with hij| rfl | hji
    · exact hco _ _ hij
    · linarith [hsk i i]
    · have h := hsk i j
      rwa [hco _ _ hji,add_zero] at h
  apply albertFrameFixed_zero_of_firstSlot_zero F
  intro x
  conv_lhs => rw [oct_axisExpansion x]
  simp only [map_sum,map_smul,hcol,smul_zero,Finset.sum_const_zero]

private def slotCommutator (x y : Octonion) : AlbertFrameFixedDerivation :=
  let D := albertInnerDerivation (derivationUpperSlot 0 x) (derivationUpperSlot 0 y)
  ⟨D, LinearMap.mem_ker.mpr ((albertDerivationFrameCoords_zero_iff D).mpr (fun i => by
    rw [albertInnerDerivation_apply,jordanMul_comm (derivationUpperSlot 0 y) (diagAtom i),
      jordanMul_comm (derivationUpperSlot 0 x) (diagAtom i),jordanMul_diagAtom_upperSlot,
      jordanMul_diagAtom_upperSlot,jordanMul_smul_right,jordanMul_smul_right,
      jordanMul_comm (derivationUpperSlot 0 x) (derivationUpperSlot 0 y),sub_self]) )⟩

private theorem slotCommutator_apply (x y z : Octonion) :
    albertFrameFixedSlotAction (slotCommutator x y) 0 z = octDot y z • x - octDot x z • y := by
  have hsum (u : Octonion) : jordanMul (derivationUpperSlot 0 u) (diagAtom 0 + diagAtom 1) =
      derivationUpperSlot 0 u := by
    rw [jordanMul_comm,jordanMul_add_left,jordanMul_diagAtom_upperSlot,jordanMul_diagAtom_upperSlot]
    norm_num [derivationSlotWeight,derivationFirst,derivationSecond]
    module
  change derivationSlotCoord 0 ((albertInnerDerivation _ _).val (derivationUpperSlot 0 z)) = _
  rw [albertInnerDerivation_apply, jordanMul_derivationUpperSlot_same, jordanMul_derivationUpperSlot_same]
  change derivationSlotCoord 0 (jordanMul (derivationUpperSlot 0 x) (octDot y z • (diagAtom 0 + diagAtom 1)) -
    jordanMul (derivationUpperSlot 0 y) (octDot x z • (diagAtom 0 + diagAtom 1))) = _
  simp only [jordanMul_smul_right,hsum,map_sub,map_smul,derivationSlotCoord_upperSlot,ite_true]

private theorem skewEntry (i j k l : Fin 8) (hij : i<j) (hkl : k<l) :
    (if l=j then (1 : ℝ) else 0) * (if k=i then 1 else 0) -
      (if l=i then 1 else 0) * (if k=j then 1 else 0) = if k=i ∧ l=j then 1 else 0 := by
  have hs : (if l=i then (1 : ℝ) else 0) * (if k=j then 1 else 0) = 0 := by
    by_cases e : l=i
    · have hf : k ≠ j := by omega
      rw [ite_eq_left e,ite_eq_right hf,mul_zero]
    · rw [ite_eq_right e,zero_mul]
  rw [hs,sub_zero]
  by_cases hki : k=i <;> by_cases hlj : l=j <;> simp [hki,hlj]

private theorem skewSlotEntry (i j k l : Fin 8) :
    octCoordinates (albertFrameFixedSlotAction (slotCommutator (octAxis i) (octAxis j)) 0 (octAxis l)) k =
      (if l=j then (1 : ℝ) else 0) * (if k=i then 1 else 0) -
        (if l=i then 1 else 0) * (if k=j then 1 else 0) := by
  rw [slotCommutator_apply,octDot_axis,octDot_axis,map_sub octCoordinates,map_smul octCoordinates,
    map_smul octCoordinates]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,octCoordinates_axis]

private theorem elementarySkewCoordinates (ij kl : AlbertSkewCoordinate) :
    albertFrameFixedSkewCoords (slotCommutator (octAxis ij.val.1) (octAxis ij.val.2)) kl =
      if kl = ij then 1 else 0 := by
  have he : kl.val.1=ij.val.1 ∧ kl.val.2=ij.val.2 ↔ kl=ij := by
    constructor
    · rintro ⟨h1,h2⟩
      exact Subtype.ext (Prod.ext h1 h2)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  have hi : (if kl.val.1=ij.val.1 ∧ kl.val.2=ij.val.2 then (1 : ℝ) else 0) = if kl=ij then 1 else 0 := by
    by_cases h : kl=ij
    · rw [ite_eq_left (he.mpr h),ite_eq_left h]
    · rw [ite_eq_right (mt he.mp h),ite_eq_right h]
  exact (albertFrameFixedSkewCoords_apply _ _).trans ((skewSlotEntry _ _ _ _).trans
    ((skewEntry _ _ _ _ ij.property kl.property).trans hi))

theorem albertFrameFixedSkewCoords_surjective : Function.Surjective albertFrameFixedSkewCoords := by
  intro v
  refine ⟨∑ ij, v ij • slotCommutator (octAxis ij.val.1) (octAxis ij.val.2), ?_⟩
  funext kl
  rw [map_sum,Finset.sum_apply]
  simp [map_smul,elementarySkewCoordinates,mul_ite]

theorem finrank_albertFrameFixedDerivation : Module.finrank ℝ AlbertFrameFixedDerivation = 28 := by
  let e := LinearEquiv.ofBijective albertFrameFixedSkewCoords
    ⟨albertFrameFixedSkewCoords_injective,albertFrameFixedSkewCoords_surjective⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
  decide +kernel

theorem finrank_albertDerivation : Module.finrank ℝ AlbertDerivation = 52 := by
  let : FiniteDimensional ℝ Albert := nativeAlbertModuleFinite
  let : FiniteDimensional ℝ Octonion := octCoordinates.symm.finiteDimensional
  have h := albertDerivationFrameCoords.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr albertDerivationFrameCoords_surjective,finrank_albertFrameFixedDerivation,
    finrank_top,Module.finrank_pi_fintype] at h
  have hO : Module.finrank ℝ Octonion = 8 := by rw [octCoordinates.finrank_eq]; simp
  simpa [hO] using h.symm

end AlbertSequential
