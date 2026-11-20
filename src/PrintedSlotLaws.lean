/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FrameSlotNormalizers
public import NativePeirceHalfOperators

@[expose] public section
noncomputable section
namespace AlbertSequential

/-- Slots 23, 31, 12 in the order of the deposited appendix. -/
def cyclicSlot (i : Fin 3) (a : Octonion) : Albert :=
  ![slotElem12 a,slotElem02 (octonionConj a),slotElem01 a] i

theorem cyclicSlot_product (i : Fin 3) (a b : Octonion) :
    jordanMul (cyclicSlot i a) (cyclicSlot (i+1) b) =
      (1/2 : ℝ) • cyclicSlot (i+2) (octonionConj (octonionMul a b)) := by
  fin_cases i
  · change jordanMul (slotElem12 a) (slotElem02 (octonionConj b)) = _
    rw [jordanMul_comm,jordanMul_slotElem02_slotElem12,octonionConj_mul]
    rfl
  · change jordanMul (slotElem02 (octonionConj a)) (slotElem01 b) = _
    rw [jordanMul_comm,jordanMul_slotElem01_slotElem02,octonionConj_mul]
    rfl
  · change jordanMul (slotElem01 a) (slotElem12 b) =
        (1/2 : ℝ) • slotElem02 (octonionConj (octonionConj (octonionMul a b)))
    rw [jordanMul_slotElem01_slotElem12,octonionConj_conj]

def cyclicSlotComponent (i : Fin 3) (x : Albert) : Albert :=
  ![slotElem12 (x.2 2),slotElem02 (x.2 1),slotElem01 (x.2 0)] i

theorem cyclicSlot_extract (k : Fin 3) (x : Albert) :
    (4 : ℝ) • jordanMul (diagAtom (k+1)) (jordanMul (diagAtom (k+2)) x) = cyclicSlotComponent k x ∧
    (4 : ℝ) • jordanMul (diagAtom (k+2)) (jordanMul (diagAtom (k+1)) x) = cyclicSlotComponent k x := by
  have he (i j : Fin 3) (h : i ≠ j) := NativeAnalysis.native_peirceZero_commute (diagAtom i) (diagAtom j) x
    (diagAtom_isAtom i).1 (diagAtom_orthogonal h)
  fin_cases k
  · change _ = slotElem12 (x.2 2) ∧ _ = _
    exact ⟨peirce12_extract x,(congrArg ((4:ℝ) • ·) (he 2 1 (by decide))).trans (peirce12_extract x)⟩
  · exact ⟨(congrArg ((4:ℝ) • ·) (he 2 0 (by decide))).trans (peirce02_extract x),peirce02_extract x⟩
  · exact ⟨peirce01_extract x,(congrArg ((4:ℝ) • ·) (he 1 0 (by decide))).trans (peirce01_extract x)⟩

theorem cyclicSlot_coefficientSubalgebra (B : NativeJordanSubalgebra)
    (hd : ∀ i, diagAtom i ∈ B.carrier) (hu : ∀ i, cyclicSlot i octOne ∈ B.carrier) :
    ∃ S : OctSubalgebra, (∀ i a, a ∈ S.carrier ↔ cyclicSlot i a ∈ B.carrier) ∧
      (S.carrier : Set Octonion) = {a | ∀ i, cyclicSlot i a ∈ B.carrier} := by
  have h12 : slotElem12 octOne ∈ B.carrier := hu 0
  have h02 : slotElem02 octOne ∈ B.carrier := by
    have h : slotElem02 (octonionConj octOne) ∈ B.carrier := hu 1
    simpa only [octonionConj_one] using h
  have h01 : slotElem01 octOne ∈ B.carrier := hu 2
  let S := slotSubalgebraOfJordanSubalgebra B (hd 0) (hd 1) (hd 2) h01 h02 h12
  have iffSlot (i : Fin 3) (a : Octonion) : a ∈ S.carrier ↔ cyclicSlot i a ∈ B.carrier := by
    fin_cases i
    · exact mem_slotSubalgebra_iff_slotElem12 B (hd 0) (hd 1) (hd 2) h01 h02 h12 _
    · have hc : a ∈ S.carrier ↔ octonionConj a ∈ S.carrier :=
        ⟨S.conj_mem _,fun h => by simpa only [octonionConj_conj] using S.conj_mem _ h⟩
      exact hc.trans (mem_slotSubalgebra_iff_slotElem02 B (hd 0) (hd 1) (hd 2) h01 h02 h12 _)
    · exact Iff.rfl
  exact ⟨S,iffSlot,Set.ext fun a => ⟨fun h i => (iffSlot i a).mp h,fun h => (iffSlot 0 a).mpr (h 0)⟩⟩

end AlbertSequential
