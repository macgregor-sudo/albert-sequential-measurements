/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTracePartitions
public import NativeScalarAccess
public import CornerNumericalData

/-! Literal fixed-S menus and scalar conditions. Four bases have two
scalar shapes. Normalizers are fixed positive real square roots, never masses. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis

def fixedSCornerOrder : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 2, 3], ![2, 0, 1, 3], ![3, 0, 1, 2]]

theorem fixedSCornerOrder_injective (j : Fin 4) : Function.Injective (fixedSCornerOrder j) := by
  intro a b h
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp_all [fixedSCornerOrder]

def fixedSCornerRelabelling (j : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (fixedSCornerOrder j) (Finite.injective_iff_bijective.mp (fixedSCornerOrder_injective j))

theorem fixedSCornerRelabelling_apply (j a : Fin 4) :
    fixedSCornerRelabelling j a = fixedSCornerOrder j a := rfl

theorem fixedSCornerRelabelling_base (j : Fin 4) : fixedSCornerRelabelling j 0 = j := by
  fin_cases j <;> rfl

def fixedSCornerMenu (j : Fin 4) : Fin 4 → Albert := fixedS ∘ fixedSCornerRelabelling j

def fixedSCornerScalar (j a : Fin 4) (w : Word (Fin 4)) : ℝ :=
  nativeWordProbability (fixedSCornerMenu j) (fixedSCornerMenu j a) w

def fixedSABCornerData : CornerNumericalData where
  o01 := 1 / 2; o02 := 1 / 3; o03 := 1 / 3
  o12 := 1 / 3; o23 := 1 / 3; o31 := 1 / 3
  r012 := 1 / 6; r023 := 1 / 9; r031 := 1 / 6; r123 := 1 / 9
  q123 := 1 / 18; q231 := 1 / 18; q312 := 1 / 18
  ν0 := Real.sqrt (1 / 18); ν1 := Real.sqrt (1 / 27); ν2 := Real.sqrt (1 / 18)

def fixedSCDCornerData : CornerNumericalData where
  o01 := 1 / 3; o02 := 1 / 3; o03 := 1 / 3
  o12 := 1 / 2; o23 := 1 / 3; o31 := 1 / 3
  r012 := 1 / 6; r023 := 1 / 9; r031 := 1 / 9; r123 := 1 / 6
  q123 := 1 / 18; q231 := 1 / 18; q312 := 1 / 18
  ν0 := Real.sqrt (1 / 18); ν1 := Real.sqrt (1 / 27); ν2 := Real.sqrt (1 / 27)

def fixedSCornerData (j : Fin 4) : CornerNumericalData :=
  if j.val < 2 then fixedSABCornerData else fixedSCDCornerData

theorem fixedSCorner_isAtom (j a : Fin 4) : IsAtom (fixedSCornerMenu j a) :=
  fixedS_isAtom (fixedSCornerRelabelling j a)

theorem fixedSCorner_Q (j : Fin 4) : nativeCornerQ (fixedSCornerMenu j) = ![1 / 18, 1 / 18, 1 / 18] := by
  have h0 := congrFun nativeCornerQ_fixedS 0
  have h1 := congrFun nativeCornerQ_fixedS 1
  have h2 := congrFun nativeCornerQ_fixedS 2
  change tracePairing (fixedS 0) (jordanTriple (fixedS 1) (fixedS 2) (fixedS 3)) = 1 / 18 at h0
  change tracePairing (fixedS 0) (jordanTriple (fixedS 2) (fixedS 3) (fixedS 1)) = 1 / 18 at h1
  change tracePairing (fixedS 0) (jordanTriple (fixedS 3) (fixedS 1) (fixedS 2)) = 1 / 18 at h2
  funext i
  fin_cases j <;> fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact (native_quartic_cyclic _ _ _ _).trans h1
  · exact (native_quartic_cyclic_thrice _ _ _ _).trans h0
  · exact (native_quartic_cyclic_twice _ _ _ _).trans ((native_quartic_reverse _ _ _ _).trans h2)
  · exact (native_quartic_cyclic _ _ _ _).trans ((native_quartic_reverse _ _ _ _).trans h1)
  · exact (native_quartic_cyclic_thrice _ _ _ _).trans ((native_quartic_reverse _ _ _ _).trans h2)
  · exact (native_quartic_cyclic_twice _ _ _ _).trans h0
  · exact (native_quartic_cyclic _ _ _ _).trans h0
  · exact (native_quartic_cyclic_thrice _ _ _ _).trans h2
  · exact (native_quartic_cyclic_twice _ _ _ _).trans ((native_quartic_reverse _ _ _ _).trans h1)

end AlbertSequential
