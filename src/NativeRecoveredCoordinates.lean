module

public import NativeWordDuality
public import Glennie.Native

/-! Literal six-coordinate equivalence to the recovered compact real model.
The old model is an isolated proof representation. No old native norm or
coordinatewise multiplication instance is installed on the current carriers.
Both products below are the explicit symmetrized binary octonion-matrix product. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def recoveredCoordinateEquiv : Albert ≃ₗ[ℝ] Glennie.Albert where
  toFun x := ⟨x.1 0, x.1 1, x.1 2, x.2 0, x.2 1, x.2 2⟩
  invFun y := (![y.d0, y.d1, y.d2], ![y.o01, y.o02, y.o12])
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv y := rfl
  map_add' x y := by apply Glennie.Albert.ext <;> rfl
  map_smul' r x := by apply Glennie.Albert.ext <;> rfl

theorem recoveredCoordinateEquiv_matrix (x : Albert) :
    Glennie.toMatrix (recoveredCoordinateEquiv x) = albertMatrix x := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem recoveredCoordinateEquiv_octonionMul (x y : Octonion) :
    Glennie.octMul x y = octonionMul x y := rfl

theorem recoveredCoordinateEquiv_matrixMul
    (M N : Fin 3 → Fin 3 → Octonion) :
    Glennie.matrixMul M N = octonionMatrixMul M N := rfl

theorem recoveredCoordinateEquiv_jordanMul (x y : Albert) :
    recoveredCoordinateEquiv (jordanMul x y) =
      Glennie.jordan (recoveredCoordinateEquiv x) (recoveredCoordinateEquiv y) := by
  unfold Glennie.jordan
  rw [recoveredCoordinateEquiv_matrix, recoveredCoordinateEquiv_matrix,
    recoveredCoordinateEquiv_matrixMul, recoveredCoordinateEquiv_matrixMul]
  apply Glennie.Albert.ext
  · change (1 / 2 : ℝ) * octonionReal _ = octonionReal ((1 / 2 : ℝ) • _)
    exact (octonionReal_smul _ _).symm

  · change (1 / 2 : ℝ) * octonionReal _ = octonionReal ((1 / 2 : ℝ) • _)
    exact (octonionReal_smul _ _).symm
  · change (1 / 2 : ℝ) * octonionReal _ = octonionReal ((1 / 2 : ℝ) • _)
    exact (octonionReal_smul _ _).symm
  · rfl
  · rfl
  · rfl

theorem recoveredCoordinateEquiv_trace (x : Albert) :
    Glennie.trace (recoveredCoordinateEquiv x) = albertTrace x := by
  change x.1 0 + x.1 1 + x.1 2 = ∑ i : Fin 3, x.1 i
  rw [Fin.sum_univ_three]

theorem recoveredCoordinateEquiv_unit :
    recoveredCoordinateEquiv albertUnit = (1 : Glennie.Albert) := rfl

theorem recoveredCoordinateEquiv_tracePairing (x y : Albert) :
    Glennie.inner (recoveredCoordinateEquiv x) (recoveredCoordinateEquiv y) = tracePairing x y := by
  unfold Glennie.inner tracePairing
  rw [← recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_trace]

theorem recoveredCoordinateEquiv_quadraticMap (a x : Albert) :
    recoveredCoordinateEquiv (quadraticMap a x) =
      Glennie.U (recoveredCoordinateEquiv a) (recoveredCoordinateEquiv x) := by
  unfold quadraticMap Glennie.U
  rw [map_sub]
  simp only [two_smul, map_add, recoveredCoordinateEquiv_jordanMul]

theorem recoveredCoordinateEquiv_first_diagonal_control :
    recoveredCoordinateEquiv (diagAtom 0) = (⟨1, 0, 0, 0, 0, 0⟩ : Glennie.Albert) := by
  apply Glennie.Albert.ext <;> rfl

end AlbertSequential.NativeAnalysis
