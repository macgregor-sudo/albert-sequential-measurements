module

public import NativeAutomorphisms

/-! Diagonal multiplication acts by actual real scalars in each native slot.
This module imports the diagonalization modules, with no
whole-native Jordan or cubic identity. No repeated-spectrum exclusion is used. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def diagonalElement (d : Fin 3 → ℝ) : Albert := (d, fun _ => 0)

@[simp] theorem recoveredCoordinateEquiv_coordinates (x : Albert) :
    recoveredCoordinateEquiv x =
      (⟨x.1 0, x.1 1, x.1 2, x.2 0, x.2 1, x.2 2⟩ : Glennie.Albert) := rfl

theorem recovered_diagonal_mul (a b c : ℝ) (y : Glennie.Albert) :
    Glennie.jordan (⟨a, b, c, 0, 0, 0⟩ : Glennie.Albert) y =
      ⟨a * y.d0, b * y.d1, c * y.d2,
        ((a + b) / 2 : ℝ) • y.o01, ((a + c) / 2 : ℝ) • y.o02,
        ((b + c) / 2 : ℝ) • y.o12⟩ := by
  apply Glennie.Albert.ext
  all_goals simp [Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
    Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
    Glennie.octDot_coordinates, Glennie.octMul, Glennie.octConj,
    show ((0 : Quaternion ℝ), (0 : Quaternion ℝ)) = (0 : Glennie.Octonion) from rfl,
    smul_smul]
  all_goals (congr 1; ring)

theorem jordanMul_diagonal (d : Fin 3 → ℝ) (x : Albert) :
    jordanMul (diagonalElement d) x =
      (fun i => d i * x.1 i,
        ![((d 0 + d 1) / 2 : ℝ) • x.2 0,
          ((d 0 + d 2) / 2 : ℝ) • x.2 1,
          ((d 1 + d 2) / 2 : ℝ) • x.2 2]) := by
  apply recoveredCoordinateEquiv.injective
  rw [recoveredCoordinateEquiv_jordanMul]
  change Glennie.jordan (⟨d 0, d 1, d 2, 0, 0, 0⟩ : Glennie.Albert)
      (recoveredCoordinateEquiv x) = _
  rw [recovered_diagonal_mul]
  rfl

theorem diagonal_square (d : Fin 3 → ℝ) :
    jordanMul (diagonalElement d) (diagonalElement d) =
      diagonalElement (fun i => (d i)^2) := by
  rw [jordanMul_diagonal]
  apply Prod.ext
  · funext i
    change d i * d i = (d i)^2
    ring
  · funext i
    fin_cases i <;> simp [diagonalElement]

theorem diagonal_product (d e : Fin 3 → ℝ) :
    jordanMul (diagonalElement d) (diagonalElement e) =
      diagonalElement (fun i => d i * e i) := by
  rw [jordanMul_diagonal]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [diagonalElement]

theorem diagonal_trace (d : Fin 3 → ℝ) :
    albertTrace (diagonalElement d) = ∑ i : Fin 3, d i := rfl

/-- Actual full-space diagonalization, expressed in the existing native
automorphism structure. The scalar diagonal entries are unconstrained reals. -/
theorem nativeDiagonalization (x : Albert) :
    ∃ g : NativeAlbertAutomorphism, ∃ d : Fin 3 → ℝ,
      g.linearEquiv x = diagonalElement d := by
  obtain ⟨g, hg⟩ := Glennie.native_diagonalization (recoveredCoordinateEquiv x)
  let d : Fin 3 → ℝ := ![(g.equiv (recoveredCoordinateEquiv x)).d0,
    (g.equiv (recoveredCoordinateEquiv x)).d1,
    (g.equiv (recoveredCoordinateEquiv x)).d2]
  refine ⟨recoveredNativeAutomorphism g, d, ?_⟩
  apply recoveredCoordinateEquiv.injective
  change g.equiv (recoveredCoordinateEquiv x) = recoveredCoordinateEquiv (diagonalElement d)
  apply Glennie.Albert.ext
  · rfl
  · rfl
  · rfl
  · exact hg.1
  · exact hg.2.1
  · exact hg.2.2

end AlbertSequential.NativeAnalysis
