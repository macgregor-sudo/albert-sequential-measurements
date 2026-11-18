module

public import NativeDiagonalProduct

/-! The raw-trace Newton cubic from actual compact diagonalization. The scalar
factorization is the ordinary three-root characteristic polynomial. No old
cubic residual, Jordan identity theorem or Jordan instance is imported. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem scalar_newton_factorization (a b c t : ℝ) :
    6 * t^3 - 6 * (a + b + c) * t^2 +
      (3 * (a + b + c)^2 - 3 * (a^2 + b^2 + c^2)) * t -
      ((a + b + c)^3 - 3 * (a + b + c) * (a^2 + b^2 + c^2) +
        2 * (a^3 + b^3 + c^3)) = 6 * (t - a) * (t - b) * (t - c) := by
  ring

private theorem scalar_newton_root (a b c t : ℝ) (ht : t = a ∨ t = b ∨ t = c) :
    6 * t^3 - 6 * (a + b + c) * t^2 +
      (3 * (a + b + c)^2 - 3 * (a^2 + b^2 + c^2)) * t -
      ((a + b + c)^3 - 3 * (a + b + c) * (a^2 + b^2 + c^2) +
        2 * (a^3 + b^3 + c^3)) = 0 := by
  rw [scalar_newton_factorization]
  rcases ht with rfl | rfl | rfl <;> ring

private def recoveredDiagonal (a b c : ℝ) : Glennie.Albert := ⟨a, b, c, 0, 0, 0⟩

private theorem recovered_diagonal_newton (a b c : ℝ) :
    let x := recoveredDiagonal a b c
    (6 : ℝ) • Glennie.jordan x (Glennie.jordan x x) -
      (6 * Glennie.trace x) • Glennie.jordan x x +
      (3 * (Glennie.trace x)^2 - 3 * Glennie.trace (Glennie.jordan x x)) • x -
      ((Glennie.trace x)^3 - 3 * Glennie.trace x * Glennie.trace (Glennie.jordan x x) +
        2 * Glennie.trace (Glennie.jordan x (Glennie.jordan x x))) • (1 : Glennie.Albert) = 0 := by
  dsimp only
  apply Glennie.Albert.ext
  all_goals simp [recoveredDiagonal, recovered_diagonal_mul, Glennie.trace]
  · convert scalar_newton_root a b c a (Or.inl rfl) using 1
    ring
  · convert scalar_newton_root a b c b (Or.inr (Or.inl rfl)) using 1
    ring
  · convert scalar_newton_root a b c c (Or.inr (Or.inr rfl)) using 1
    ring

private theorem recovered_newton_identity (x : Glennie.Albert) :
    (6 : ℝ) • Glennie.jordan x (Glennie.jordan x x) -
      (6 * Glennie.trace x) • Glennie.jordan x x +
      (3 * (Glennie.trace x)^2 - 3 * Glennie.trace (Glennie.jordan x x)) • x -
      ((Glennie.trace x)^3 - 3 * Glennie.trace x * Glennie.trace (Glennie.jordan x x) +
        2 * Glennie.trace (Glennie.jordan x (Glennie.jordan x x))) • (1 : Glennie.Albert) = 0 := by
  obtain ⟨g, hg⟩ := Glennie.native_diagonalization x
  have hd : g.equiv x = recoveredDiagonal (g.equiv x).d0 (g.equiv x).d1 (g.equiv x).d2 := by
    apply Glennie.Albert.ext
    · rfl
    · rfl
    · rfl
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2
  have h := recovered_diagonal_newton (g.equiv x).d0 (g.equiv x).d1 (g.equiv x).d2
  dsimp only at h
  simp only [← hd, ← g.map_jordan, g.map_trace] at h
  apply g.equiv.injective
  simpa only [map_sub, map_add, map_smul, map_zero, g.map_unit] using h

/-- Exact six-times Newton cubic on every compact native element, with raw
trace(e)=3 and the actual trace-square norm coefficient. -/
theorem newton_cubic_identity (x : Albert) :
    (6 : ℝ) • jordanMul x (jordanMul x x) -
      (6 * albertTrace x) • jordanMul x x +
      (3 * (albertTrace x)^2 - 3 * albertTrace (jordanMul x x)) • x -
      ((albertTrace x)^3 - 3 * albertTrace x * albertTrace (jordanMul x x) +
        2 * albertTrace (jordanMul x (jordanMul x x))) • albertUnit = 0 := by
  have h := recovered_newton_identity (recoveredCoordinateEquiv x)
  apply recoveredCoordinateEquiv.injective
  simpa only [map_sub, map_add, map_smul, map_zero,
    ← recoveredCoordinateEquiv_trace, recoveredCoordinateEquiv_jordanMul,
    recoveredCoordinateEquiv_unit] using h

theorem cubic_characteristic_identity (x : Albert) :
    jordanMul x (jordanMul x x) =
      albertTrace x • jordanMul x x -
        (((albertTrace x)^2 - albertTrace (jordanMul x x)) / 2 : ℝ) • x +
        (((albertTrace x)^3 - 3 * albertTrace x * albertTrace (jordanMul x x) +
          2 * albertTrace (jordanMul x (jordanMul x x))) / 6 : ℝ) • albertUnit := by
  have h : (6 : ℝ) • (jordanMul x (jordanMul x x) -
      (albertTrace x • jordanMul x x -
        (((albertTrace x)^2 - albertTrace (jordanMul x x)) / 2 : ℝ) • x +
        (((albertTrace x)^3 - 3 * albertTrace x * albertTrace (jordanMul x x) +
          2 * albertTrace (jordanMul x (jordanMul x x))) / 6 : ℝ) • albertUnit)) = 0 := by
    calc
      _ = (6 : ℝ) • jordanMul x (jordanMul x x) -
          (6 * albertTrace x) • jordanMul x x +
          (3 * (albertTrace x)^2 - 3 * albertTrace (jordanMul x x)) • x -
          ((albertTrace x)^3 - 3 * albertTrace x * albertTrace (jordanMul x x) +
            2 * albertTrace (jordanMul x (jordanMul x x))) • albertUnit := by module
      _ = 0 := newton_cubic_identity x
  have hh := congrArg (fun z : Albert => (1 / 6 : ℝ) • z) h
  simpa only [smul_smul, show (1 / 6 : ℝ) * 6 = 1 by norm_num,
    one_smul, smul_zero, sub_eq_zero] using hh

end AlbertSequential.NativeAnalysis
