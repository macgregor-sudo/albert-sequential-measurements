module

public import NativeDiagonalProduct

/-! The native Jordan identity from genuine diagonalization and commuting
scalar slot actions. No native cubic residual or abstract Jordan instance
supplies the result. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem diagonal_jordan_identity (d : Fin 3 → ℝ) (y : Albert) :
    jordanMul (jordanMul (diagonalElement d) y)
        (jordanMul (diagonalElement d) (diagonalElement d)) =
      jordanMul (diagonalElement d)
        (jordanMul y (jordanMul (diagonalElement d) (diagonalElement d))) := by
  simp only [diagonal_square]
  rw [jordanMul_comm (jordanMul (diagonalElement d) y)
    (diagonalElement (fun i => d i ^ 2)),
    jordanMul_comm y (diagonalElement (fun i => d i ^ 2))]
  simp only [jordanMul_diagonal]
  -- Transparent rewriting is needed only for projections of the sealed carrier.
  erw [jordanMul_diagonal, jordanMul_diagonal]
  apply Prod.ext
  · funext i
    change (d i)^2 * (d i * y.1 i) = d i * ((d i)^2 * y.1 i)
    ring
  · funext i
    fin_cases i <;> exact smul_comm _ _ _

/-- The exact Jordan identity on every pair of current compact native elements. -/
theorem jordan_identity (x y : Albert) :
    jordanMul (jordanMul x y) (jordanMul x x) =
      jordanMul x (jordanMul y (jordanMul x x)) := by
  obtain ⟨g, d, hgx⟩ := nativeDiagonalization x
  apply g.linearEquiv.injective
  simp only [g.preserves_product, hgx]
  exact diagonal_jordan_identity d (g.linearEquiv y)

end AlbertSequential.NativeAnalysis
