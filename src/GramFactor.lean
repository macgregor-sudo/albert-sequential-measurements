/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! A singular-safe real Gram factor and exact column-span rank.
Use finite spectral theory directly; no global norm instance is changed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

theorem exists_realGramFactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, G = B.transpose * B := by
  let U : Matrix ι ι ℝ := hG.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (hG.isHermitian.eigenvalues i))
  refine ⟨D * U.transpose, ?_⟩
  have hD : D * D = Matrix.diagonal hG.isHermitian.eigenvalues := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hG.eigenvalues_nonneg i)
  have hstar : star U = U.transpose := by ext i j; rfl
  have hDt : D.transpose = D := Matrix.diagonal_transpose _
  have hspec : G = U * Matrix.diagonal hG.isHermitian.eigenvalues * star U := by
    simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def] using hG.isHermitian.spectral_theorem
  calc
    G = U * Matrix.diagonal hG.isHermitian.eigenvalues * U.transpose := by
      simpa only [hstar] using hspec
    _ = (D * U.transpose).transpose * (D * U.transpose) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, hDt]
      calc
        U * Matrix.diagonal hG.isHermitian.eigenvalues * U.transpose = U * (D * D) * U.transpose := by rw [hD]
        _ = U * D * (D * U.transpose) := by simp only [Matrix.mul_assoc]

theorem realGramFactor_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B G : Matrix ι ι ℝ) (hG : G = B.transpose * B) :
    G.rank = B.rank := by
  rw [hG, Matrix.rank_transpose_mul_self]

end AlbertSequential
