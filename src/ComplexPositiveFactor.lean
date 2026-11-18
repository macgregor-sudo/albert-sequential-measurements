module

public import Mathlib.Analysis.Matrix.PosDef

/-! Singular-safe finite complex PSD square factor. The spectral argument is
that of the real finite-Gram factor, with the conjugate transpose
preserved. No general CFC/order API is needed.
-/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential

theorem exists_complexPositiveFactor {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.PosSemidef) :
    ∃ B : Matrix n n ℂ, C = B * B.conjTranspose := by
  let U : Matrix n n ℂ := hC.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    Matrix.diagonal (fun i => (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ))
  have hD : D * D = Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hC.eigenvalues_nonneg i)
  have hDstar : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.conjTranspose_apply, RCLike.star_def]
    · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hspec : C = U * Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)) *
      U.conjTranspose := by
    simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hC.isHermitian.spectral_theorem
  refine ⟨U * D, ?_⟩
  rw [Matrix.conjTranspose_mul, hDstar]
  calc
    C = U * (D * D) * U.conjTranspose := by rw [hD]; exact hspec
    _ = U * D * (D * U.conjTranspose) := by simp only [Matrix.mul_assoc]

end AlbertSequential
