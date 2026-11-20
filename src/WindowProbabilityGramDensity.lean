/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The triangular Cholesky coordinates for the unnormalized complex Gram density. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open scoped Matrix ComplexOrder

/-- Unit lower triangular complex Cholesky factor. The coordinates are the
upper entries of the resulting Hermitian matrix before pivot scaling. -/
def unitLowerComplexCholesky (z w v : ℂ) : ComplexMatrix3 :=
  !![1, 0, 0; star z, 1, 0; star w, star v, 1]

/-- Columns of the exact pivot-scaled complex Cholesky chart. -/
def complexCholeskyMatrix (r : Fin 3 → ℝ) (z w v : ℂ) : ComplexMatrix3 :=
  let L := unitLowerComplexCholesky z w v
  L * Matrix.diagonal (fun i => (r i : ℂ)) * L.conjTranspose

private theorem complexCholeskyMatrix_apply (r : Fin 3 → ℝ) (z w v : ℂ) (i j : Fin 3) :
    complexCholeskyMatrix r z w v i j =
      ∑ k, unitLowerComplexCholesky z w v i k * (r k : ℂ) *
        star (unitLowerComplexCholesky z w v j k) := by
  unfold complexCholeskyMatrix
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

theorem complexCholeskyMatrix_det (r : Fin 3 → ℝ) (z w v : ℂ) :
    (complexCholeskyMatrix r z w v).det = ((∏ i, r i : ℝ) : ℂ) := by
  have hL : (unitLowerComplexCholesky z w v).det = 1 := by
    rw [Matrix.det_fin_three]
    simp [unitLowerComplexCholesky]
  unfold complexCholeskyMatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hL, star_one,
    one_mul, mul_one, Matrix.det_diagonal, Complex.ofReal_prod]

/-- The exact trace polynomial in the independent Cholesky coordinates. -/
theorem complexCholeskyMatrix_trace_re (r : Fin 3 → ℝ) (z w v : ℂ) :
    (complexCholeskyMatrix r z w v).trace.re =
      r 0 + r 1 + r 2 + r 0 * (Complex.normSq z + Complex.normSq w) + r 1 * Complex.normSq v := by
  simp [complexCholeskyMatrix_apply, unitLowerComplexCholesky, Matrix.trace, Matrix.diag,
    Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The nine real Cholesky coordinates are interlaced by their elimination order.
The pivots occur at positions 0, 5 and 8. -/
def complexCholeskyChart (u : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![u 0, u 0 * u 1, u 0 * u 2, u 0 * u 3, u 0 * u 4,
    u 5 + u 0 * (u 1^2 + u 2^2),
    u 5 * u 6 + u 0 * (u 1 * u 3 + u 2 * u 4),
    u 5 * u 7 + u 0 * (u 1 * u 4 - u 2 * u 3),
    u 8 + u 0 * (u 3^2 + u 4^2) + u 5 * (u 6^2 + u 7^2)]

/-- The column of a Cholesky input that determines the derivative of the same output coordinate. -/
def complexCholeskyJacobianDiagonal (u : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![1, u 0, u 0, u 0, u 0, 1, u 5, u 5, 1]

private theorem differentiable_complexCholeskyChart : Differentiable ℝ complexCholeskyChart := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> simp [complexCholeskyChart] <;> fun_prop

private theorem deriv_complexCholeskyChart_axis (u : Fin 9 → ℝ) (i j : Fin 9) :
    deriv (fun t : ℝ => complexCholeskyChart (u + t • Pi.single j 1) i) 0 =
      LinearMap.toMatrix' (fderiv ℝ complexCholeskyChart u).toLinearMap i j := by
  let e : Fin 9 → ℝ := Pi.single j 1
  let f := fun t : ℝ => u + t • e
  have h₀ : f 0 = u := by simp [f]
  have hf : HasDerivAt f e 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add u
    simp only [one_smul] at h
    exact h
  have h := (differentiable_complexCholeskyChart u).hasFDerivAt.comp_hasDerivAt_of_eq 0 hf h₀.symm
  have h' := (hasFDerivAt_apply (𝕜 := ℝ) i (complexCholeskyChart u)).comp_hasDerivAt_of_eq 0 h
    (congrArg complexCholeskyChart h₀.symm)
  exact h'.deriv

/-- The real chart determinant is the Bartlett pivot multiplier. -/
theorem complexCholeskyChart_det_fderiv (u : Fin 9 → ℝ) :
    LinearMap.det (fderiv ℝ complexCholeskyChart u).toLinearMap = u 0 ^ 4 * u 5 ^ 2 := by
  let J := LinearMap.toMatrix' (fderiv ℝ complexCholeskyChart u).toLinearMap
  have hL : J.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    change LinearMap.toMatrix' (fderiv ℝ complexCholeskyChart u).toLinearMap i j = 0
    rw [← deriv_complexCholeskyChart_axis]
    have hLine : (fun t : ℝ => complexCholeskyChart (u + t • Pi.single j 1) i) =
        fun _ => complexCholeskyChart u i := by
      funext t
      fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij <;>
        simp [complexCholeskyChart]
    rw [hLine, deriv_const]
  have hD (i : Fin 9) : J i i = complexCholeskyJacobianDiagonal u i := by
    change LinearMap.toMatrix' (fderiv ℝ complexCholeskyChart u).toLinearMap i i = _
    rw [← deriv_complexCholeskyChart_axis]
    have hLine : (fun t : ℝ => complexCholeskyChart (u + t • Pi.single i 1) i) =
        fun t => complexCholeskyChart u i + t * complexCholeskyJacobianDiagonal u i := by
      funext t
      fin_cases i <;> simp [complexCholeskyChart, complexCholeskyJacobianDiagonal] <;> ring
    rw [hLine]
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const (complexCholeskyJacobianDiagonal u i)).const_add
      (complexCholeskyChart u i)
    rw [one_mul] at h
    exact h.deriv
  rw [← LinearMap.det_toMatrix']
  change J.det = _
  rw [Matrix.det_of_isLowerTriangular _ hL]
  simp [hD, complexCholeskyJacobianDiagonal, Fin.prod_univ_succ]
  ring

/-- The interlaced coordinates of a Hermitian matrix in the Cholesky chart. -/
def hermitianCholeskyCoordinates (M : ComplexMatrix3) : Fin 9 → ℝ :=
  ![(M 0 0).re, (M 0 1).re, (M 0 1).im, (M 0 2).re, (M 0 2).im,
    (M 1 1).re, (M 1 2).re, (M 1 2).im, (M 2 2).re]

/-- The triangular polynomial chart is the literal complex matrix factorization. -/
theorem hermitianCholeskyCoordinates_complexCholeskyMatrix (u : Fin 9 → ℝ) :
    hermitianCholeskyCoordinates
      (complexCholeskyMatrix ![u 0, u 5, u 8] ⟨u 1, u 2⟩ ⟨u 3, u 4⟩ ⟨u 6, u 7⟩) =
      complexCholeskyChart u := by
  funext i
  fin_cases i <;>
    simp [complexCholeskyChart, hermitianCholeskyCoordinates, complexCholeskyMatrix_apply,
      unitLowerComplexCholesky,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

/-- Every strictly positive pivot tuple gives a positive definite matrix. -/
theorem complexCholeskyMatrix_posDef (r : Fin 3 → ℝ) (z w v : ℂ) (hr : ∀ i, 0 < r i) :
    (complexCholeskyMatrix r z w v).PosDef := by
  let L := unitLowerComplexCholesky z w v
  have hL : L.det = 1 := by
    unfold L
    rw [Matrix.det_fin_three]
    simp [unitLowerComplexCholesky]
  have hD : (Matrix.diagonal (fun i => (r i : ℂ))).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun i => by exact_mod_cast hr i
  have hu : IsUnit L.conjTranspose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_conjTranspose, hL, star_one]
    exact isUnit_one
  have h := hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  simpa [complexCholeskyMatrix, L] using h

/-- The open pivot domain of the real chart. -/
def complexCholeskyPivotRegion : Set (Fin 9 → ℝ) :=
  {u | 0 < u 0 ∧ 0 < u 5 ∧ 0 < u 8}

/-- Successive elimination recovers all real coordinates from the matrix chart. -/
theorem complexCholeskyChart_injective_on_pivots : Set.InjOn complexCholeskyChart complexCholeskyPivotRegion := by
  intro u hu v _ h
  have hh (i : Fin 9) := congrFun h i
  have h0 : u 0 = v 0 := hh 0
  have h1 : u 1 = v 1 := by
    have he := hh 1
    change u 0 * u 1 = v 0 * v 1 at he
    rw [← h0] at he
    exact mul_left_cancel₀ (ne_of_gt hu.1) he
  have h2 : u 2 = v 2 := by
    have he := hh 2
    change u 0 * u 2 = v 0 * v 2 at he
    rw [← h0] at he
    exact mul_left_cancel₀ (ne_of_gt hu.1) he
  have h3 : u 3 = v 3 := by
    have he := hh 3
    change u 0 * u 3 = v 0 * v 3 at he
    rw [← h0] at he
    exact mul_left_cancel₀ (ne_of_gt hu.1) he
  have h4 : u 4 = v 4 := by
    have he := hh 4
    change u 0 * u 4 = v 0 * v 4 at he
    rw [← h0] at he
    exact mul_left_cancel₀ (ne_of_gt hu.1) he
  have h5 : u 5 = v 5 := by
    have he := hh 5
    change u 5 + u 0 * (u 1^2 + u 2^2) = v 5 + v 0 * (v 1^2 + v 2^2) at he
    rw [← h0, ← h1, ← h2] at he
    exact add_right_cancel he
  have h6 : u 6 = v 6 := by
    have he := hh 6
    change u 5 * u 6 + u 0 * (u 1 * u 3 + u 2 * u 4) =
      v 5 * v 6 + v 0 * (v 1 * v 3 + v 2 * v 4) at he
    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5] at he
    exact mul_left_cancel₀ (ne_of_gt hu.2.1) (add_right_cancel he)
  have h7 : u 7 = v 7 := by
    have he := hh 7
    change u 5 * u 7 + u 0 * (u 1 * u 4 - u 2 * u 3) =
      v 5 * v 7 + v 0 * (v 1 * v 4 - v 2 * v 3) at he
    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5] at he
    exact mul_left_cancel₀ (ne_of_gt hu.2.1) (add_right_cancel he)
  have h8 : u 8 = v 8 := by
    have he := hh 8
    change u 8 + u 0 * (u 3^2 + u 4^2) + u 5 * (u 6^2 + u 7^2) =
      v 8 + v 0 * (v 3^2 + v 4^2) + v 5 * (v 6^2 + v 7^2) at he
    rw [← h0, ← h3, ← h4, ← h5, ← h6, ← h7] at he
    exact add_right_cancel (add_right_cancel he)
  funext i
  fin_cases i <;> assumption

end AlbertSequential.WindowProbability
