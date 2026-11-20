/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralLinearization
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! The real derivative of the conjugation chart giving the local spectral factor. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open NormedSpace
open scoped Matrix Matrix.Norms.Frobenius

/-- The real Fréchet derivative at the origin of the literal exponential
conjugation map is diagonal variation plus the commutator. -/
theorem fderiv_matrixExpConjugation_zero (D : ComplexMatrix3) (u : ComplexMatrix3 × ComplexMatrix3) :
    fderiv ℝ (fun q : ComplexMatrix3 × ComplexMatrix3 =>
      exp q.2 * (D + q.1) * exp (-q.2)) 0 u = u.1 + u.2 * D - D * u.2 := by
  let E := ComplexMatrix3 × ComplexMatrix3
  let fl := ContinuousLinearMap.fst ℝ ComplexMatrix3 ComplexMatrix3
  let fr := ContinuousLinearMap.snd ℝ ComplexMatrix3 ComplexMatrix3
  have hExp := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ComplexMatrix3))
  have hd : HasFDerivAt (fun q : E => D + q.1) fl (0 : E) := by
    convert (hasFDerivAt_const D (0 : E)).add fl.hasFDerivAt using 1 <;> first
      | rfl
      | exact heq_of_eq (zero_add fl).symm
  have hl : HasFDerivAt (fun q : E => exp q.2) fr (0 : E) := by
    have h : HasFDerivAt exp (1 : ComplexMatrix3 →L[ℝ] ComplexMatrix3) (fr (0 : E)) := by
      rw [fr.map_zero]
      exact hExp
    convert h.comp (0 : E) fr.hasFDerivAt using 1 <;> rfl
  have hr : HasFDerivAt (fun q : E => exp (-q.2)) (-fr) (0 : E) := by
    have h : HasFDerivAt exp (1 : ComplexMatrix3 →L[ℝ] ComplexMatrix3) ((-fr) (0 : E)) := by
      rw [ContinuousLinearMap.map_zero]
      exact hExp
    convert h.comp (0 : E) (-fr).hasFDerivAt using 1 <;> rfl
  have h := ((hl.mul' hd).mul' hr).fderiv
  have hEq := congrArg (fun L : E →L[ℝ] ComplexMatrix3 => L u) h
  refine hEq.trans ?_
  change (exp (0 : ComplexMatrix3) * (D + 0)) * (-u.2) +
    (exp (0 : ComplexMatrix3) * u.1 + u.2 * (D + 0)) * exp (-(0 : ComplexMatrix3)) = _
  simp only [NormedSpace.exp_zero, add_zero, one_mul, neg_zero, mul_one, mul_neg, sub_eq_add_neg]
  abel

/-- In the companion's spectral coordinates the literal conjugation
derivative has the specified nine real weights. -/
theorem spectralExpConjugation_derivative_coordinates (eigenvalues variation : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (eigenvalues i : ℂ)
    let u : ComplexMatrix3 × ComplexMatrix3 :=
      (Matrix.diagonal (fun i => (variation i : ℂ)), spectralSkewMatrix v)
    hermitianMatrixRealCoordinates
      (fderiv ℝ (fun q : ComplexMatrix3 × ComplexMatrix3 => exp q.2 * (D + q.1) * exp (-q.2)) 0 u) =
      (Matrix.diagonal (spectralLinearizationWeights eigenvalues)).mulVec
        ![variation 0, variation 1, variation 2, (v 0).re, (v 0).im,
          (v 1).re, (v 1).im, (v 2).re, (v 2).im] := by
  intro D u
  rw [fderiv_matrixExpConjugation_zero]
  exact spectralLinearization_coordinates eigenvalues variation v

/-- The three unnormalized eigenvalues from trace and the two free simplex coordinates. -/
def eigenvaluesFromTraceAndSimplex (r a b : ℝ) : Fin 3 → ℝ :=
  ![r * a, r * b, r * (1 - a - b)]

/-- The radial/simplex coordinate derivative, in order trace and two simplex coordinates. -/
def traceSimplexJacobian (r a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![a, r, 0], ![b, 0, r], ![1 - a - b, -r, -r]]

/-- The literal radial map has the displayed real derivative at every point. -/
theorem fderiv_eigenvaluesFromTraceAndSimplex (u v : Fin 3 → ℝ) :
    fderiv ℝ (fun q : Fin 3 → ℝ => eigenvaluesFromTraceAndSimplex (q 0) (q 1) (q 2)) u v =
      (traceSimplexJacobian (u 0) (u 1) (u 2)).mulVec v := by
  let J := traceSimplexJacobian (u 0) (u 1) (u 2)
  let L := J.mulVecLin.toContinuousLinearMap
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) u
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) u
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) u
  have ha := h0.mul h1
  have hb := h0.mul h2
  have hc := h0.mul (((hasFDerivAt_const (1 : ℝ) u).sub h1).sub h2)
  have h : HasFDerivAt (fun q : Fin 3 → ℝ => eigenvaluesFromTraceAndSimplex (q 0) (q 1) (q 2)) L u := by
    apply hasFDerivAt_pi''
    intro i
    fin_cases i
    · convert ha using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        change (J.mulVec w) 0 = _
        simp [J, traceSimplexJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring
    · convert hb using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        change (J.mulVec w) 1 = _
        simp [J, traceSimplexJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring
    · convert hc using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        change (J.mulVec w) 2 = _
        simp [J, traceSimplexJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring
  exact congrArg (fun F : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) => F v) h.fderiv

theorem traceSimplexJacobian_det (r a b : ℝ) : (traceSimplexJacobian r a b).det = r ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [traceSimplexJacobian]
  ring

/-- The unnormalized three-eigenvalue polynomial at environment dimension four. -/
def fourColumnEigenvalueWeight (c : Fin 3 → ℝ) : ℝ :=
  c 0 * c 1 * c 2 * ((c 0 - c 1) ^ 2 * (c 0 - c 2) ^ 2 * (c 1 - c 2) ^ 2)

/-- The polynomial and radial Jacobian split into the printed simplex
factor and the eleventh power of the trace. -/
theorem fourColumnEigenvalueWeight_trace_simplex (r a b : ℝ) :
    fourColumnEigenvalueWeight (eigenvaluesFromTraceAndSimplex r a b) * (traceSimplexJacobian r a b).det =
      r ^ 11 * fourColumnEigenvalueWeight ![a, b, 1 - a - b] := by
  rw [traceSimplexJacobian_det]
  simp [fourColumnEigenvalueWeight, eigenvaluesFromTraceAndSimplex]
  ring

/-- The radial integral in the four-column trace normalization. -/
theorem fourColumn_radialGammaIntegral :
    (∫ r in Set.Ioi (0 : ℝ), r ^ (11 : ℕ) * Real.exp (-r)) = (Nat.factorial 11 : ℝ) := by
  have h := Real.Gamma_eq_integral (show (0 : ℝ) < 12 by norm_num)
  rw [show (12 : ℝ) - 1 = (11 : ℕ) by norm_num] at h
  simp only [Real.rpow_natCast] at h
  calc
    _ = Real.Gamma 12 := by simpa only [mul_comm] using h.symm
    _ = _ := by
      rw [← (show ((11 : ℕ) : ℝ) + 1 = 12 by norm_num)]
      exact Real.Gamma_nat_eq_factorial 11

/-- The real coordinate weights of diagonal congruence on Hermitian matrices. -/
def hermitianDiagonalCongruenceWeights (d : Fin 3 → ℝ) : Fin 9 → ℝ :=
  ![d 0 ^ 2, d 1 ^ 2, d 2 ^ 2, d 0 * d 1, d 0 * d 1,
    d 0 * d 2, d 0 * d 2, d 1 * d 2, d 1 * d 2]

theorem hermitianDiagonalCongruence_coordinates (d : Fin 3 → ℝ) (M : ComplexMatrix3) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    hermitianMatrixRealCoordinates (D * M * D) =
      (Matrix.diagonal (hermitianDiagonalCongruenceWeights d)).mulVec
        (hermitianMatrixRealCoordinates M) := by
  intro D
  funext i
  fin_cases i <;>
    simp [D, hermitianMatrixRealCoordinates, hermitianDiagonalCongruenceWeights,
      Matrix.mulVec_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- The volume multiplier of diagonal congruence in the nine real coordinates. -/
theorem hermitianDiagonalCongruence_det (d : Fin 3 → ℝ) :
    (Matrix.diagonal (hermitianDiagonalCongruenceWeights d)).det = (d 0 * d 1 * d 2) ^ 6 := by
  rw [Matrix.det_diagonal]
  simp [hermitianDiagonalCongruenceWeights, Fin.prod_univ_succ]
  ring

end AlbertSequential.WindowProbability
