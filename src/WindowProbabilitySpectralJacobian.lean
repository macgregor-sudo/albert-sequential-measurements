/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralDerivative

/-! Differential of a spectral chart with independently varying diagonal
and unitary factors. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open scoped Matrix Matrix.Norms.Frobenius

private def matrixConjTransposeRealCLM : ComplexMatrix3 →L[ℝ] ComplexMatrix3 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by intro r M; rw [Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply] }

private theorem hasFDerivAt_matrixConjTranspose
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ComplexMatrix3} {D : E →L[ℝ] ComplexMatrix3} {v : E}
    (hD : HasFDerivAt U D v) :
    HasFDerivAt (fun x => (U x).conjTranspose) (matrixConjTransposeRealCLM.comp D) v :=
  matrixConjTransposeRealCLM.hasFDerivAt.comp v hD

/-- The left-translated derivative of a genuinely unitary family is skew-Hermitian. -/
theorem unitary_tangent_conjTranspose
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Matrix.unitaryGroup (Fin 3) ℂ) (D : E →L[ℝ] ComplexMatrix3) (v w : E)
    (hD : HasFDerivAt (fun x => (U x : ComplexMatrix3)) D v) :
    let K := (U v : ComplexMatrix3).conjTranspose * D w
    K.conjTranspose = -K := by
  intro K
  have hS := hasFDerivAt_matrixConjTranspose hD
  have hProd := (hS.mul' hD).fderiv
  have hOne : (fun x => (U x : ComplexMatrix3).conjTranspose * U x) = fun _ => 1 := by
    funext x
    exact Unitary.coe_star_mul_self (U x)
  change fderiv ℝ (fun x => (U x : ComplexMatrix3).conjTranspose * U x) v = _ at hProd
  rw [hOne, fderiv_const_apply] at hProd
  have hEq := congrArg (fun L : E →L[ℝ] ComplexMatrix3 => L w) hProd
  change 0 = (U v : ComplexMatrix3).conjTranspose * D w + (D w).conjTranspose * U v at hEq
  change ((U v : ComplexMatrix3).conjTranspose * D w).conjTranspose = -K
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact eq_neg_of_add_eq_zero_right hEq.symm

/-- In a moving unitary frame, the genuine derivative separates the diagonal
variation from the commutator with the angular tangent. -/
theorem fderiv_unitaryConjugation_movingFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Matrix.unitaryGroup (Fin 3) ℂ) (A : E → ComplexMatrix3)
    (DU DA : E →L[ℝ] ComplexMatrix3) (v w : E)
    (hU : HasFDerivAt (fun x => (U x : ComplexMatrix3)) DU v) (hA : HasFDerivAt A DA v) :
    let K := (U v : ComplexMatrix3).conjTranspose * DU w
    fderiv ℝ (fun x => (U x : ComplexMatrix3) * A x * (U x : ComplexMatrix3).conjTranspose) v w =
      (U v : ComplexMatrix3) * (DA w + K * A v - A v * K) * (U v : ComplexMatrix3).conjTranspose := by
  intro K
  have hS := hasFDerivAt_matrixConjTranspose hU
  have hD := ((hU.mul' hA).mul' hS).fderiv
  have hEq := congrArg (fun L : E →L[ℝ] ComplexMatrix3 => L w) hD
  change fderiv ℝ (fun x => (U x : ComplexMatrix3) * A x * (U x : ComplexMatrix3).conjTranspose) v w =
    ((U v : ComplexMatrix3) * A v) * (DU w).conjTranspose +
      ((U v : ComplexMatrix3) * DA w + DU w * A v) * (U v : ComplexMatrix3).conjTranspose at hEq
  have hUnit : (U v : ComplexMatrix3) * (U v : ComplexMatrix3).conjTranspose = 1 :=
    Unitary.coe_mul_star_self (U v)
  have hK : K.conjTranspose = -K := unitary_tangent_conjTranspose U DU v w hU
  have hLeft : DU w = (U v : ComplexMatrix3) * K := by
    change DU w = (U v : ComplexMatrix3) * ((U v : ComplexMatrix3).conjTranspose * DU w)
    rw [← Matrix.mul_assoc, hUnit, Matrix.one_mul]
  have hRight : (DU w).conjTranspose = -K * (U v : ComplexMatrix3).conjTranspose := by
    calc
      _ = ((DU w).conjTranspose * U v) * (U v : ComplexMatrix3).conjTranspose :=
        by rw [Matrix.mul_assoc, hUnit, Matrix.mul_one]
      _ = _ := by
        congr 1
        exact (by simpa [K, Matrix.conjTranspose_mul] using hK)
  rw [hEq, hRight, hLeft]
  noncomm_ring

/-- The real coordinates of the commutator depend exactly on the upper
entries of the angular tangent. This identity applies at every chart point. -/
theorem spectralCommutator_coordinates (s radial : Fin 3 → ℝ) (K : ComplexMatrix3) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (s i : ℂ)
    hermitianMatrixRealCoordinates
      (Matrix.diagonal (fun i => (radial i : ℂ)) + K * D - D * K) =
      (Matrix.diagonal (spectralLinearizationWeights s)).mulVec
        ![radial 0, radial 1, radial 2, (K 0 1).re, (K 0 1).im,
          (K 0 2).re, (K 0 2).im, (K 1 2).re, (K 1 2).im] := by
  intro D
  funext i
  fin_cases i <;>
    simp [D, hermitianMatrixRealCoordinates, spectralLinearizationWeights, Matrix.mulVec_diagonal,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.mul_re, Complex.mul_im] <;> ring

end AlbertSequential.WindowProbability
