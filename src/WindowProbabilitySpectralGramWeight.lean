/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramCandidate

/-! Values of the exact Hermitian Gram density on a positive spectral chart. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Set
open scoped Matrix ComplexOrder

/-- The exact Hermitian Gram weight at a genuinely unitarily diagonalized
matrix has the trace-exponential and the eigenvalue product in the claim. -/
theorem complexFourColumnGramWeight_of_unitaryDiagonal (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) (M : Hermitian3)
    (hM : M.val = Unitary.conjStarAlgAut ℂ ComplexMatrix3 U (Matrix.diagonal fun i => (x i : ℂ))) :
    complexFourColumnGramWeight M = Real.exp (-(∑ i, x i)) * ∏ i, x i := by
  let D : ComplexMatrix3 := Matrix.diagonal fun i => (x i : ℂ)
  have hD : D.PosDef := Matrix.posDef_diagonal_iff.mpr (fun i => Complex.zero_lt_real.mpr (hx i))
  have hP : M ∈ complexPositiveDefiniteCone := by
    change M.val.PosDef
    rw [hM, Unitary.conjStarAlgAut_apply]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr hD
  have hTrace : M.val.trace.re = ∑ i, x i := by
    rw [hM, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      Matrix.one_mul, Matrix.trace_diagonal]
    simp [Complex.re_sum]
  have hUnit : (U : ComplexMatrix3).det * (star (U : ComplexMatrix3)).det = 1 := by
    rw [← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one]
  have hDet : M.val.det.re = ∏ i, x i := by
    rw [hM, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      hUnit, one_mul, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [complexFourColumnGramWeight, indicator_of_mem hP, hTrace, hDet]

end AlbertSequential.WindowProbability
