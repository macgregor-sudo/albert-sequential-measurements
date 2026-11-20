/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramCongruence

/-! Laplace integrals of the unnormalized Hermitian Gram density candidate. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator ENNReal MatrixOrder ComplexOrder

/-- Unnormalized density with an arbitrary Hermitian trace tilt. -/
def complexFourColumnGramTilt (T : ComplexMatrix3) (M : Hermitian3) : ℝ :=
  complexPositiveDefiniteCone.indicator
    (fun H => Real.exp (-(T * H.val).trace.re) * H.val.det.re) M

private theorem measurable_complexFourColumnGramWeight_ennreal :
    Measurable (fun M => ENNReal.ofReal (complexFourColumnGramWeight M)) :=
  (measurable_complexFourColumnGramWeight).ennreal_ofReal

private theorem complexFourColumnGramTilt_diagonal_apply
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) (M : Hermitian3) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    complexFourColumnGramTilt (D * D) M =
      ((d 0 * d 1 * d 2) ^ 2)⁻¹ * complexFourColumnGramWeight (hermitianDiagonalCongruence d M) := by
  intro D
  let N := hermitianDiagonalCongruence d M
  let p := d 0 * d 1 * d 2
  have hv : N.val = D * M.val * D := hermitianDiagonalCongruence_apply d M
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (fun _ => by simp [IsSelfAdjoint])
  have hdD : D.det = (p : ℂ) := by
    rw [Matrix.det_diagonal]
    simp [p, Fin.prod_univ_three, mul_assoc]
  have hp : 0 < p := mul_pos (mul_pos (hd 0) (hd 1)) (hd 2)
  have hu : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr
    (isUnit_iff_ne_zero.mpr (hdD.symm ▸ Complex.ofReal_ne_zero.mpr hp.ne'))
  have hP : N ∈ complexPositiveDefiniteCone ↔ M ∈ complexPositiveDefiniteCone := by
    change N.val.PosDef ↔ M.val.PosDef
    rw [hv]
    have h := Matrix.IsUnit.posDef_star_right_conjugate_iff (x := M.val) hu
    change (D * M.val * D.conjTranspose).PosDef ↔ M.val.PosDef at h
    simpa only [hD.eq] using h
  by_cases hm : M ∈ complexPositiveDefiniteCone
  · have ht : N.val.trace.re = ((D * D) * M.val).trace.re := by
      rw [hv, Matrix.trace_mul_cycle]
    have hdet : N.val.det.re = p ^ 2 * M.val.det.re := by
      rw [hv, Matrix.det_mul, Matrix.det_mul, hdD]
      simp [Complex.mul_re, Complex.mul_im, pow_two, mul_left_comm, mul_comm]
    rw [complexFourColumnGramTilt, indicator_of_mem hm, complexFourColumnGramWeight,
      indicator_of_mem (hP.mpr hm), ht, hdet]
    have hcancel (t w s : ℝ) (hs : s ≠ 0) : t * w = s⁻¹ * (t * (s * w)) := calc
      _ = t * ((s⁻¹ * s) * w) := by rw [inv_mul_cancel₀ hs, one_mul]
      _ = _ := by ring
    exact hcancel _ _ _ (pow_ne_zero 2 hp.ne')
  · rw [complexFourColumnGramTilt, indicator_of_notMem hm, complexFourColumnGramWeight,
      indicator_of_notMem (fun h => hm (hP.mp h)), mul_zero]

/-- The diagonal tilt yields exactly the fourth inverse power of its determinant. -/
theorem lintegral_complexFourColumnGramTilt_diagonal
    (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    (∫⁻ M, ENNReal.ofReal (complexFourColumnGramTilt (D * D) M) ∂μ) =
      ((ENNReal.ofReal (d 0 * d 1 * d 2)) ^ 8)⁻¹ * ∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂μ := by
  intro D
  let p := d 0 * d 1 * d 2
  have hp : 0 < p := mul_pos (mul_pos (hd 0) (hd 1)) (hd 2)
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpT : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  have hC : Measurable (hermitianDiagonalCongruence d) :=
    (hermitianDiagonalCongruence d).continuous_of_finiteDimensional.measurable
  have hrewrite : (∫⁻ M, ENNReal.ofReal (complexFourColumnGramTilt (D * D) M) ∂μ) =
      ∫⁻ M, ENNReal.ofReal ((p ^ 2)⁻¹) *
        ENNReal.ofReal (complexFourColumnGramWeight (hermitianDiagonalCongruence d M)) ∂μ := by
    apply lintegral_congr
    intro M
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hp.le _))]
    exact congrArg ENNReal.ofReal (complexFourColumnGramTilt_diagonal_apply d hd M)
  rw [hrewrite]
  have hMap := lintegral_map (μ := μ) measurable_complexFourColumnGramWeight_ennreal hC
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hMap,
    map_hermitianDiagonalCongruence_haar μ d hd, lintegral_smul_measure, smul_eq_mul]
  change ENNReal.ofReal ((p ^ 2)⁻¹) * (ENNReal.ofReal ((p ^ 6)⁻¹) *
    (∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂μ)) = _
  rw [← mul_assoc, ENNReal.ofReal_inv_of_pos (pow_pos hp 2), ENNReal.ofReal_inv_of_pos (pow_pos hp 6),
    ENNReal.ofReal_pow hp.le 2, ENNReal.ofReal_pow hp.le 6,
    ← ENNReal.mul_inv (Or.inl (pow_ne_zero 2 hp0)) (Or.inl (ENNReal.pow_ne_top hpT)), ← pow_add]

/-- Unitary conjugation preserves the complex matrix determinant. -/
theorem det_conjStarAlgAut (U : Matrix.unitaryGroup (Fin 3) ℂ) (A : ComplexMatrix3) :
    (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U A).det = A.det := by
  have h := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Unitary.coe_star] at h
  rw [Matrix.det_mul, Matrix.det_one] at h
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h, one_mul]

private theorem complexFourColumnGramTilt_unitary_apply
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (T : ComplexMatrix3) (M : Hermitian3) :
    complexFourColumnGramTilt (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U T)
        (hermitianUnitaryConjugate U M) = complexFourColumnGramTilt T M := by
  let N := hermitianUnitaryConjugate U M
  let C := Unitary.conjStarAlgAut ℂ ComplexMatrix3 U
  have hv : N.val = C M.val := rfl
  have hP : N ∈ complexPositiveDefiniteCone ↔ M ∈ complexPositiveDefiniteCone := by
    change N.val.PosDef ↔ M.val.PosDef
    rw [hv, Unitary.conjStarAlgAut_apply]
    exact Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe
  by_cases hm : M ∈ complexPositiveDefiniteCone
  · have ht : (C T * N.val).trace.re = (T * M.val).trace.re := by
      rw [hv, ← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
        Unitary.coe_star_mul_self, Matrix.one_mul]
    have hd : N.val.det.re = M.val.det.re := by rw [hv, det_conjStarAlgAut]
    rw [complexFourColumnGramTilt, indicator_of_mem (hP.mpr hm), complexFourColumnGramTilt,
      indicator_of_mem hm]
    change Real.exp (-(C T * N.val).trace.re) * N.val.det.re = _
    rw [ht, hd]
  · rw [complexFourColumnGramTilt, indicator_of_notMem (fun h => hm (hP.mp h)),
      complexFourColumnGramTilt, indicator_of_notMem hm]

/-- The normalized candidate's unnormalized tilt integral has the exact fourth inverse determinant. -/
theorem lintegral_complexFourColumnGramTilt_posDef (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (T : ComplexMatrix3) (hT : T.PosDef) :
    (∫⁻ M, ENNReal.ofReal (complexFourColumnGramTilt T M) ∂μ) =
      ((ENNReal.ofReal T.det.re) ^ 4)⁻¹ * ∫⁻ M, ENNReal.ofReal (complexFourColumnGramWeight M) ∂μ := by
  let hHerm := hT.isHermitian
  let U := hHerm.eigenvectorUnitary
  let d (i : Fin 3) := Real.sqrt (hHerm.eigenvalues i)
  let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
  have hd (i : Fin 3) : 0 < d i := Real.sqrt_pos.mpr (hT.eigenvalues_pos i)
  have hD : D * D = Matrix.diagonal (fun i => (hHerm.eigenvalues i : ℂ)) := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hT.eigenvalues_pos i).le]
  have hU : T = (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U) (D * D) := by
    rw [hD]
    exact hHerm.spectral_theorem
  let f (M : Hermitian3) := ENNReal.ofReal (complexFourColumnGramTilt T M)
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    unfold complexFourColumnGramTilt
    exact (by fun_prop : Continuous (fun H : Hermitian3 =>
      Real.exp (-(T * H.val).trace.re) * H.val.det.re)).measurable.indicator
      measurableSet_complexPositiveDefiniteCone
  have hp := measurePreserving_hermitianUnitaryConjugate μ U
  have hInv : (∫⁻ M, f M ∂μ) = ∫⁻ M, ENNReal.ofReal (complexFourColumnGramTilt (D * D) M) ∂μ := by
    calc
      _ = ∫⁻ M, f M ∂(μ.map (hermitianUnitaryConjugate U)) := by rw [hp.map_eq]
      _ = _ := ?_
    rw [lintegral_map hf hp.measurable]
    apply lintegral_congr
    intro M
    exact congrArg ENNReal.ofReal ((congrArg (fun A => complexFourColumnGramTilt A _) hU).trans
      (complexFourColumnGramTilt_unitary_apply U (D * D) M))
  change (∫⁻ M, f M ∂μ) = _
  rw [hInv]
  have hDiag := lintegral_complexFourColumnGramTilt_diagonal μ d hd
  rw [hDiag]
  have hdet : T.det.re = (d 0 * d 1 * d 2) ^ 2 := by
    rw [hU, det_conjStarAlgAut, Matrix.det_mul]
    have he : D.det = ((d 0 * d 1 * d 2 : ℝ) : ℂ) := by
      dsimp only [D]
      rw [Matrix.det_diagonal]
      simp [Fin.prod_univ_three, mul_assoc]
    rw [he, ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  rw [hdet, ENNReal.ofReal_pow (mul_nonneg (mul_nonneg (hd 0).le (hd 1).le) (hd 2).le), ← pow_mul]

end AlbertSequential.WindowProbability
