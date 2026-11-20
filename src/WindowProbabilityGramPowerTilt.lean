/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGramTilt
public import WindowProbabilityGramPowerCandidate

/-! Laplace integrals of generic determinant-power Hermitian weights. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator ENNReal MatrixOrder ComplexOrder

/-- Unnormalized density with an arbitrary Hermitian trace tilt. -/
def complexGramPowerTilt (m : ℕ) (T : ComplexMatrix3) (M : Hermitian3) : ℝ :=
  complexPositiveDefiniteCone.indicator
    (fun H => Real.exp (-(T * H.val).trace.re) * H.val.det.re ^ m) M

private theorem measurable_complexGramPowerWeight_ennreal (m : ℕ) :
    Measurable (fun M => ENNReal.ofReal (complexGramPowerWeight m M)) :=
  (measurable_complexGramPowerWeight m).ennreal_ofReal

private theorem complexGramPowerTilt_diagonal_apply (m : ℕ)
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) (M : Hermitian3) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    complexGramPowerTilt m (D * D) M =
      ((d 0 * d 1 * d 2) ^ (2 * m))⁻¹ * complexGramPowerWeight m (hermitianDiagonalCongruence d M) := by
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
    rw [complexGramPowerTilt, indicator_of_mem hm, complexGramPowerWeight,
      indicator_of_mem (hP.mpr hm), ht, hdet, mul_pow (p ^ 2) M.val.det.re m, ← pow_mul]
    have hcancel (t w s : ℝ) (hs : s ≠ 0) : t * w = s⁻¹ * (t * (s * w)) := calc
      _ = t * ((s⁻¹ * s) * w) := by rw [inv_mul_cancel₀ hs, one_mul]
      _ = _ := by ring
    exact hcancel _ _ _ (pow_ne_zero (2 * m) hp.ne')
  · rw [complexGramPowerTilt, indicator_of_notMem hm, complexGramPowerWeight,
      indicator_of_notMem (fun h => hm (hP.mp h)), mul_zero]

/-- The positive diagonal tilt contributes the exact inverse determinant power. -/
theorem lintegral_complexGramPowerTilt_diagonal (m : ℕ)
    (μ : Measure Hermitian3) [μ.IsAddHaarMeasure] (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) :
    let D : ComplexMatrix3 := Matrix.diagonal fun i => (d i : ℂ)
    (∫⁻ M, ENNReal.ofReal (complexGramPowerTilt m (D * D) M) ∂μ) =
      ((ENNReal.ofReal (d 0 * d 1 * d 2)) ^ (2 * (m + 3)))⁻¹ * ∫⁻ M, ENNReal.ofReal (complexGramPowerWeight m M) ∂μ := by
  intro D
  let p := d 0 * d 1 * d 2
  have hp : 0 < p := mul_pos (mul_pos (hd 0) (hd 1)) (hd 2)
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpT : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have : FiniteDimensional ℝ Hermitian3 :=
    FiniteDimensional.of_injective hermitian3Equiv.toLinearMap hermitian3Equiv.injective
  have hC : Measurable (hermitianDiagonalCongruence d) :=
    (hermitianDiagonalCongruence d).continuous_of_finiteDimensional.measurable
  have hrewrite : (∫⁻ M, ENNReal.ofReal (complexGramPowerTilt m (D * D) M) ∂μ) =
      ∫⁻ M, ENNReal.ofReal ((p ^ (2 * m))⁻¹) *
        ENNReal.ofReal (complexGramPowerWeight m (hermitianDiagonalCongruence d M)) ∂μ := by
    apply lintegral_congr
    intro M
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hp.le _))]
    exact congrArg ENNReal.ofReal (complexGramPowerTilt_diagonal_apply m d hd M)
  rw [hrewrite]
  have hMap := lintegral_map (μ := μ) (measurable_complexGramPowerWeight_ennreal m) hC
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hMap,
    map_hermitianDiagonalCongruence_haar μ d hd, lintegral_smul_measure, smul_eq_mul]
  change ENNReal.ofReal ((p ^ (2 * m))⁻¹) * (ENNReal.ofReal ((p ^ 6)⁻¹) *
    (∫⁻ M, ENNReal.ofReal (complexGramPowerWeight m M) ∂μ)) = _
  rw [← mul_assoc, ENNReal.ofReal_inv_of_pos (pow_pos hp (2 * m)), ENNReal.ofReal_inv_of_pos (pow_pos hp 6),
    ENNReal.ofReal_pow hp.le (2 * m), ENNReal.ofReal_pow hp.le 6,
    ← ENNReal.mul_inv (Or.inl (pow_ne_zero (2 * m) hp0)) (Or.inl (ENNReal.pow_ne_top hpT)), ← pow_add]
  rw [show 2 * m + 6 = 2 * (m + 3) by omega]

private theorem complexGramPowerTilt_unitary_apply (m : ℕ)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (T : ComplexMatrix3) (M : Hermitian3) :
    complexGramPowerTilt m (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U T)
        (hermitianUnitaryConjugate U M) = complexGramPowerTilt m T M := by
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
    rw [complexGramPowerTilt, indicator_of_mem (hP.mpr hm), complexGramPowerTilt,
      indicator_of_mem hm]
    change Real.exp (-(C T * N.val).trace.re) * N.val.det.re ^ m = _
    rw [ht, hd]
  · rw [complexGramPowerTilt, indicator_of_notMem (fun h => hm (hP.mp h)),
      complexGramPowerTilt, indicator_of_notMem hm]

/-- The generic Hermitian exponential tilt gives the exact inverse determinant power. -/
theorem lintegral_complexGramPowerTilt_posDef (m : ℕ) (μ : Measure Hermitian3) [μ.IsAddHaarMeasure]
    (T : ComplexMatrix3) (hT : T.PosDef) :
    (∫⁻ M, ENNReal.ofReal (complexGramPowerTilt m T M) ∂μ) =
      ((ENNReal.ofReal T.det.re) ^ (m + 3))⁻¹ * ∫⁻ M, ENNReal.ofReal (complexGramPowerWeight m M) ∂μ := by
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
  let f (M : Hermitian3) := ENNReal.ofReal (complexGramPowerTilt m T M)
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    unfold complexGramPowerTilt
    exact (by fun_prop : Continuous (fun H : Hermitian3 =>
      Real.exp (-(T * H.val).trace.re) * H.val.det.re ^ m)).measurable.indicator
      measurableSet_complexPositiveDefiniteCone
  have hp := measurePreserving_hermitianUnitaryConjugate μ U
  have hInv : (∫⁻ M, f M ∂μ) = ∫⁻ M, ENNReal.ofReal (complexGramPowerTilt m (D * D) M) ∂μ := by
    calc
      _ = ∫⁻ M, f M ∂(μ.map (hermitianUnitaryConjugate U)) := by rw [hp.map_eq]
      _ = _ := ?_
    rw [lintegral_map hf hp.measurable]
    apply lintegral_congr
    intro M
    exact congrArg ENNReal.ofReal ((congrArg (fun A => complexGramPowerTilt m A _) hU).trans
      (complexGramPowerTilt_unitary_apply m U (D * D) M))
  change (∫⁻ M, f M ∂μ) = _
  rw [hInv]
  have hDiag := lintegral_complexGramPowerTilt_diagonal m μ d hd
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
