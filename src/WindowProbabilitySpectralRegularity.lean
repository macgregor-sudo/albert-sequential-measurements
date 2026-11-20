/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGaussianRank
public import WindowProbabilitySpectralLinearization
public import Mathlib.Analysis.Matrix.Spectrum

/-! The cubic discriminant and the simple spectrum stratum of a complex Gram sample. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Polynomial ProbabilityTheory Set
open scoped Matrix NNReal

/-- The cubic discriminant from the trace, second trace and determinant.
The explicit half permits evaluation in a polynomial ring as well as `ℂ`. -/
def cubicMatrixDiscriminant {R : Type*} [CommRing R] (half : R) (M : Matrix (Fin 3) (Fin 3) R) : R :=
  let a := M.trace
  let b := half * (a ^ 2 - (M * M).trace)
  let c := M.det
  a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c

theorem map_cubicMatrixDiscriminant {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (half : R) (M : Matrix (Fin 3) (Fin 3) R) :
    f (cubicMatrixDiscriminant half M) = cubicMatrixDiscriminant (f half) (M.map f) := by
  have ht (N : Matrix (Fin 3) (Fin 3) R) : f N.trace = (N.map f).trace := by
    simp [Matrix.trace, Matrix.diag]
  simp only [cubicMatrixDiscriminant, map_add, map_sub, map_mul, map_pow, map_ofNat,
    RingHom.map_det, ht, RingHom.mapMatrix_apply]
  rw [Matrix.map_mul]

/-- Each nonzero scalar matrix rescaling preserves the simple spectrum stratum. -/
theorem cubicMatrixDiscriminant_smul (r : ℂ) (M : ComplexMatrix3) :
    cubicMatrixDiscriminant (1 / 2 : ℂ) (r • M) = r ^ 6 * cubicMatrixDiscriminant (1 / 2 : ℂ) M := by
  simp only [cubicMatrixDiscriminant, Matrix.trace_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_eq_mul, Matrix.det_smul, Fintype.card_fin, smul_smul]
  ring

/-- The discriminant of a three-by-three Hermitian matrix is the product
of its three squared eigenvalue gaps. -/
theorem cubicMatrixDiscriminant_eq_eigenvalue_gaps (M : ComplexMatrix3) (hM : M.IsHermitian) :
    cubicMatrixDiscriminant (1 / 2 : ℂ) M =
      (((hM.eigenvalues 0 - hM.eigenvalues 1) ^ 2 * (hM.eigenvalues 0 - hM.eigenvalues 2) ^ 2 *
        (hM.eigenvalues 1 - hM.eigenvalues 2) ^ 2 : ℝ) : ℂ) := by
  let U := hM.eigenvectorUnitary
  let D := Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)
  let A : ComplexMatrix3 := U.val
  have h : M = A * D * star A := hM.spectral_theorem
  have hu : star A * A = 1 := Unitary.coe_star_mul_self U
  have hDet : (star A).det * A.det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hA : M.trace = D.trace := by rw [h, Matrix.trace_mul_cycle, hu, one_mul]
  have hB : (M * M).trace = (D * D).trace := by
    have he : M * M = A * (D * D) * star A := by
      rw [h]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star A) A, hu, one_mul]
    rw [he, Matrix.trace_mul_cycle, hu, one_mul]
  have hC : M.det = D.det := by
    rw [h, Matrix.det_mul, Matrix.det_mul]
    calc
      A.det * D.det * (star A).det = ((star A).det * A.det) * D.det := by ring
      _ = D.det := by rw [hDet, one_mul]
  rw [cubicMatrixDiscriminant, hA, hB, hC]
  simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.det_diagonal,
    Fin.sum_univ_three, Fin.prod_univ_three, ← Complex.ofReal_mul]
  push_cast
  ring

theorem continuous_cubicMatrixDiscriminant : Continuous (cubicMatrixDiscriminant (1 / 2 : ℂ) : ComplexMatrix3 → ℂ) := by
  have ht : Continuous (fun M : ComplexMatrix3 => M.trace) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hs : Continuous (fun M : ComplexMatrix3 => (M * M).trace) :=
    ht.comp (continuous_id.matrix_mul continuous_id)
  have hd : Continuous (fun M : ComplexMatrix3 => M.det) := continuous_id.matrix_det
  unfold cubicMatrixDiscriminant
  fun_prop

private abbrev SpectralInputIndex := Fin 3 × (Fin 4 × Fin 2)

private def exactRealCoordinateGaussian : Measure ℂ :=
  (gaussianReal 0 (1 / 2)).map Complex.ofReal

private instance : IsProbabilityMeasure exactRealCoordinateGaussian := by
  unfold exactRealCoordinateGaussian
  infer_instance

private instance : NullSingletonClass exactRealCoordinateGaussian := by
  constructor
  intro z
  unfold exactRealCoordinateGaussian
  rw [Measure.map_apply Complex.continuous_ofReal.measurable (measurableSet_singleton _)]
  by_cases h : ∃ a : ℝ, (a : ℂ) = z
  · obtain ⟨a, rfl⟩ := h
    have he : Complex.ofReal ⁻¹' {(a : ℂ)} = {a} := by ext x; simp
    rw [he, gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
    simp
  · have he : Complex.ofReal ⁻¹' {z} = ∅ := by ext x; simpa using fun hx => h ⟨x, hx⟩
    simp [he]

private theorem ae_exactRealCoordinateGaussian_im_zero : ∀ᵐ z ∂exactRealCoordinateGaussian, z.im = 0 := by
  unfold exactRealCoordinateGaussian
  rw [ae_map_iff Complex.continuous_ofReal.measurable.aemeasurable
    (measurableSet_eq_fun Complex.continuous_im.measurable measurable_const)]
  simp

private theorem measurePreserving_combineSpectralCoordinates :
    MeasurePreserving (fun w : Fin 2 → ℂ => w 0 + Complex.I * w 1)
      (Measure.pi fun _ : Fin 2 => exactRealCoordinateGaussian) standardComplexGaussian := by
  let f := fun p : ℂ × ℂ => p.1 + Complex.I * p.2
  have hf : Measurable f := by unfold f; fun_prop
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℂ)
  have he := measurePreserving_piFinTwo (fun _ : Fin 2 => exactRealCoordinateGaussian)
  have h : MeasurePreserving f (exactRealCoordinateGaussian.prod exactRealCoordinateGaussian)
      standardComplexGaussian := by
    refine ⟨hf, ?_⟩
    unfold exactRealCoordinateGaussian standardComplexGaussian
    rw [Measure.map_prod_map _ _ Complex.continuous_ofReal.measurable Complex.continuous_ofReal.measurable,
      Measure.map_map hf (Complex.continuous_ofReal.measurable.prodMap Complex.continuous_ofReal.measurable)]
    congr 1
    funext p
    apply Complex.ext <;> simp [f, Prod.map]
  exact h.comp he

private def spectralInputPoly : MvPolynomial SpectralInputIndex ℂ :=
  let X : Matrix (Fin 3) (Fin 4) (MvPolynomial SpectralInputIndex ℂ) := fun i j =>
    MvPolynomial.X (i, j, 0) + MvPolynomial.C Complex.I * MvPolynomial.X (i, j, 1)
  let Y : Matrix (Fin 4) (Fin 3) (MvPolynomial SpectralInputIndex ℂ) := fun j i =>
    MvPolynomial.X (i, j, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (i, j, 1)
  cubicMatrixDiscriminant (MvPolynomial.C (1 / 2 : ℂ)) (X * Y)

private def decodeSpectralInput (w : SpectralInputIndex → ℂ) : Matrix (Fin 3) (Fin 4) ℂ :=
  fun i j => w (i, j, 0) + Complex.I * w (i, j, 1)

private theorem star_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : star z = z := by
  apply Complex.ext <;> simp [hz]

private theorem eval_spectralInputPoly (w : SpectralInputIndex → ℂ) (hw : ∀ i, (w i).im = 0) :
    MvPolynomial.eval w spectralInputPoly =
      cubicMatrixDiscriminant (1 / 2 : ℂ) (decodeSpectralInput w * (decodeSpectralInput w).conjTranspose) := by
  let X : Matrix (Fin 3) (Fin 4) (MvPolynomial SpectralInputIndex ℂ) := fun i j =>
    MvPolynomial.X (i, j, 0) + MvPolynomial.C Complex.I * MvPolynomial.X (i, j, 1)
  let Y : Matrix (Fin 4) (Fin 3) (MvPolynomial SpectralInputIndex ℂ) := fun j i =>
    MvPolynomial.X (i, j, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (i, j, 1)
  let ev := MvPolynomial.eval w
  change ev (cubicMatrixDiscriminant (MvPolynomial.C (1 / 2 : ℂ)) (X * Y)) = _
  rw [map_cubicMatrixDiscriminant, MvPolynomial.eval_C, Matrix.map_mul]
  congr 1
  congr 1
  · ext i j
    change ev _ = decodeSpectralInput w i j
    simp [X, ev, decodeSpectralInput]
  · ext j i
    change ev _ = star (decodeSpectralInput w i j)
    simp [Y, ev, decodeSpectralInput, star_of_im_eq_zero (hw (i, j, 0)),
      star_of_im_eq_zero (hw (i, j, 1)), sub_eq_add_neg]

private theorem spectralInputPoly_ne_zero : spectralInputPoly ≠ 0 := by
  intro hzero
  let w : SpectralInputIndex → ℂ := fun q =>
    if q.2.2 = 0 ∧ q.1.val = q.2.1.val then q.1.val + 1 else 0
  have hw (q : SpectralInputIndex) : (w q).im = 0 := by
    unfold w
    split <;> simp
  have h := eval_spectralInputPoly w hw
  rw [hzero, map_zero] at h
  have hg : decodeSpectralInput w * (decodeSpectralInput w).conjTranspose =
      Matrix.diagonal (![1, 4, 9] : Fin 3 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        decodeSpectralInput, w, Fin.sum_univ_succ, Complex.star_def] <;>
      norm_num [map_ofNat]
  rw [hg, cubicMatrixDiscriminant, Matrix.trace_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Matrix.det_diagonal, Fin.sum_univ_three, Fin.prod_univ_three] at h
  norm_num [Fin.sum_univ_three] at h

/-- The unnormalized four-column sample is almost surely on the
simple-spectrum stratum. -/
theorem ae_cubicMatrixDiscriminant_complexGaussianGram_four_ne_zero :
    ∀ᵐ Z ∂standardComplexGaussianMatrix 4,
      cubicMatrixDiscriminant (1 / 2 : ℂ) (Z * Z.conjTranspose) ≠ 0 := by
  let ν := exactRealCoordinateGaussian
  let μ : Measure (Fin 3 → Fin 4 → Fin 2 → ℂ) :=
    Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin 4 => Measure.pi fun _ : Fin 2 => ν
  let η : Measure (SpectralInputIndex → ℂ) := Measure.pi fun _ => ν
  let flat : (Fin 3 → Fin 4 → Fin 2 → ℂ) → SpectralInputIndex → ℂ :=
    fun q p => q p.1 p.2.1 p.2.2
  let decode : (Fin 3 → Fin 4 → Fin 2 → ℂ) → Matrix (Fin 3) (Fin 4) ℂ :=
    fun q => decodeSpectralInput (flat q)
  have hflat : MeasurePreserving flat μ η := by
    have hpre := measurePreserving_pi
      (fun _ : Fin 3 => Measure.pi fun _ : Fin 4 => Measure.pi fun _ : Fin 2 => ν)
      (fun _ : Fin 3 => Measure.pi fun _ : Fin 4 × Fin 2 => ν)
      (fun _ => measurePreserving_uncurry_product (I := Fin 4) (J := Fin 2) ν)
    exact (measurePreserving_uncurry_product (I := Fin 3) (J := Fin 4 × Fin 2) ν).comp hpre
  have hdecode : MeasurePreserving decode μ (standardComplexGaussianMatrix 4) := by
    exact measurePreserving_pi _ _ fun _ =>
      measurePreserving_pi _ _ fun _ => measurePreserving_combineSpectralCoordinates
  have hP := ae_mvPolynomial_eval_ne_zero ν spectralInputPoly spectralInputPoly_ne_zero
  have hr (i : SpectralInputIndex) : ∀ᵐ w ∂η, (w i).im = 0 := by
    have he := measurePreserving_eval (μ := fun _ : SpectralInputIndex => ν) i
    have h : ∀ᵐ z ∂η.map (Function.eval i), z.im = 0 := by
      rw [he.map_eq]
      exact ae_exactRealCoordinateGaussian_im_zero
    exact ae_of_ae_map he.measurable.aemeasurable h
  have hall : ∀ᵐ w ∂η, ∀ i, (w i).im = 0 := Filter.eventually_all.mpr hr
  have hgood : ∀ᵐ w ∂η, cubicMatrixDiscriminant (1 / 2 : ℂ)
      (decodeSpectralInput w * (decodeSpectralInput w).conjTranspose) ≠ 0 := by
    filter_upwards [hP, hall] with w hp hR
    rwa [← eval_spectralInputPoly w hR]
  have hm : MeasurableSet {Z : Matrix (Fin 3) (Fin 4) ℂ |
      cubicMatrixDiscriminant (1 / 2 : ℂ) (Z * Z.conjTranspose) ≠ 0} :=
    (isClosed_eq (continuous_cubicMatrixDiscriminant.comp
      (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)) continuous_const).isOpen_compl.measurableSet
  rw [← hdecode.map_eq, ae_map_iff hdecode.measurable.aemeasurable hm]
  exact ae_of_ae_map hflat.measurable.aemeasurable (hflat.map_eq.symm ▸ hgood)

/-- Trace normalization preserves Hermitian symmetry of every Gram matrix. -/
theorem normalizedComplexGram_isHermitian (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) :
    (normalizedComplexGram k Z).IsHermitian := by
  let M := Z * Z.conjTranspose
  have hM : M.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self Z
  have ht : star M.trace = M.trace := by rw [← Matrix.trace_conjTranspose, hM.eq]
  change ((M.trace)⁻¹ • M).conjTranspose = (M.trace)⁻¹ • M
  rw [Matrix.conjTranspose_smul, star_inv₀, ht, hM.eq]

/-- The normalized four-column complex matrix law is supported on the
Hermitian stratum with three distinct eigenvalues up to a null set. -/
theorem ae_inducedComplexStateLaw_four_distinct_eigenvalues :
    ∀ᵐ M ∂inducedComplexStateLaw 4, ∃ hM : M.IsHermitian, Function.Injective hM.eigenvalues := by
  have hmeas : MeasurableSet {M : ComplexMatrix3 |
      M.IsHermitian ∧ cubicMatrixDiscriminant (1 / 2 : ℂ) M ≠ 0} := by
    exact (isClosed_eq (continuous_id.matrix_conjTranspose : Continuous (fun M : ComplexMatrix3 => M.conjTranspose))
      continuous_id).measurableSet.inter (isClosed_eq continuous_cubicMatrixDiscriminant
        continuous_const).isOpen_compl.measurableSet
  have h : ∀ᵐ M ∂inducedComplexStateLaw 4,
      M.IsHermitian ∧ cubicMatrixDiscriminant (1 / 2 : ℂ) M ≠ 0 := by
    unfold inducedComplexStateLaw normalizedGramPushforward
    rw [ae_map_iff (measurable_normalizedComplexGram 4).aemeasurable hmeas]
    filter_upwards [ae_cubicMatrixDiscriminant_complexGaussianGram_four_ne_zero,
      ae_gaussianGram_trace_ne_zero 4 (by decide)] with Z hZ ht
    refine ⟨normalizedComplexGram_isHermitian 4 Z, ?_⟩
    unfold normalizedComplexGram
    rw [cubicMatrixDiscriminant_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hZ
  filter_upwards [h] with M hM
  obtain ⟨hM, hd⟩ := hM
  rw [cubicMatrixDiscriminant_eq_eigenvalue_gaps M hM] at hd
  have e01 : hM.eigenvalues 0 ≠ hM.eigenvalues 1 := fun hh => hd (by simp [hh])
  have e02 : hM.eigenvalues 0 ≠ hM.eigenvalues 2 := fun hh => hd (by simp [hh])
  have e12 : hM.eigenvalues 1 ≠ hM.eigenvalues 2 := fun hh => hd (by simp [hh])
  refine ⟨hM, ?_⟩
  intro i j he
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (e01 he).elim | exact (e01 he.symm).elim |
      exact (e02 he).elim | exact (e02 he.symm).elim | exact (e12 he).elim | exact (e12 he.symm).elim

end AlbertSequential.WindowProbability
