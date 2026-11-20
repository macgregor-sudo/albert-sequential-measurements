/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGaussian
public import WindowProbabilityPiDensity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Unitary invariance of a full complex Gaussian column. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory MeasureTheory.Measure Real Set WithLp
open scoped ENNReal BigOperators Matrix

private theorem integrable_complexGaussian_density :
    Integrable (fun z : ℂ => π⁻¹ * exp (-Complex.normSq z)) := by
  apply Integrable.of_integral_ne_zero
  simp_rw [← Complex.sq_norm, ← Real.rpow_two, integral_const_mul]
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 0) (b := 1) (by norm_num) (by norm_num) zero_lt_one
  have h' : (∫ z : ℂ, exp (-‖z‖ ^ (2 : ℝ))) = π := by
    simpa [Real.Gamma_one, show (2 : ℝ) / 2 = 1 by norm_num,
      show 2 * π / 2 = π by ring] using h
  rw [h']
  positivity

/-- The independent complex Gaussian column has exactly the radial
Euclidean density with respect to the coordinate Lebesgue measure. -/
theorem complexGaussianColumn_eq_withDensity (ι : Type*) [Fintype ι] :
    (Measure.pi fun _ : ι => standardComplexGaussian) =
      volume.withDensity (fun v : ι → ℂ =>
        ENNReal.ofReal (π⁻¹ ^ Fintype.card ι * exp (-∑ i, Complex.normSq (v i)))) := by
  simp_rw [standardComplexGaussian_eq_withDensity]
  rw [measure_pi_withDensity_ofReal volume _ integrable_complexGaussian_density (fun _ => by positivity)]
  change volume.withDensity _ = volume.withDensity _
  apply congrArg (fun f : (ι → ℂ) → ℝ≥0∞ => volume.withDensity f)
  funext v
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← exp_sum, Finset.sum_neg_distrib]

private theorem volume_preserving_unitaryMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    MeasurePreserving (fun v : ι → ℂ => (U : Matrix ι ι ℂ).mulVec v) := by
  let E := EuclideanSpace ℂ ι
  let e : (ι → ℂ) ≃L[ℝ] E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).symm
  let ue : E ≃ₗᵢ[ℂ] E := Unitary.linearIsometryEquiv
    (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))) U)
  let ur : E ≃ₗᵢ[ℝ] E := ⟨ue.toLinearEquiv.restrictScalars ℝ, ue.norm_map⟩
  let V : Measure E := (volume : Measure (ι → ℂ)).map e
  have : IsAddHaarMeasure V := e.isAddHaarMeasure_map _
  have hU : MeasurePreserving ur volume volume := ur.measurePreserving
  have hre : (V.map ur) = V := by
    rw [isAddLeftInvariant_eq_smul V (volume : Measure E), Measure.map_smul _ hU.aemeasurable, hU.map_eq]
  let f := fun v : ι → ℂ => (U : Matrix ι ι ℂ).mulVec v
  have hfeq : e ∘ f = ur ∘ e := by
    funext v
    change (toLp 2 ((U : Matrix ι ι ℂ).mulVec v) : E) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (U : Matrix ι ι ℂ) (toLp 2 v)
    rw [Matrix.toEuclideanCLM_toLp]
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun v : ι → ℂ => ∑ j, (U : Matrix ι ι ℂ) i j * v j)
    fun_prop
  refine ⟨hf, ?_⟩
  apply e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_injective
  change ((volume : Measure (ι → ℂ)).map f).map e = (volume : Measure (ι → ℂ)).map e
  rw [Measure.map_map e.continuous.measurable hf, hfeq,
    ← Measure.map_map hU.measurable e.continuous.measurable]
  exact hre

/-- Multiplying a standard complex Gaussian column by a unitary matrix
preserves its law. -/
theorem measurePreserving_standardComplexGaussianColumn_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    MeasurePreserving (fun v : ι → ℂ => (U : Matrix ι ι ℂ).mulVec v)
      (Measure.pi fun _ : ι => standardComplexGaussian)
      (Measure.pi fun _ : ι => standardComplexGaussian) := by
  let f := fun v : ι → ℂ => (U : Matrix ι ι ℂ).mulVec v
  let g := fun v : ι → ℂ => ENNReal.ofReal (π⁻¹ ^ Fintype.card ι * exp (-∑ i, Complex.normSq (v i)))
  have hf := volume_preserving_unitaryMulVec U
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hn (v : ι → ℂ) : ∑ i, Complex.normSq (f v i) = ∑ i, Complex.normSq (v i) := by
    let u := Unitary.linearIsometryEquiv
      (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))) U)
    have h := u.norm_map (toLp 2 v)
    change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (U : Matrix ι ι ℂ) (toLp 2 v)‖ = ‖(toLp 2 v : EuclideanSpace ℂ ι)‖ at h
    rw [Matrix.toEuclideanCLM_toLp] at h
    have hsq (w : ι → ℂ) : ‖(toLp 2 w : EuclideanSpace ℂ ι)‖ ^ (2 : ℕ) =
        ∑ i, Complex.normSq (w i) := by
      simpa only [Complex.sq_norm] using (EuclideanSpace.norm_sq_eq (toLp 2 w : EuclideanSpace ℂ ι))
    exact (hsq (f v)).symm.trans ((congrArg (fun r : ℝ => r ^ (2 : ℕ)) h).trans (hsq v))
  refine ⟨hf.measurable, ?_⟩
  rw [complexGaussianColumn_eq_withDensity]
  change (volume.withDensity g).map f = volume.withDensity g
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply g (hf.measurable hs),
    withDensity_apply g hs]
  have he (v : ι → ℂ) : g (f v) = g v := by dsimp only [g]; rw [hn v]
  calc
    _ = ∫⁻ v in f ⁻¹' s, g (f v) ∂volume :=
      setLIntegral_congr_fun (hf.measurable hs) (fun v _ => (he v).symm)
    _ = _ := by
      rw [← setLIntegral_map hs hg hf.measurable, hf.map_eq]

private def transposeEntriesMeasurableEquiv (I J : Type*) [Fintype I] [Fintype J] :
    (I → J → ℂ) ≃ᵐ (J → I → ℂ) where
  toFun z j i := z i j
  invFun z i j := z j i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.mpr fun j =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply j).comp (measurable_pi_apply i)
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    measurable_pi_iff.mpr fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)

private theorem measurePreserving_transposeGaussianEntries (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (transposeEntriesMeasurableEquiv I J)
      (Measure.pi fun _ : I => Measure.pi fun _ : J => standardComplexGaussian)
      (Measure.pi fun _ : J => Measure.pi fun _ : I => standardComplexGaussian) := by
  let e := transposeEntriesMeasurableEquiv I J
  refine ⟨e.measurable, ?_⟩
  have hf : Measurable (fun z : J → I → ℂ => fun p : J × I => z p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hEmb : MeasurableEmbedding (fun z : J → I → ℂ => fun p : J × I => z p.1 p.2) := by
    let u : (J → I → ℂ) ≃ᵐ (J × I → ℂ) :=
      { toFun := fun z p => z p.1 p.2
        invFun := fun z j i => z (j, i)
        left_inv := fun _ => rfl
        right_inv := fun z => funext fun ⟨_, _⟩ => rfl
        measurable_toFun := hf
        measurable_invFun := measurable_pi_iff.mpr fun j =>
          measurable_pi_iff.mpr fun i => measurable_pi_apply (j, i) }
    exact u.measurableEmbedding
  apply hEmb.map_injective
  rw [Measure.map_map hf e.measurable]
  have hL : (Measure.pi fun _ : I => Measure.pi fun _ : J => standardComplexGaussian).map
      ((fun z : J → I → ℂ => fun p : J × I => z p.1 p.2) ∘ e) =
      Measure.pi fun _ : J × I => standardComplexGaussian := by
    refine (Measure.pi_eq (μ := fun _ : J × I => standardComplexGaussian) (fun q hq => ?_)).symm
    rw [Measure.map_apply (hf.comp e.measurable) (MeasurableSet.univ_pi hq)]
    have hpre : ((fun z : J → I → ℂ => fun p : J × I => z p.1 p.2) ∘ e) ⁻¹' pi univ q =
        pi univ (fun i : I => pi univ fun j : J => q (j,i)) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      change (∀ p : J × I, z p.2 p.1 ∈ q p) ↔ ∀ i j, z i j ∈ q (j, i)
      exact ⟨fun h i j => h (j, i), fun h p => h p.2 p.1⟩
    rw [hpre, Measure.pi_pi, ← Finset.univ_product_univ, Finset.prod_product]
    simp_rw [Measure.pi_pi]
    exact Finset.prod_comm
  rw [hL]
  refine Measure.pi_eq (μ := fun _ : J × I => standardComplexGaussian) (fun q hq => ?_)
  rw [Measure.map_apply hf (MeasurableSet.univ_pi hq)]
  have hpre : (fun z : J → I → ℂ => fun p : J × I => z p.1 p.2) ⁻¹' pi univ q =
      pi univ (fun j : J => pi univ fun i : I => q (j,i)) := by ext z; simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi, ← Finset.univ_product_univ, Finset.prod_product]
  simp_rw [Measure.pi_pi]

/-- Applying a fixed unitary to every column preserves the entire matrix ensemble. -/
theorem measurePreserving_standardComplexGaussianMatrix_unitary (k : ℕ)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    MeasurePreserving (fun Z : Matrix (Fin 3) (Fin k) ℂ => (U : ComplexMatrix 3) * Z)
      (standardComplexGaussianMatrix k) (standardComplexGaussianMatrix k) := by
  let e := transposeEntriesMeasurableEquiv (Fin 3) (Fin k)
  have he := measurePreserving_transposeGaussianEntries (Fin 3) (Fin k)
  have hcol := measurePreserving_pi
    (fun _ : Fin k => Measure.pi fun _ : Fin 3 => standardComplexGaussian)
    (fun _ : Fin k => Measure.pi fun _ : Fin 3 => standardComplexGaussian)
    (fun _ => measurePreserving_standardComplexGaussianColumn_unitary U)
  exact ((he.symm e).comp hcol).comp he

/-- The unnormalized complex Gaussian Gram law has its determinant
transform for any Hermitian test matrix and any positive spectral scales. -/
theorem integral_gaussianMatrix_exp_hermitian_trace (k : ℕ) (H : ComplexMatrix 3)
    (hH : H.IsHermitian) (t : ℝ) (ht : ∀ i, t * hH.eigenvalues i < 1) :
    (∫ Z, exp (t * (H * (Z * Z.conjTranspose)).trace.re)
      ∂standardComplexGaussianMatrix k) =
      ((((1 : ComplexMatrix 3) - t • H).det.re)^k)⁻¹ := by
  let U := hH.eigenvectorUnitary
  let eigenvalue := hH.eigenvalues
  let D : ComplexMatrix 3 := Matrix.diagonal fun i => (eigenvalue i : ℂ)
  let a := fun i => -(t * eigenvalue i)
  have ha (i : Fin 3) : -1 < a i := neg_lt_neg (ht i)
  have hUD : H = Unitary.conjStarAlgAut ℂ _ U D := hH.spectral_theorem
  have hdiag (Z : Matrix (Fin 3) (Fin k) ℂ) :
      (D * (Z * Z.conjTranspose)).trace.re =
        ∑ i, eigenvalue i * ∑ j, Complex.normSq (Z i j) := by
    simp only [D, Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.diagonal_mul,
      Complex.re_ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  have hm (Z : Matrix (Fin 3) (Fin k) ℂ) :
      (H * (((U : ComplexMatrix 3) * Z) * ((U : ComplexMatrix 3) * Z).conjTranspose)).trace.re =
        (D * (Z * Z.conjTranspose)).trace.re := by
    have hM : H * (((U : ComplexMatrix 3) * Z) * ((U : ComplexMatrix 3) * Z).conjTranspose) =
        ((U : ComplexMatrix 3) * (D * (Z * Z.conjTranspose))) * star (U : ComplexMatrix 3) := by
      have hUU : star (U : ComplexMatrix 3) * (U : ComplexMatrix 3) = 1 := by
        simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self U
      rw [hUD, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose] at hUU ⊢
      rw [← Matrix.mul_assoc ((U : ComplexMatrix 3).conjTranspose) (U : ComplexMatrix 3), hUU,
        Matrix.one_mul]
    rw [hM, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  let f (Z : Matrix (Fin 3) (Fin k) ℂ) := exp (t * (H * (Z * Z.conjTranspose)).trace.re)
  have hf : Measurable f := by
    dsimp only [f, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  let μ := standardComplexGaussianMatrix k
  have hu := measurePreserving_standardComplexGaussianMatrix_unitary k U
  change (∫ Z, f Z ∂μ) = _
  calc
    _ = ∫ Z, f ((U : ComplexMatrix 3) * Z) ∂μ := by
      have he : μ.map (fun Z => (U : ComplexMatrix 3) * Z) = μ := hu.map_eq
      calc
        _ = ∫ Z, f Z ∂(μ.map (fun Z => (U : ComplexMatrix 3) * Z)) := by rw [he]
        _ = _ := integral_map hu.aemeasurable hf.aestronglyMeasurable
    _ = ∏ i, ((1 + a i)⁻¹)^k := by
      rw [← integral_gaussianMatrix_exp_weighted_normSq k a ha]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun Z => ?_
      dsimp only [f]
      rw [hm, hdiag, ← Finset.sum_neg_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      ring
    _ = _ := by
      have hD : (1 : ComplexMatrix 3) - t • D = Matrix.diagonal (fun i => ((1 - t * eigenvalue i : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [D, Complex.real_smul]
        · simp [D, hij]
      have hdenom : ((1 : ComplexMatrix 3) - t • H).det.re = ∏ i, (1 + a i) := by
        have hU : (U : ComplexMatrix 3).det * (star (U : ComplexMatrix 3)).det = 1 := by
          rw [← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one]
        let C := Unitary.conjStarAlgAut ℂ (ComplexMatrix 3) U
        have hsmul (M : ComplexMatrix 3) : t • M = (t : ℂ) • M := by
          ext i j
          simp [Complex.real_smul]
        have he : 1 - t • H = C (1 - t • D) := by
          rw [map_sub, map_one, hsmul D, map_smul, ← hUD, hsmul H]
        rw [he, hD, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
        rw [mul_right_comm, hU, one_mul, ← Complex.ofReal_prod, Complex.ofReal_re]
        simp only [a, sub_eq_add_neg]
      rw [hdenom, ← Finset.prod_pow]
      simp_rw [inv_pow, Finset.prod_inv_distrib]

end AlbertSequential.WindowProbability
