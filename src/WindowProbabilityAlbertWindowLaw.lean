/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityAlbertInvariance
public import WindowProbabilityGaussianUnitary
public import WindowProbabilityGaussianRank

/-! The probability comparison for an arbitrary native complex window in
the full octonionic Albert algebra. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped AlbertSequential.WindowProbability Topology Matrix BigOperators

local instance : NormedAddCommGroup ComplexMatrix3 :=
  inferInstanceAs (NormedAddCommGroup (Fin 3 → Fin 3 → ℂ))
local instance : NormedSpace ℝ ComplexMatrix3 :=
  inferInstanceAs (NormedSpace ℝ (Fin 3 → Fin 3 → ℂ))
local instance : CompleteSpace ComplexMatrix3 :=
  inferInstanceAs (CompleteSpace (Fin 3 → Fin 3 → ℂ))
local instance : SecondCountableTopology ComplexMatrix3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℂ))
local instance : BorelSpace ComplexMatrix3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℂ))

private theorem tracePairing_real_conjTranspose_test (H M : ComplexMatrix3)
    (hM : M.IsHermitian) :
    ((H.conjTranspose * M).trace).re = (H * M).trace.re := by
  have h : H.conjTranspose * M = (M * H).conjTranspose := by
    rw [Matrix.conjTranspose_mul, hM.eq]
  rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.trace_mul_comm]

/-- On Hermitian matrices a real continuous linear functional has a Hermitian trace representative. -/
theorem exists_hermitian_test (L : StrongDual ℝ ComplexMatrix3) :
    ∃ H : Hermitian3, ∀ M : ComplexMatrix3, M.IsHermitian → L M = ((H : ComplexMatrix3) * M).trace.re := by
  let a (i j : Fin 3) := L (Matrix.single i j (1 : ℂ))
  let b (i j : Fin 3) := L (Matrix.single i j Complex.I)
  let H₀ : ComplexMatrix3 := fun j i => ⟨a i j, -b i j⟩
  let H : ComplexMatrix3 := (1/2 : ℝ) • (H₀ + H₀.conjTranspose)
  have hH : IsSelfAdjoint H := by
    change H.conjTranspose = H
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
  refine ⟨⟨H, hH⟩, ?_⟩
  intro M hM
  have hdec : M = ∑ i, ∑ j,
      ((M i j).re • Matrix.single i j (1 : ℂ) + (M i j).im • Matrix.single i j Complex.I) := by
    calc
      M = ∑ i, ∑ j, Matrix.single i j (M i j) := Matrix.matrix_eq_sum_single M
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
        simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  have hlin : L M = (H₀ * M).trace.re := by
    calc
      _ = ∑ i, ∑ j, ((M i j).re * a i j + (M i j).im * b i j) := by
        conv_lhs => rw [hdec]
        simp only [map_sum, map_add, map_smul, smul_eq_mul, a, b]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, Complex.mul_re]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (M j i).re * a j i + (M j i).im * b j i =
          a j i * (M j i).re - -b j i * (M j i).im
        ring
  change L M = (H * M).trace.re
  rw [hlin]
  unfold H
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add,
    Complex.real_smul, Complex.re_ofReal_mul, Complex.add_re, tracePairing_real_conjTranspose_test H₀ M hM]
  ring

private theorem exists_gaussian_test_radius (H : ComplexMatrix3) (hH : H.IsHermitian) :
    ∃ ε : ℝ, ε > 0 ∧ ∀ t ∈ Ioo (-ε) ε, ∀ i, t * hH.eigenvalues i < 1 := by
  have hloc (i : Fin 3) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t * hH.eigenvalues i < 1 := by
    have hc : Continuous (fun t : ℝ => t * hH.eigenvalues i) := continuous_id.mul continuous_const
    exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds (by simp : (0 : ℝ) * hH.eigenvalues i ∈ Iio 1))
  have hAll : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ i, t * hH.eigenvalues i < 1 :=
    Filter.eventually_all.mpr hloc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hAll
  refine ⟨ε, hε, fun t ht => hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using ht

private theorem projectedAlbertChartRayMeasure_eq_complexGram (W : ComplexWindow) :
    albertChartRayMeasure.map (projectedMatrix W) =
      (standardComplexGaussianMatrix 4).map
        (fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose) := by
  let gram := fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose
  let μ := albertChartRayMeasure.map (projectedMatrix W)
  let ν := (standardComplexGaussianMatrix 4).map gram
  have hg : Measurable gram := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have hw := measurable_projectedMatrix W
  change μ = ν
  have : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have : IsProbabilityMeasure ν := by unfold ν; infer_instance
  apply measure_eq_of_local_exponential_transforms
  intro L
  obtain ⟨H, hL⟩ := exists_hermitian_test L
  have hHerm : (H : ComplexMatrix3).IsHermitian := H.prop
  let τ := fun M : ComplexMatrix3 => ((H : ComplexMatrix3) * M).trace.re
  have hτ : Measurable τ := by
    dsimp only [τ, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hset : MeasurableSet {M : ComplexMatrix3 | L M = τ M} :=
    measurableSet_eq_fun L.continuous.measurable hτ
  have hμ : ∀ᵐ M ∂μ, L M = τ M := by
    rw [ae_map_iff hw.aemeasurable hset]
    exact Filter.Eventually.of_forall fun X => hL _ (windowProj W X).prop
  have hν : ∀ᵐ M ∂ν, L M = τ M := by
    rw [ae_map_iff hg.aemeasurable hset]
    exact Filter.Eventually.of_forall fun Z => hL _ (Matrix.isHermitian_mul_conjTranspose_self Z)
  obtain ⟨δ, hδ, hsrc⟩ := exists_local_projected_albertChartRayMeasure_transform W H
  obtain ⟨ξ, hξ, hscales⟩ := exists_gaussian_test_radius _ hHerm
  let ε := min δ ξ
  have hd : Ioo (-ε) ε ⊆ Ioo (-δ) δ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have he : Ioo (-ε) ε ⊆ Ioo (-ξ) ξ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hνTransform (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (∫ M, exp (t * τ M) ∂ν) = (∫ M, exp (t * τ M) ∂μ) := by
    have hm : Measurable (fun M => exp (t * τ M)) :=
      continuous_exp.measurable.comp (hτ.const_mul t)
    rw [integral_map hg.aemeasurable hm.aestronglyMeasurable]
    rw [(hsrc t (hd ht)).2]
    exact integral_gaussianMatrix_exp_hermitian_trace 4 (H : ComplexMatrix3) hHerm t (hscales t (he ht))
  refine ⟨ε, lt_min hδ hξ, ?_, ?_, ?_⟩
  · intro t ht
    exact (hsrc t (hd ht)).1.congr
      (hμ.mono fun _ h => congrArg (fun r : ℝ => exp (t * r)) h.symm)
  · intro t ht
    have hi : Integrable (fun M => exp (t * τ M)) ν := by
      apply Integrable.of_integral_ne_zero
      rw [hνTransform t ht]
      exact (integral_exp_pos (hsrc t (hd ht)).1).ne'
    exact hi.congr (hν.mono fun _ h => congrArg (fun r : ℝ => exp (t * r)) h.symm)
  · intro t ht
    change (∫ M, exp (t * L M) ∂μ) = (∫ M, exp (t * L M) ∂ν)
    calc
      _ = ∫ M, exp (t * τ M) ∂μ := integral_congr_ae (hμ.mono fun _ h => by rw [h])
      _ = ∫ M, exp (t * τ M) ∂ν := (hνTransform t ht).symm
      _ = _ := integral_congr_ae (hν.mono fun _ h => by rw [h])

/-- In the full Albert algebra, projecting its unique invariant atom
probability into any complex window gives the exact induced complex
state law with four Gaussian columns. -/
theorem albert_complexWindow_probability_law (W : ComplexWindow) :
    albertChartAtomMeasure.map (projectedMatrix W) = inducedComplexStateLaw 4 := by
  let gram := fun Z : Matrix (Fin 3) (Fin 4) ℂ => Z * Z.conjTranspose
  have hgram : Measurable gram := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have h : albertChartAtomMeasure = albertChartRayMeasure.map normalizeAlbert := by
    unfold albertChartAtomMeasure albertChartRayMeasure
    rw [Measure.map_map measurable_normalizeAlbert measurable_sampleAlbertChartRay]
  rw [h, map_projectedMatrix_normalizeAlbert, projectedAlbertChartRayMeasure_eq_complexGram,
    Measure.map_map measurable_normalizeMatrix hgram]
  rfl

/-- The same probability law holds for every invariant probability
presentation of the native Albert atoms. -/
theorem albert_complexWindow_probability_law_of_invariant (W : ComplexWindow)
    (μ : Measure Albert) [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, IsAtom p)
    (hinv : ∀ (f : Albert ≃ₗ[ℝ] Albert),
      (∀ x y, f (jordanMul x y) = jordanMul (f x) (f y)) →
      f albertUnit = albertUnit → μ.map f = μ) :
    μ.map (projectedMatrix W) = inducedComplexStateLaw 4 := by
  have hinv' (g : NativeAlbertAutomorphism) : μ.map g.linearEquiv = μ :=
    hinv g.linearEquiv g.preserves_product g.preserves_unit
  rw [invariantAlbertAtomMeasure_unique μ albertChartAtomMeasure hμ
    ae_albertChartAtomMeasure_isAtom hinv' map_nativeAutomorphism_albertChartAtomMeasure,
    albert_complexWindow_probability_law]

/-- The exact four-column output probability is carried by the
full-rank stratum of complex density matrices. -/
theorem ae_inducedComplexStateLaw_four_rank :
    ∀ᵐ M ∂inducedComplexStateLaw 4, M.rank = 3 := by
  have hdet (M : ComplexMatrix3) : M.rank = 3 ↔ M.det ≠ 0 := by
    simpa using complexMatrix_rank_eq_card_iff_det_ne_zero M
  have hd : Continuous (fun M : ComplexMatrix3 => M.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  have hset : MeasurableSet {M : ComplexMatrix3 | M.rank = 3} := by
    simp_rw [hdet]
    exact (isClosed_eq hd continuous_const).isOpen_compl.measurableSet
  unfold inducedComplexStateLaw normalizedGramPushforward
  rw [ae_map_iff (measurable_normalizedComplexGram 4).aemeasurable hset]
  simpa using ae_rank_normalizedComplexGram 4

/-- The projected native Albert atom has rank three almost surely for
every native complex window. -/
theorem ae_albert_complexWindow_probability_rank (W : ComplexWindow) :
    ∀ᵐ M ∂(albertChartAtomMeasure.map (projectedMatrix W)), M.rank = 3 := by
  rw [albert_complexWindow_probability_law W]
  exact ae_inducedComplexStateLaw_four_rank

/-- An observable-dependent interval of real exponential moments with positive determinant. -/
theorem exists_gaussian_test_radius_with_pos_det (H : Hermitian3) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (-ε) ε,
      (∀ i, t * (show H.val.IsHermitian from H.property).eigenvalues i < 1) ∧
        0 < (((1 : ComplexMatrix3) - t • H.val).det).re := by
  obtain ⟨δ, hδ, hscales⟩ := exists_gaussian_test_radius H.val H.property
  have hc : Continuous (fun t : ℝ => (((1 : ComplexMatrix3) - t • H.val).det).re) :=
    Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.sub (continuous_id.smul continuous_const)))
  have ht : ∀ᶠ t : ℝ in 𝓝 0, 0 < (((1 : ComplexMatrix3) - t • H.val).det).re :=
    hc.continuousAt.eventually (isOpen_Ioi.mem_nhds (by simp :
      (((1 : ComplexMatrix3) - (0 : ℝ) • H.val).det).re ∈ Ioi 0))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨min δ r, lt_min hδ hr, fun t h => ⟨hscales t ?_, hb ?_⟩⟩
  · exact Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _) h
  · simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using
      (Ioo_subset_Ioo (neg_le_neg (min_le_right δ r)) (min_le_right δ r) h)

/-- The exact unnormalized complex Gram law is independent of the
parametrization of a fixed native complex window carrier. -/
theorem map_projectedMatrix_eq_gram_of_same_carrier (k : ℕ) (μ : Measure Albert) [IsProbabilityMeasure μ]
    (W₀ W : ComplexWindow) (hW : W.toSubalgebra.carrier = W₀.toSubalgebra.carrier)
    (hμ : μ.map (projectedMatrix W₀) = (standardComplexGaussianMatrix k).map
      (fun Z : Matrix (Fin 3) (Fin k) ℂ => Z * Z.conjTranspose)) :
    μ.map (projectedMatrix W) = (standardComplexGaussianMatrix k).map
      (fun Z : Matrix (Fin 3) (Fin k) ℂ => Z * Z.conjTranspose) := by
  let gram := fun Z : Matrix (Fin 3) (Fin k) ℂ => Z * Z.conjTranspose
  let ν := (standardComplexGaussianMatrix k).map gram
  have hg : Measurable gram := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have hWm := measurable_projectedMatrix W
  have hW₀m := measurable_projectedMatrix W₀
  have : IsProbabilityMeasure ν := by unfold ν; infer_instance
  change μ.map (projectedMatrix W) = ν
  apply measure_eq_of_local_exponential_transforms
  intro L
  obtain ⟨H, hL⟩ := exists_hermitian_test L
  have hmem : W.embedding H ∈ W₀.toSubalgebra.carrier := by rw [← hW]; exact ⟨H, rfl⟩
  obtain ⟨T, hT⟩ := hmem
  have ht (t : ℝ) : ((1 : ComplexMatrix3) - t • T.val).det.re =
      ((1 : ComplexMatrix3) - t • H.val).det.re := by
    change (((1 : Hermitian3) - t • T : Hermitian3) : ComplexMatrix3).det.re =
      (((1 : Hermitian3) - t • H : Hermitian3) : ComplexMatrix3).det.re
    rw [← (complexWindow_albertCubicNorm_eq_det W₀ _).1, ← (complexWindow_albertCubicNorm_eq_det W _).1,
      map_sub, map_sub, map_smul, map_smul, W₀.unit, W.unit, hT]
  have hPair (X : Albert) : L (projectedMatrix W X) = (T.val * projectedMatrix W₀ X).trace.re := by
    change L (windowProj W X).val = (T.val * (windowProj W₀ X).val).trace.re
    rw [hL _ (windowProj W X).property, Matrix.trace_mul_comm H.val, windowProj_tracePairing W,
      Matrix.trace_mul_comm T.val, windowProj_tracePairing W₀, hT]
  obtain ⟨δ, hδ, hTestH⟩ := exists_gaussian_test_radius_with_pos_det H
  obtain ⟨r, hr, hTestT⟩ := exists_gaussian_test_radius_with_pos_det T
  let ε := min δ r
  have hδ' : Ioo (-ε) ε ⊆ Ioo (-δ) δ := Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hr' : Ioo (-ε) ε ⊆ Ioo (-r) r := Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hExp (A : Hermitian3) (t : ℝ) : Measurable
      (fun M : ComplexMatrix3 => exp (t * (A.val * M).trace.re)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hHermEq (t : ℝ) : (fun M : ComplexMatrix3 => exp (t * L M)) =ᵐ[ν]
      (fun M : ComplexMatrix3 => exp (t * (H.val * M).trace.re)) := by
    have hF : Measurable (fun M : ComplexMatrix3 => exp (t * L M)) :=
      continuous_exp.measurable.comp (L.continuous.measurable.const_mul t)
    change ∀ᵐ M ∂ν, exp (t * L M) = exp (t * (H.val * M).trace.re)
    rw [ae_map_iff hg.aemeasurable (measurableSet_eq_fun hF (hExp H t))]
    exact Eventually.of_forall fun Z => congrArg (fun y : ℝ => exp (t * y))
      (hL (gram Z) (Matrix.isHermitian_mul_conjTranspose_self Z))
  have hRaw (A : Hermitian3) (t : ℝ) (ha : ∀ i, t * (show A.val.IsHermitian from A.property).eigenvalues i < 1) :
      (∫ M, exp (t * (A.val * M).trace.re) ∂ν) = ((((1 : ComplexMatrix3) - t • A.val).det.re) ^ k)⁻¹ := by
    rw [integral_map hg.aemeasurable (hExp A t).aestronglyMeasurable]
    exact integral_gaussianMatrix_exp_hermitian_trace k A.val A.property t ha
  have hSource (t : ℝ) (ht' : t ∈ Ioo (-ε) ε) :
      (∫ M, exp (t * L M) ∂μ.map (projectedMatrix W)) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ k)⁻¹ := by
    have hF : Measurable (fun M : ComplexMatrix3 => exp (t * L M)) :=
      continuous_exp.measurable.comp (L.continuous.measurable.const_mul t)
    rw [integral_map hWm.aemeasurable hF.aestronglyMeasurable]
    simp_rw [hPair]
    rw [← integral_map hW₀m.aemeasurable (hExp T t).aestronglyMeasurable, hμ]
    exact (hRaw T t (hTestT t (hr' ht')).1).trans (by rw [ht])
  have hTarget (t : ℝ) (ht' : t ∈ Ioo (-ε) ε) :
      (∫ M, exp (t * L M) ∂ν) = ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ k)⁻¹ :=
    (integral_congr_ae (hHermEq t)).trans (hRaw H t (hTestH t (hδ' ht')).1)
  have hNZ (t : ℝ) (ht' : t ∈ Ioo (-ε) ε) :
      ((((1 : ComplexMatrix3) - t • H.val).det.re) ^ k)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero k (hTestH t (hδ' ht')).2.ne')
  exact ⟨ε, lt_min hδ hr,
    fun t h => Integrable.of_integral_ne_zero (by rw [hSource t h]; exact hNZ t h),
    fun t h => Integrable.of_integral_ne_zero (by rw [hTarget t h]; exact hNZ t h),
    fun t h => (hSource t h).trans (hTarget t h).symm⟩

end AlbertSequential.WindowProbability
