module

import WindowProbabilitySpectralPowerSymmetric

open AlbertSequential AlbertSequential.WindowProbability Filter MeasureTheory Set
open scoped ENNReal Matrix

noncomputable section

private def printedWeight (m : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  let c := 1 - p.1 - p.2
  ENNReal.ofReal ((p.1 * p.2 * c) ^ m * ((p.1 - p.2)^2 * (p.1 - c)^2 * (p.2 - c)^2))

private def printedDensity (m : ℕ) (S : Set (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (∫⁻ p in S, printedWeight m p)⁻¹ • (volume.restrict S).withDensity (printedWeight m)

private def closedSimplex : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

example (k : ℕ) : (standardComplexGaussianMatrix k : Measure (Matrix (Fin 3) (Fin k) ℂ)) =
    Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin k => standardComplexGaussian)) := rfl

example (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) :
    normalizedComplexGram k Z = ((Z * Z.conjTranspose).trace)⁻¹ • (Z * Z.conjTranspose) := rfl

example (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) : normalizedGramEigenvaluePair k Z =
    (sortedHermitianSpectrum (normalizedComplexGram_isHermitian k Z) 0,
      sortedHermitianSpectrum (normalizedComplexGram_isHermitian k Z) 1) := rfl

example (k : ℕ) (hk : 3 ≤ k) :
    ∀ᵐ Z ∂standardComplexGaussianMatrix k, (normalizedComplexGram k Z).rank = 3 := by
  simpa only [min_eq_left hk] using ae_rank_normalizedComplexGram k

example (k : ℕ) (hk : 3 ≤ k) :
    (standardComplexGaussianMatrix k).map (normalizedGramEigenvaluePair k) =
      printedDensity (k - 3)
        {p | (0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1) ∧ p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2} := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, (Nat.sub_add_cancel hk).symm⟩
  rw [Nat.add_sub_cancel]
  exact normalizedGramEigenvaluePair_law_eq_density m

example (k : ℕ) (hk : 3 ≤ k) :
    (6 : ℝ≥0∞)⁻¹ • ∑ i : Fin 6,
      ((standardComplexGaussianMatrix k).map (normalizedGramEigenvaluePair k)).map (simplexRelabel i) =
        printedDensity (k - 3) {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} :=
  uniformlyRelabelledGramEigenvalueLaw_eq_density k hk

private theorem orderedMass_pos_lt_top (m : ℕ) :
    0 < (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p) ∧
      (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p) < ∞ := by
  let a := ∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p
  have hProb : IsProbabilityMeasure (normalizedPowerOrderedSimplexDensity m) := by
    rw [← normalizedGramEigenvaluePair_law_eq_density]
    exact (Measure.isProbabilityMeasure_map_iff (aemeasurable_normalizedGramEigenvaluePair m)).mpr inferInstance
  have hNorm : (normalizedPowerOrderedSimplexDensity m) univ = 1 := measure_univ
  unfold normalizedPowerOrderedSimplexDensity at hNorm
  rw [smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul] at hNorm
  change a⁻¹ * a = 1 at hNorm
  change 0 < a ∧ a < ∞
  constructor
  · apply pos_iff_ne_zero.mpr
    intro ha
    simp [ha] at hNorm
  · apply lt_top_iff_ne_top.mpr
    intro ha
    simp [ha] at hNorm

example (m : ℕ) : 0 < (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p) ∧
    (∫⁻ p in positiveEigenvalueSimplex, powerSimplexWeight m p) < ∞ := by
  rw [powerSimplexWeight_mass]
  have h := orderedMass_pos_lt_top m
  change 0 < (6 : ℝ≥0∞) * (∫⁻ p in orderedEigenvalueSimplex, powerSimplexWeight m p) ∧ _
  exact ⟨ENNReal.mul_pos (by norm_num) h.1.ne', ENNReal.mul_lt_top (by norm_num) h.2⟩

example (m : ℕ) :
    (normalizedPowerSymmetricSimplexDensity m) positiveEigenvalueSimplexᶜ = 0 := by
  rw [normalizedPowerSymmetricSimplexDensity, smul_apply,
    withDensity_apply _ measurableSet_positiveEigenvalueSimplex.compl,
    Measure.restrict_restrict measurableSet_positiveEigenvalueSimplex.compl,
    compl_inter_self, Measure.restrict_empty, lintegral_zero_measure, smul_zero]

private theorem ae_snd_ne_graph (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.2 ≠ f p.1 := by
  rw [Measure.volume_eq_prod, ae_iff]
  have hs : {p : ℝ × ℝ | ¬ p.2 ≠ f p.1} = {p : ℝ × ℝ | p.2 = f p.1} := by ext p; simp
  rw [hs]
  apply Measure.measure_prod_null_of_ae_null (isClosed_eq continuous_snd (hf.comp continuous_fst)).measurableSet
  filter_upwards with x
  change (volume : Measure ℝ) {f x} = 0
  exact measure_singleton _

private theorem positiveSimplex_ae_closed :
    positiveEigenvalueSimplex =ᵐ[(volume : Measure (ℝ × ℝ))] closedSimplex := by
  have hs := ae_snd_ne_graph (fun _ => 0) continuous_const
  have hd := ae_snd_ne_graph (fun x => 1 - x) (continuous_const.sub continuous_id)
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hf : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    have hs' : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).map MeasurableEquiv.prodComm), p.2 ≠ 0 :=
      hswap.map_eq.symm ▸ hs
    exact ae_of_ae_map hswap.measurable.aemeasurable hs'
  filter_upwards [hf, hs, hd] with p hp hq hr
  change (0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1) ↔ (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1)
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨ha.le, hb.le, hc.le⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨lt_of_le_of_ne ha hp.symm, lt_of_le_of_ne hb hq.symm, lt_of_le_of_ne hc (by
      intro h
      apply hr
      linarith)⟩

example (k : ℕ) (hk : 3 ≤ k) : uniformlyRelabelledGramEigenvalueLaw k = printedDensity (k - 3) closedSimplex := by
  rw [uniformlyRelabelledGramEigenvalueLaw_eq_density k hk]
  change printedDensity (k - 3) positiveEigenvalueSimplex = _
  unfold printedDensity
  rw [Measure.restrict_congr_set positiveSimplex_ae_closed]

example : uniformlyRelabelledGramEigenvalueLaw 3 = printedDensity 0 closedSimplex := by
  rw [uniformlyRelabelledGramEigenvalueLaw_eq_density 3 (by decide)]
  change printedDensity 0 positiveEigenvalueSimplex = _
  unfold printedDensity
  rw [Measure.restrict_congr_set positiveSimplex_ae_closed]

example (p : ℝ × ℝ) : printedWeight 0 p =
    ENNReal.ofReal ((p.1 - p.2)^2 * (p.1 - (1 - p.1 - p.2))^2 * (p.2 - (1 - p.1 - p.2))^2) := by
  simp [printedWeight]

example (M : Hermitian3) : gramPowerDetRatio 0 M = ENNReal.ofReal ((M.val.det.re)⁻¹) := by
  simp [gramPowerDetRatio, one_div]

example (M : Hermitian3) (h : 0 < M.val.det.re) :
    gramPowerDetRatio 2 M = ENNReal.ofReal M.val.det.re := by
  rw [gramPowerDetRatio, pow_two, mul_div_cancel_right₀ _ h.ne']

example (m : ℕ) : rawPowerHermitianGramLaw m ≪ rawFourColumnHermitianGramLaw :=
  rawPowerHermitianGramLaw_absolutelyContinuous_four m

#print axioms gaussianGram_add_three_eq_powerDensity
#print axioms rawPowerHermitianGramLaw_reweight_four
#print axioms rawPowerHermitianGramLaw_absolutelyContinuous_four
#print axioms lintegral_rawPowerSpectrum_eq_weight
#print axioms lintegral_traceNormalizedPowerSpectrum_eq_weight
#print axioms normalizedGramEigenvaluePair_law_eq_density
#print axioms uniformlyRelabelledGramEigenvalueLaw_eq_density
#print axioms orderedMass_pos_lt_top
#print axioms positiveSimplex_ae_closed
