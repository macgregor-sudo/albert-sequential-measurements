module

import PaperRobustVectors

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.Robust
open scoped InnerProductSpace

noncomputable section

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i)) (Ω : H) :
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecsM‖^2 =
      evalF (fun w => residualVectorProbability P Ω ((0,true)::w)) (gramTableTerms pairsM) +
      ((gramResidualOccurrences pairsM).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ,robustResidualVector P ζ o.2⟫_ℝ).sum :=
  gram_norm_unconditioned_eq_table_add_residuals P hp Ω vecsM pairsM pairsM_spec pairsM_ok

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i)) (Ω : H) :
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecsS‖^2 =
      evalF (fun w => residualVectorProbability P Ω ((0,true)::w)) (gramTableTerms pairsS) +
      ((gramResidualOccurrences pairsS).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ,robustResidualVector P ζ o.2⟫_ℝ).sum :=
  gram_norm_unconditioned_eq_table_add_residuals P hp Ω vecsS pairsS pairsS_spec pairsS_ok

#print axioms BlockB.atomCornerData_scalarParameters_eq_finiteTetrahedron
#print axioms BlockB.atomCornerResidualTelescope_vectorIdentity
#print axioms gram_norm_unconditioned_eq_table_add_residuals
#print axioms robustResidualVector_square
#print axioms nativeResidualOccurrences_spec
#print axioms maximizerConfig_nativeBucketWeights
#print axioms fixedS_nativeBucketWeights
#print axioms maximizerConfig_rawTableBound
#print axioms fixedS_rawTableBound
#print axioms maximizerConfig_gramTableValue_e3
#print axioms fixedS_gramTableValue_e3
#print axioms maximizerConfig_weightedBucketTotal
#print axioms fixedS_weightedBucketTotal
#print axioms maximizerConfig_gramRows_bucket_example
#print axioms pairsM_paperEntryShape
#print axioms pairsS_paperEntryShape
