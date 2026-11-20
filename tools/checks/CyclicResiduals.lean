module

import PaperResidualCyclic
import BoundedWordEffects
import QuaternionicProjectiveData

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.Robust
open scoped InnerProductSpace

example {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData Letter 𝕜 H) :
    let P := cyclicHilbertProjection M.toAlgebraic
    let Ω := cyclicHilbertVector M.toAlgebraic
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecsM‖ ^ 2 =
      evalF (fun w => M.probability ((0,true) :: w)) (gramTableTerms pairsM) +
      ((gramResidualOccurrences pairsM).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ, robustResidualVector P ζ o.2⟫_ℝ).sum := by
  simpa only [M.toAlgebraic_probability] using
    gram_norm_cyclic_eq_table_add_residuals M.toAlgebraic vecsM pairsM pairsM_spec pairsM_ok

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData Letter Q) :
    let P := cyclicHilbertProjection M.toAlgebraic
    let Ω := cyclicHilbertVector M.toAlgebraic
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecsS‖ ^ 2 =
      evalF (fun w => M.state (M.wordEffect ((0,true) :: w))) (gramTableTerms pairsS) +
      ((gramResidualOccurrences pairsS).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ, robustResidualVector P ζ o.2⟫_ℝ).sum := by
  simpa only [M.toAlgebraic_probability] using
    gram_norm_cyclic_eq_table_add_residuals M.toAlgebraic vecsS pairsS pairsS_spec pairsS_ok

#print axioms gram_norm_cyclic_eq_table_add_residuals
#print axioms robustResidualVector_cyclic_square
#print axioms atomCornerResidualTelescope_cyclicIdentity
