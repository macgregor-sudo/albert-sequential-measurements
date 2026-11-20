module

import PartnerVariancePhysical

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.MatchingModels

example {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (h : HasPrintedGram W τ) :
    W.form (printedPhi W) (printedPhi W) = printedPhiAffine τ - 56 *
      (4 * (τ.om 1 + τ.om 2 + τ.om 3)^2 -
        8 * ((τ.om 1)^2 + (τ.om 2)^2 + (τ.om 3)^2)) :=
  (printedPhi_form W h).trans (printedPhi_variance_decomposition τ)

set_option maxHeartbeats 1000000 in
example (s : Bool) : ∃ h : 0 < (horizonMVarianceModel s).probability [(0, true)],
    let W := WalkForm.ofAlgebraic (horizonMVarianceModel s) h
    W.form (printedPhi W) (printedPhi W) -
      printedPhiValue (nativeTraceData maximizerConfig) = 896 / 729 := by
  obtain ⟨h, hpart⟩ := horizonMVarianceModel_printedPhi s
  refine ⟨h, ?_⟩
  dsimp only at hpart ⊢
  rw [hpart, printedPhiValue_maximizer]
  norm_num

#print axioms printedKappa_pairing
#print axioms printedKappa_HC
#print axioms printedPhi_form
#print axioms printedPhi_variance_decomposition
#print axioms printedPhiAffine_omegas
#print axioms printedPhiValue_maximizer
#print axioms printedPhiValue_M_partner
#print axioms horizonMVarianceModel_matches
#print axioms horizonMVarianceModel_printedPhi
