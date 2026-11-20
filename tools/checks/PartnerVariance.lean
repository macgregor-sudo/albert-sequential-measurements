module

import PartnerVarianceTraceBinding

open AlbertSequential
open AlbertSequential.LengthSeven
open AlbertSequential.MatchingModels

noncomputable section

example {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (hτ : HasPrintedGram W τ) :
    let φ := (4 : ℝ) • printedKappa W .corner + (10 : ℝ) • printedKappa W .ret -
      (9 : ℝ) • printedKappa W .head
    W.form φ φ = printedPhiAffine τ - 56 * (4 * (τ.om 1 + τ.om 2 + τ.om 3)^2 -
      8 * ((τ.om 1)^2 + (τ.om 2)^2 + (τ.om 3)^2)) := by
  change W.form (printedPhi W) (printedPhi W) = _
  rw [printedPhi_form W hτ, printedPhi_variance_decomposition]

example (τ : TraceData) (x y : Letter → ℝ) :
    printedPhiAffine (τ.withOmegas (fun i => (x i + y i) / 2)) =
      (printedPhiAffine (τ.withOmegas x) + printedPhiAffine (τ.withOmegas y)) / 2 := by
  have h := printedPhiAffine_omegas τ x y (1 / 2 : ℝ)
  have hmid : (fun i => (x i + y i) / 2) =
      (fun i => (1 / 2 : ℝ) * x i + (1 - 1 / 2) * y i) := by
    funext i
    ring
  rw [hmid, h]
  ring

example {V : Type*} [AddCommGroup V] [Module ℝ V] (W U : WalkForm V) (s : Bool)
    (hM : HasPrintedGram W (nativeTraceData maximizerConfig))
    (hP : HasPrintedGram U (nativeTraceData (horizonMSector s))) :
    W.form (printedPhi W) (printedPhi W) = -4 / 27 ∧
      U.form (printedPhi U) (printedPhi U) = 788 / 729 := by
  rw [printedPhi_form W hM, printedPhi_form U hP, printedPhiValue_maximizer,
    printedPhiValue_M_partner]
  exact ⟨rfl, rfl⟩

#print axioms printedKappa_pairing
#print axioms printedKappa_HC
#print axioms printedPhi_form
#print axioms printedPhi_variance_decomposition
#print axioms printedPhiAffine_omegas
#print axioms printedPhiValue_maximizer
#print axioms printedPhiValue_M_partner
