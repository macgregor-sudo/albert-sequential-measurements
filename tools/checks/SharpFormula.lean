module

import PaperSharpDilationFormula
open AlbertSequential
open scoped Matrix ComplexOrder
noncomputable section
example {d : ℕ} (E : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)
    (hE : IsCompletelyPositiveMatrixMap E) (τ : ComplexMatrix d) (hτ : IsMatrixDensity τ) :
    ∃ (s : FiniteSpectralSupport (matrixMapEffect E)) (F : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d),
      IsCompletelyPositiveMatrixMap F ∧
      (∀ Y, Matrix.trace (F Y) = Matrix.trace Y) ∧
      (∀ Y, F Y = E (s.inverseRoot * Y * s.inverseRoot) +
        Matrix.trace ((1 - s.support) * Y) • τ) ∧
      (∀ X, E X = F (s.root * X * s.root)) :=
  exists_displayed_completelyPositive_channel_factorization E hE τ hτ

example {d : ℕ} {T : Type*} (ρ : ComplexMatrix d) (hρ : IsMatrixDensity ρ)
    (E : T → Bool → ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)
    (hE : ∀ x a, IsCompletelyPositiveMatrixMap (E x a))
    (hTP : ∀ x Y, Matrix.trace (E x true Y + E x false Y) = Matrix.trace Y)
    (hR : HasRealCPBranchKraus ρ E) :
    ∃ s : SharpDilationData d T, IsRealSharpDilation s ∧
      (∀ x, compressFirstBlock (s.projection x) = matrixMapEffect (E x true)) ∧
      (∀ x a Y, s.branch x a (embedFirstBlock Y) = embedFirstBlock (E x a Y)) ∧
      (∀ w, s.wordProbability ρ w =
        (Matrix.trace (w.foldl (fun Y a => E a.1 a.2 Y) ρ)).re) := by
  obtain ⟨r, s, hinit, hK, hs, he, hscene, hword, hrep, hr⟩ :=
    exists_completelyPositive_same_choice_sharpDilation ρ hρ E hE hTP
  exact ⟨s, (hr hR).2, he, hscene, hword⟩

#print axioms exists_displayed_completelyPositive_channel_factorization
#print axioms binaryKrausDilation_channel_action
#print axioms exists_completelyPositive_same_choice_sharpDilation
