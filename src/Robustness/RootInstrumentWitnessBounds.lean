/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.HilbertSquareRootModels
public import Robustness.QuaternionicSquareRootModels
public import Robustness.WitnessTransport

/-! The printed square-root-instrument witness inequality. A witness's model
and target signs remain explicit inputs; no particular certificate or numerical
margin is asserted. Its merged coefficient norm is the canonical one. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential

def hilbertBranchWordProbability {ι 𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra 𝕜 H) →ₗ[ℝ] ℝ)
    (sYes sNo : ι → H →L[𝕜] H) (w : Word ι) : ℝ :=
  psi (hilbertAmplitudeEffect (chronologicalProduct (binaryBranchOperator sYes sNo) w))

def quaternionicBranchWordProbability {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (sYes sNo : ι → S.toOperatorStructure.operatorAlgebra) (w : Word ι) : ℝ :=
  psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
    (chronologicalProduct (binaryBranchOperator sYes sNo) w))

theorem FiniteRealWordFunctional.root_approximation_forces_witness_bound
    {n : ℕ} {Model : Type*} (c : FiniteRealWordFunctional n)
    (probability : Model → Word (Fin n) → ℝ) (L : ℕ) (hL : c.HasHorizon L)
    (target measured : Word (Fin n) → ℝ) {gamma delta tau : ℝ}
    (hgamma : 0 < gamma) (hmodel : ∀ M, 0 ≤ c.evaluate (probability M))
    (htarget : c.evaluate target ≤ -gamma)
    (hobserved : ∀ w ∈ c.coefficients.support, |measured w - target w| ≤ delta)
    (happrox : ∃ M, ∀ w, |measured w - probability M w| ≤
      2 * (w.length : ℝ) * Real.sqrt tau) :
    delta + 2 * (L : ℝ) * Real.sqrt tau ≥ gamma / c.coefficientNorm := by
  obtain ⟨M, hM⟩ := happrox
  obtain ⟨_, w, hw, _⟩ :=
    c.positive_witness_margin_forces_some_word target (probability M) hgamma (hmodel M) htarget
  have hdelta : 0 ≤ delta := (abs_nonneg _).trans (hobserved w hw)
  have hupdate : ∀ v ∈ c.coefficients.support,
      |probability M v - measured v| ≤ (v.length : ℝ) * (2 * Real.sqrt tau) := by
    intro v _
    calc
      _ = |measured v - probability M v| := abs_sub_comm _ _
      _ ≤ 2 * (v.length : ℝ) * Real.sqrt tau := hM v
      _ = (v.length : ℝ) * (2 * Real.sqrt tau) := by ring
  have hb := c.positive_witness_margin_normalized_error L hL target measured (probability M)
    hdelta (mul_nonneg (by norm_num) (Real.sqrt_nonneg tau)) hgamma
    hobserved hupdate (hmodel M) htarget
  calc
    gamma / c.coefficientNorm ≤ delta + (L : ℝ) * (2 * Real.sqrt tau) := hb.2
    _ = delta + 2 * (L : ℝ) * Real.sqrt tau := by ring

theorem complex_square_root_instrument_witness_bound
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℂ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℂ H),
      (operatorValue ℂ H T.val).IsPositive → 0 ≤ psi T)
    (E : Fin n → H →L[ℂ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {gamma delta : ℝ} (hgamma : 0 < gamma)
    (hmodel : ∀ M : HilbertProjectiveData (Fin n) ℂ H, 0 ≤ c.evaluate M.toAlgebraic.probability)
    (htarget : c.evaluate target ≤ -gamma)
    (hobserved : ∀ w ∈ c.coefficients.support,
      |hilbertBranchWordProbability psi (fun i => cfc Real.sqrt (E i))
        (fun i => cfc Real.sqrt (1 - E i)) w - target w| ≤ delta) :
    delta + 2 * (L : ℝ) * Real.sqrt (spectralRoundingError epsilon) ≥
      gamma / c.coefficientNorm := by
  obtain ⟨M, _, hM⟩ := exists_complex_canonical_root_word_model
    psi hnormalized hpositive E hE hEc hdefect hepsilon
  exact c.root_approximation_forces_witness_bound
    (fun N : HilbertProjectiveData (Fin n) ℂ H => N.toAlgebraic.probability)
    L hL target _ hgamma hmodel htarget hobserved ⟨M, hM⟩

theorem real_square_root_instrument_witness_bound
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (psi : selfAdjoint (HilbertOperatorAlgebra ℝ H) →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint (HilbertOperatorAlgebra ℝ H),
      (operatorValue ℝ H T.val).IsPositive → 0 ≤ psi T)
    (E : Fin n → H →L[ℝ] H)
    (hE : ∀ i, (E i).IsPositive) (hEc : ∀ i, (1 - E i).IsPositive)
    {epsilon : ℝ} (hdefect : ∀ i, ‖E i * E i - E i‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {gamma delta : ℝ} (hgamma : 0 < gamma)
    (hmodel : ∀ M : HilbertProjectiveData (Fin n) ℝ H, 0 ≤ c.evaluate M.toAlgebraic.probability)
    (htarget : c.evaluate target ≤ -gamma)
    (hobserved : ∀ w ∈ c.coefficients.support,
      |hilbertBranchWordProbability psi (fun i => realPositiveSquareRoot (E i) (hE i))
        (fun i => realPositiveSquareRoot (1 - E i) (hEc i)) w - target w| ≤ delta) :
    delta + 2 * (L : ℝ) * Real.sqrt (spectralRoundingError epsilon) ≥
      gamma / c.coefficientNorm := by
  obtain ⟨M, _, hM⟩ := exists_real_canonical_root_word_model
    psi hnormalized hpositive E hE hEc hdefect hepsilon
  exact c.root_approximation_forces_witness_bound
    (fun N : HilbertProjectiveData (Fin n) ℝ H => N.toAlgebraic.probability)
    L hL target _ hgamma hmodel htarget hobserved ⟨M, hM⟩

theorem quaternionic_square_root_instrument_witness_bound
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (E : Fin n → S.toOperatorStructure.operatorAlgebra)
    (hE : ∀ i, S.IsQuaternionPositive (E i))
    (hEc : ∀ i, S.IsQuaternionPositive (1 - E i))
    {epsilon : ℝ} (hdefect : ∀ i, ‖(E i).val * (E i).val - (E i).val‖ ≤ epsilon)
    (hepsilon : epsilon < 1 / 4)
    (c : FiniteRealWordFunctional n) (L : ℕ) (hL : c.HasHorizon L)
    (target : Word (Fin n) → ℝ) {gamma delta : ℝ} (hgamma : 0 < gamma)
    (hmodel : ∀ M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure,
      0 ≤ c.evaluate M.toAlgebraic.probability)
    (htarget : c.evaluate target ≤ -gamma)
    (hobserved : ∀ w ∈ c.coefficients.support,
      |quaternionicBranchWordProbability S psi
        (fun i => S.canonicalPositiveSquareRoot (E i) (hE i))
        (fun i => S.canonicalPositiveSquareRoot (1 - E i) (hEc i)) w - target w| ≤ delta) :
    delta + 2 * (L : ℝ) * Real.sqrt (spectralRoundingError epsilon) ≥
      gamma / c.coefficientNorm := by
  obtain ⟨M, _, hM⟩ := S.exists_quaternionic_canonical_root_word_model
    psi hnormalized hpositive E hE hEc hdefect hepsilon
  exact c.root_approximation_forces_witness_bound
    (fun N : QuaternionicProjectiveData (Fin n) S.toOperatorStructure => N.toAlgebraic.probability)
    L hL target _ hgamma hmodel htarget hobserved ⟨M, hM⟩

end AlbertSequential
