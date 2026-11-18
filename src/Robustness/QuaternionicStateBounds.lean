module
public import QuaternionicClassIConstructor
public import Robustness.OperatorSubalgebraStates

/-! Ordinary-source quaternionic positivity and the ORIGINAL commutant state.
The right-Hilbert/operator model is reused without a state extension. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential.RightQuaternionicHilbertStructure
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem positive_state_abs_le_operator_norm (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (T : selfAdjoint S.toOperatorStructure.operatorAlgebra) :
    |psi T| ≤ ‖S.toOperatorStructure.operatorValue T.val‖ :=
  operatorSubalgebra_state_abs_le_norm S.toOperatorStructure.operatorAlgebra
    psi hnormalized (fun X hX => hpositive X ((S.positive_iff_real_operator X.val).mpr hX)) T

theorem positive_state_word_error (S : RightQuaternionicHilbertStructure H)
    (psi : selfAdjoint S.toOperatorStructure.operatorAlgebra →ₗ[ℝ] ℝ)
    (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint S.toOperatorStructure.operatorAlgebra,
      S.IsQuaternionPositive T.val → 0 ≤ psi T)
    (a b : I → S.toOperatorStructure.operatorAlgebra)
    (ha : ∀ i, ‖S.toOperatorStructure.operatorValue (a i)‖ ≤ 1)
    (hb : ∀ i, ‖S.toOperatorStructure.operatorValue (b i)‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hab : ∀ i, ‖S.toOperatorStructure.operatorValue (a i) -
      S.toOperatorStructure.operatorValue (b i)‖ ≤ epsilon) (w : List I) :
    |psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
        (chronologicalProduct a w)) -
      psi (operatorSubalgebraAmplitudeEffect S.toOperatorStructure.operatorAlgebra
        (chronologicalProduct b w))| ≤ 2 * (w.length : ℝ) * epsilon :=
  operatorSubalgebra_state_word_error S.toOperatorStructure.operatorAlgebra
    psi hnormalized (fun X hX => hpositive X ((S.positive_iff_real_operator X.val).mpr hX))
    a b ha hb hepsilon hab w

end AlbertSequential.RightQuaternionicHilbertStructure
