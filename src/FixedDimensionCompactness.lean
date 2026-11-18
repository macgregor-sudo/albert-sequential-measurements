module

public import ChoiParameterCompactness
public import FiniteMenuCompactness

/-! All four fields of the fixed-dimensional compactness contract.
Concrete PSD Choi data and actual unconditional chronological word evaluation
are used throughout. CP/Kraus interpretation remains a separate explicit bridge.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem fixedDimensionCompactness (d : ℕ) (P X : Type*) (A : X → Type*)
    [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)] :
    FixedDimensionCompactnessObligations d P X A := {
  parameter_compact := fun _ => isCompact_normalized_finiteCPModels d P X A
  word_continuous := continuous_finiteCPWordProbability
  finite_menu_iff := fun _ t => finite_menu_iff_of_parameter_compact
    (isCompact_normalized_finiteCPModels d P X A) t
  finite_error_gap := fun _ t hnone => finite_error_gap_of_parameter_compact
    (isCompact_normalized_finiteCPModels d P X A) t hnone
}

end AlbertSequential
