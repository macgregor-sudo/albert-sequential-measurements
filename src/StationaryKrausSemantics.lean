module

public import ChoiKrausEquivalence

/-! Actual all-word stationary finite-Kraus interpretation of normalized Choi
parameters. This is finite complex matrix CP semantics, not a general abstract
operator-algebraic CP class. Initial states are not required faithful.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

theorem choiKrausObligations (d : ℕ) : ChoiKrausObligations d where
  choi_iff_kraus := choi_positive_iff_kraus
  trace_preservation := choi_trace_preservation_iff
  effect_binding := choi_kraus_effect_binding

def finiteKrausWordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (rho : P → ComplexMatrix d) (K : (x : X) → A x → List (ComplexMatrix d))
    (p : P) (w : InstrumentWord A) : ComplexMatrix d :=
  w.foldl (fun Y a => krausAction (K a.1 a.2) Y) (rho p)

def finiteKrausWordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (rho : P → ComplexMatrix d) (K : (x : X) → A x → List (ComplexMatrix d))
    (p : P) (w : InstrumentWord A) : ℝ :=
  (Matrix.trace (finiteKrausWordState rho K p w)).re

theorem choiWordState_eq_krausWordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (K : (x : X) → A x → List (ComplexMatrix d))
    (hK : ∀ x a Y, choiAction (r.2 x a) Y = krausAction (K x a) Y)
    (p : P) (w : InstrumentWord A) :
    finiteCPWordState r p w = finiteKrausWordState r.1 K p w := by
  simp only [finiteCPWordState, finiteKrausWordState, hK]

theorem choiWordProbability_eq_krausWordProbability {d : ℕ}
    {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (K : (x : X) → A x → List (ComplexMatrix d))
    (hK : ∀ x a Y, choiAction (r.2 x a) Y = krausAction (K x a) Y)
    (p : P) (w : InstrumentWord A) :
    finiteCPWordProbability r p w = finiteKrausWordProbability r.1 K p w := by
  unfold finiteCPWordProbability finiteKrausWordProbability
  rw [choiWordState_eq_krausWordState r K hK]

theorem normalizedChoiModel_has_stationaryKraus {d : ℕ}
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (r : RawFiniteCPModel d P X A) (hr : IsNormalizedFiniteCPModel r) :
    ∃ K : (x : X) → A x → List (ComplexMatrix d),
      (∀ x, ∑ a, krausEffect (K x a) = 1) ∧
      (∀ x a Y, choiAction (r.2 x a) Y = krausAction (K x a) Y) ∧
      ∀ p w, finiteCPWordProbability r p w = finiteKrausWordProbability r.1 K p w := by
  classical
  have hk : ∀ x a, ∃ K : List (ComplexMatrix d),
      ∀ Y, choiAction (r.2 x a) Y = krausAction K Y :=
    fun x a => (choi_positive_iff_kraus _).mp (hr.2.1 x a)
  choose K hK using hk
  refine ⟨K, fun x => ?_, hK, fun p w => choiWordProbability_eq_krausWordProbability r K hK p w⟩
  have hpartial : ∑ a, (krausEffect (K x a)).transpose = 1 := by
    calc
      _ = ∑ a, choiOutputTrace (r.2 x a) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (choi_kraus_effect_binding (r.2 x a) (K x a) (hK x a)).symm
      _ = 1 := hr.2.2 x
  have ht := congrArg Matrix.transpose hpartial
  simpa only [Matrix.transpose_sum, Matrix.transpose_transpose, Matrix.transpose_one] using ht

def stationaryKrausToChoi {d : ℕ} {P X : Type*} {A : X → Type*}
    (rho : P → ComplexMatrix d) (K : (x : X) → A x → List (ComplexMatrix d)) :
    RawFiniteCPModel d P X A := (rho, fun x a => krausChoi (K x a))

theorem stationaryKrausToChoi_normalized {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (rho : P → ComplexMatrix d)
    (K : (x : X) → A x → List (ComplexMatrix d))
    (hrho : ∀ p, IsMatrixDensity (rho p)) (hK : ∀ x, ∑ a, krausEffect (K x a) = 1) :
    IsNormalizedFiniteCPModel (stationaryKrausToChoi rho K) := by
  classical
  refine ⟨hrho, fun x a => krausChoi_positive (K x a), fun x => ?_⟩
  change ∑ a, choiOutputTrace (krausChoi (K x a)) = 1
  simp only [krausChoi_outputTrace, ← Matrix.transpose_sum, hK x, Matrix.transpose_one]

end AlbertSequential
