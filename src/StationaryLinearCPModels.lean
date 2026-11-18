module

public import LinearMapChoi

/-! Stationary instruments specified as arbitrary complex-linear CP maps.
The sum is trace preserving; individual branches are not required TP.
The Choi parameterization below is an exact all-input/all-word bijection.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

abbrev RawStationaryLinearCPModel (d : ℕ) (P X : Type*) (A : X → Type*) :=
  (P → ComplexMatrix d) ×
    ((x : X) → A x → (ComplexMatrix d →ₗ[ℂ] ComplexMatrix d))

def IsNormalizedStationaryLinearCPModel {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawStationaryLinearCPModel d P X A) : Prop :=
  (∀ p, IsMatrixDensity (r.1 p)) ∧
  (∀ x a, IsCompletelyPositiveMatrixMap (r.2 x a)) ∧
  (∀ x Y, Matrix.trace ((∑ a, r.2 x a) Y) = Matrix.trace Y)

def stationaryLinearCPWordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawStationaryLinearCPModel d P X A) (p : P) (w : InstrumentWord A) :
    ComplexMatrix d := w.foldl (fun Y a => r.2 a.1 a.2 Y) (r.1 p)

def stationaryLinearCPWordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawStationaryLinearCPModel d P X A) (p : P) (w : InstrumentWord A) : ℝ :=
  (Matrix.trace (stationaryLinearCPWordState r p w)).re

def linearCPModelToChoi {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawStationaryLinearCPModel d P X A) : RawFiniteCPModel d P X A :=
  (r.1, fun x a => linearMapChoi (r.2 x a))

def choiModelToLinearCP {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) : RawStationaryLinearCPModel d P X A :=
  (r.1, fun x a => choiLinearMap (r.2 x a))

theorem linearMapChoi_finset_sum {d : ℕ} {I : Type*} (s : Finset I)
    (Phi : I → (ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)) :
    linearMapChoi (∑ i ∈ s, Phi i) = ∑ i ∈ s, linearMapChoi (Phi i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [linearMapChoi, Matrix.sum_apply]

theorem choiOutputTrace_finset_sum {d : ℕ} {I : Type*} (s : Finset I)
    (C : I → ChoiMatrix d) :
    choiOutputTrace (∑ i ∈ s, C i) = ∑ i ∈ s, choiOutputTrace (C i) := by
  ext i j
  simp only [choiOutputTrace, Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem linearCPModelToChoi_normalized {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawStationaryLinearCPModel d P X A)
    (hr : IsNormalizedStationaryLinearCPModel r) :
    IsNormalizedFiniteCPModel (linearCPModelToChoi r) := by
  refine ⟨hr.1, fun x a => (linearMapChoi_positive_iff (r.2 x a)).mpr (hr.2.1 x a), fun x => ?_⟩
  have hn := (linearMapChoi_trace_preservation_iff (∑ a, r.2 x a)).mpr (hr.2.2 x)
  simpa only [linearCPModelToChoi, linearMapChoi_finset_sum, choiOutputTrace_finset_sum] using hn

theorem choiModelToLinearCP_normalized {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) :
    IsNormalizedStationaryLinearCPModel (choiModelToLinearCP r) := by
  refine ⟨hr.1, fun x a => (choi_positive_iff_completelyPositive (r.2 x a)).mp (hr.2.1 x a),
    fun x => ?_⟩
  apply (linearMapChoi_trace_preservation_iff (∑ a, choiLinearMap (r.2 x a))).mp
  simp only [linearMapChoi_finset_sum, linearMapChoi_choiLinearMap,
    choiOutputTrace_finset_sum]
  exact hr.2.2 x

theorem linearCPModelToChoi_wordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawStationaryLinearCPModel d P X A) (p : P) (w : InstrumentWord A) :
    finiteCPWordState (linearCPModelToChoi r) p w = stationaryLinearCPWordState r p w := by
  simp only [finiteCPWordState, stationaryLinearCPWordState, linearCPModelToChoi,
    choiAction_linearMapChoi]

theorem choiModelToLinearCP_wordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (p : P) (w : InstrumentWord A) :
    stationaryLinearCPWordState (choiModelToLinearCP r) p w = finiteCPWordState r p w := rfl

theorem linearCPModelToChoi_wordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawStationaryLinearCPModel d P X A) (p : P) (w : InstrumentWord A) :
    finiteCPWordProbability (linearCPModelToChoi r) p w = stationaryLinearCPWordProbability r p w := by
  unfold finiteCPWordProbability stationaryLinearCPWordProbability
  rw [linearCPModelToChoi_wordState]

theorem choiModelToLinearCP_wordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (p : P) (w : InstrumentWord A) :
    stationaryLinearCPWordProbability (choiModelToLinearCP r) p w = finiteCPWordProbability r p w := rfl

end AlbertSequential
