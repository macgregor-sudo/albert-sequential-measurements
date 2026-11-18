module

public import PositiveMatrixCompactness
public import ChoiWordContinuity

/-! Compactness of normalized finite-outcome stationary Choi parameters.
The outcomes may depend on the arbitrary test label. Singular matrices and
zero outcome branches are retained. No Choi/Kraus bridge is assumed here.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def IsNormalizedChoiInstrument {d : ℕ} {B : Type*} [Fintype B]
    (C : B → ChoiMatrix d) : Prop :=
  (∀ a, (C a).PosSemidef) ∧ ∑ a, choiOutputTrace (C a) = 1

theorem trace_choiOutputTrace {d : ℕ} (C : ChoiMatrix d) :
    Matrix.trace (choiOutputTrace C) = Matrix.trace C := by
  simp only [Matrix.trace, Matrix.diag, choiOutputTrace, Fintype.sum_prod_type]

theorem normalized_instrument_trace_sum {d : ℕ} {B : Type*} [Fintype B]
    {C : B → ChoiMatrix d} (hC : IsNormalizedChoiInstrument C) :
    ∑ a, (Matrix.trace (C a)).re = (d : ℝ) := by
  have ht := congrArg (fun M : ComplexMatrix d => (Matrix.trace M).re) hC.2
  have hre : (∑ a, Matrix.trace (C a)).re = ∑ a, (Matrix.trace (C a)).re := by
    simpa only [Complex.reCLM_apply] using
      (map_sum Complex.reCLM (fun a => Matrix.trace (C a)) Finset.univ)
  simpa only [Matrix.trace_sum, trace_choiOutputTrace, hre, Matrix.trace_one,
    Fintype.card_fin, Complex.natCast_re] using ht

theorem normalized_instrument_trace_le {d : ℕ} {B : Type*} [Fintype B]
    {C : B → ChoiMatrix d} (hC : IsNormalizedChoiInstrument C) (a : B) :
    (Matrix.trace (C a)).re ≤ (d : ℝ) := by
  classical
  rw [← normalized_instrument_trace_sum hC]
  apply Finset.single_le_sum (fun b _ => ?_) (Finset.mem_univ a)
  exact (Complex.nonneg_iff.mp (hC.1 b).trace_nonneg).1

theorem isClosed_normalized_choi_instruments (d : ℕ) (B : Type*) [Fintype B] :
    IsClosed {C : B → ChoiMatrix d | IsNormalizedChoiInstrument C} := by
  classical
  have heq : {C : B → ChoiMatrix d | IsNormalizedChoiInstrument C} =
      (⋂ a, {C : B → ChoiMatrix d | (C a).PosSemidef}) ∩
      {C : B → ChoiMatrix d | ∑ a, choiOutputTrace (C a) = 1} := by
    ext C
    simp [IsNormalizedChoiInstrument]
  rw [heq]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro a
    have hpos : IsClosed {M : ChoiMatrix d | M.PosSemidef} := isClosed_positive_matrices
    have hca : Continuous (fun C : B → ChoiMatrix d => C a) := continuous_apply a
    exact hpos.preimage hca
  · apply isClosed_eq _ continuous_const
    unfold choiOutputTrace
    fun_prop

theorem isCompact_normalized_choi_instruments (d : ℕ) (B : Type*) [Fintype B] :
    IsCompact {C : B → ChoiMatrix d | IsNormalizedChoiInstrument C} := by
  have hbox : IsCompact {C : B → ChoiMatrix d |
      ∀ a, (C a).PosSemidef ∧ (Matrix.trace (C a)).re ≤ (d : ℝ)} :=
    isCompact_pi_infinite fun _ =>
      isCompact_positive_trace_le (n := Fin d × Fin d) d
  apply hbox.of_isClosed_subset (isClosed_normalized_choi_instruments d B)
  intro C hC a
  exact ⟨hC.1 a, normalized_instrument_trace_le hC a⟩

theorem isCompact_normalized_finiteCPModels (d : ℕ) (P X : Type*)
    (A : X → Type*) [∀ x, Fintype (A x)] :
    IsCompact {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r} := by
  have hp : IsCompact {rho : P → ComplexMatrix d | ∀ p, IsMatrixDensity (rho p)} :=
    isCompact_pi_infinite fun _ => isCompact_matrix_density d
  have hi : IsCompact {C : (x : X) → A x → ChoiMatrix d |
      ∀ x, IsNormalizedChoiInstrument (C x)} :=
    isCompact_pi_infinite fun x => isCompact_normalized_choi_instruments d (A x)
  have heq : {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r} =
      {rho : P → ComplexMatrix d | ∀ p, IsMatrixDensity (rho p)} ×ˢ
      {C : (x : X) → A x → ChoiMatrix d | ∀ x, IsNormalizedChoiInstrument (C x)} := by
    ext r
    simp only [Set.mem_ofPred_eq, IsNormalizedFiniteCPModel, IsNormalizedChoiInstrument,
      Set.mem_prod, forall_and]
  rw [heq]
  exact hp.prod hi

end AlbertSequential
