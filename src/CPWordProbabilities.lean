module

public import StationaryLinearCPModels

/-! Positivity and reality of unconditional word states. In particular, using
the real trace component in the shared interface loses no complex equality
for normalized CP models. No conditional probabilities or divisions occur.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

theorem krausAction_positive {d : ℕ} (K : List (ComplexMatrix d))
    {Y : ComplexMatrix d} (hY : Y.PosSemidef) : (krausAction K Y).PosSemidef := by
  induction K with
  | nil => simpa [krausAction] using (Matrix.PosSemidef.zero : (0 : ComplexMatrix d).PosSemidef)
  | cons V K ih =>
      simpa only [krausAction, List.map_cons, List.sum_cons] using
        (hY.mul_mul_conjTranspose_same V).add ih

theorem choiAction_positive {d : ℕ} {C : ChoiMatrix d} (hC : C.PosSemidef)
    {Y : ComplexMatrix d} (hY : Y.PosSemidef) : (choiAction C Y).PosSemidef := by
  obtain ⟨K, hK⟩ := (choi_positive_iff_kraus C).mp hC
  rw [hK Y]
  exact krausAction_positive K hY

theorem finiteCPWordState_positive {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) (w : InstrumentWord A) :
    (finiteCPWordState r p w).PosSemidef := by
  induction w using List.reverseRecOn with
  | nil => exact (hr.1 p).1
  | append_singleton w a ih =>
      simpa only [finiteCPWordState, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        choiAction_positive (hr.2.1 a.1 a.2) ih

theorem finiteCPWordProbability_nonneg {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) (w : InstrumentWord A) :
    0 ≤ finiteCPWordProbability r p w :=
  (Complex.nonneg_iff.mp (finiteCPWordState_positive r hr p w).trace_nonneg).1

theorem finiteCPWord_trace_eq_probability {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) (w : InstrumentWord A) :
    Matrix.trace (finiteCPWordState r p w) = (finiteCPWordProbability r p w : ℂ) := by
  have him := (Complex.nonneg_iff.mp (finiteCPWordState_positive r hr p w).trace_nonneg).2
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him.symm

theorem instrument_sum_trace_re {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (x : X) (Y : ComplexMatrix d) :
    ∑ a, (Matrix.trace (choiAction (r.2 x a) Y)).re = (Matrix.trace Y).re := by
  have hs := (choiModelToLinearCP_normalized r hr).2.2 x Y
  change Matrix.trace ((∑ a, choiLinearMap (r.2 x a)) Y) = Matrix.trace Y at hs
  simp only [LinearMap.sum_apply] at hs
  change Matrix.trace (∑ a, choiAction (r.2 x a) Y) = Matrix.trace Y at hs
  rw [Matrix.trace_sum] at hs
  have hreal := congrArg (fun z : ℂ => Complex.reCLM z) hs
  simpa only [map_sum, Complex.reCLM_apply] using hreal

theorem instrument_branch_trace_re_le {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (x : X) (a : A x)
    {Y : ComplexMatrix d} (hY : Y.PosSemidef) :
    (Matrix.trace (choiAction (r.2 x a) Y)).re ≤ (Matrix.trace Y).re := by
  classical
  rw [← instrument_sum_trace_re r hr x Y]
  apply Finset.single_le_sum (fun b _ => ?_) (Finset.mem_univ a)
  exact (Complex.nonneg_iff.mp (choiAction_positive (hr.2.1 x b) hY).trace_nonneg).1

theorem finiteCPWordProbability_le_one {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) (w : InstrumentWord A) :
    finiteCPWordProbability r p w ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil =>
      have ht := congrArg Complex.re (hr.1 p).2
      exact ht.le
  | append_singleton w a ih =>
      have hb := instrument_branch_trace_re_le r hr a.1 a.2
        (finiteCPWordState_positive r hr p w)
      simpa only [finiteCPWordProbability, finiteCPWordState, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using hb.trans ih

theorem stationaryLinearCPWord_trace_eq_probability {d : ℕ}
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (r : RawStationaryLinearCPModel d P X A) (hr : IsNormalizedStationaryLinearCPModel r)
    (p : P) (w : InstrumentWord A) :
    Matrix.trace (stationaryLinearCPWordState r p w) =
      (stationaryLinearCPWordProbability r p w : ℂ) := by
  simpa only [linearCPModelToChoi_wordState, linearCPModelToChoi_wordProbability] using
    finiteCPWord_trace_eq_probability (linearCPModelToChoi r) (linearCPModelToChoi_normalized r hr) p w

end AlbertSequential
