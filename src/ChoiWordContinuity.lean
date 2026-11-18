module

public import Interfaces.InstrumentsAndCompactness

/-! Continuity of the actual chronological unconditional Choi word semantics.
No normalization, positivity, nonzero outcome, or finite label-set assumption
is needed for continuity. This module does not assume a word-continuity field.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

theorem continuous_choiAction (d : ℕ) :
    Continuous (fun r : ChoiMatrix d × ComplexMatrix d => choiAction r.1 r.2) := by
  unfold choiAction
  fun_prop

theorem continuous_choiOutputTrace (d : ℕ) :
    Continuous (fun C : ChoiMatrix d => choiOutputTrace C) := by
  unfold choiOutputTrace
  fun_prop

theorem continuous_finiteCPWordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (p : P) (w : InstrumentWord A) :
    Continuous (fun r : RawFiniteCPModel d P X A => finiteCPWordState r p w) := by
  induction w using List.reverseRecOn with
  | nil =>
      simpa only [finiteCPWordState, List.foldl_nil, Function.comp_def] using
        ((continuous_apply p).comp continuous_fst :
          Continuous (fun r : RawFiniteCPModel d P X A => r.1 p))
  | append_singleton w a ih =>
      have hc : Continuous (fun r : RawFiniteCPModel d P X A => r.2 a.1 a.2) := by
        fun_prop
      simpa only [finiteCPWordState, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Function.comp_def] using
        (continuous_choiAction d).comp (hc.prodMk ih)

theorem continuous_finiteCPWordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (p : P) (w : InstrumentWord A) :
    Continuous (fun r : RawFiniteCPModel d P X A => finiteCPWordProbability r p w) := by
  have h := continuous_finiteCPWordState (d := d) p w
  unfold finiteCPWordProbability Matrix.trace
  fun_prop

end AlbertSequential
