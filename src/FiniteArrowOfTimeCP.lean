/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteArrowOfTime
public import CPWordProbabilities
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.List

/-! A finite normalized diagonal Choi instrument for the history register. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.FiniteArrowOfTime

open scoped BigOperators ComplexOrder

variable {I : Type*} {A : I → Type*} {N d : ℕ} [∀ i, Fintype (A i)]

/-- A single history basis state with its unnormalized weight. -/
def historyState (e : History A N ≃ Fin d) (h : History A N) (weight : ℂ) : ComplexMatrix d :=
  Matrix.diagonal fun k => if k = e h then weight else 0

/-- The diagonal branch contributes only at the deterministic updated history. -/
def transitionChoi (R : Register A N) (e : History A N ≃ Fin d) (i : I) (a : A i) :
    ChoiMatrix d :=
  Matrix.diagonal fun ik =>
    if ik.2 = e (advance (e.symm ik.1) ⟨i,a⟩) then (R.readout (e.symm ik.1) i a : ℂ) else 0

private theorem action_diagonalChoi (c : Fin d × Fin d → ℂ) (Y : ComplexMatrix d) :
    choiAction (Matrix.diagonal c) Y = Matrix.diagonal (fun k => ∑ i, Y i i * c (i,k)) := by
  classical
  ext k l
  by_cases hk : k = l
  · subst l
    simp [choiAction, Matrix.diagonal_apply, mul_ite]
  · simp [choiAction, hk]

private theorem action_historyState (R : Register A N) (e : History A N ≃ Fin d)
    (i : I) (a : A i) (h : History A N) (w : ℂ) :
    choiAction (transitionChoi R e i a) (historyState e h w) =
      historyState e (advance h ⟨i,a⟩) (w * (R.readout h i a : ℂ)) := by
  rw [transitionChoi, action_diagonalChoi]
  congr 1
  funext k
  simp only [historyState, Matrix.diagonal_apply_eq]
  rw [Finset.sum_eq_single (e h)]
  · simp [mul_ite]
  · intro j _ hj
    simp [hj]
  · simp

private theorem outputTrace_transitionChoi (R : Register A N) (e : History A N ≃ Fin d)
    (i : I) (a : A i) :
    choiOutputTrace (transitionChoi R e i a) =
      Matrix.diagonal (fun k => (R.readout (e.symm k) i a : ℂ)) := by
  classical
  ext k l
  by_cases hk : k = l
  · subst l
    simp [choiOutputTrace, transitionChoi]
  · simp [choiOutputTrace, transitionChoi, hk]

/-- The finite history instrument with diagonal Choi blocks and a basis state per preparation. -/
def Register.diagonalCP (R : Register A N) (e : History A N ≃ Fin d) {P : Type*}
    (prepare : P → History A N) : RawFiniteCPModel d P I A :=
  (fun p => historyState e (prepare p) 1, transitionChoi R e)

theorem Register.diagonalCP_normalized (R : Register A N) (e : History A N ≃ Fin d) {P : Type*}
    (prepare : P → History A N) : IsNormalizedFiniteCPModel (R.diagonalCP e prepare) := by
  refine ⟨fun p => ⟨?_, ?_⟩, fun i a => ?_, fun i => ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro j
    change (0 : ℂ) ≤ if j = e (prepare p) then 1 else 0
    split
    · simp
    · exact le_refl 0
  · change Matrix.trace (historyState e (prepare p) 1) = 1
    simp [historyState, Matrix.trace]
  · apply Matrix.PosSemidef.diagonal
    intro j
    change (0 : ℂ) ≤ if j.2 = e (advance (e.symm j.1) ⟨i,a⟩) then
      (R.readout (e.symm j.1) i a : ℂ) else 0
    split
    · exact Complex.nonneg_iff.mpr ⟨R.nonneg .., rfl⟩
    · exact le_refl 0
  · change ∑ a, choiOutputTrace (transitionChoi R e i a) = 1
    simp only [outputTrace_transitionChoi]
    ext j k
    by_cases h : j = k
    · subst k
      simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact_mod_cast R.normalized (e.symm j) i
    · simp [h]

omit [∀ i, Fintype (A i)] in
private theorem trace_historyState (e : History A N ≃ Fin d) (h : History A N) (w : ℂ) :
    Matrix.trace (historyState e h w) = w := by
  simp [historyState, Matrix.trace]

private theorem trace_continue (R : Register A N) (e : History A N ≃ Fin d)
    (h : History A N) (w : InstrumentWord A) (weight : ℝ) :
    (Matrix.trace (w.foldl (fun Y a => choiAction (transitionChoi R e a.1 a.2) Y)
      (historyState e h weight))).re = weight * R.run h w := by
  induction w generalizing h weight with
  | nil => simp [trace_historyState, Register.run]
  | cons a w ih =>
    simp only [List.foldl_cons, action_historyState, ← Complex.ofReal_mul, ih, Register.run, mul_assoc]

theorem Register.diagonalCP_probability (R : Register A N) (e : History A N ≃ Fin d)
    {P : Type*} (prepare : P → History A N) (p : P) (w : InstrumentWord A) :
    finiteCPWordProbability (R.diagonalCP e prepare) p w = R.run (prepare p) w := by
  simpa only [finiteCPWordProbability, finiteCPWordState, Register.diagonalCP, Complex.ofReal_one,
    one_mul] using trace_continue R e (prepare p) w 1

theorem cpTable_causal {P : Type*} (r : RawFiniteCPModel d P I A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) :
    IsCausal (fun h : History A N => finiteCPWordProbability r p h.val) where
  root := by
    change (Matrix.trace (r.1 p)).re = 1
    rw [(hr.1 p).2, Complex.one_re]
  marginal h _hn i := by
    simp only [snoc, finiteCPWordProbability, finiteCPWordState, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    exact instrument_sum_trace_re r hr i (finiteCPWordState r p h.val)

def HasFiniteCPRealization (t : Table A N) : Prop :=
  ∃ (d : ℕ) (r : RawFiniteCPModel d Unit I A), IsNormalizedFiniteCPModel r ∧
    ∀ h : History A N, finiteCPWordProbability r () h.val = t h

variable [Finite I] [∀ i, Nonempty (A i)]

/-- Causality and pointwise nonnegativity are exactly finite-matrix instrument realizability. -/
theorem exists_diagonalCP_iff (t : Table A N) :
    HasFiniteCPRealization t ↔ IsCausal t ∧ ∀ h, 0 ≤ t h := by
  constructor
  · rintro ⟨d, r, hr, he⟩
    have e : (fun h : History A N => finiteCPWordProbability r () h.val) = t := funext he
    rw [← e]
    exact ⟨cpTable_causal r hr (), fun h => finiteCPWordProbability_nonneg r hr () h.val⟩
  · intro ht
    obtain ⟨R, hR⟩ := (exists_register_iff t).mpr ht
    let _ : Finite (History A N) := (List.finite_length_le (Sigma A) N).to_subtype
    let _ : Fintype (History A N) := Fintype.ofFinite _
    let e := Fintype.equivFin (History A N)
    refine ⟨Fintype.card (History A N), R.diagonalCP e (fun _ => empty),
      R.diagonalCP_normalized e _, ?_⟩
    intro h
    exact (R.diagonalCP_probability e (fun _ : Unit => empty) () h.val).trans (congrFun hR h)

/-- The only affine equalities of the finite CP tables are the arrow-of-time equations. -/
theorem mem_affineSpan_cpTables_iff (t : Table A N) :
    t ∈ affineSpan ℝ {s | HasFiniteCPRealization s} ↔ IsCausal t := by
  have h : {s : Table A N | HasFiniteCPRealization s} = Set.range (Register.table (A := A) (N := N)) := by
    ext s
    exact (exists_diagonalCP_iff s).trans (exists_register_iff s).symm
  rw [h]
  exact mem_affineSpan_registerTables_iff t

end AlbertSequential.FiniteArrowOfTime
