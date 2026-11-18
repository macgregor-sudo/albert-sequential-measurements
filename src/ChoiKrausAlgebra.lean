module

public import Interfaces.InstrumentsAndCompactness

/-! Concrete Choi/Kraus coordinate bridges, with the input/output convention
of `Interfaces.InstrumentsAndCompactness`. No nonzero-map or faithful-state assumption occurs.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def rankOneChoi {d : ℕ} (V : ComplexMatrix d) : ChoiMatrix d :=
  Matrix.vecMulVec (fun i : Fin d × Fin d => V i.2 i.1)
    (star (fun i : Fin d × Fin d => V i.2 i.1))

def krausChoi {d : ℕ} (K : List (ComplexMatrix d)) : ChoiMatrix d :=
  (K.map rankOneChoi).sum

theorem rankOneChoi_positive {d : ℕ} (V : ComplexMatrix d) :
    (rankOneChoi V).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

theorem krausChoi_positive {d : ℕ} (K : List (ComplexMatrix d)) :
    (krausChoi K).PosSemidef := by
  induction K with
  | nil => simpa [krausChoi] using (Matrix.PosSemidef.zero : (0 : ChoiMatrix d).PosSemidef)
  | cons V K ih => simpa [krausChoi] using (rankOneChoi_positive V).add ih

theorem choiAction_zero {d : ℕ} (Y : ComplexMatrix d) : choiAction 0 Y = 0 := by
  ext i j
  simp [choiAction]

theorem choiAction_add {d : ℕ} (C D : ChoiMatrix d) (Y : ComplexMatrix d) :
    choiAction (C + D) Y = choiAction C Y + choiAction D Y := by
  ext i j
  simp [choiAction, mul_add, Finset.sum_add_distrib]

theorem rankOneChoi_action {d : ℕ} (V Y : ComplexMatrix d) :
    choiAction (rankOneChoi V) Y = V * Y * V.conjTranspose := by
  classical
  ext k l
  simp only [choiAction, rankOneChoi, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem krausChoi_action {d : ℕ} (K : List (ComplexMatrix d)) (Y : ComplexMatrix d) :
    choiAction (krausChoi K) Y = krausAction K Y := by
  induction K with
  | nil => simp [krausChoi, krausAction, choiAction_zero]
  | cons V K ih =>
      simpa only [krausChoi, List.map_cons, List.sum_cons, krausAction] using
        (choiAction_add (rankOneChoi V) (krausChoi K) Y).trans
          (congrArg₂ (· + ·) (rankOneChoi_action V Y) ih)

theorem choiAction_single {d : ℕ} (C : ChoiMatrix d) (i j k l : Fin d) :
    choiAction C (Matrix.single i j 1) k l = C (i, k) (j, l) := by
  classical
  simp [choiAction, Matrix.single_apply, ite_and]

theorem choiAction_injective {d : ℕ} {C D : ChoiMatrix d}
    (h : ∀ Y, choiAction C Y = choiAction D Y) : C = D := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simpa only [choiAction_single] using congrFun (congrFun (h (Matrix.single i j 1)) k) l

theorem rankOneChoi_outputTrace {d : ℕ} (V : ComplexMatrix d) :
    choiOutputTrace (rankOneChoi V) = (V.conjTranspose * V).transpose := by
  ext i j
  simp only [choiOutputTrace, rankOneChoi, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem choiOutputTrace_zero {d : ℕ} : choiOutputTrace (0 : ChoiMatrix d) = 0 := by
  ext i j
  simp [choiOutputTrace]

theorem choiOutputTrace_add {d : ℕ} (C D : ChoiMatrix d) :
    choiOutputTrace (C + D) = choiOutputTrace C + choiOutputTrace D := by
  ext i j
  simp [choiOutputTrace, Finset.sum_add_distrib]

theorem krausChoi_outputTrace {d : ℕ} (K : List (ComplexMatrix d)) :
    choiOutputTrace (krausChoi K) = (krausEffect K).transpose := by
  induction K with
  | nil => simp [krausChoi, krausEffect, choiOutputTrace_zero]
  | cons V K ih =>
      simpa only [krausChoi, krausEffect, List.map_cons, List.sum_cons,
        Matrix.transpose_add] using
        (choiOutputTrace_add (rankOneChoi V) (krausChoi K)).trans
          (congrArg₂ (· + ·) (rankOneChoi_outputTrace V) ih)

theorem trace_choiAction {d : ℕ} (C : ChoiMatrix d) (Y : ComplexMatrix d) :
    Matrix.trace (choiAction C Y) = ∑ i, ∑ j, Y i j * choiOutputTrace C i j := by
  simp only [Matrix.trace, Matrix.diag, choiAction, choiOutputTrace, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem choi_trace_preservation_iff {d : ℕ} (C : ChoiMatrix d) :
    choiOutputTrace C = 1 ↔
      ∀ Y, Matrix.trace (choiAction C Y) = Matrix.trace Y := by
  classical
  constructor
  · intro hC Y
    rw [trace_choiAction, hC]
    simp [Matrix.trace, Matrix.diag, Matrix.one_apply]
  · intro h
    ext i j
    have hm := h (Matrix.single i j 1)
    simp only [Matrix.trace, Matrix.diag, choiAction_single] at hm
    simpa [choiOutputTrace, Matrix.single_apply, Matrix.one_apply, ite_and, eq_comm] using hm

theorem choi_kraus_effect_binding {d : ℕ} (C : ChoiMatrix d)
    (K : List (ComplexMatrix d))
    (h : ∀ Y, choiAction C Y = krausAction K Y) :
    choiOutputTrace C = (krausEffect K).transpose := by
  have heq : C = krausChoi K :=
    choiAction_injective (fun Y => (h Y).trans (krausChoi_action K Y).symm)
  rw [heq, krausChoi_outputTrace]

end AlbertSequential
