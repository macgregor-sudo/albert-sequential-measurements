/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BinaryTestReduction

/-! One stationary finite instrument after fixed outcome relabeling/trivial
settings. Initial state and Hilbert dimension are exactly unchanged. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def BinaryTestReduction.model {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) : BinaryKrausRealization d X where
  initial := r.initial
  density := r.density
  kraus := BinaryTestReduction.kraus r m
  normalized x := by
    cases hm : m x with
    | direct => simpa only [BinaryTestReduction.kraus, hm] using r.normalized x
    | complement =>
      simpa only [BinaryTestReduction.kraus, hm, Bool.not_true, Bool.not_false, add_comm] using r.normalized x
    | deterministic c => cases c <;> simp [BinaryTestReduction.kraus, hm, krausEffect]

theorem BinaryTestReduction.model_real {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (hr : IsRealKrausRealization r) :
    IsRealKrausRealization (BinaryTestReduction.model r m) := by
  refine ⟨hr.1, ?_⟩
  intro x b K hK
  change K ∈ BinaryTestReduction.kraus r m x b at hK
  cases hm : m x with
  | direct => exact hr.2 x b K (by simpa only [BinaryTestReduction.kraus, hm] using hK)
  | complement => exact hr.2 x (!b) K (by simpa only [BinaryTestReduction.kraus, hm] using hK)
  | deterministic c =>
    simp only [BinaryTestReduction.kraus, hm] at hK
    split_ifs at hK
    · have h : K = 1 := List.mem_singleton.mp hK
      subst K
      intro i j
      simp only [Matrix.one_apply]
      split_ifs <;> rfl
    · simp at hK

private theorem krausAction_zero_input {d : ℕ} (K : List (ComplexMatrix d)) : krausAction K 0 = 0 := by
  induction K with
  | nil => rfl
  | cons V K ih => simpa only [krausAction, List.map_cons, List.sum_cons,
      Matrix.mul_zero, Matrix.zero_mul, zero_add] using ih

theorem BinaryTestReduction.action {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (a : Outcome X) (Y : ComplexMatrix d) :
    krausAction (BinaryTestReduction.kraus r m a.1 a.2) Y =
      WordReduction.applyStep (fun b => krausAction (r.kraus b.1 b.2))
        (BinaryTestReduction.outcomeStep m a) Y := by
  rcases a with ⟨x,b⟩
  cases hm : m x with
  | direct => simp only [BinaryTestReduction.kraus, BinaryTestReduction.outcomeStep, hm,
      WordReduction.applyStep]
  | complement => simp only [BinaryTestReduction.kraus, BinaryTestReduction.outcomeStep, hm,
      WordReduction.applyStep]
  | deterministic c =>
    by_cases hb : b = c <;>
      simp [BinaryTestReduction.kraus, BinaryTestReduction.outcomeStep, hm, hb,
        WordReduction.applyStep, krausAction]

theorem BinaryTestReduction.word_state {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (Y : ComplexMatrix d) (w : Word X) :
    w.foldl (fun Z a => krausAction (BinaryTestReduction.kraus r m a.1 a.2) Z) Y =
      match WordReduction.translate (BinaryTestReduction.outcomeStep m) w with
      | none => 0
      | some v => v.foldl (fun Z a => krausAction (r.kraus a.1 a.2) Z) Y := by
  simp_rw [BinaryTestReduction.action]
  have h := WordReduction.foldl_translate
    (A := Outcome X) (B := Outcome X) (M := ComplexMatrix d)
    (fun a Z => krausAction (r.kraus a.1 a.2) Z)
    (BinaryTestReduction.outcomeStep m) (fun _ => krausAction_zero_input _) Y w
  cases ht : WordReduction.translate (BinaryTestReduction.outcomeStep m) w <;>
    simpa only [ht] using h

theorem BinaryTestReduction.probability {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (w : Word X) :
    binaryKrausProbability (BinaryTestReduction.model r m) w =
      match WordReduction.translate (BinaryTestReduction.outcomeStep m) w with
      | none => 0
      | some v => binaryKrausProbability r v := by
  change (Matrix.trace (w.foldl (fun Z a => krausAction (BinaryTestReduction.kraus r m a.1 a.2) Z)
    r.initial)).re = _
  rw [BinaryTestReduction.word_state]
  cases h : WordReduction.translate (BinaryTestReduction.outcomeStep m) w
  · simp
  · rfl

theorem BinaryTestReduction.model_supported {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (hr : HasCertaintySupportedOutputs r) :
    HasCertaintySupportedOutputs (BinaryTestReduction.model r m) := by
  intro x Y hY
  cases hm : m x with
  | direct => simpa only [BinaryTestReduction.model, BinaryTestReduction.kraus, hm] using hr x Y hY
  | complement =>
    have he : krausEffect (r.kraus x false) = 1 - krausEffect (r.kraus x true) :=
      eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using r.normalized x)
    obtain ⟨hy,hn⟩ := hr x Y hY
    change krausEffect (BinaryTestReduction.kraus r m x true) *
        krausAction (BinaryTestReduction.kraus r m x true) Y =
          krausAction (BinaryTestReduction.kraus r m x true) Y ∧
      krausEffect (BinaryTestReduction.kraus r m x true) *
        krausAction (BinaryTestReduction.kraus r m x false) Y = 0
    simp only [BinaryTestReduction.kraus, hm, Bool.not_true, Bool.not_false]
    constructor
    · rw [he, Matrix.sub_mul, Matrix.one_mul, hn, sub_zero]
    · rw [he, Matrix.sub_mul, Matrix.one_mul, hy, sub_self]
  | deterministic c =>
    cases c <;> simp [BinaryTestReduction.model, BinaryTestReduction.kraus, hm, krausEffect, krausAction]

end AlbertSequential
