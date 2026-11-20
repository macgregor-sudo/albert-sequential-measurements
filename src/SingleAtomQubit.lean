/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealPairJordanSpan
public import RealMatrixComplexification
import NativeOneTestConsequences

public section
noncomputable section

namespace AlbertSequential

open scoped Matrix ComplexOrder

theorem singleAtom_complementary_spans_disjoint (p : Albert) (hp : IsAtom p) :
    Disjoint (Submodule.span ℝ ({p} : Set Albert))
      (Submodule.span ℝ ({albertUnit - p} : Set Albert)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
  have hpp : tracePairing p p = 1 := by rw [tracePairing, hp.1, hp.2]
  have hpu : tracePairing p albertUnit = 1 := by rw [NativeAnalysis.tracePairing_unit_right, hp.2]
  have hab := congrArg (tracePairing p) (ha.trans hb.symm)
  rw [tracePairing_smul_right, tracePairing_smul_right, tracePairing_sub_right, hpp, hpu,
    sub_self, mul_zero, mul_one] at hab
  rw [← ha, hab, zero_smul]

private def answerBit (i : Fin 2) : Bool := ![true, false] i

private def answerIndicator (b : Bool) (i : Fin 2) : ℂ := if b = answerBit i then 1 else 0

private def oneAtomProjection : ComplexMatrix 2 := Matrix.diagonal (answerIndicator true)

private theorem oneAtomProjection_star : star oneAtomProjection = oneAtomProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oneAtomProjection, answerIndicator, answerBit, Matrix.star_apply]

private theorem oneAtomProjection_idempotent : oneAtomProjection * oneAtomProjection = oneAtomProjection := by
  rw [oneAtomProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [answerIndicator, answerBit]

private theorem oneAtomProjection_rank : oneAtomProjection.rank = 1 := by
  let v : Fin 2 → ℂ := ![1,0]
  have hv : oneAtomProjection = Matrix.vecMulVec v v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oneAtomProjection, answerIndicator, answerBit, v, Matrix.vecMulVec_apply]
  have hd : (oneAtomProjection.submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)).det ≠ 0 := by
    rw [Matrix.det_unique]
    simp [oneAtomProjection, answerIndicator, answerBit]
  have hl := Matrix.rank_submatrix_le oneAtomProjection (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
  rw [Matrix.rank_of_det_ne_zero hd] at hl
  refine le_antisymm ?_ (by simpa using hl)
  rw [hv]
  exact Matrix.rank_vecMulVec_le _ _

private theorem oneAtom_outcome (a : Outcome Unit) :
    algebraicOutcome (fun _ => oneAtomProjection) a = Matrix.diagonal (answerIndicator a.2) := by
  obtain ⟨_,b⟩ := a
  cases b
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [algebraicOutcome, oneAtomProjection, answerIndicator, answerBit]
  · rfl

private def matchingDiagonal (w : Word Unit) (i : Fin 2) : ℂ :=
  if w.all (fun a => a.2 == answerBit i) then 1 else 0

private theorem oneAtom_operator (w : Word Unit) :
    wordOperator (fun _ => oneAtomProjection) w = Matrix.diagonal (matchingDiagonal w) := by
  induction w with
  | nil =>
    rw [wordOperator_nil]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matchingDiagonal]
  | cons a w ih =>
    rw [wordOperator_cons _ (fun _ => oneAtomProjection_star), ih, oneAtom_outcome,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : a.2 = answerBit i <;> simp [matchingDiagonal, answerIndicator, h]

/-- A fixed complex qubit projection reproduces the native one-atom table.
The real diagonal entries of the density are its initial yes and no probabilities. -/
theorem singleAtom_qubit_word_model (p : Albert) (hp : IsAtom p) :
    ∃ P : ComplexMatrix 2, star P = P ∧ P * P = P ∧ P.rank = 1 ∧
      ∀ ρ : Albert, IsDensity ρ → ∃ τ : ComplexMatrix 2,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ∀ w : Word Unit, (τ * wordOperator (fun _ => P) w).trace.re =
          nativeWordProbability (fun _ => p) ρ w := by
  refine ⟨oneAtomProjection, oneAtomProjection_star, oneAtomProjection_idempotent,
    oneAtomProjection_rank, fun ρ hρ => ?_⟩
  let t := tracePairing ρ p
  have htn : 0 ≤ t := NativeAnalysis.tracePairing_positive_nonnegative _ _ hρ.1 ⟨p,hp.1.symm⟩
  have hno : tracePairing ρ (albertUnit - p) = 1 - t := by
    rw [tracePairing_sub_right, NativeAnalysis.tracePairing_unit_right, hρ.2]
  have hpositive : IsPositive (albertUnit - p) :=
    ⟨_, (NativeAnalysis.complementary_idempotent p hp.1).symm⟩
  have htc : 0 ≤ 1 - t := hno ▸ NativeAnalysis.tracePairing_positive_nonnegative _ _ hρ.1 hpositive
  let weight : Fin 2 → ℝ := ![t, 1 - t]
  let τ : ComplexMatrix 2 := Matrix.diagonal (fun i => (weight i : ℂ))
  refine ⟨τ, ?_, ?_, fun w => ?_⟩
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr htn
    · exact Complex.zero_le_real.mpr htc
  · simp [τ, weight, Matrix.trace, Fin.sum_univ_two]
  · have hw : (w.map Prod.snd).map (fun b => ((),b)) = w := by
      induction w with
      | nil => rfl
      | cons a w ih => obtain ⟨⟨⟩,_⟩ := a; simp [ih]
    have hword := NativeAnalysis.native_same_test_two_state_model p ρ hp (w.map Prod.snd)
    rw [hw] at hword
    rw [hword, oneAtom_operator, Matrix.diagonal_mul_diagonal]
    cases w with
    | nil => simp [NativeAnalysis.persistentAnswerProbability, weight, matchingDiagonal, Matrix.trace,
        Fin.sum_univ_two, nativeOutcome, hno, t]
    | cons a w =>
      obtain ⟨⟨⟩,b⟩ := a
      cases b <;> simp [NativeAnalysis.persistentAnswerProbability, weight, matchingDiagonal,
        answerBit, Matrix.trace, Fin.sum_univ_two, nativeOutcome, hno, t, List.all_map] <;>
        split <;> simp_all

end AlbertSequential
