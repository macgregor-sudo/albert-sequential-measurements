/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectiveWordProbabilities
public import ReducedWords
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Direct finite Gram construction for the existing positive real star-functional
comparator. No Hilbert completion, faithfulness, trace or finite-dimensionality. -/

@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators

namespace AlgebraicProjectiveData
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem finiteFamily_gram_positive (M : AlgebraicProjectiveData ι A)
    {κ : Type*} [Fintype κ] (v : κ → A) :
    Matrix.PosSemidef (fun i j => M.state (star (v i) * v j)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change M.state (star (v j) * v i) = M.state (star (v i) * v j)
    simpa only [star_mul, star_star] using M.state_star (star (v i) * v j)
  · intro c
    have h : dotProduct (star c)
        (Matrix.mulVec ((fun i j => M.state (star (v i) * v j)) : Matrix κ κ ℝ) c) =
        M.state (star (∑ i, c i • v i) * (∑ j, c j • v j)) := by
      simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
        star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hs : M.state (star (v j) * v i) = M.state (star (v i) * v j) := by
        simpa only [star_mul, star_star] using M.state_star (star (v i) * v j)
      rw [hs]
      ring
    rw [h]
    exact M.state_positive _

theorem finiteGram {n : ℕ} (M : AlgebraicProjectiveData (Fin n) A) (L : ℕ) :
    Nonempty (FiniteGramWitness n L M.probability) := by
  classical
  let words := reducedWordsUpTo (Fin n) L
  refine ⟨{
    words := words
    complete := mem_reducedWordsUpTo L
    gram := fun u v => M.state
      (star (wordAmplitude M.projection u.val) * wordAmplitude M.projection v.val)
    positive := M.finiteFamily_gram_positive _
    normalized := M.probability_nil
    probabilities := fun w hw => ⟨M.probability_nonneg w, M.probability_le_one w⟩
    diagonal := fun _ => rfl
    complement := ?_
    orthogonal := ?_ }⟩
  · intro u v i hlen hred hy hn
    rw [wordAmplitude_append_singleton, wordAmplitude_append_singleton]
    rw [← map_add, ← mul_add, ← add_mul, algebraicOutcome_add_complement, one_mul]
  · intro u v i hu hv
    obtain ⟨u', hu'⟩ := List.getLast?_eq_some_iff.mp hu
    obtain ⟨v', hv'⟩ := List.getLast?_eq_some_iff.mp hv
    rw [hu', hv', wordAmplitude_append_singleton, wordAmplitude_append_singleton]
    have hop := algebraicOutcome_opposite_mul M.projection M.idempotent i false
    simp only [Bool.not_false] at hop
    have hzero :
        star (algebraicOutcome M.projection (i, true) * wordAmplitude M.projection u') *
          (algebraicOutcome M.projection (i, false) * wordAmplitude M.projection v') = 0 := by
      rw [star_mul, algebraicOutcome_star M.projection M.selfAdjoint]
      calc
        star (wordAmplitude M.projection u') * algebraicOutcome M.projection (i, true) *
            (algebraicOutcome M.projection (i, false) * wordAmplitude M.projection v') =
          star (wordAmplitude M.projection u') *
            (algebraicOutcome M.projection (i, true) * algebraicOutcome M.projection (i, false)) *
            wordAmplitude M.projection v' := by simp only [mul_assoc]
        _ = 0 := by rw [hop, mul_zero, zero_mul]
    rw [hzero, map_zero]

end AlgebraicProjectiveData
end AlbertSequential
