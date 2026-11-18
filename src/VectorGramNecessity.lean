/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteGramModel
public import ReducedWords
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Finite Gram necessity for actual real vector-state projective data.
No completion or faithfulness assumption enters this direction. -/

@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators

theorem realVectorGram_positive {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) :
    Matrix.PosSemidef (fun i j => inner ℝ (v i) (v j)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    exact real_inner_comm _ _
  · intro c
    have h : dotProduct (star c)
        (Matrix.mulVec ((fun i j => inner ℝ (v i) (v j)) : Matrix ι ι ℝ) c) =
        inner ℝ (∑ i, c i • v i) (∑ j, c j • v j) := by
      simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
        Finset.mul_sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_comm (v j) (v i)]
      ring
    rw [h]
    exact real_inner_self_nonneg

namespace RealVectorProjectiveData
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complementary_inner_sum (M : RealVectorProjectiveData ι E) (i : ι) (x : E) :
    inner ℝ (M.projection i x) (M.projection i x) +
      inner ℝ (x - M.projection i x) (x - M.projection i x) = inner ℝ x x := by
  have hPP : inner ℝ (M.projection i x) (M.projection i x) =
      inner ℝ x (M.projection i x) := by
    rw [M.symmetric, M.idempotent]
  simp only [inner_sub_left, inner_sub_right]
  rw [hPP, real_inner_comm (M.projection i x) x]
  ring

theorem outcome_inner_le (M : RealVectorProjectiveData ι E) (a : Outcome ι) (x : E) :
    inner ℝ (M.outcome a x) (M.outcome a x) ≤ inner ℝ x x := by
  have hsum := M.complementary_inner_sum a.1 x
  have hP := real_inner_self_nonneg (x := M.projection a.1 x)
  have hQ := real_inner_self_nonneg (x := x - M.projection a.1 x)
  rcases a with ⟨i, b⟩
  cases b <;> simp only [outcome, Bool.false_eq_true, ↓reduceIte,
    LinearMap.sub_apply, LinearMap.id_apply] <;> linarith

theorem probability_nonneg (M : RealVectorProjectiveData ι E) (w : Word ι) :
    0 ≤ M.probability w := real_inner_self_nonneg

theorem probability_le_one (M : RealVectorProjectiveData ι E) (w : Word ι) :
    M.probability w ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil => rw [M.probability_nil]
  | append_singleton w a ih =>
    unfold probability
    rw [M.branchVector_append_singleton]
    exact (M.outcome_inner_le a _).trans ih

theorem inner_yes_no (M : RealVectorProjectiveData ι E) (i : ι) (x y : E) :
    inner ℝ (M.outcome (i, true) x) (M.outcome (i, false) y) = 0 := by
  change inner ℝ (M.projection i x) (y - M.projection i y) = 0
  rw [inner_sub_right, M.symmetric, M.symmetric, M.idempotent, sub_self]

theorem finiteGram {n : ℕ} (M : RealVectorProjectiveData (Fin n) E) (L : ℕ) :
    Nonempty (FiniteGramWitness n L M.probability) := by
  classical
  let words := reducedWordsUpTo (Fin n) L
  refine ⟨{
    words := words
    complete := mem_reducedWordsUpTo L
    gram := fun u v => inner ℝ (M.branchVector u.val) (M.branchVector v.val)
    positive := realVectorGram_positive _
    normalized := M.probability_nil
    probabilities := fun w hw => ⟨M.probability_nonneg w, M.probability_le_one w⟩
    diagonal := fun _ => rfl
    complement := ?_
    orthogonal := ?_ }⟩
  · intro u v i hlen hred hy hn
    rw [M.branchVector_append_singleton, M.branchVector_append_singleton]
    simp only [outcome, Bool.false_eq_true, ↓reduceIte,
      LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right]
    ring
  · intro u v i hu hv
    obtain ⟨u', hu'⟩ := List.getLast?_eq_some_iff.mp hu
    obtain ⟨v', hv'⟩ := List.getLast?_eq_some_iff.mp hv
    rw [hu', hv', M.branchVector_append_singleton, M.branchVector_append_singleton]
    exact M.inner_yes_no i _ _

end RealVectorProjectiveData
end AlbertSequential
