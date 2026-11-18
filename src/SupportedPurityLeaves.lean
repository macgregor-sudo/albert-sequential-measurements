/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PurityResiduals
public import Interfaces.SeparationAndConverse

/-! Actual three measured words for a supported purity occurrence. The stored
prefix makes the full right history end in its base outcome by construction.
Longer left coefficient words are not part of this measured support. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure SupportedPurityLeaf (ι : Type*) where
  historyPrefix : Word ι
  outcome : Outcome ι
  suffix : Word ι
  constant : ℝ

namespace SupportedPurityLeaf
variable {ι : Type*} (l : SupportedPurityLeaf ι)

def history : Word ι := l.historyPrefix ++ [l.outcome]
def shortWord : Word ι := l.history
def middleWord : Word ι := l.history ++ l.suffix
def longWord : Word ι :=
  match l.suffix with
  | [] => l.history
  | _ :: _ => l.history ++ l.suffix ++ purityMirror l.suffix ++ [l.outcome]

def residualElement {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : ι → A) : A :=
  outcomePurityElement P l.outcome l.suffix l.constant * wordAmplitude P l.history

theorem shortWord_length : l.shortWord.length = l.history.length := rfl
theorem middleWord_length : l.middleWord.length = l.history.length + l.suffix.length :=
  List.length_append

theorem longWord_length_le : l.longWord.length ≤ l.history.length + 2 * l.suffix.length := by
  cases hv : l.suffix with
  | nil => simp only [longWord, hv, List.length_nil, mul_zero, Nat.add_zero, le_refl]
  | cons a v =>
      simp only [longWord, hv, List.length_append, List.length_reverse,
        purityMirror, List.length_dropLast, List.length_cons, List.length_nil]
      omega

theorem middleWord_length_le : l.middleWord.length ≤ l.history.length + 2 * l.suffix.length := by
  rw [middleWord_length]
  omega

theorem shortWord_length_le : l.shortWord.length ≤ l.history.length + 2 * l.suffix.length := by
  rw [shortWord_length]
  exact Nat.le_add_right _ _

theorem collapse_base_probability {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    M.probability (l.history ++ [l.outcome] ++ w) = M.probability (l.history ++ w) := by
  simpa only [history, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    M.probability_repeat_context l.historyPrefix w l.outcome

theorem long_probability {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) :
    M.probability (l.history ++ [l.outcome] ++ l.suffix ++
      purityMirror l.suffix ++ [l.outcome]) = M.probability l.longWord := by
  cases hv : l.suffix with
  | nil =>
      simp only [hv, purityMirror, List.dropLast_nil, List.reverse_nil,
        List.append_nil, longWord]
      calc
        M.probability (l.history ++ [l.outcome] ++ [l.outcome]) =
            M.probability (l.history ++ [l.outcome]) := l.collapse_base_probability M _
        _ = M.probability l.history := by
          simpa only [List.append_nil] using l.collapse_base_probability M []
  | cons a v =>
      simpa only [longWord, hv, List.append_assoc] using
        l.collapse_base_probability M ((a :: v) ++ purityMirror (a :: v) ++ [l.outcome])

theorem residual_threeHistories {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) :
    M.squareMass (l.residualElement M.projection) =
      M.probability l.longWord - 2 * l.constant * M.probability l.middleWord +
      l.constant ^ 2 * M.probability l.shortWord := by
  have h := purityResidual_threeHistories M l.outcome l.suffix l.history l.constant
  rw [l.long_probability M, l.collapse_base_probability M l.suffix] at h
  have hshort : M.probability (l.history ++ [l.outcome]) = M.probability l.history := by
    simpa only [List.append_nil] using l.collapse_base_probability M []
  rw [hshort] at h
  exact h

end SupportedPurityLeaf

namespace SupportedPurityLeaf
variable {n : ℕ} (l : SupportedPurityLeaf (Fin n))

def wordFunctional : FiniteRealWordFunctional n where
  terms := [(1, l.longWord), (-2 * l.constant, l.middleWord), (l.constant ^ 2, l.shortWord)]

theorem wordFunctional_evaluate (f : Word (Fin n) → ℝ) :
    l.wordFunctional.evaluate f =
      f l.longWord - 2 * l.constant * f l.middleWord + l.constant ^ 2 * f l.shortWord := by
  simp only [wordFunctional, FiniteRealWordFunctional.evaluate, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_mul]
  ring

theorem wordFunctional_hasHorizon (L : ℕ) (h : l.history.length + 2 * l.suffix.length ≤ L) :
    l.wordFunctional.HasHorizon L := by
  intro t ht
  simp only [wordFunctional, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact l.longWord_length_le.trans h
  · exact l.middleWord_length_le.trans h
  · exact l.shortWord_length_le.trans h

theorem residual_eq_wordFunctional {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) :
    M.squareMass (l.residualElement M.projection) = l.wordFunctional.evaluate M.probability := by
  rw [wordFunctional_evaluate]
  exact l.residual_threeHistories M

theorem wordFunctional_nonnegative {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) : 0 ≤ l.wordFunctional.evaluate M.probability := by
  rw [← l.residual_eq_wordFunctional M]
  exact M.squareMass_nonneg _

end SupportedPurityLeaf
end AlbertSequential
