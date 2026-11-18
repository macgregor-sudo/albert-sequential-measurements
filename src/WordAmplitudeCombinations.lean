/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectiveWordProbabilities
public import PositiveFunctionalNull
public import Interfaces.SeparationAndConverse
public import Mathlib.Tactic.Linarith

/-! Explicit finite combinations of genuine word amplitudes and their universal
coefficient bounds. The raw coefficient bound is not a merged functional norm. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def wordAmplitudeCombination {ι A : Type*} [Ring A] [Module ℝ A]
    (P : ι → A) (c : List (ℝ × Word ι)) : A :=
  (c.map (fun t => t.1 • wordAmplitude P t.2)).sum

def wordAmplitudeCoefficientBound {ι : Type*} (c : List (ℝ × Word ι)) : ℝ :=
  (c.map (fun t => |t.1|)).sum

theorem wordAmplitudeCombination_nil {ι A : Type*} [Ring A] [Module ℝ A] (P : ι → A) :
    wordAmplitudeCombination P [] = 0 := rfl

theorem wordAmplitudeCombination_cons {ι A : Type*} [Ring A] [Module ℝ A]
    (P : ι → A) (r : ℝ) (w : Word ι) (c : List (ℝ × Word ι)) :
    wordAmplitudeCombination P ((r, w) :: c) =
      r • wordAmplitude P w + wordAmplitudeCombination P c := rfl

theorem wordAmplitudeCoefficientBound_nil {ι : Type*} :
    wordAmplitudeCoefficientBound ([] : List (ℝ × Word ι)) = 0 := rfl

theorem wordAmplitudeCoefficientBound_cons {ι : Type*}
    (r : ℝ) (w : Word ι) (c : List (ℝ × Word ι)) :
    wordAmplitudeCoefficientBound ((r, w) :: c) = |r| + wordAmplitudeCoefficientBound c := rfl

theorem wordAmplitudeCoefficientBound_nonneg {ι : Type*} (c : List (ℝ × Word ι)) :
    0 ≤ wordAmplitudeCoefficientBound c := by
  induction c with
  | nil => exact le_refl _
  | cons t c ih => exact add_nonneg (abs_nonneg t.1) ih

namespace AlgebraicProjectiveData
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (M : AlgebraicProjectiveData ι A)

theorem pair_abs_le_one_of_squareMass_le_one (x y : A)
    (hx : M.squareMass x ≤ 1) (hy : M.squareMass y ≤ 1) :
    |M.state (star x * y)| ≤ 1 := by
  have hp := M.state_positive (x + y)
  have hm := M.state_positive ((-1 : ℝ) • x + y)
  have hep := positiveForm_expansion M.state M.state_star x y 1
  have hem := positiveForm_expansion M.state M.state_star x y (-1)
  simp only [one_smul, one_pow, one_mul] at hep
  norm_num only [neg_one_sq, neg_mul, one_mul] at hem
  rw [hep] at hp
  rw [hem] at hm
  change M.state (star x * x) ≤ 1 at hx
  change M.state (star y * y) ≤ 1 at hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem wordAmplitude_squareMass_le_one (w : Word ι) :
    M.squareMass (wordAmplitude M.projection w) ≤ 1 := by
  simpa only [mul_one, M.squareMass_one] using M.squareMass_word_le w 1

theorem wordAmplitude_pair_abs_le_one (u v : Word ι) :
    |M.state (star (wordAmplitude M.projection u) * wordAmplitude M.projection v)| ≤ 1 :=
  M.pair_abs_le_one_of_squareMass_le_one _ _
    (M.wordAmplitude_squareMass_le_one u) (M.wordAmplitude_squareMass_le_one v)

theorem amplitudeCombination_word_pair_bound (c : List (ℝ × Word ι)) (v : Word ι) :
    |M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| ≤
      wordAmplitudeCoefficientBound c := by
  induction c with
  | nil => simp only [wordAmplitudeCombination_nil, star_zero, zero_mul, map_zero,
      abs_zero, wordAmplitudeCoefficientBound_nil, le_refl]
  | cons t c ih =>
      rcases t with ⟨r, u⟩
      rw [wordAmplitudeCombination_cons, wordAmplitudeCoefficientBound_cons]
      simp only [star_add, star_smul, star_trivial, add_mul, smul_mul_assoc,
        map_add, map_smul, smul_eq_mul]
      calc
        |r * M.state (star (wordAmplitude M.projection u) * wordAmplitude M.projection v) +
            M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| ≤
            |r * M.state (star (wordAmplitude M.projection u) * wordAmplitude M.projection v)| +
              |M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| :=
          abs_add_le _ _
        _ = |r| * |M.state (star (wordAmplitude M.projection u) * wordAmplitude M.projection v)| +
              |M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| := by
          rw [abs_mul]
        _ ≤ |r| * 1 + wordAmplitudeCoefficientBound c :=
          add_le_add (mul_le_mul_of_nonneg_left (M.wordAmplitude_pair_abs_le_one u v) (abs_nonneg r)) ih
        _ = _ := by ring

theorem amplitudeCombination_pair_bound (c d : List (ℝ × Word ι)) :
    |M.state (star (wordAmplitudeCombination M.projection c) *
      wordAmplitudeCombination M.projection d)| ≤
      wordAmplitudeCoefficientBound c * wordAmplitudeCoefficientBound d := by
  induction d with
  | nil => simp only [wordAmplitudeCombination_nil, mul_zero, map_zero,
      abs_zero, wordAmplitudeCoefficientBound_nil, le_refl]
  | cons t d ih =>
      rcases t with ⟨r, v⟩
      rw [wordAmplitudeCombination_cons, wordAmplitudeCoefficientBound_cons]
      simp only [mul_add, mul_smul_comm, map_add, map_smul, smul_eq_mul]
      calc
        |r * M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v) +
            M.state (star (wordAmplitudeCombination M.projection c) *
              wordAmplitudeCombination M.projection d)| ≤
            |r * M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| +
              |M.state (star (wordAmplitudeCombination M.projection c) *
                wordAmplitudeCombination M.projection d)| := abs_add_le _ _
        _ = |r| * |M.state (star (wordAmplitudeCombination M.projection c) * wordAmplitude M.projection v)| +
              |M.state (star (wordAmplitudeCombination M.projection c) *
                wordAmplitudeCombination M.projection d)| := by rw [abs_mul]
        _ ≤ |r| * wordAmplitudeCoefficientBound c +
              wordAmplitudeCoefficientBound c * wordAmplitudeCoefficientBound d :=
          add_le_add (mul_le_mul_of_nonneg_left (M.amplitudeCombination_word_pair_bound c v) (abs_nonneg r)) ih
        _ = _ := by ring

theorem amplitudeCombination_squareMass_bound (c : List (ℝ × Word ι)) :
    M.squareMass (wordAmplitudeCombination M.projection c) ≤
      wordAmplitudeCoefficientBound c ^ 2 := by
  change M.state (star (wordAmplitudeCombination M.projection c) *
    wordAmplitudeCombination M.projection c) ≤ _
  exact (le_abs_self _).trans (by simpa only [pow_two] using M.amplitudeCombination_pair_bound c c)

end AlgebraicProjectiveData

namespace FiniteRealWordFunctional
variable {n : ℕ}

/-- Coefficients here act on amplitudes, distinct from probability evaluation. -/
def amplitudeValue {A : Type*} [Ring A] [Module ℝ A]
    (c : FiniteRealWordFunctional n) (P : Fin n → A) : A :=
  wordAmplitudeCombination P c.terms

/-- Conservative bound of the supplied amplitude expansion, retaining repeats. -/
def rawCoefficientBound (c : FiniteRealWordFunctional n) : ℝ :=
  wordAmplitudeCoefficientBound c.terms

theorem rawCoefficientBound_nonneg (c : FiniteRealWordFunctional n) :
    0 ≤ c.rawCoefficientBound := wordAmplitudeCoefficientBound_nonneg _

end FiniteRealWordFunctional
end AlbertSequential
