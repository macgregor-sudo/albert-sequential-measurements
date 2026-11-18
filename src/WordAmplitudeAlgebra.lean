/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PrimitiveResidualOccurrences

/-! Finite amplitude-polynomial operations for the actual telescope constructor.
These operations act on amplitudes, not products/stars of probability tables.
Chronological multiplication reverses the order of the concatenated words. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def multiplyWordAmplitudeTerms {ι : Type*} (a b : List (ℝ × Word ι)) : List (ℝ × Word ι) :=
  a.flatMap (fun x => b.map (fun y => (x.1 * y.1, y.2 ++ x.2)))

def starWordAmplitudeTerms {ι : Type*} (a : List (ℝ × Word ι)) : List (ℝ × Word ι) :=
  a.map (fun x => (x.1, x.2.reverse))

section AmplitudeTerms
variable {ι A : Type*} [Ring A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (P : ι → A)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem wordAmplitudeCombination_append (a b : List (ℝ × Word ι)) :
    wordAmplitudeCombination P (a ++ b) = wordAmplitudeCombination P a + wordAmplitudeCombination P b := by
  simp only [wordAmplitudeCombination, List.map_append, List.sum_append]

private theorem wordAmplitudeCombination_term_multiply (r : ℝ) (w : Word ι)
    (b : List (ℝ × Word ι)) :
    wordAmplitudeCombination P (b.map (fun y => (r * y.1, y.2 ++ w))) =
      (r • wordAmplitude P w) * wordAmplitudeCombination P b := by
  induction b with
  | nil => simp only [List.map_nil, wordAmplitudeCombination_nil, mul_zero]
  | cons y b ih =>
      rcases y with ⟨s, v⟩
      simp only [List.map_cons, wordAmplitudeCombination_cons, wordAmplitude_append,
        ih, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
      module

theorem wordAmplitudeCombination_multiply (a b : List (ℝ × Word ι)) :
    wordAmplitudeCombination P (multiplyWordAmplitudeTerms a b) =
      wordAmplitudeCombination P a * wordAmplitudeCombination P b := by
  induction a with
  | nil => simp only [multiplyWordAmplitudeTerms, List.flatMap_nil,
      wordAmplitudeCombination_nil, zero_mul]
  | cons x a ih =>
      rcases x with ⟨r, w⟩
      change wordAmplitudeCombination P
        ((b.map (fun y => (r * y.1, y.2 ++ w))) ++ multiplyWordAmplitudeTerms a b) = _
      rw [wordAmplitudeCombination_append, wordAmplitudeCombination_term_multiply, ih,
        wordAmplitudeCombination_cons, add_mul]

end AmplitudeTerms

section StarTerms
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A] [StarModule ℝ A]
  (P : ι → A) (hstar : ∀ i, star (P i) = P i)

include hstar in
theorem wordAmplitudeCombination_star (a : List (ℝ × Word ι)) :
    wordAmplitudeCombination P (starWordAmplitudeTerms a) = star (wordAmplitudeCombination P a) := by
  induction a with
  | nil => simp only [starWordAmplitudeTerms, List.map_nil, wordAmplitudeCombination_nil, star_zero]
  | cons x a ih =>
      rcases x with ⟨r, w⟩
      change wordAmplitudeCombination P ((r, w.reverse) :: starWordAmplitudeTerms a) = _
      simp only [wordAmplitudeCombination_cons, wordAmplitude_reverse P hstar,
        ih, star_add, star_smul, star_trivial]

end StarTerms

namespace FiniteRealWordFunctional
variable {n : ℕ}

def amplitudeWord (w : Word (Fin n)) : FiniteRealWordFunctional n := ⟨[(1, w)]⟩
def amplitudeMultiply (a b : FiniteRealWordFunctional n) : FiniteRealWordFunctional n :=
  ⟨multiplyWordAmplitudeTerms a.terms b.terms⟩
def amplitudeStar (a : FiniteRealWordFunctional n) : FiniteRealWordFunctional n :=
  ⟨starWordAmplitudeTerms a.terms⟩

theorem amplitudeValue_word {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (w : Word (Fin n)) : (amplitudeWord w).amplitudeValue P = wordAmplitude P w := by
  simp only [amplitudeWord, amplitudeValue, wordAmplitudeCombination,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]

theorem amplitudeValue_emptyWordTerm {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (r : ℝ) : (emptyWordTerm r : FiniteRealWordFunctional n).amplitudeValue P = r • (1 : A) := by
  simp only [emptyWordTerm, amplitudeValue, wordAmplitudeCombination,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wordAmplitude_nil, add_zero]

theorem amplitudeValue_append {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (a b : FiniteRealWordFunctional n) :
    (append a b).amplitudeValue P = a.amplitudeValue P + b.amplitudeValue P :=
  wordAmplitudeCombination_append P a.terms b.terms

theorem amplitudeValue_multiply {A : Type*} [Ring A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (P : Fin n → A) (a b : FiniteRealWordFunctional n) :
    (amplitudeMultiply a b).amplitudeValue P = a.amplitudeValue P * b.amplitudeValue P :=
  wordAmplitudeCombination_multiply P a.terms b.terms

theorem amplitudeValue_star {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [StarModule ℝ A]
    (P : Fin n → A) (hstar : ∀ i, star (P i) = P i) (a : FiniteRealWordFunctional n) :
    (amplitudeStar a).amplitudeValue P = star (a.amplitudeValue P) :=
  wordAmplitudeCombination_star P hstar a.terms

end FiniteRealWordFunctional
end AlbertSequential
