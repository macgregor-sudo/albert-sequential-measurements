/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerNumericalData
public import WordAmplitudeAlgebra

/-! Actual right histories for h0,h1,h2 and their adjoints. A path's first
entry is the newest left multiplier. Each block contributes three letters;
the shared yes-0 at joins is removed by a proved amplitude identity. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace HolonomyPath

def firstLabel : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 1]
def secondLabel : Fin 6 → Fin 4 := ![2, 3, 1, 1, 2, 3]
def normalizerIndex : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]
def positiveIndex (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩
def negativeIndex (i : Fin 3) : Fin 6 := ⟨i.val + 3, by omega⟩

def word : List (Fin 6) → Word (Fin 4)
  | [] => [(0, true)]
  | a :: p => word p ++ [(secondLabel a, true), (firstLabel a, true), (0, true)]

def historyPrefix : List (Fin 6) → Word (Fin 4)
  | [] => []
  | a :: p => word p ++ [(secondLabel a, true), (firstLabel a, true)]

def coefficient (d : CornerNumericalData) : List (Fin 6) → ℝ
  | [] => 1
  | a :: p => (d.normalizer (normalizerIndex a))⁻¹ * coefficient d p

def polynomial (d : CornerNumericalData) (p : List (Fin 6)) : FiniteRealWordFunctional 4 :=
  ⟨[(coefficient d p, word p)]⟩

theorem word_eq_prefix (p : List (Fin 6)) : word p = historyPrefix p ++ [(0, true)] := by
  cases p with
  | nil => rfl
  | cons a p => rw [word, historyPrefix, List.append_assoc]; rfl

theorem word_length (p : List (Fin 6)) : (word p).length = 1 + 3 * p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [word, List.length_append, List.length_cons, List.length_nil, ih]
      omega

theorem prefix_length (p : List (Fin 6)) : (historyPrefix p).length = 3 * p.length := by
  have h := congrArg List.length (word_eq_prefix p)
  rw [word_length] at h
  simp only [List.length_append, List.length_singleton] at h
  omega

theorem word_nonempty (p : List (Fin 6)) : word p ≠ [] := by
  intro h
  have hh := word_length p
  rw [h, List.length_nil] at hh
  omega

section Operators
variable {A : Type*} [Ring A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

def generatorOperator (P : Fin 4 → A) (d : CornerNumericalData) (a : Fin 6) : A :=
  CornerHolonomy.normalizedCornerWord (P 0) (P (firstLabel a)) (P (secondLabel a))
    (d.normalizer (normalizerIndex a))

def operator (P : Fin 4 → A) (d : CornerNumericalData) : List (Fin 6) → A
  | [] => P 0
  | a :: p => generatorOperator P d a * operator P d p

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem amplitude_supported (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (p : List (Fin 6)) :
    P 0 * wordAmplitude P (word p) = wordAmplitude P (word p) := by
  rw [word_eq_prefix, wordAmplitude_append_singleton]
  change P 0 * (P 0 * wordAmplitude P (historyPrefix p)) = _
  rw [← mul_assoc, hp 0]
  simp only [algebraicOutcome, ite_true]

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem amplitude_cons (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i)
    (a : Fin 6) (p : List (Fin 6)) :
    wordAmplitude P (word (a :: p)) =
      (P 0 * P (firstLabel a) * P (secondLabel a) * P 0) * wordAmplitude P (word p) := by
  rw [word, wordAmplitude_append]
  simp only [wordAmplitude_cons, wordAmplitude_nil, algebraicOutcome, ite_true, one_mul, mul_assoc]
  rw [amplitude_supported P hp p]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem polynomial_value (P : Fin 4 → A) (d : CornerNumericalData) (p : List (Fin 6)) :
    (polynomial d p).amplitudeValue P = coefficient d p • wordAmplitude P (word p) := by
  simp only [polynomial, FiniteRealWordFunctional.amplitudeValue, wordAmplitudeCombination,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem polynomial_evaluates_operator (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i)
    (d : CornerNumericalData) (p : List (Fin 6)) :
    (polynomial d p).amplitudeValue P = operator P d p := by
  induction p with
  | nil =>
      simp only [polynomial_value, coefficient, word, operator, wordAmplitude_singleton,
        algebraicOutcome, ite_true, one_smul]
  | cons a p ih =>
      rw [polynomial_value, coefficient, amplitude_cons P hp, operator, ← ih, polynomial_value]
      simp only [generatorOperator, CornerHolonomy.normalizedCornerWord,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      module

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem generator_positive (P : Fin 4 → A) (d : CornerNumericalData) (i : Fin 3) :
    generatorOperator P d (positiveIndex i) =
      CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i := by
  fin_cases i <;> rfl

end Operators

theorem generator_negative {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [StarModule ℝ A]
    (P : Fin 4 → A) (hstar : ∀ i, star (P i) = P i) (d : CornerNumericalData) (i : Fin 3) :
    generatorOperator P d (negativeIndex i) =
      star (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) := by
  fin_cases i <;>
    simp [negativeIndex, generatorOperator, firstLabel, secondLabel, normalizerIndex,
      CornerNumericalData.normalizer, CornerHolonomy.normalizedCyclicHolonomies,
      CornerHolonomy.normalizedCornerWord, star_smul, star_mul, hstar, mul_assoc]

end HolonomyPath
end AlbertSequential
