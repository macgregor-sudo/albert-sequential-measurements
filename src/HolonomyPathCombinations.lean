/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HolonomyPaths

/-! Actual finite right-path combinations for the constructor. The depth bound
is structural: each generator/skew action adds exactly one path entry. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

namespace FiniteRealWordFunctional
theorem amplitudeValue_combine {n : ℕ} {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (cs : List (FiniteRealWordFunctional n)) :
    (combine cs).amplitudeValue P = (cs.map (fun c => c.amplitudeValue P)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change (append c (combine cs)).amplitudeValue P = _
      rw [amplitudeValue_append, ih]
      rfl
end FiniteRealWordFunctional

namespace HolonomyPath
abbrev Combination := List (ℝ × List (Fin 6))

def baseCombination : Combination := [(1, [])]
def combinationPolynomial (d : CornerNumericalData) (e : Combination) : FiniteRealWordFunctional 4 :=
  FiniteRealWordFunctional.combine
    (e.map (fun t => FiniteRealWordFunctional.scale t.1 (polynomial d t.2)))
def combinationValue {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin 4 → A) (d : CornerNumericalData) (e : Combination) : A :=
  (combinationPolynomial d e).amplitudeValue P
def scaleCombination (r : ℝ) (e : Combination) : Combination :=
  e.map (fun t => (r * t.1, t.2))
def generatorAction (a : Fin 6) (e : Combination) : Combination :=
  e.map (fun t => (t.1, a :: t.2))
def skewAction (i : Fin 3) (e : Combination) : Combination :=
  scaleCombination (1 / 2) (generatorAction (positiveIndex i) e) ++
    scaleCombination (-(1 / 2)) (generatorAction (negativeIndex i) e)
def HasDepth (e : Combination) (d : ℕ) : Prop := ∀ t ∈ e, t.2.length ≤ d

section Values
variable {A : Type*} [Ring A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  (P : Fin 4 → A) (d : CornerNumericalData)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem combinationValue_nil : combinationValue P d [] = 0 := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem combinationValue_cons (r : ℝ) (p : List (Fin 6)) (e : Combination) :
    combinationValue P d ((r, p) :: e) =
      r • (polynomial d p).amplitudeValue P + combinationValue P d e := by
  simp only [combinationValue, combinationPolynomial, List.map_cons,
    FiniteRealWordFunctional.amplitudeValue_combine, List.sum_cons, List.map_map,
    Function.comp_def, FiniteRealWordFunctional.amplitudeValue_scale]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem combinationValue_append (e f : Combination) :
    combinationValue P d (e ++ f) = combinationValue P d e + combinationValue P d f := by
  simp only [combinationValue, combinationPolynomial, List.map_append,
    FiniteRealWordFunctional.amplitudeValue_combine, List.sum_append]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem combinationValue_scale (r : ℝ) (e : Combination) :
    combinationValue P d (scaleCombination r e) = r • combinationValue P d e := by
  induction e with
  | nil => simp only [scaleCombination, List.map_nil, combinationValue_nil, smul_zero]
  | cons t e ih =>
      rcases t with ⟨s, p⟩
      simp only [scaleCombination, List.map_cons, combinationValue_cons] at ih ⊢
      rw [ih, mul_smul, smul_add]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem combinationValue_base : combinationValue P d baseCombination = P 0 := by
  simp only [baseCombination, combinationValue_cons, combinationValue_nil, polynomial_value,
    coefficient, word, wordAmplitude_singleton, algebraicOutcome, ite_true, one_smul, add_zero]

theorem polynomial_cons_value (hp : ∀ i, P i * P i = P i) (a : Fin 6) (p : List (Fin 6)) :
    (polynomial d (a :: p)).amplitudeValue P =
      generatorOperator P d a * (polynomial d p).amplitudeValue P := by
  rw [polynomial_evaluates_operator P hp, operator, ← polynomial_evaluates_operator P hp d p]

theorem combinationValue_generatorAction (hp : ∀ i, P i * P i = P i)
    (a : Fin 6) (e : Combination) :
    combinationValue P d (generatorAction a e) =
      generatorOperator P d a * combinationValue P d e := by
  induction e with
  | nil => simp only [generatorAction, List.map_nil, combinationValue_nil, mul_zero]
  | cons t e ih =>
      rcases t with ⟨r, p⟩
      simp only [generatorAction, List.map_cons, combinationValue_cons] at ih ⊢
      rw [polynomial_cons_value P d hp, ih, mul_add, mul_smul_comm]

omit [IsScalarTower ℝ A A] in
theorem polynomial_supported (hp : ∀ i, P i * P i = P i) (p : List (Fin 6)) :
    P 0 * (polynomial d p).amplitudeValue P = (polynomial d p).amplitudeValue P := by
  rw [polynomial_value, mul_smul_comm, amplitude_supported P hp]

omit [IsScalarTower ℝ A A] in
theorem combinationValue_supported (hp : ∀ i, P i * P i = P i) (e : Combination) :
    P 0 * combinationValue P d e = combinationValue P d e := by
  induction e with
  | nil => simp only [combinationValue_nil, mul_zero]
  | cons t e ih =>
      rcases t with ⟨r, p⟩
      rw [combinationValue_cons, mul_add, mul_smul_comm, polynomial_supported P d hp, ih]

end Values

theorem combinationValue_skewAction {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (d : CornerNumericalData) (i : Fin 3) (e : Combination) :
    combinationValue P d (skewAction i e) =
      CornerHolonomy.skewHermitianPart
        (CornerHolonomy.normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) *
          combinationValue P d e := by
  simp only [skewAction, combinationValue_append, combinationValue_scale,
    combinationValue_generatorAction P d hp, generator_positive, generator_negative P hstar,
    CornerHolonomy.skewHermitianPart, smul_mul_assoc, sub_mul, smul_sub]
  module

theorem baseCombination_hasDepth : HasDepth baseCombination 0 := by
  intro t ht
  have ht' : t = (1, []) := List.mem_singleton.mp ht
  rw [ht']
  exact le_refl _

theorem hasDepth_append (e f : Combination) (d : ℕ)
    (he : HasDepth e d) (hf : HasDepth f d) : HasDepth (e ++ f) d := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact he t h
  · exact hf t h

theorem hasDepth_scale (r : ℝ) (e : Combination) (d : ℕ) (h : HasDepth e d) :
    HasDepth (scaleCombination r e) d := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact h u hu

theorem hasDepth_generatorAction (a : Fin 6) (e : Combination) (d : ℕ) (h : HasDepth e d) :
    HasDepth (generatorAction a e) (d + 1) := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact Nat.succ_le_succ (h u hu)

theorem hasDepth_skewAction (i : Fin 3) (e : Combination) (d : ℕ) (h : HasDepth e d) :
    HasDepth (skewAction i e) (d + 1) :=
  hasDepth_append _ _ _
    (hasDepth_scale _ _ _ (hasDepth_generatorAction _ _ _ h))
    (hasDepth_scale _ _ _ (hasDepth_generatorAction _ _ _ h))

theorem twoGenerator_base_hasDepth (a b : Fin 6) :
    HasDepth (generatorAction a (generatorAction b baseCombination)) 2 :=
  hasDepth_generatorAction _ _ _ (hasDepth_generatorAction _ _ _ baseCombination_hasDepth)

theorem twoSkew_base_hasDepth (i j : Fin 3) :
    HasDepth (skewAction i (skewAction j baseCombination)) 2 :=
  hasDepth_skewAction _ _ _ (hasDepth_skewAction _ _ _ baseCombination_hasDepth)

end HolonomyPath
end AlbertSequential
