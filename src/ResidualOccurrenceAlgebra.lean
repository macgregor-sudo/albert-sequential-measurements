/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PurityVectorExpressions

/-! Actual scalar residual-list operations. Real coefficients move into the
left amplitude, with their signs and repeated occurrences retained. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace ResidualOccurrenceExpression
variable {n : ℕ}

def value {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (φ : A →ₗ[ℝ] ℝ) (P : Fin n → A) (es : List (ResidualTelescopeOccurrence n)) : ℝ :=
  (es.map (fun o => φ (star (o.leftElement P) * o.leaf.residualElement P))).sum

def scale (r : ℝ) (es : List (ResidualTelescopeOccurrence n)) : List (ResidualTelescopeOccurrence n) :=
  es.map (fun o => { o with leftTerms := FiniteRealWordFunctional.scale r o.leftTerms })

def combine (ess : List (List (ResidualTelescopeOccurrence n))) : List (ResidualTelescopeOccurrence n) :=
  ess.flatten

def HasHorizon (es : List (ResidualTelescopeOccurrence n)) (L : ℕ) : Prop :=
  ∀ o ∈ es, o.leaf.wordFunctional.HasHorizon L

section Values
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ) (P : Fin n → A)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem value_nil : value φ P [] = 0 := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem value_append (es fs : List (ResidualTelescopeOccurrence n)) :
    value φ P (es ++ fs) = value φ P es + value φ P fs := by
  simp only [value, List.map_append, List.sum_append]

omit [SMulCommClass ℝ A A] in
theorem value_scale (r : ℝ) (es : List (ResidualTelescopeOccurrence n)) :
    value φ P (scale r es) = r * value φ P es := by
  induction es with
  | nil => simp only [scale, List.map_nil, value_nil, mul_zero]
  | cons o es ih =>
      simp only [scale, List.map_cons, value, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [ResidualTelescopeOccurrence.leftElement,
        FiniteRealWordFunctional.amplitudeValue_scale, star_smul, star_trivial,
        smul_mul_assoc, map_smul, smul_eq_mul]
      ring

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem value_combine (ess : List (List (ResidualTelescopeOccurrence n))) :
    value φ P (combine ess) = (ess.map (value φ P)).sum := by
  induction ess with
  | nil => rfl
  | cons es ess ih =>
      change value φ P (es ++ combine ess) = _
      rw [value_append, ih]
      rfl

theorem value_pairAgainst (hstar : ∀ i, star (P i) = P i)
    (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    value φ P (PurityVectorExpression.pairAgainst U e) =
      realStarPairing φ (U.amplitudeValue P) (PurityVectorExpression.evaluate P e) :=
  (PurityVectorExpression.pairAgainst_evaluate φ P hstar U e).symm

end Values

theorem hasHorizon_scale (es : List (ResidualTelescopeOccurrence n)) (r : ℝ) (L : ℕ)
    (he : HasHorizon es L) : HasHorizon (scale r es) L := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  exact he u hu

theorem hasHorizon_combine (ess : List (List (ResidualTelescopeOccurrence n))) (L : ℕ)
    (he : ∀ es ∈ ess, HasHorizon es L) : HasHorizon (combine ess) L := by
  intro o ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  exact he es hes o ho

theorem hasHorizon_pairAgainst (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n)
    (L : ℕ) (he : e.HasHorizon L) : HasHorizon (PurityVectorExpression.pairAgainst U e) L :=
  PurityVectorExpression.hasHorizon_pairAgainst U e L he

end ResidualOccurrenceExpression
end AlbertSequential
