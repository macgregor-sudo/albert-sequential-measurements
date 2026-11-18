/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WordAmplitudeAlgebra
public import CliffordDefectData

/-! Finite residual-vector syntax for the actual telescope constructor.
The multiplier acts as L*r; pairing conversion uses star(L)*U as its left
vector. No record field assumes a telescope identity or vanishing residual. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

structure PurityVectorTerm (n : ℕ) where
  multiplier : FiniteRealWordFunctional n
  leaf : SupportedPurityLeaf (Fin n)

abbrev PurityVectorExpression (n : ℕ) := List (PurityVectorTerm n)

namespace PurityVectorExpression
variable {n : ℕ}

def evaluate {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : Fin n → A) (e : PurityVectorExpression n) : A :=
  (e.map (fun t => t.multiplier.amplitudeValue P * t.leaf.residualElement P)).sum

def scale (r : ℝ) (e : PurityVectorExpression n) : PurityVectorExpression n :=
  e.map (fun t => ⟨FiniteRealWordFunctional.scale r t.multiplier, t.leaf⟩)

def leftMultiply (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    PurityVectorExpression n :=
  e.map (fun t => ⟨FiniteRealWordFunctional.amplitudeMultiply U t.multiplier, t.leaf⟩)

def pairAgainst (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    List (ResidualTelescopeOccurrence n) :=
  e.map (fun t =>
    { leaf := t.leaf
      leftTerms := FiniteRealWordFunctional.amplitudeMultiply
        (FiniteRealWordFunctional.amplitudeStar t.multiplier) U })

def ofPrimitiveTerms (a : Fin n) (c : Word (Fin n) → ℝ)
    (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (U : FiniteRealWordFunctional n) : PurityVectorExpression n :=
  (primitiveResidualOccurrences a c ts historyPrefix U).map (fun o => ⟨o.leftTerms, o.leaf⟩)

def HasHorizon (e : PurityVectorExpression n) (L : ℕ) : Prop :=
  ∀ t ∈ e, t.leaf.wordFunctional.HasHorizon L

section Semantics
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (P : Fin n → A)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluate_nil : evaluate P [] = 0 := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluate_cons (t : PurityVectorTerm n) (e : PurityVectorExpression n) :
    evaluate P (t :: e) = t.multiplier.amplitudeValue P * t.leaf.residualElement P + evaluate P e := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem evaluate_append (e f : PurityVectorExpression n) :
    evaluate P (e ++ f) = evaluate P e + evaluate P f := by
  simp only [evaluate, List.map_append, List.sum_append]

omit [SMulCommClass ℝ A A] in
theorem evaluate_scale (r : ℝ) (e : PurityVectorExpression n) :
    evaluate P (scale r e) = r • evaluate P e := by
  induction e with
  | nil => simp only [scale, List.map_nil, evaluate_nil, smul_zero]
  | cons t e ih =>
      simp only [scale, List.map_cons, evaluate_cons] at ih ⊢
      rw [FiniteRealWordFunctional.amplitudeValue_scale, ih, smul_mul_assoc, smul_add]

theorem evaluate_leftMultiply (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    evaluate P (leftMultiply U e) = U.amplitudeValue P * evaluate P e := by
  induction e with
  | nil => simp only [leftMultiply, List.map_nil, evaluate_nil, mul_zero]
  | cons t e ih =>
      simp only [leftMultiply, List.map_cons, evaluate_cons] at ih ⊢
      rw [FiniteRealWordFunctional.amplitudeValue_multiply, ih, mul_add, mul_assoc]

theorem evaluate_ofPrimitiveTerms (a : Fin n) (c : Word (Fin n) → ℝ)
    (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (U : FiniteRealWordFunctional n) :
    evaluate P (ofPrimitiveTerms a c ts historyPrefix U) = U.amplitudeValue P *
      (weightedPurityResidual P a c ts * wordAmplitude P (historyPrefix ++ [(a, true)])) := by
  induction ts with
  | nil => simp only [ofPrimitiveTerms, primitiveResidualOccurrences, List.map_nil,
      evaluate_nil, weightedPurityResidual, List.sum_nil, zero_mul, mul_zero]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      simp only [ofPrimitiveTerms, primitiveResidualOccurrences, List.map_cons, evaluate_cons] at ih ⊢
      rw [ih]
      change (FiniteRealWordFunctional.scale r U).amplitudeValue P *
          (outcomePurityElement P (a, true) w (c w) *
            wordAmplitude P (historyPrefix ++ [(a, true)])) +
          U.amplitudeValue P * (weightedPurityResidual P a c ts *
            wordAmplitude P (historyPrefix ++ [(a, true)])) =
        U.amplitudeValue P * ((r • outcomePurityElement P (a, true) w (c w) +
          weightedPurityResidual P a c ts) * wordAmplitude P (historyPrefix ++ [(a, true)]))
      rw [FiniteRealWordFunctional.amplitudeValue_scale]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]

end Semantics

theorem pairAgainst_evaluate {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (φ : A →ₗ[ℝ] ℝ) (P : Fin n → A) (hstar : ∀ i, star (P i) = P i)
    (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    realStarPairing φ (U.amplitudeValue P) (evaluate P e) =
      ((pairAgainst U e).map (fun o => φ
        (star (o.leftElement P) * o.leaf.residualElement P))).sum := by
  induction e with
  | nil => simp only [pairAgainst, List.map_nil, List.sum_nil, evaluate_nil,
      realStarPairing, mul_zero, map_zero]
  | cons t e ih =>
      simp only [evaluate_cons, realStarPairing_add_right, ih,
        pairAgainst, List.map_cons, List.sum_cons]
      simp only [ResidualTelescopeOccurrence.leftElement,
        FiniteRealWordFunctional.amplitudeValue_multiply,
        FiniteRealWordFunctional.amplitudeValue_star P hstar, star_mul, star_star,
        realStarPairing, mul_assoc]

theorem hasHorizon_append (e f : PurityVectorExpression n) (L : ℕ)
    (he : e.HasHorizon L) (hf : f.HasHorizon L) : (e ++ f).HasHorizon L := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact he t h
  · exact hf t h

theorem hasHorizon_scale (e : PurityVectorExpression n) (r : ℝ) (L : ℕ)
    (he : e.HasHorizon L) : (scale r e).HasHorizon L := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact he u hu

theorem hasHorizon_leftMultiply (U : FiniteRealWordFunctional n)
    (e : PurityVectorExpression n) (L : ℕ) (he : e.HasHorizon L) :
    (leftMultiply U e).HasHorizon L := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact he u hu

theorem hasHorizon_pairAgainst (U : FiniteRealWordFunctional n)
    (e : PurityVectorExpression n) (L : ℕ) (he : e.HasHorizon L) :
    ∀ o ∈ pairAgainst U e, o.leaf.wordFunctional.HasHorizon L := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨t, ht, rfl⟩
  exact he t ht

theorem hasHorizon_ofPrimitiveTerms (a : Fin n) (c : Word (Fin n) → ℝ)
    (ts : List (ℝ × Word (Fin n))) (historyPrefix : Word (Fin n))
    (U : FiniteRealWordFunctional n) (L : ℕ)
    (h : ∀ t ∈ ts, historyPrefix.length + 1 + 2 * t.2.length ≤ L) :
    (ofPrimitiveTerms a c ts historyPrefix U).HasHorizon L := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨o, ho, rfl⟩
  exact primitiveResidualOccurrences_horizon a c ts historyPrefix U L h o ho

end PurityVectorExpression
end AlbertSequential
