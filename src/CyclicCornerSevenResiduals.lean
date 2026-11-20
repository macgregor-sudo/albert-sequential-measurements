/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicGeneratedPurity
public import BlockB.ElevenCore

@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis CornerResidualBuilder ConstructorCalibration CornerHolonomy

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance cyclicCornerSevenResidualsSourceAlgebra : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def CyclicAnchoredSevenMatch (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (ρ : Albert) : Prop :=
  ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
    M.probability w = nativeWordProbability p ρ w

private def AnchoredLeaves (C : Fin 4 → Word (Fin 4) → ℝ) (e : PurityVectorExpression 4) : Prop :=
  ∀ t ∈ e, LeafCalibrated C t.leaf ∧ t.leaf.shortWord.head? = some (0, true)

private theorem anchored_append (C : Fin 4 → Word (Fin 4) → ℝ) (e f : PurityVectorExpression 4) :
    AnchoredLeaves C (e ++ f) ↔ AnchoredLeaves C e ∧ AnchoredLeaves C f := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (List.mem_append_left f ht), fun t ht => h t (List.mem_append_right e ht)⟩
  · rintro ⟨he, hf⟩ t ht
    exact (List.mem_append.mp ht).elim (he t) (hf t)

private theorem anchored_scale (C : Fin 4 → Word (Fin 4) → ℝ) (r : ℝ) (e : PurityVectorExpression 4) :
    AnchoredLeaves C (PurityVectorExpression.scale r e) ↔ AnchoredLeaves C e := by
  simp only [AnchoredLeaves, PurityVectorExpression.scale, List.forall_mem_map]

private theorem anchored_primitive (C : Fin 4 → Word (Fin 4) → ℝ) (a : Fin 4)
    (ts : List (ℝ × Word (Fin 4))) (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4)
    (ht : (t ++ [(a, true)]).head? = some (0, true)) :
    AnchoredLeaves C (PurityVectorExpression.ofPrimitiveTerms a (C a) ts t U) := by
  intro v hv
  have hc := vector_primitive C a ts t U v hv
  rcases List.mem_map.mp hv with ⟨o, ho, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, _, rfl⟩
  exact ⟨hc, ht⟩

private theorem hermitianAtBase_anchored (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) : AnchoredLeaves C (hermitianOnPath d C i []) :=
  anchored_primitive C 0 _ _ _ rfl

private theorem reverseProductAtBase_anchored (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (k l : Fin 4) : AnchoredLeaves C (reverseProductOnPath d C k l []) := by
  simp only [reverseProductOnPath, anchored_append, pairOnWord, pairBaseOnPath]
  exact ⟨⟨anchored_primitive C _ _ _ _ rfl, anchored_primitive C _ _ _ _ rfl⟩,
    anchored_primitive C _ _ _ _ rfl⟩

private theorem mixedAtBase_anchored (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)
    (i : Fin 3) : AnchoredLeaves C (mixedOnPath d C i []) := by
  simp only [mixedOnPath, anchored_scale, anchored_append, pairOnWord, tripleBaseOnPath]
  exact ⟨⟨anchored_primitive C _ _ _ _ rfl, anchored_primitive C _ _ _ _ rfl⟩,
    anchored_primitive C _ _ _ _ rfl⟩

private theorem cubicAtBase_anchored (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) :
    AnchoredLeaves C (cubicAtBase d C) := by
  simp only [cubicAtBase, anchored_scale, anchored_append, pairOnWord, triangleFarOnWord, pairBaseOnPath]
  exact ⟨⟨⟨⟨⟨anchored_primitive C _ _ _ _ rfl, anchored_primitive C _ _ _ _ rfl⟩,
    anchored_primitive C _ _ _ _ rfl⟩, anchored_primitive C _ _ _ _ rfl⟩,
    anchored_primitive C _ _ _ _ rfl⟩, anchored_primitive C _ _ _ _ rfl⟩

private theorem head_of_leaf_term (l : SupportedPurityLeaf (Fin 4))
    (h : l.shortWord.head? = some (0, true)) (t : ℝ × Word (Fin 4))
    (ht : t ∈ l.wordFunctional.terms) : t.2.head? = some (0, true) := by
  have hh (s : Word (Fin 4)) : (l.history ++ s).head? = some (0, true) := by
    rw [List.head?_append, ← SupportedPurityLeaf.shortWord, h]
    rfl
  simp only [SupportedPurityLeaf.wordFunctional, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · cases hs : l.suffix with
    | nil => simpa only [SupportedPurityLeaf.longWord, hs, SupportedPurityLeaf.shortWord] using h
    | cons q w =>
      simp only [SupportedPurityLeaf.longWord, hs, List.append_assoc]
      exact hh _
  · exact hh _
  · exact h

/-- A stored three-word leaf is the squared norm of its literal cyclic residual. -/
theorem cyclicSupportedLeaf_norm_sq (M : AlgebraicProjectiveData (Fin 4) A)
    (l : SupportedPurityLeaf (Fin 4)) :
    ‖l.residualElement (cyclicHilbertProjection M) (cyclicHilbertVector M)‖ ^ 2 =
      l.wordFunctional.evaluate M.probability := by
  rw [SupportedPurityLeaf.residualElement, mul_apply_eq_comp, ← cyclicPurityElement_representation,
    cyclic_history_norm_sq, cyclicPurityElement_value, ← SupportedPurityLeaf.residualElement,
    l.residual_eq_wordFunctional M]

private theorem cyclic_anchoredExpression_zero (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hm : CyclicAnchoredSevenMatch M p ρ)
    (e : PurityVectorExpression 4)
    (he : e.HasHorizon 7) (ha : AnchoredLeaves (BlockB.atomCornerScalar p) e) :
    PurityVectorExpression.evaluate (cyclicHilbertProjection M) e (cyclicHilbertVector M) = 0 := by
  induction e with
  | nil => rw [PurityVectorExpression.evaluate_nil]; rfl
  | cons t e ih =>
    have ht := ha t (List.mem_cons_self)
    have hmatch (u : ℝ × Word (Fin 4)) (hu : u ∈ t.leaf.wordFunctional.terms) :
        M.probability u.2 = nativeWordProbability p ρ u.2 :=
      hm u.2 (he t List.mem_cons_self u hu) (head_of_leaf_term t.leaf ht.2 u hu)
    have hval : t.leaf.wordFunctional.evaluate M.probability =
        t.leaf.wordFunctional.evaluate (nativeWordProbability p ρ) := by
      unfold FiniteRealWordFunctional.evaluate
      exact congrArg List.sum (List.map_congr_left fun u hu => congrArg (u.1 * ·) (hmatch u hu))
    have hn := cyclicSupportedLeaf_norm_sq M t.leaf
    rw [hval, BlockB.atomCorner_leaf_native_zero p hp ρ t.leaf ht.1] at hn
    have hz := norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hn)
    rw [PurityVectorExpression.evaluate_cons, add_apply, mul_apply_eq_comp, hz,
      map_zero, ih (fun u hu => he u (List.mem_cons_of_mem _ hu))
        (fun u hu => ha u (List.mem_cons_of_mem _ hu)), zero_add]

attribute [local irreducible] fourPointInvariant

/-- All the printed holonomy defects annihilate the actual affirmative-A vector
already from matching the measured words of length at most seven beginning at A. -/
theorem cyclic_seven_corner_defects (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hm : CyclicAnchoredSevenMatch M p ρ) :
    let P := cyclicHilbertProjection M
    let d := BlockB.atomCornerData p
    let h := normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2
    let ξ := P 0 (cyclicHilbertVector M)
    (∀ i, hermitianDefect (P 0) (h i) (d.hermitianConstants i) ξ = 0 ∧
      leftUnitarityDefect (P 0) (h i) ξ = 0 ∧ rightUnitarityDefect (P 0) (h i) ξ = 0) ∧
    (∀ i, pairProductDefect (P 0) (h i) (h (nextHolonomy i)) (mixedConstant d i) ξ = 0) ∧
    cornerCubicDefect (P 0) h d.cubicConstant ξ = 0 := by
  let P := cyclicHilbertProjection M
  let d := BlockB.atomCornerData p
  let C := BlockB.atomCornerScalar p
  have hi (i : Fin 4) : P i * P i = P i := (cyclicHilbertProjection_isStarProjection M i).isIdempotentElem.eq
  have hs (i : Fin 4) : star (P i) = P i := (cyclicHilbertProjection_isStarProjection M i).isSelfAdjoint.star_eq
  have hc := BlockB.atomCorner_conditions p hp hA
  have hz (e : PurityVectorExpression 4) (he : e.HasHorizon 7) (ha : AnchoredLeaves C e) :=
    cyclic_anchoredExpression_zero M p hp ρ hm e he ha
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun i => ?_, ?_⟩
  · have h := hz _ (hasHorizon_mono (hermitianOnPath_horizon d C i []) (by decide))
      (hermitianAtBase_anchored d C i)
    rw [hermitianOnPath_value P hi hs d C hc] at h
    exact h
  · have h := hz _ (hasHorizon_mono (leftUnitarityOnPath_horizon d C i []) (by decide))
      ((anchored_scale C _ _).mpr (reverseProductAtBase_anchored d C _ _))
    rw [leftUnitarityOnPath_value P hi hs d C hc] at h
    exact h
  · have h := hz _ (hasHorizon_mono (rightUnitarityOnPath_horizon d C i []) (by decide))
      ((anchored_scale C _ _).mpr (reverseProductAtBase_anchored d C _ _))
    rw [rightUnitarityOnPath_value P hi hs d C hc] at h
    exact h
  · have h := hz _ (mixedOnPath_horizon d C i []) (mixedAtBase_anchored d C i)
    rw [mixedOnPath_value P hi hs d C hc] at h
    exact h
  · have h := hz _ (hasHorizon_mono (cubicAtBase_horizon d C) (by decide)) (cubicAtBase_anchored d C)
    rw [cubicAtBase_value P hi hs d C hc] at h
    exact h

end AlbertSequential
