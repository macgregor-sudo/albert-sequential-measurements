/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ConstructedCornerTelescope

/-! Structural calibration of every actual constructor leaf. This proof tracks
stored bases/constants through list operations; it neither expands a numerical
ledger nor assumes native purity or a horizon. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
namespace ConstructorCalibration

variable {n : ℕ}
def LeafCalibrated (C : Fin n → Word (Fin n) → ℝ) (l : SupportedPurityLeaf (Fin n)) : Prop :=
  l.outcome.2 = true ∧ l.constant = C l.outcome.1 l.suffix

def VectorCalibrated (C : Fin n → Word (Fin n) → ℝ) (e : PurityVectorExpression n) : Prop :=
  ∀ t ∈ e, LeafCalibrated C t.leaf

def OccurrencesCalibrated (C : Fin n → Word (Fin n) → ℝ)
    (e : List (ResidualTelescopeOccurrence n)) : Prop := ∀ t ∈ e, LeafCalibrated C t.leaf

theorem vector_append (C : Fin n → Word (Fin n) → ℝ) (e f : PurityVectorExpression n) :
    VectorCalibrated C (e ++ f) ↔ VectorCalibrated C e ∧ VectorCalibrated C f := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (List.mem_append_left f ht),
      fun t ht => h t (List.mem_append_right e ht)⟩
  · rintro ⟨he, hf⟩ t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact he t ht
    · exact hf t ht

theorem vector_scale (C : Fin n → Word (Fin n) → ℝ) (r : ℝ) (e : PurityVectorExpression n) :
    VectorCalibrated C (PurityVectorExpression.scale r e) ↔ VectorCalibrated C e := by
  simp only [VectorCalibrated, PurityVectorExpression.scale, List.forall_mem_map]

theorem vector_leftMultiply (C : Fin n → Word (Fin n) → ℝ)
    (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    VectorCalibrated C (PurityVectorExpression.leftMultiply U e) ↔ VectorCalibrated C e := by
  simp only [VectorCalibrated, PurityVectorExpression.leftMultiply, List.forall_mem_map]

theorem vector_primitive (C : Fin n → Word (Fin n) → ℝ) (a : Fin n)
    (ts : List (ℝ × Word (Fin n))) (t : Word (Fin n)) (U : FiniteRealWordFunctional n) :
    VectorCalibrated C (PurityVectorExpression.ofPrimitiveTerms a (C a) ts t U) := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨o, ho, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, _hu, rfl⟩
  exact ⟨rfl, rfl⟩

theorem occurrences_scale (C : Fin n → Word (Fin n) → ℝ) (r : ℝ)
    (e : List (ResidualTelescopeOccurrence n)) :
    OccurrencesCalibrated C (ResidualOccurrenceExpression.scale r e) ↔ OccurrencesCalibrated C e := by
  simp only [OccurrencesCalibrated, ResidualOccurrenceExpression.scale, List.forall_mem_map]

theorem occurrences_pairAgainst (C : Fin n → Word (Fin n) → ℝ)
    (U : FiniteRealWordFunctional n) (e : PurityVectorExpression n) :
    OccurrencesCalibrated C (PurityVectorExpression.pairAgainst U e) ↔ VectorCalibrated C e := by
  simp only [OccurrencesCalibrated, VectorCalibrated, PurityVectorExpression.pairAgainst,
    List.forall_mem_map]

theorem occurrences_combine (C : Fin n → Word (Fin n) → ℝ)
    (es : List (List (ResidualTelescopeOccurrence n))) :
    OccurrencesCalibrated C (ResidualOccurrenceExpression.combine es) ↔
      ∀ e ∈ es, OccurrencesCalibrated C e := by
  simp only [OccurrencesCalibrated, ResidualOccurrenceExpression.combine, List.mem_flatten]
  constructor
  · intro h e he o ho; exact h o ⟨e, he, ho⟩
  · intro h o ⟨e, he, ho⟩; exact h e he o ho

open CornerResidualBuilder
variable (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ)

private theorem pairOnWord_calibrated (a b : Fin 4) (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) :
    VectorCalibrated C (pairOnWord C a b t U) := vector_primitive C a _ t U
private theorem pairBaseOnPath_calibrated (b : Fin 4) (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    VectorCalibrated C (pairBaseOnPath C b p U) := vector_primitive C 0 _ _ U
private theorem triangleBaseOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    VectorCalibrated C (triangleBaseOnPath C i p U) := vector_primitive C 0 _ _ U
private theorem tripleBaseOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) (U : FiniteRealWordFunctional 4) :
    VectorCalibrated C (tripleBaseOnPath C i p U) := vector_primitive C 0 _ _ _
private theorem triangleFarOnWord_calibrated (t : Word (Fin 4)) (U : FiniteRealWordFunctional 4) :
    VectorCalibrated C (triangleFarOnWord C t U) := vector_primitive C 1 _ t U

private theorem hermitianOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (hermitianOnPath d C i p) := triangleBaseOnPath_calibrated C i p _
private theorem reverseProductOnPath_calibrated (k l : Fin 4) (p : List (Fin 6)) :
    VectorCalibrated C (reverseProductOnPath d C k l p) := by
  simp only [reverseProductOnPath, vector_append, pairOnWord_calibrated,
    pairBaseOnPath_calibrated, and_self]
private theorem leftUnitarityOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (leftUnitarityOnPath d C i p) := by
  rw [leftUnitarityOnPath, vector_scale]
  exact reverseProductOnPath_calibrated d C _ _ p
private theorem rightUnitarityOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (rightUnitarityOnPath d C i p) := by
  rw [rightUnitarityOnPath, vector_scale]
  exact reverseProductOnPath_calibrated d C _ _ p
private theorem squareOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (squareOnPath d C i p) := by
  simp only [squareOnPath, vector_append, vector_leftMultiply, vector_scale,
    hermitianOnPath_calibrated, rightUnitarityOnPath_calibrated, leftUnitarityOnPath_calibrated, and_self]

private theorem extendPaths_calibrated (f : List (Fin 6) → PurityVectorExpression 4)
    (hf : ∀ p, VectorCalibrated C (f p)) (e : HolonomyPath.Combination) :
    VectorCalibrated C (extendPaths d f e) := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨u, _hu, htu⟩
  exact (vector_scale C _ _).mpr (hf u.2) t htu
private theorem hermitianOnCombination_calibrated (i : Fin 3) (e : HolonomyPath.Combination) :
    VectorCalibrated C (hermitianOnCombination d C i e) :=
  extendPaths_calibrated d C _ (hermitianOnPath_calibrated d C i) e
private theorem squareOnCombination_calibrated (i : Fin 3) (e : HolonomyPath.Combination) :
    VectorCalibrated C (squareOnCombination d C i e) :=
  extendPaths_calibrated d C _ (squareOnPath_calibrated d C i) e
private theorem mixedOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (mixedOnPath d C i p) := by
  simp only [mixedOnPath, vector_scale, vector_append, pairOnWord_calibrated,
    tripleBaseOnPath_calibrated, and_self]
private theorem pairOnPath_calibrated (i : Fin 3) (p : List (Fin 6)) :
    VectorCalibrated C (pairOnPath d C i p) := by
  simp only [pairOnPath, vector_scale, vector_append, vector_leftMultiply,
    mixedOnPath_calibrated, hermitianOnPath_calibrated, and_self]
private theorem pairOnCombination_calibrated (i : Fin 3) (e : HolonomyPath.Combination) :
    VectorCalibrated C (pairOnCombination d C i e) :=
  extendPaths_calibrated d C _ (pairOnPath_calibrated d C i) e
private theorem allPairs_calibrated (e : HolonomyPath.Combination) (i j : Fin 3) :
    VectorCalibrated C (allPairs d C e i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [allPairs, Matrix.cons_val_zero', Matrix.cons_val_succ', vector_scale,
      squareOnCombination_calibrated, pairOnCombination_calibrated]
private theorem cubicAtBase_calibrated : VectorCalibrated C (cubicAtBase d C) := by
  simp only [cubicAtBase, vector_scale, vector_append, pairOnWord_calibrated,
    pairBaseOnPath_calibrated, triangleFarOnWord_calibrated, and_self]
private theorem hermitianProductAtBase_calibrated : VectorCalibrated C (hermitianProductAtBase d C) := by
  simp only [hermitianProductAtBase, vector_scale, vector_append, vector_leftMultiply,
    hermitianOnCombination_calibrated, and_self]
private theorem dataAtBase_calibrated : VectorCalibrated C (dataAtBase d C) := by
  simp only [dataAtBase, vector_append, vector_scale, cubicAtBase_calibrated,
    hermitianProductAtBase_calibrated, allPairs_calibrated, and_self]
private theorem volumeAtBase_calibrated : VectorCalibrated C (volumeAtBase d C) := by
  simp only [volumeAtBase, vector_append, vector_scale, vector_leftMultiply, allPairs_calibrated, and_self]
private theorem gramAtBase_calibrated (i j : Fin 3) : OccurrencesCalibrated C (gramAtBase d C i j) := by
  simp only [gramAtBase, occurrences_scale, occurrences_pairAgainst, allPairs_calibrated]
private theorem crossAtBase_calibrated (i : Fin 3) : OccurrencesCalibrated C (crossAtBase d C i) := by
  fin_cases i <;>
    simp only [crossAtBase, Matrix.cons_val_zero', Matrix.cons_val_succ',
      crossFirstAtBase, crossSecondAtBase, crossThirdAtBase, occurrences_combine,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      occurrences_scale, occurrences_pairAgainst, vector_append, vector_leftMultiply, vector_scale,
      gramAtBase_calibrated, squareOnCombination_calibrated, allPairs_calibrated, and_self]
private theorem normAtBase_calibrated : OccurrencesCalibrated C (normAtBase d C) := by
  simp only [normAtBase, occurrences_combine, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, occurrences_scale, occurrences_pairAgainst,
    squareOnCombination_calibrated, and_self]
private theorem gramRowAtBase_calibrated (i : Fin 3) : OccurrencesCalibrated C (gramRowAtBase d C i) := by
  simp only [gramRowAtBase, occurrences_combine, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, occurrences_scale, gramAtBase_calibrated, and_self]

theorem cornerResidualTelescope_calibrated :
    OccurrencesCalibrated C (cornerResidualTelescopeOccurrences d C) := by
  simp only [cornerResidualTelescopeOccurrences, occurrences_combine,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    occurrences_scale, occurrences_pairAgainst, dataAtBase_calibrated,
    volumeAtBase_calibrated, normAtBase_calibrated, crossAtBase_calibrated, gramRowAtBase_calibrated, and_self]

end ConstructorCalibration
end AlbertSequential
