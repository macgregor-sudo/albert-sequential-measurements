/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PrimitiveResidualOccurrences

/-! Literal finite primitive access lists: multiplicities and actual word
lengths, rather than a reduced/deduplicated purity ledger. -/
@[expose] public section
namespace AlbertSequential

theorem accessWordTerms_length {ι : Type*} (i : ι) (w : Word ι) :
    (accessWordTerms i w).length = 3 := rfl

theorem accessWordTerms_wordLength {ι : Type*} (i : ι) (w : Word ι)
    (t : ℝ × Word ι) (ht : t ∈ accessWordTerms i w) : t.2.length ≤ w.length + 1 := by
  simp only [accessWordTerms, signedAccessChoices, List.map_cons, List.map_nil,
    accessPrefix, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact Nat.le_add_right _ _
  · exact le_refl _
  · exact le_refl _

theorem scaleWordTerms_length {ι : Type*} (r : ℝ) (ts : List (ℝ × Word ι)) :
    (scaleWordTerms r ts).length = ts.length := by exact List.length_map _

theorem scaleWordTerms_wordLength {ι : Type*} (r : ℝ) (ts : List (ℝ × Word ι))
    (L : ℕ) (h : ∀ t ∈ ts, t.2.length ≤ L) :
    ∀ u ∈ scaleWordTerms r ts, u.2.length ≤ L := by
  intro u hu
  rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
  exact h t ht

theorem accessLiftWordTerms_length {ι : Type*} (i : ι) (ts : List (ℝ × Word ι)) :
    (accessLiftWordTerms i ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [accessLiftWordTerms, List.flatMap_cons, List.length_append,
        scaleWordTerms_length, accessWordTerms_length] at ih ⊢
      rw [ih, List.length_cons]
      omega

theorem accessLiftWordTerms_wordLength {ι : Type*} (i : ι) (ts : List (ℝ × Word ι))
    (L : ℕ) (h : ∀ t ∈ ts, t.2.length ≤ L) :
    ∀ u ∈ accessLiftWordTerms i ts, u.2.length ≤ L + 1 := by
  intro u hu
  rcases List.mem_flatMap.mp hu with ⟨t, ht, hu⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  exact (accessWordTerms_wordLength i t.2 v hv).trans (Nat.add_le_add_right (h t ht) 1)

theorem doubleAccessWordTerms_length {ι : Type*} (k l m : ι) :
    (doubleAccessWordTerms k l m).length = 9 := by
  rw [doubleAccessWordTerms, accessLiftWordTerms_length, accessWordTerms_length]

theorem doubleAccessWordTerms_wordLength {ι : Type*} (k l m : ι) :
    ∀ t ∈ doubleAccessWordTerms k l m, t.2.length ≤ 3 := by
  apply accessLiftWordTerms_wordLength k _ 2
  intro t ht
  exact accessWordTerms_wordLength l [(m, true)] t ht

theorem polarizedTripleWordTerms_length {ι : Type*} (k l m : ι) :
    (polarizedTripleWordTerms k l m).length = 27 := by
  simp only [polarizedTripleWordTerms, List.length_append, scaleWordTerms_length,
    doubleAccessWordTerms_length]

theorem polarizedTripleWordTerms_wordLength {ι : Type*} (k l m : ι) :
    ∀ t ∈ polarizedTripleWordTerms k l m, t.2.length ≤ 3 := by
  intro t ht
  have hmem : t ∈ doubleAccessWordTerms k l m ∨ t ∈ doubleAccessWordTerms m k l ∨
      t ∈ scaleWordTerms (-1) (doubleAccessWordTerms l k m) := by
    simpa only [polarizedTripleWordTerms, List.mem_append, or_assoc] using ht
  rcases hmem with h | h | h
  · exact doubleAccessWordTerms_wordLength k l m t h
  · exact doubleAccessWordTerms_wordLength m k l t h
  · exact scaleWordTerms_wordLength (-1) _ 3 (doubleAccessWordTerms_wordLength l k m) t h

theorem trianglePrimitiveOccurrences_horizon {n : ℕ} (a b d : Fin n)
    (c : Word (Fin n) → ℝ) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) :
    ∀ o ∈ primitiveResidualOccurrences a c (accessWordTerms b [(d, true)]) historyPrefix left,
      o.leaf.wordFunctional.HasHorizon (historyPrefix.length + 5) := by
  apply primitiveResidualOccurrences_horizon
  intro t ht
  have h := accessWordTerms_wordLength b [(d, true)] t ht
  simp only [List.length_singleton] at h
  omega

theorem triplePrimitiveOccurrences_horizon {n : ℕ} (a k l m : Fin n)
    (c : Word (Fin n) → ℝ) (historyPrefix : Word (Fin n))
    (left : FiniteRealWordFunctional n) :
    ∀ o ∈ primitiveResidualOccurrences a c (polarizedTripleWordTerms k l m) historyPrefix left,
      o.leaf.wordFunctional.HasHorizon (historyPrefix.length + 7) := by
  apply primitiveResidualOccurrences_horizon
  intro t ht
  have h := polarizedTripleWordTerms_wordLength k l m t ht
  omega

end AlbertSequential
