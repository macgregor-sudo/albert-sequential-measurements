/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WordRelabelling
public import ResidualOccurrenceAlgebra

/-! Relabel actual supported leaves and pairings together. Label maps need
not be injective; preservation of reducedness is deliberately not asserted. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem purityMirror_relabel {ι κ : Type*} (f : ι → κ) (w : Word ι) :
    purityMirror (relabelWord f w) = relabelWord f (purityMirror w) := by
  simp only [purityMirror, relabelWord, List.map_reverse, List.map_dropLast]

namespace SupportedPurityLeaf
variable {ι κ : Type*}

def relabel (f : ι → κ) (l : SupportedPurityLeaf ι) : SupportedPurityLeaf κ where
  historyPrefix := relabelWord f l.historyPrefix
  outcome := relabelOutcome f l.outcome
  suffix := relabelWord f l.suffix
  constant := l.constant

theorem history_relabel (f : ι → κ) (l : SupportedPurityLeaf ι) :
    (relabel f l).history = relabelWord f l.history := by
  simp only [history, relabel, relabelWord_append, relabelWord_cons, relabelWord_nil]

theorem shortWord_relabel (f : ι → κ) (l : SupportedPurityLeaf ι) :
    (relabel f l).shortWord = relabelWord f l.shortWord := history_relabel f l

theorem middleWord_relabel (f : ι → κ) (l : SupportedPurityLeaf ι) :
    (relabel f l).middleWord = relabelWord f l.middleWord := by
  rw [middleWord, middleWord, history_relabel, relabelWord_append]
  rfl

theorem longWord_relabel (f : ι → κ) (l : SupportedPurityLeaf ι) :
    (relabel f l).longWord = relabelWord f l.longWord := by
  cases hv : l.suffix with
  | nil =>
      simpa only [longWord, relabel, hv, relabelWord_nil] using history_relabel f l
  | cons a w =>
      simp only [longWord, relabel, hv, relabelWord_cons, relabelWord_append,
        ← purityMirror_relabel, relabelWord_nil]
      simp only [history, relabelWord_append, relabelWord_cons, relabelWord_nil]

theorem residualElement_relabel {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : κ → A) (f : ι → κ) (l : SupportedPurityLeaf ι) :
    (relabel f l).residualElement P = l.residualElement (P ∘ f) := by
  rw [residualElement, residualElement, history_relabel, wordAmplitude_relabel]
  change outcomePurityElement P (relabelOutcome f l.outcome) (relabelWord f l.suffix) l.constant * _ = _
  simp only [outcomePurityElement, algebraicOutcome_relabel, wordOperator_relabel]

theorem wordFunctional_relabel {m n : ℕ} (f : Fin m → Fin n) (l : SupportedPurityLeaf (Fin m)) :
    (relabel f l).wordFunctional = FiniteRealWordFunctional.relabel f l.wordFunctional := by
  simp only [wordFunctional, FiniteRealWordFunctional.relabel, longWord_relabel,
    middleWord_relabel, shortWord_relabel, List.map_cons, List.map_nil]
  rfl

theorem wordFunctional_hasHorizon_relabel {m n : ℕ} (f : Fin m → Fin n)
    (l : SupportedPurityLeaf (Fin m)) (L : ℕ) (hl : l.wordFunctional.HasHorizon L) :
    (relabel f l).wordFunctional.HasHorizon L := by
  rw [wordFunctional_relabel]
  exact FiniteRealWordFunctional.hasHorizon_relabel f _ L hl

end SupportedPurityLeaf

namespace ResidualTelescopeOccurrence
variable {m n : ℕ}

def relabel (f : Fin m → Fin n) (o : ResidualTelescopeOccurrence m) : ResidualTelescopeOccurrence n where
  leaf := SupportedPurityLeaf.relabel f o.leaf
  leftTerms := FiniteRealWordFunctional.relabel f o.leftTerms

theorem leftElement_relabel {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (f : Fin m → Fin n) (o : ResidualTelescopeOccurrence m) :
    (relabel f o).leftElement P = o.leftElement (P ∘ f) := by
  exact FiniteRealWordFunctional.amplitudeValue_relabel P f o.leftTerms

end ResidualTelescopeOccurrence

namespace ResidualOccurrenceExpression
variable {m n : ℕ}

def relabel (f : Fin m → Fin n) (es : List (ResidualTelescopeOccurrence m)) :
    List (ResidualTelescopeOccurrence n) := es.map (ResidualTelescopeOccurrence.relabel f)

theorem value_relabel {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (φ : A →ₗ[ℝ] ℝ) (P : Fin n → A) (f : Fin m → Fin n)
    (es : List (ResidualTelescopeOccurrence m)) :
    value φ P (relabel f es) = value φ (P ∘ f) es := by
  simp only [value, relabel, List.map_map, Function.comp_def,
    ResidualTelescopeOccurrence.leftElement_relabel]
  simp only [ResidualTelescopeOccurrence.relabel, SupportedPurityLeaf.residualElement_relabel]
  rfl

theorem hasHorizon_relabel (f : Fin m → Fin n) (es : List (ResidualTelescopeOccurrence m)) (L : ℕ)
    (he : HasHorizon es L) : HasHorizon (relabel f es) L := by
  intro o ho
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  exact SupportedPurityLeaf.wordFunctional_hasHorizon_relabel f u.leaf L (he u hu)

end ResidualOccurrenceExpression
end AlbertSequential
