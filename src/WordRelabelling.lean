/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WordAmplitudeAlgebra

/-! Arbitrary label maps preserve chronology and length. No injectivity,
faithfulness, trace or dimension condition is imposed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def relabelOutcome {ι κ : Type*} (f : ι → κ) (a : Outcome ι) : Outcome κ := (f a.1, a.2)
def relabelWord {ι κ : Type*} (f : ι → κ) (w : Word ι) : Word κ := w.map (relabelOutcome f)

theorem relabelWord_nil {ι κ : Type*} (f : ι → κ) : relabelWord f [] = [] := rfl
theorem relabelWord_cons {ι κ : Type*} (f : ι → κ) (a : Outcome ι) (w : Word ι) :
    relabelWord f (a :: w) = relabelOutcome f a :: relabelWord f w := rfl
theorem relabelWord_append {ι κ : Type*} (f : ι → κ) (u v : Word ι) :
    relabelWord f (u ++ v) = relabelWord f u ++ relabelWord f v := List.map_append
theorem relabelWord_length {ι κ : Type*} (f : ι → κ) (w : Word ι) :
    (relabelWord f w).length = w.length := List.length_map _
theorem relabelWord_reverse {ι κ : Type*} (f : ι → κ) (w : Word ι) :
    relabelWord f w.reverse = (relabelWord f w).reverse := List.map_reverse

theorem algebraicOutcome_relabel {ι κ A : Type*} [Ring A] (P : κ → A) (f : ι → κ) (a : Outcome ι) :
    algebraicOutcome P (relabelOutcome f a) = algebraicOutcome (P ∘ f) a := rfl

theorem wordAmplitude_relabel {ι κ A : Type*} [Ring A] (P : κ → A) (f : ι → κ) (w : Word ι) :
    wordAmplitude P (relabelWord f w) = wordAmplitude (P ∘ f) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [relabelWord_cons, wordAmplitude_cons, wordAmplitude_cons, ih, algebraicOutcome_relabel]

theorem wordOperator_relabel {ι κ A : Type*} [Ring A] [StarRing A]
    (P : κ → A) (f : ι → κ) (w : Word ι) :
    wordOperator P (relabelWord f w) = wordOperator (P ∘ f) w := by
  simp only [wordOperator, wordAmplitude_relabel]

namespace AlgebraicProjectiveData
variable {ι κ A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

def comap (f : ι → κ) (M : AlgebraicProjectiveData κ A) : AlgebraicProjectiveData ι A where
  projection := M.projection ∘ f
  idempotent := fun i => M.idempotent (f i)
  selfAdjoint := fun i => M.selfAdjoint (f i)
  state := M.state
  state_unit := M.state_unit
  state_star := M.state_star
  state_positive := M.state_positive

theorem comap_probability (M : AlgebraicProjectiveData κ A) (f : ι → κ) (w : Word ι) :
    (comap f M).probability w = M.probability (relabelWord f w) := by
  simp only [probability, comap, wordOperator_relabel]

end AlgebraicProjectiveData

namespace FiniteRealWordFunctional
variable {m n : ℕ}

def relabel (f : Fin m → Fin n) (c : FiniteRealWordFunctional m) : FiniteRealWordFunctional n where
  terms := c.terms.map (fun t => (t.1, relabelWord f t.2))

theorem evaluate_relabel (f : Fin m → Fin n) (c : FiniteRealWordFunctional m)
    (g : Word (Fin n) → ℝ) :
    (relabel f c).evaluate g = c.evaluate (fun w => g (relabelWord f w)) := by
  simp only [relabel, evaluate, List.map_map, Function.comp_def]

theorem amplitudeValue_relabel {A : Type*} [Ring A] [Module ℝ A]
    (P : Fin n → A) (f : Fin m → Fin n) (c : FiniteRealWordFunctional m) :
    (relabel f c).amplitudeValue P = c.amplitudeValue (P ∘ f) := by
  simp only [relabel, amplitudeValue, wordAmplitudeCombination, List.map_map,
    Function.comp_def, wordAmplitude_relabel]

theorem rawCoefficientBound_relabel (f : Fin m → Fin n) (c : FiniteRealWordFunctional m) :
    (relabel f c).rawCoefficientBound = c.rawCoefficientBound := by
  simp only [relabel, rawCoefficientBound, wordAmplitudeCoefficientBound, List.map_map, Function.comp_def]

theorem hasHorizon_relabel (f : Fin m → Fin n) (c : FiniteRealWordFunctional m) (L : ℕ)
    (hc : c.HasHorizon L) : (relabel f c).HasHorizon L := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  simpa only [relabelWord_length] using hc u hu

end FiniteRealWordFunctional
end AlbertSequential
